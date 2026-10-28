package com.holmes.leanqr;

import android.app.Activity;
import android.content.ClipData;
import android.content.ContentProvider;
import android.content.ContentValues;
import android.content.Intent;
import android.database.Cursor;
import android.graphics.Bitmap;
import android.graphics.ImageDecoder;
import android.net.Uri;
import android.os.ParcelFileDescriptor;
import android.provider.MediaStore;
import android.util.Log;
import android.widget.Button;
import android.widget.HorizontalScrollView;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.TextView;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * The composer's image tools, as little native code as the platform
 * allows: the system Photo Picker (multi-select) and the system camera
 * (ACTION_IMAGE_CAPTURE into an app-private file), each decoded by the
 * platform's ImageDecoder (which applies EXIF orientation), downsampled to
 * the size Lean's `fit` gives (at most 2048 px on the longer side), and
 * handed to Lean as RGBA. Lean checks it, stores it as QOI and draws the
 * tray; this shows Lean's tray as it is. Native code: Pics.java (this)
 * and jni/pic_jni.c.
 */
public final class Pics {
  static final String TAG = "LeanPics";
  static final int REQ_PHOTOS = 7001;
  static final int REQ_CAMERA = 7002;
  static final int EDGE = 2048;
  static final int TRAY = 240;  // the tray's height in pixels

  // Lean (pic_jni.c -> Pic/Composer.lean)
  static native long fit(int w, int h, int edge);
  static native String add(int ow, int oh, ByteBuffer rgba, int w, int h);
  static native byte[] tray(int height);
  static native byte[] blob(int i);

  private final Activity activity;
  private final ExecutorService work = Executors.newSingleThreadExecutor();
  private final ImageView trayView;
  private final TextView info;
  private File capture;
  private int stored;

  /** The bar: Photos and Camera buttons, the tray, and what was added. */
  Pics(Activity a, LinearLayout bar) {
    activity = a;
    // A capture whose process died before it was read is nobody's.
    File[] left = new File(a.getCacheDir(), "captures").listFiles();
    if (left != null) for (File f : left) f.delete();
    LinearLayout buttons = new LinearLayout(a);
    Button photos = new Button(a);
    photos.setText("Photos");
    photos.setContentDescription("pics-photos");
    photos.setOnClickListener(v -> pickPhotos());
    Button camera = new Button(a);
    camera.setText("Camera");
    camera.setContentDescription("pics-camera");
    camera.setOnClickListener(v -> takePhoto());
    buttons.addView(photos);
    buttons.addView(camera);
    trayView = new ImageView(a);
    trayView.setContentDescription("pics-tray");
    HorizontalScrollView scroll = new HorizontalScrollView(a);
    scroll.addView(trayView);
    info = new TextView(a);
    info.setTextColor(0xFFFFFFFF);
    info.setContentDescription("pics-info");
    bar.addView(buttons);
    bar.addView(scroll);
    bar.addView(info);
  }

  void pickPhotos() {
    Intent i = new Intent(MediaStore.ACTION_PICK_IMAGES).setType("image/*")
        .putExtra(MediaStore.EXTRA_PICK_IMAGES_MAX, MediaStore.getPickImagesMaxLimit());
    activity.startActivityForResult(i, REQ_PHOTOS);
  }

  void takePhoto() {
    File dir = new File(activity.getCacheDir(), "captures");
    dir.mkdirs();
    capture = new File(dir, "capture-" + System.currentTimeMillis() + ".jpg");
    Intent i = new Intent(MediaStore.ACTION_IMAGE_CAPTURE)
        .putExtra(MediaStore.EXTRA_OUTPUT, Out.uri(capture))
        .addFlags(Intent.FLAG_GRANT_WRITE_URI_PERMISSION | Intent.FLAG_GRANT_READ_URI_PERMISSION);
    activity.startActivityForResult(i, REQ_CAMERA);
  }

  /** From the activity's onActivityResult. */
  boolean onResult(int req, int res, Intent data) {
    if (req != REQ_PHOTOS && req != REQ_CAMERA) return false;
    List<ImageDecoder.Source> sources = new ArrayList<>();
    File taken = req == REQ_CAMERA ? capture : null;
    if (res == Activity.RESULT_OK) {
      if (taken != null) sources.add(ImageDecoder.createSource(taken));
      else if (data != null && data.getClipData() != null) {
        ClipData c = data.getClipData();
        for (int k = 0; k < c.getItemCount(); k++) sources.add(source(c.getItemAt(k).getUri()));
      } else if (data != null && data.getData() != null) sources.add(source(data.getData()));
    }
    work.execute(() -> {
      for (ImageDecoder.Source s : sources) take(s);
      if (taken != null) {
        activity.revokeUriPermission(Out.uri(taken),
            Intent.FLAG_GRANT_WRITE_URI_PERMISSION | Intent.FLAG_GRANT_READ_URI_PERMISSION);
        taken.delete();
      }
    });
    return true;
  }

  private ImageDecoder.Source source(Uri u) {
    return ImageDecoder.createSource(activity.getContentResolver(), u);
  }

  /** Decode, downsample to Lean's fit, hand over RGBA, show Lean's tray. */
  private void take(ImageDecoder.Source s) {
    int[] orig = new int[2];
    String said;
    try {
      Bitmap b = ImageDecoder.decodeBitmap(s, (decoder, img, src) -> {
        orig[0] = img.getSize().getWidth();
        orig[1] = img.getSize().getHeight();
        long f = fit(orig[0], orig[1], EDGE);
        decoder.setTargetSize((int) (f >>> 32), (int) (f & 0xffffffffL));
        decoder.setAllocator(ImageDecoder.ALLOCATOR_SOFTWARE);
        decoder.setUnpremultipliedRequired(true);
      });
      if (b.getConfig() != Bitmap.Config.ARGB_8888) b = b.copy(Bitmap.Config.ARGB_8888, false);
      ByteBuffer rgba = ByteBuffer.allocateDirect(b.getWidth() * b.getHeight() * 4);
      b.copyPixelsToBuffer(rgba);
      said = add(orig[0], orig[1], rgba, b.getWidth(), b.getHeight());
      b.recycle();
    } catch (Exception e) {
      said = "could not read that picture: " + e;
    }
    Log.i(TAG, "added: " + said);
    // the stored blob, where the e2e test reads it back
    byte[] qoi = blob(stored);
    if (qoi.length > 0) {
      File dir = new File(activity.getFilesDir(), "attachments");
      dir.mkdirs();
      try (FileOutputStream o = new FileOutputStream(new File(dir, stored + ".qoi"))) {
        o.write(qoi);
        stored++;
      } catch (Exception e) {
        Log.e(TAG, "store", e);
      }
    }
    byte[] px = tray(TRAY);
    int w = px.length / 4 / TRAY;
    Bitmap t = Bitmap.createBitmap(w, TRAY, Bitmap.Config.ARGB_8888);
    t.copyPixelsFromBuffer(ByteBuffer.wrap(px));
    String shown = said;
    activity.runOnUiThread(() -> {
      trayView.setImageBitmap(t);
      info.setText(shown);
    });
  }

  /** The camera's output: a file in the app's cache, lent by content URI. */
  public static final class Out extends ContentProvider {
    static final String AUTHORITY = "com.holmes.leanqr.out";

    static Uri uri(File f) {
      return Uri.parse("content://" + AUTHORITY + "/" + f.getName());
    }

    @Override public boolean onCreate() { return true; }

    @Override public ParcelFileDescriptor openFile(Uri uri, String mode) throws FileNotFoundException {
      String name = uri.getLastPathSegment();
      if (name == null || name.contains("/") || name.startsWith(".")) throw new FileNotFoundException(name);
      File f = new File(new File(getContext().getCacheDir(), "captures"), name);
      return ParcelFileDescriptor.open(f, ParcelFileDescriptor.parseMode(mode));
    }

    @Override public String getType(Uri uri) { return "image/jpeg"; }
    @Override public Cursor query(Uri u, String[] p, String s, String[] a, String o) { return null; }
    @Override public Uri insert(Uri u, ContentValues v) { return null; }
    @Override public int delete(Uri u, String s, String[] a) { return 0; }
    @Override public int update(Uri u, ContentValues v, String s, String[] a) { return 0; }
  }
}
