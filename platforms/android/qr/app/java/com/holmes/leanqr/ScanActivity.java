package com.holmes.leanqr;

import android.Manifest;
import android.app.Activity;
import android.content.pm.PackageManager;
import android.graphics.Color;
import android.graphics.ImageFormat;
import android.graphics.SurfaceTexture;
import android.hardware.camera2.CameraCaptureSession;
import android.hardware.camera2.CameraCharacteristics;
import android.hardware.camera2.CameraDevice;
import android.hardware.camera2.CameraManager;
import android.hardware.camera2.CaptureRequest;
import android.hardware.camera2.params.StreamConfigurationMap;
import android.media.Image;
import android.media.ImageReader;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.os.SystemClock;
import android.util.Log;
import android.util.Size;
import android.view.Gravity;
import android.view.Surface;
import android.view.TextureView;
import android.content.Intent;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;

/**
 * The camera harness: Camera2 preview frames, the Y (luma) plane of each
 * handed to Lean's decoder (libleanqr.so, Qr.decodeLuma) as the direct
 * buffer the camera filled, and what Lean decodes shown on screen and
 * logged (tag LeanQR). No parsing here: the buffer goes to Lean as is.
 */
public class ScanActivity extends Activity {
  static final String TAG = "LeanQR";

  static {
    System.loadLibrary("leanqr");
  }

  /** Lean's decoder on a luma plane: {payload, description}, or null. */
  static native Object[] decode(ByteBuffer y, int width, int height, int rowStride);

  private TextureView preview;
  private TextView text;
  private HandlerThread thread;
  private Handler handler;
  private CameraDevice camera;
  private ImageReader reader;
  private long frames;
  private long busyMs;
  private String last;
  private Pics pics;

  @Override protected void onCreate(Bundle saved) {
    super.onCreate(saved);
    FrameLayout root = new FrameLayout(this);
    preview = new TextureView(this);
    root.addView(preview);
    text = new TextView(this);
    text.setTextColor(Color.WHITE);
    text.setTextSize(16);
    text.setPadding(32, 32, 32, 32);
    text.setText("Point the camera at a QR code");
    // the bottom: the composer's image tools (Pics), then the scanner's text
    LinearLayout bottom = new LinearLayout(this);
    bottom.setOrientation(LinearLayout.VERTICAL);
    bottom.setBackgroundColor(0xAA000000);
    pics = new Pics(this, bottom);
    bottom.addView(text);
    FrameLayout.LayoutParams lp = new FrameLayout.LayoutParams(
        FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM);
    root.addView(bottom, lp);
    setContentView(root);
  }

  @Override protected void onActivityResult(int req, int res, Intent data) {
    if (!pics.onResult(req, res, data)) super.onActivityResult(req, res, data);
  }

  @Override protected void onResume() {
    super.onResume();
    thread = new HandlerThread("lean-qr");
    thread.start();
    handler = new Handler(thread.getLooper());
    if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
      requestPermissions(new String[] {Manifest.permission.CAMERA}, 1);
    } else {
      whenPreviewReady();
    }
  }

  @Override public void onRequestPermissionsResult(int code, String[] perms, int[] res) {
    if (res.length > 0 && res[0] == PackageManager.PERMISSION_GRANTED) whenPreviewReady();
    else text.setText("No camera permission");
  }

  @Override protected void onPause() {
    // Closed on the frames' own thread, between frames: closing the reader
    // from here while a frame is being handed to Lean closed that frame
    // under it ("Image is already closed").
    handler.post(() -> {
      if (camera != null) camera.close();
      camera = null;
      if (reader != null) reader.close();
      reader = null;
    });
    thread.quitSafely();
    super.onPause();
  }

  private void whenPreviewReady() {
    if (preview.isAvailable()) open();
    else preview.setSurfaceTextureListener(new TextureView.SurfaceTextureListener() {
      @Override public void onSurfaceTextureAvailable(SurfaceTexture s, int w, int h) { open(); }
      @Override public void onSurfaceTextureSizeChanged(SurfaceTexture s, int w, int h) {}
      @Override public boolean onSurfaceTextureDestroyed(SurfaceTexture s) { return true; }
      @Override public void onSurfaceTextureUpdated(SurfaceTexture s) {}
    });
  }

  /** The back camera's YUV size nearest 1280x720 (else the largest under it). */
  private static Size pick(Size[] sizes) {
    Size best = null;
    for (Size s : sizes) {
      long a = (long) s.getWidth() * s.getHeight();
      if (a > 1280L * 720) continue;
      if (best == null || a > (long) best.getWidth() * best.getHeight()) best = s;
    }
    return best != null ? best : sizes[0];
  }

  private void open() {
    try {
      CameraManager cm = getSystemService(CameraManager.class);
      String id = null;
      for (String c : cm.getCameraIdList()) {
        Integer f = cm.getCameraCharacteristics(c).get(CameraCharacteristics.LENS_FACING);
        if (f != null && f == CameraCharacteristics.LENS_FACING_BACK) { id = c; break; }
      }
      if (id == null) id = cm.getCameraIdList()[0];
      StreamConfigurationMap map = cm.getCameraCharacteristics(id)
          .get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP);
      Size size = pick(map.getOutputSizes(ImageFormat.YUV_420_888));
      Log.i(TAG, "camera " + id + " " + size + " of " + Arrays.toString(map.getOutputSizes(ImageFormat.YUV_420_888)));
      reader = ImageReader.newInstance(size.getWidth(), size.getHeight(), ImageFormat.YUV_420_888, 2);
      reader.setOnImageAvailableListener(this::frame, handler);
      preview.getSurfaceTexture().setDefaultBufferSize(size.getWidth(), size.getHeight());
      cm.openCamera(id, new CameraDevice.StateCallback() {
        @Override public void onOpened(CameraDevice d) { camera = d; start(); }
        @Override public void onDisconnected(CameraDevice d) { d.close(); }
        @Override public void onError(CameraDevice d, int e) { Log.e(TAG, "camera error " + e); d.close(); }
      }, handler);
    } catch (Exception e) {
      Log.e(TAG, "open", e);
    }
  }

  private void start() {
    try {
      Surface view = new Surface(preview.getSurfaceTexture());
      Surface frames = reader.getSurface();
      CaptureRequest.Builder rb = camera.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW);
      rb.addTarget(view);
      rb.addTarget(frames);
      rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_PICTURE);
      camera.createCaptureSession(Arrays.asList(view, frames), new CameraCaptureSession.StateCallback() {
        @Override public void onConfigured(CameraCaptureSession s) {
          try { s.setRepeatingRequest(rb.build(), null, handler); } catch (Exception e) { Log.e(TAG, "repeat", e); }
        }
        @Override public void onConfigureFailed(CameraCaptureSession s) { Log.e(TAG, "session failed"); }
      }, handler);
    } catch (Exception e) {
      Log.e(TAG, "start", e);
    }
  }

  /** One camera frame: its Y plane to Lean. */
  private void frame(ImageReader r) {
    Image img = r.acquireLatestImage();
    if (img == null) return;
    try {
      Image.Plane y = img.getPlanes()[0];
      long t0 = SystemClock.elapsedRealtime();
      Object[] res = decode(y.getBuffer(), img.getWidth(), img.getHeight(), y.getRowStride());
      long ms = SystemClock.elapsedRealtime() - t0;
      frames++;
      busyMs += ms;
      if (frames % 30 == 0) {
        Log.i(TAG, "frames " + frames + " " + img.getWidth() + "x" + img.getHeight()
            + " mean decode " + (busyMs / frames) + " ms");
      }
      if (res != null) {
        String payload = new String((byte[]) res[0], StandardCharsets.UTF_8);
        String info = (String) res[1];
        if (!payload.equals(last)) {
          last = payload;
          Log.i(TAG, "decoded (" + info + ", " + ms + " ms, frame " + frames + "): " + payload);
        }
        runOnUiThread(() -> text.setText(payload + "\n\n" + info + " · " + ms + " ms in Lean"));
      }
    } finally {
      img.close();
    }
  }
}
