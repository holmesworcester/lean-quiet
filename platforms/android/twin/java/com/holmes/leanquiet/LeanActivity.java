package com.holmes.leanquiet;

import android.app.NativeActivity;
import android.content.Context;
import android.content.res.Configuration;
import android.graphics.drawable.ColorDrawable;
import android.view.WindowInsetsController;
import android.graphics.Color;
import android.graphics.Insets;
import android.os.Bundle;
import android.text.Editable;
import android.text.InputType;
import android.text.TextWatcher;
import android.view.KeyEvent;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowInsets;
import android.view.WindowInsetsAnimation;
import android.view.inputmethod.BaseInputConnection;
import android.view.inputmethod.EditorInfo;
import android.view.inputmethod.InputConnection;
import android.view.inputmethod.InputConnectionWrapper;
import android.view.inputmethod.InputMethodManager;
import android.widget.EditText;
import android.widget.FrameLayout;
import java.nio.ByteBuffer;
import java.util.Arrays;
import java.util.List;

/**
 * The OS's half of the seam that NativeActivity lacks: the window's
 * insets (status bar, navigation bar, keyboard, the keyboard's height at
 * every frame of its animation) and the keyboard's text. The text lives
 * in an invisible EditText, so every input method works as in any app:
 * composition, glide typing, emoji, other scripts. Each change is
 * mirrored to native (the text, the selection and the composing span, in
 * code points); Lean draws the composer from it. Touches still go to
 * native first (NativeActivity's input queue), and keys native leaves
 * unhandled reach the EditText.
 */
public class LeanActivity extends NativeActivity implements BarState.Window {
  private static LeanActivity active;
  private boolean imeWanted;
  private boolean imeWasVisible;
  native void nAppearance(boolean dark, int textDpi);
  native void nInsets(int top, int bottom, int ime, int left, int right,
      int cutLeft, int cutTop, int cutRight, int cutBottom);
  native void nText(long owner, long revision, String text, int selStart, int selEnd, int compStart, int compEnd, boolean installed);
  native void nActionDone(long ticket);
  native boolean nEditorReady(long owner, long revision);
  native int nAction(long owner, long revision, int kind, int code, int action);
  native void nLink(String url);
  /** A camera frame's Y plane, as the camera filled it (copied in native),
   * and the sensor's clockwise orientation in degrees. */
  native void nLuma(ByteBuffer y, int width, int height, int rowStride, int orientation);

  native void nPhoto(int token, int status, int width, int height, byte[] rgba);
  private int pickerToken;
  private volatile int photoToken;
  private final java.util.concurrent.ExecutorService photoWorker =
      java.util.concurrent.Executors.newSingleThreadExecutor();

  /** A system picker grants access to only the selected image. The app's
   * worker receives bounded, oriented sRGB pixels, never a full-size decode. */
  public void pickPhoto(int token) {
    photoToken = token;
    runOnUiThread(() -> {
      if (active != this || isDestroyed()) return;
      if (token == 0 || photoToken != token) return;
      if (pickerToken != 0) { nPhoto(token, 3, 0, 0, null); return; }
      pickerToken = token;
      showIme(false);
      android.content.Intent intent = new android.content.Intent(
          android.os.Build.VERSION.SDK_INT >= 33
              ? android.provider.MediaStore.ACTION_PICK_IMAGES
              : android.content.Intent.ACTION_OPEN_DOCUMENT);
      intent.setType("image/*");
      if (android.os.Build.VERSION.SDK_INT < 33) intent.addCategory(android.content.Intent.CATEGORY_OPENABLE);
      try { startActivityForResult(intent, 42); }
      catch (RuntimeException error) {
        pickerToken = 0;
        nPhoto(token, 3, 0, 0, null);
      }
    });
  }

  @Override protected void onActivityResult(int request, int result, android.content.Intent data) {
    super.onActivityResult(request, result, data);
    if (request != 42) return;
    final int token = pickerToken;
    pickerToken = 0;
    if (token == 0 || photoToken != token) return;
    if (result != RESULT_OK || data == null || data.getData() == null) {
      nPhoto(token, 2, 0, 0, null);
      return;
    }
    final android.net.Uri uri = data.getData();
    nPhoto(token, 4, 0, 0, null); // selection precedes provider loading/decode
    photoWorker.execute(() -> {
      android.graphics.Bitmap bitmap = null;
      try {
        bitmap = android.graphics.ImageDecoder.decodeBitmap(
            android.graphics.ImageDecoder.createSource(getContentResolver(), uri),
            (decoder, info, source) -> {
              decoder.setAllocator(android.graphics.ImageDecoder.ALLOCATOR_SOFTWARE);
              decoder.setTargetColorSpace(android.graphics.ColorSpace.get(android.graphics.ColorSpace.Named.SRGB));
              int w = info.getSize().getWidth(), h = info.getSize().getHeight();
              int side = Math.max(w, h);
              if (side > 2048) decoder.setTargetSize(Math.max(1, (int)((long)w*2048/side)), Math.max(1, (int)((long)h*2048/side)));
            });
        if (photoToken != token || isDestroyed()) return;
        int w = bitmap.getWidth(), h = bitmap.getHeight();
        if (w < 1 || h < 1 || w > 2048 || h > 2048) throw new IllegalArgumentException("image dimensions");
        int[] argb = new int[w*h];
        bitmap.getPixels(argb, 0, w, 0, 0, w, h);
        byte[] rgba = new byte[w*h*4];
        for (int i = 0; i < argb.length; i++) {
          int c = argb[i];
          rgba[4*i] = (byte)(c >>> 16); rgba[4*i+1] = (byte)(c >>> 8);
          rgba[4*i+2] = (byte)c; rgba[4*i+3] = (byte)(c >>> 24);
        }
        if (photoToken == token && !isDestroyed()) nPhoto(token, 1, w, h, rgba);
      } catch (Exception | OutOfMemoryError error) {
        android.util.Log.w("lean", "photo decode failed", error);
        if (photoToken == token && !isDestroyed()) nPhoto(token, 3, 0, 0, null);
      } finally { if (bitmap != null) bitmap.recycle(); }
    });
  }

  private boolean appliedDark;
  private int appliedBackground = -1;

  private void reportAppearance(Configuration config) {
    // Ask Android to convert the 15 sp body: Android 14+ uses a nonlinear
    // curve. Grow its surrounding layout by the same ratio to avoid clipping.
    int textDpi = Math.round(android.util.TypedValue.applyDimension(
        android.util.TypedValue.COMPLEX_UNIT_SP, 15f, getResources().getDisplayMetrics()) * 160f / 15f);
    nAppearance((config.uiMode & Configuration.UI_MODE_NIGHT_MASK) == Configuration.UI_MODE_NIGHT_YES, textDpi);
  }

  @Override public void onConfigurationChanged(Configuration config) {
    super.onConfigurationChanged(config);
    reportAppearance(config);
  }

  /** Called with Lean's effective theme; never changes the OS observation. */
  public void appearance(boolean dark, int background) {
    runOnUiThread(() -> {
      if (active != this || isDestroyed()) return;
      if (appliedBackground == background && appliedDark == dark) return;
      appliedDark = dark;
      appliedBackground = background;
      int mask = WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS
          | WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS;
      getWindow().getInsetsController().setSystemBarsAppearance(dark ? 0 : mask, mask);
      getWindow().setBackgroundDrawable(new ColorDrawable(0xff000000 | background));
    });
  }

  private static final BarState bars = new BarState();

  public void applyBars(int top, int bottom, boolean lightTop, boolean lightBottom) {
    bars.set(new BarState.Choice(top, bottom, lightTop, lightBottom));
  }

  public void postBars(Runnable work) { runOnUiThread(work); }

  public void paintBars(BarState.Choice choice) {
    getWindow().setStatusBarColor(0xff000000 | choice.top());
    getWindow().setNavigationBarColor(0xff000000 | choice.bottom());
    android.view.WindowInsetsController c = getWindow().getInsetsController();
    if (c != null) {
      int status = android.view.WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS;
      int nav = android.view.WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS;
      c.setSystemBarsAppearance((choice.lightTop() ? 0 : status) | (choice.lightBottom() ? 0 : nav), status | nav);
    }
  }

  @Override public void onWindowFocusChanged(boolean focused) {
    super.onWindowFocusChanged(focused);
    if (focused) {
      bars.attach(this);
      if (imeWanted) applyIme();
    }
  }

  @Override protected void onDestroy() {
    if (active == this) active = null;
    imeWanted = false;
    bars.detach(this);
    // The native run survives configuration replacement. Finish its exact
    // outstanding request before NativeActivity releases this Java owner.
    int cancelledPhoto = photoToken;
    photoToken = 0;
    if (cancelledPhoto != 0) nPhoto(cancelledPhoto, 2, 0, 0, null);
    photoWorker.shutdownNow();
    super.onDestroy();
  }

  private EditText edit;
  private InputMethodManager imm;
  private long editorOwner, editorRevision;
  private boolean installingEditor, editorRevisionExhausted;
  private volatile long lastActionTicket;
  private volatile int lastActionDisposition;
  private volatile long pendingClearTicket;
  private volatile int lastActionRefusal;
  private final Object actionDispositionLock = new Object();
  private boolean dispositionQueued;
  private long pendingDispositionTicket;
  private int pendingDisposition;
  private android.widget.Toast actionRefusal;
  private final Object editorCommandLock = new Object();
  private boolean editorCommandQueued;
  private long requestedEditorOwner, requestedEditorRevision;
  private byte[] requestedEditorText;
  private int requestedEditorMode;
  private boolean clearCommandQueued;
  private long clearCommandOwner, clearCommandRevision;

  private void refuseAction(int code) {
    lastActionRefusal=code;
    if(code==0)return;
    String text=code==1?"Your previous action is still finishing. Try again.":
      code==3?"This message is too large to send. Shorten it and try again.":
      code==6?"Opening the editor…":
      "This editor changed. Please try the action again.";
    if(actionRefusal==null)actionRefusal=android.widget.Toast.makeText(this,text,android.widget.Toast.LENGTH_SHORT);
    else actionRefusal.setText(text);
    actionRefusal.show();
  }
  private void submitAction(int kind,int code,int action) {
    refuseAction(nAction(editorOwner,editorRevision,kind,code,action));
  }

  /** At most one pending editor command. No native/Lean thread waits for it.
   * An overwritten CAS has no waiter; latest native state is the receipt. */
  public void updateEditor(long owner,long expected,byte[] utf8,int mode) {
    synchronized(editorCommandLock) {
      if(requestedEditorText!=null &&
          (Long.compareUnsigned(owner,requestedEditorOwner)<0 ||
           (owner==requestedEditorOwner&&requestedEditorMode!=2&&mode==2)))return;
      requestedEditorOwner=owner;requestedEditorRevision=expected;
      requestedEditorText=utf8;requestedEditorMode=mode;
      if(editorCommandQueued)return;
      editorCommandQueued=true;
    }
    runOnUiThread(() -> {
      long next,revision;byte[] bytes;int kind;
      synchronized(editorCommandLock) {
        next=requestedEditorOwner;revision=requestedEditorRevision;
        bytes=requestedEditorText;kind=requestedEditorMode;
        requestedEditorText=null;editorCommandQueued=false;
      }
      if(active!=this||isDestroyed()||bytes==null)return;
      if(kind==4) {
        // Explicit legacy component clients do not participate in ownership.
        edit.setEnabled(true);imm.restartInput(edit);if(imeWanted)applyIme();return;
      }
      boolean replacing=kind!=2;
      boolean preserve=kind==5&&editorOwner!=0;
      boolean consumed=preserve&&revision!=0&&editorRevision==revision;
      if(replacing) {
        if(Long.compareUnsigned(next,editorOwner)<0)return;
        if(next==editorOwner&&editorRevision!=0) { reportInstalled();return; }
        editorOwner=next;editorRevision=0;editorRevisionExhausted=false;
      } else if(editorOwner!=next||editorRevision!=revision||editorRevision==0)return;
      installingEditor=true;
      try {
        String value=consumed?"":new String(bytes,java.nio.charset.StandardCharsets.UTF_8);
        if((!preserve||consumed)&&!edit.getText().toString().equals(value)) {
          edit.setText(value);edit.setSelection(value.length());
        }
      } finally { installingEditor=false; }
      if(replacing)reportInstalled();else report();
    });
  }
  /** One coalesced terminal receipt; rejected batches cannot retain a slot. */
  public void actionDisposition(long ticket,int disposition) {
    synchronized(actionDispositionLock) {
      pendingDispositionTicket=ticket;pendingDisposition=disposition;
      if(dispositionQueued)return;
      dispositionQueued=true;
    }
    runOnUiThread(() -> {
      long token;int result;
      synchronized(actionDispositionLock) {
        token=pendingDispositionTicket;result=pendingDisposition;dispositionQueued=false;
      }
      lastActionTicket=token;lastActionDisposition=result;
      if(active==this&&!isDestroyed()&&result==5)refuseAction(2);
    });
  }
  /** The one retained semantic slot owns this one clear until its callback.
   * Later typing wins. Completion settles the exact ticket in either case. */
  public void clearAction(long ticket,long owner,long revision) {
    synchronized(editorCommandLock) {
      if(pendingClearTicket!=0&&pendingClearTicket!=ticket)nActionDone(pendingClearTicket);
      pendingClearTicket=ticket;clearCommandOwner=owner;clearCommandRevision=revision;
      if(clearCommandQueued)return;
      clearCommandQueued=true;
    }
    runOnUiThread(() -> {
      long token,expectedOwner,expectedRevision;
      synchronized(editorCommandLock) {
        token=pendingClearTicket;expectedOwner=clearCommandOwner;expectedRevision=clearCommandRevision;
        clearCommandQueued=false;
      }
      try {
        if(active!=this||isDestroyed())return;
        if(editorOwner==expectedOwner&&editorRevision==expectedRevision&&expectedRevision!=0) {
          installingEditor=true;edit.setText("");edit.setSelection(0);installingEditor=false;
          report();
        }
      } finally {
        installingEditor=false;lastActionTicket=token;lastActionDisposition=4;
        synchronized(editorCommandLock){if(pendingClearTicket==token)pendingClearTicket=0;}
        nActionDone(token);
      }
    });
  }

  /** The EditText reports its selection too, not only its text. */
  private final class Field extends EditText {
    Field(Context c) { super(c); }

    @Override protected void onSelectionChanged(int start, int end) {
      super.onSelectionChanged(start, end);
      report();
    }

    // A composition can end, or its region move, with neither the text nor
    // the selection changing: report those too.
    @Override public InputConnection onCreateInputConnection(EditorInfo out) {
      if(!isEnabled())return null;
      InputConnection ic = super.onCreateInputConnection(out);
      if (ic == null) return null;
      return new InputConnectionWrapper(ic, false) {
        @Override public boolean finishComposingText() {
          boolean r = super.finishComposingText();
          report();
          return r;
        }

        @Override public boolean setComposingRegion(int start, int end) {
          boolean r = super.setComposingRegion(start, end);
          report();
          return r;
        }
      };
    }
  }

  @Override protected void onCreate(Bundle saved) {
    super.onCreate(saved);
    active = this;
    deliverLink(getIntent());
    reportAppearance(getResources().getConfiguration());
    getWindow().setDecorFitsSystemWindows(false);
    getWindow().setStatusBarColor(Color.TRANSPARENT);
    getWindow().setNavigationBarColor(Color.TRANSPARENT);
    getWindow().setNavigationBarContrastEnforced(false);
    getWindow().setStatusBarContrastEnforced(false);
    android.view.WindowManager.LayoutParams attrs = getWindow().getAttributes();
    attrs.layoutInDisplayCutoutMode = android.view.WindowManager.LayoutParams.LAYOUT_IN_DISPLAY_CUTOUT_MODE_ALWAYS;
    getWindow().setAttributes(attrs);
    bars.attach(this);
    imm = (InputMethodManager) getSystemService(Context.INPUT_METHOD_SERVICE);
    edit = new Field(this);
    // An empty replacement Field has no semantic owner yet. Do not let an
    // IME accept text which restoration would overwrite. The pending focus
    // request is honored after native acknowledges the actual installation.
    edit.setEnabled(false);
    edit.setAlpha(0f);
    edit.setBackground(null);
    edit.setCursorVisible(false);
    if (android.os.Build.VERSION.SDK_INT >= 33) {
      edit.setAutoHandwritingEnabled(false);  // no stylus prompt over a hidden field
    }
    edit.setTextColor(Color.TRANSPARENT);
    edit.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_FLAG_CAP_SENTENCES
        | InputType.TYPE_TEXT_FLAG_AUTO_CORRECT);
    edit.setImeOptions(EditorInfo.IME_ACTION_SEND | EditorInfo.IME_FLAG_NO_EXTRACT_UI
        | EditorInfo.IME_FLAG_NO_FULLSCREEN);
    edit.setOnKeyListener((v, code, ev) -> {
      if(code==KeyEvent.KEYCODE_ENTER) {
        if(ev.getAction()==KeyEvent.ACTION_DOWN&&ev.getRepeatCount()==0)submitAction(14,code,0);
        return true; // accepted and refused Send both consume this gesture once
      }
      nAction(editorOwner,editorRevision,14,code,ev.getAction());
      return false;  // other keys still perform OS text editing
    });
    edit.setOnEditorActionListener((v, id, ev) -> {
      if (ev == null) submitAction(5, id, 0);
      return true;

    });
    edit.addTextChangedListener(new TextWatcher() {
      @Override public void beforeTextChanged(CharSequence s, int a, int b, int c) {}
      @Override public void onTextChanged(CharSequence s, int a, int b, int c) {}
      @Override public void afterTextChanged(Editable s) { report(); }
    });
    addContentView(edit, new FrameLayout.LayoutParams(1, 1));
    View decor = getWindow().getDecorView();
    decor.setOnApplyWindowInsetsListener((v, insets) -> {
      insets(insets);
      return v.onApplyWindowInsets(insets);
    });
    decor.requestApplyInsets();
    decor.setWindowInsetsAnimationCallback(
        new WindowInsetsAnimation.Callback(WindowInsetsAnimation.Callback.DISPATCH_MODE_CONTINUE_ON_SUBTREE) {
          @Override public WindowInsets onProgress(WindowInsets insets, List<WindowInsetsAnimation> running) {
            insets(insets);
            return insets;
          }
        });
  }

  private void insets(WindowInsets in) {
    Insets bars = in.getInsets(WindowInsets.Type.systemBars());
    Insets ime = in.getInsets(WindowInsets.Type.ime());
    boolean visible = ime.bottom > 0;
    // A system Back/hide completes the request too. A later focus event must
    // not reopen a keyboard the user already dismissed.
    if (imeWasVisible && !visible) imeWanted = false;
    imeWasVisible = visible;
    android.view.DisplayCutout cut = in.getDisplayCutout();
    nInsets(bars.top, bars.bottom, ime.bottom, bars.left, bars.right,
        cut == null ? 0 : cut.getSafeInsetLeft(), cut == null ? 0 : cut.getSafeInsetTop(),
        cut == null ? 0 : cut.getSafeInsetRight(), cut == null ? 0 : cut.getSafeInsetBottom());
  }

  private static int cp(CharSequence s, int i) {
    if (i < 0) return -1;
    return Character.codePointCount(s, 0, Math.min(i, s.length()));
  }

  private void report() { reportState(false); }
  private void reportInstalled() {
    reportState(true);
    boolean ready=nEditorReady(editorOwner,editorRevision);
    boolean changed=edit.isEnabled()!=ready;
    edit.setEnabled(ready);
    if(ready) {
      if(changed)imm.restartInput(edit);
      if(imeWanted)applyIme();
    }
  }
  private void reportState(boolean installed) {
    if (edit == null || installingEditor) return;
    if(installed&&editorRevision!=0) {
      // Re-ack a recreated native binding without changing the editor revision.
    } else if(editorRevisionExhausted||editorRevision==Long.MAX_VALUE) { editorRevision=0;editorRevisionExhausted=true; }
    else editorRevision++;
    Editable t = edit.getText();
    int cs = BaseInputConnection.getComposingSpanStart(t);
    int ce = BaseInputConnection.getComposingSpanEnd(t);
    int ss = cp(t, edit.getSelectionStart());
    int se = cp(t, edit.getSelectionEnd());
    int a = cs < 0 ? ss : cp(t, cs);
    int b = cs < 0 ? ss : cp(t, ce);
    nText(editorOwner,editorRevision,t.toString(),Math.max(ss,0),Math.max(se,0),Math.max(a,0),Math.max(b,0),installed);
  }

  /** From native (any thread): opens or closes the keyboard. */
  public void showIme(boolean show) {
    runOnUiThread(() -> {
      if (active != this || isDestroyed()) return;
      imeWanted = show;
      if(show&&!edit.isEnabled())refuseAction(6);
      applyIme();
    });
  }

  // Native touch delivery can precede the replacement window's focus. Keep
  // the request until focus arrives; posting also lets IMM's window-focus
  // handler establish the input connection before requesting visibility.
  private void applyIme() {
    if (active != this || isDestroyed() || edit == null) return;
    if (imeWanted) {
      if(!edit.isEnabled())return;
      edit.requestFocus();
      if (!hasWindowFocus() || !edit.isAttachedToWindow()) return;
      edit.post(() -> {
        if (active != this || isDestroyed() || !imeWanted || !edit.isEnabled() || !hasWindowFocus()) return;
        android.view.WindowInsetsController c = getWindow().getInsetsController();
        if (c != null) c.show(WindowInsets.Type.ime());
        imm.showSoftInput(edit, 0);
      });
    } else {
      android.view.WindowInsetsController c = getWindow().getInsetsController();
      if (c != null) c.hide(WindowInsets.Type.ime());
      imm.hideSoftInputFromWindow(edit.getWindowToken(), 0);
    }
  }

  private void deliverLink(android.content.Intent intent) {
    if (intent != null && android.content.Intent.ACTION_VIEW.equals(intent.getAction())
        && intent.getData() != null) nLink(intent.getData().toString());
  }

  @Override protected void onNewIntent(android.content.Intent intent) {
    super.onNewIntent(intent);
    setIntent(intent);
    deliverLink(intent);
  }

  /** From native (any thread): the text becomes t, caret at its end; a
   * field already holding t is left alone (its caret too). */
  public void setText(String t) {
    runOnUiThread(() -> {
      if (active != this || isDestroyed()) return;
      if (edit.getText().toString().equals(t)) return;
      edit.setText(t);
      edit.setSelection(t.length());
    });
  }

  /** From native (any thread): puts text on the clipboard. */
  public void copyText(String text) {
    runOnUiThread(() -> {
      if (active != this || isDestroyed()) return;
      android.content.ClipboardManager cm =
        (android.content.ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
      if (cm != null) cm.setPrimaryClip(android.content.ClipData.newPlainText("message", text));
    });
  }

  // The camera (Join with QR code)
  // ------------------------------
  //
  // Lean turns the camera on and off (Platform.scan), draws the preview
  // itself and decodes the frames (Platform.luma, Qr.decodeLuma): this
  // only opens the back camera and hands each frame's Y plane over, with
  // the sensor's orientation. (NativeActivity owns the window's surface,
  // so no view of ours could show a preview anyway.)

  private android.os.HandlerThread camThread;
  private volatile android.os.Handler cam;
  private volatile android.hardware.camera2.CameraDevice camera;
  private volatile android.media.ImageReader reader;
  private int orientation;
  private volatile boolean wanted;

  /** From native (any thread): the camera on or off. */
  public void scan(boolean on) {
    android.util.Log.i("lean", "camera " + (on ? "on" : "off"));
    runOnUiThread(() -> {
      if (active != this || isDestroyed()) return;
      if (on) startCamera();
      else stopCamera();
    });
  }

  @Override public void onRequestPermissionsResult(int code, String[] perms, int[] res) {
    if (code == 7 && res.length > 0 && res[0] == android.content.pm.PackageManager.PERMISSION_GRANTED
        && wanted) {
      startCamera();
    }
  }

  @Override protected void onPause() {
    stopCamera();
    showIme(false);
    super.onPause();
  }

  @Override protected void onResume() {
    super.onResume();
    // Lean resumes the camera only after restoring the mounted scan page.
  }

  private void startCamera() {
    stopCamera();
    wanted = true;
    if (checkSelfPermission(android.Manifest.permission.CAMERA)
        != android.content.pm.PackageManager.PERMISSION_GRANTED) {
      android.util.Log.i("lean", "camera: asking for the permission");
      requestPermissions(new String[] {android.Manifest.permission.CAMERA}, 7);
      return;
    }
    camThread = new android.os.HandlerThread("camera");
    camThread.start();
    cam = new android.os.Handler(camThread.getLooper());
    open(cam);
  }

  private synchronized void stopCamera() {
    wanted = false;
    if (cam != null) {
      final android.hardware.camera2.CameraDevice c = camera;
      final android.media.ImageReader rd = reader;
      // closed on the frames' own thread, between frames
      cam.post(() -> {
        if (c != null) c.close();
        if (rd != null) rd.close();
      });
      camThread.quitSafely();
    }
    camera = null;
    reader = null;
    cam = null;
    camThread = null;
  }

  /** The back camera's YUV size nearest 1280x720, not over it. */
  private static android.util.Size pick(android.util.Size[] sizes) {
    android.util.Size best = null;
    for (android.util.Size s : sizes) {
      long a = (long) s.getWidth() * s.getHeight();
      if (a > 1280L * 720) continue;
      if (best == null || a > (long) best.getWidth() * best.getHeight()) best = s;
    }
    return best != null ? best : sizes[0];
  }

  private void open(final android.os.Handler h) {
    if (!wanted || cam != h) return;
    try {
      android.hardware.camera2.CameraManager cm = getSystemService(android.hardware.camera2.CameraManager.class);
      String id = null;
      for (String c : cm.getCameraIdList()) {
        Integer f = cm.getCameraCharacteristics(c).get(android.hardware.camera2.CameraCharacteristics.LENS_FACING);
        if (f != null && f == android.hardware.camera2.CameraCharacteristics.LENS_FACING_BACK) { id = c; break; }
      }
      if (id == null) id = cm.getCameraIdList()[0];
      android.hardware.camera2.CameraCharacteristics ch = cm.getCameraCharacteristics(id);
      Integer o = ch.get(android.hardware.camera2.CameraCharacteristics.SENSOR_ORIENTATION);
      orientation = o != null ? o : 90;
      android.util.Size size = pick(ch.get(android.hardware.camera2.CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)
          .getOutputSizes(android.graphics.ImageFormat.YUV_420_888));
      final android.media.ImageReader rd = android.media.ImageReader.newInstance(
          size.getWidth(), size.getHeight(), android.graphics.ImageFormat.YUV_420_888, 2);
      synchronized (this) {
        if (!wanted || cam != h) { rd.close(); return; }
        reader = rd;
      }
      rd.setOnImageAvailableListener(this::frame, h);
      cm.openCamera(id, new android.hardware.camera2.CameraDevice.StateCallback() {
        @Override public void onOpened(android.hardware.camera2.CameraDevice d) {
          synchronized (LeanActivity.this) {
            if (!wanted || cam != h || reader != rd) { d.close(); return; }
            camera = d;
          }
          android.util.Log.i("lean", "camera opened, " + rd.getWidth() + "x" + rd.getHeight() + ", orientation " + orientation);
          start(d, rd, h);
        }
        @Override public void onDisconnected(android.hardware.camera2.CameraDevice d) { d.close(); }
        @Override public void onError(android.hardware.camera2.CameraDevice d, int e) {
          android.util.Log.e("lean", "camera error " + e);
          d.close();
        }
      }, h);
    } catch (Exception e) {
      android.util.Log.e("lean", "camera", e);
    }
  }

  private void start(android.hardware.camera2.CameraDevice d, android.media.ImageReader rd,
      android.os.Handler h) {
    try {
      final android.hardware.camera2.CaptureRequest.Builder rb =
          d.createCaptureRequest(android.hardware.camera2.CameraDevice.TEMPLATE_PREVIEW);
      rb.addTarget(rd.getSurface());
      rb.set(android.hardware.camera2.CaptureRequest.CONTROL_AF_MODE,
          android.hardware.camera2.CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_PICTURE);
      d.createCaptureSession(Arrays.asList(rd.getSurface()),
          new android.hardware.camera2.CameraCaptureSession.StateCallback() {
            @Override public void onConfigured(android.hardware.camera2.CameraCaptureSession s) {
              if (!wanted || cam != h || reader != rd) { s.close(); return; }
              try { s.setRepeatingRequest(rb.build(), null, h); } catch (Exception e) { android.util.Log.e("lean", "repeat", e); }
            }
            @Override public void onConfigureFailed(android.hardware.camera2.CameraCaptureSession s) {
              android.util.Log.e("lean", "camera session failed");
            }
          }, h);
    } catch (Exception e) {
      android.util.Log.e("lean", "camera session", e);
    }
  }

  /** One camera frame: its Y plane to native, for Lean. */
  private synchronized void frame(android.media.ImageReader r) {
    if (!wanted || reader != r) return;
    android.media.Image img = r.acquireLatestImage();
    if (img == null) return;
    try {
      android.media.Image.Plane y = img.getPlanes()[0];
      nLuma(y.getBuffer(), img.getWidth(), img.getHeight(), y.getRowStride(), orientation);
    } finally {
      img.close();
    }
  }
}
