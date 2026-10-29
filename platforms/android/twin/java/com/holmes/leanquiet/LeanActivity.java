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
  static native void nAppearance(boolean dark);
  static native void nInsets(int top, int bottom, int ime, int left, int right,
      int cutLeft, int cutTop, int cutRight, int cutBottom);
  static native void nText(String text, int selStart, int selEnd, int compStart, int compEnd);
  static native void nAction(int kind, int code, int action);
  static native void nLink(String url);
  /** A camera frame's Y plane, as the camera filled it (copied in native),
   * and the sensor's clockwise orientation in degrees. */
  static native void nLuma(ByteBuffer y, int width, int height, int rowStride, int orientation);

  private boolean appliedDark;
  private int appliedBackground = -1;

  private void reportAppearance(Configuration config) {
    nAppearance((config.uiMode & Configuration.UI_MODE_NIGHT_MASK) == Configuration.UI_MODE_NIGHT_YES);
  }

  @Override public void onConfigurationChanged(Configuration config) {
    super.onConfigurationChanged(config);
    reportAppearance(config);
  }

  /** Called with Lean's effective theme; never changes the OS observation. */
  public void appearance(boolean dark, int background) {
    runOnUiThread(() -> {
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
    if (focused) bars.attach(this);
  }

  @Override protected void onDestroy() {
    bars.detach(this);
    super.onDestroy();
  }

  private EditText edit;
  private InputMethodManager imm;

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
      nAction(14, code, ev.getAction());
      return false;  // the field still performs OS text editing
    });
    edit.setOnEditorActionListener((v, id, ev) -> {
      if (ev == null) nAction(5, id, 0);
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

  private static void insets(WindowInsets in) {
    Insets bars = in.getInsets(WindowInsets.Type.systemBars());
    Insets ime = in.getInsets(WindowInsets.Type.ime());
    android.view.DisplayCutout cut = in.getDisplayCutout();
    nInsets(bars.top, bars.bottom, ime.bottom, bars.left, bars.right,
        cut == null ? 0 : cut.getSafeInsetLeft(), cut == null ? 0 : cut.getSafeInsetTop(),
        cut == null ? 0 : cut.getSafeInsetRight(), cut == null ? 0 : cut.getSafeInsetBottom());
  }

  private static int cp(CharSequence s, int i) {
    if (i < 0) return -1;
    return Character.codePointCount(s, 0, Math.min(i, s.length()));
  }

  private void report() {
    if (edit == null) return;
    Editable t = edit.getText();
    int cs = BaseInputConnection.getComposingSpanStart(t);
    int ce = BaseInputConnection.getComposingSpanEnd(t);
    int ss = cp(t, edit.getSelectionStart());
    int se = cp(t, edit.getSelectionEnd());
    int a = cs < 0 ? ss : cp(t, cs);
    int b = cs < 0 ? ss : cp(t, ce);
    nText(t.toString(), Math.max(ss, 0), Math.max(se, 0), Math.max(a, 0), Math.max(b, 0));
  }

  /** From native (any thread): opens or closes the keyboard. */
  public void showIme(boolean show) {
    runOnUiThread(() -> {
      android.view.WindowInsetsController c = getWindow().getInsetsController();
      if (show) {
        edit.requestFocus();
        // An explicit request: an implicit one is refused while a hardware
        // keyboard is attached (as on the emulator).
        if (c != null) c.show(WindowInsets.Type.ime());
        imm.showSoftInput(edit, 0);
      } else {
        if (c != null) c.hide(WindowInsets.Type.ime());
        imm.hideSoftInputFromWindow(edit.getWindowToken(), 0);
      }
    });
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
      if (edit.getText().toString().equals(t)) return;
      edit.setText(t);
      edit.setSelection(t.length());
    });
  }

  /** From native (any thread): puts text on the clipboard. */
  public void copyText(String text) {
    runOnUiThread(() -> {
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
