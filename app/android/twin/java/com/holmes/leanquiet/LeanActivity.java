package com.holmes.leanquiet;

import android.app.NativeActivity;
import android.content.Context;
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
import android.view.inputmethod.InputMethodManager;
import android.widget.EditText;
import android.widget.FrameLayout;
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
public class LeanActivity extends NativeActivity {
  static native void nInsets(int top, int bottom, int ime);
  static native void nText(String text, int selStart, int selEnd, int compStart, int compEnd);
  static native void nSend();

  private EditText edit;
  private InputMethodManager imm;

  /** The EditText reports its selection too, not only its text. */
  private final class Field extends EditText {
    Field(Context c) { super(c); }

    @Override protected void onSelectionChanged(int start, int end) {
      super.onSelectionChanged(start, end);
      report();
    }
  }

  @Override protected void onCreate(Bundle saved) {
    super.onCreate(saved);
    getWindow().setDecorFitsSystemWindows(false);
    getWindow().setStatusBarColor(Color.TRANSPARENT);
    getWindow().setNavigationBarColor(Color.TRANSPARENT);
    getWindow().setNavigationBarContrastEnforced(false);
    imm = (InputMethodManager) getSystemService(Context.INPUT_METHOD_SERVICE);
    edit = new Field(this);
    edit.setAlpha(0f);
    edit.setBackground(null);
    edit.setCursorVisible(false);
    edit.setTextColor(Color.TRANSPARENT);
    edit.setInputType(InputType.TYPE_CLASS_TEXT | InputType.TYPE_TEXT_FLAG_CAP_SENTENCES
        | InputType.TYPE_TEXT_FLAG_AUTO_CORRECT);
    edit.setImeOptions(EditorInfo.IME_ACTION_SEND | EditorInfo.IME_FLAG_NO_EXTRACT_UI
        | EditorInfo.IME_FLAG_NO_FULLSCREEN);
    edit.setOnEditorActionListener((v, id, ev) -> {
      boolean enter = ev != null && ev.getKeyCode() == KeyEvent.KEYCODE_ENTER
          && ev.getAction() == KeyEvent.ACTION_DOWN;
      if (id == EditorInfo.IME_ACTION_SEND || enter) {
        nSend();
        return true;
      }
      return id != EditorInfo.IME_NULL;
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
    nInsets(bars.top, bars.bottom, ime.bottom);
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
      if (show) {
        edit.requestFocus();
        imm.showSoftInput(edit, InputMethodManager.SHOW_IMPLICIT);
      } else {
        imm.hideSoftInputFromWindow(edit.getWindowToken(), 0);
      }
    });
  }

  /** From native (any thread): empties the text. */
  public void clearText() {
    runOnUiThread(() -> edit.setText(""));
  }
}
