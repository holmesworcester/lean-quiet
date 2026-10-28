package com.holmes.testime;

import android.graphics.Color;
import android.inputmethodservice.InputMethodService;
import android.view.Gravity;
import android.view.View;
import android.view.inputmethod.EditorInfo;
import android.view.inputmethod.InputConnection;
import android.widget.Button;
import android.widget.LinearLayout;

/**
 * A deterministic soft keyboard for the twin's end-to-end tests: a docked
 * panel 360 dp tall (the system animates it in and out, so the app sees
 * real WindowInsetsAnimation frames) with keys that commit fixed text,
 * compose a candidate, delete, and send. Emulators expose a hardware
 * keyboard, which keeps Gboard in its floating accessory mode.
 */
public class TestIme extends InputMethodService {
  @Override public boolean onEvaluateInputViewShown() {
    return true;  // shown even with a hardware keyboard attached
  }

  @Override public View onCreateInputView() {
    float dp = getResources().getDisplayMetrics().density;
    LinearLayout col = new LinearLayout(this);
    col.setOrientation(LinearLayout.VERTICAL);
    col.setBackgroundColor(Color.rgb(60, 70, 90));
    col.setMinimumHeight((int) (360 * dp));
    col.setGravity(Gravity.CENTER);
    String[][] rows = {
      { "hello ", "wörld ", "日本 ", "🌍" },
      { "compose", "commit", "del", "send" },
    };
    for (String[] row : rows) {
      LinearLayout r = new LinearLayout(this);
      for (String k : row) {
        Button b = new Button(this);
        b.setText(k);
        b.setOnClickListener(v -> key(k));
        r.addView(b, new LinearLayout.LayoutParams(0, (int) (72 * dp), 1f));
      }
      col.addView(r);
    }
    return col;
  }

  private void key(String k) {
    InputConnection ic = getCurrentInputConnection();
    if (ic == null) return;
    switch (k) {
      case "compose": ic.setComposingText("cand", 1); break;
      case "commit": ic.finishComposingText(); break;
      case "del": ic.deleteSurroundingText(1, 0); break;
      case "send": ic.performEditorAction(EditorInfo.IME_ACTION_SEND); break;
      default: ic.commitText(k, 1);
    }
  }
}
