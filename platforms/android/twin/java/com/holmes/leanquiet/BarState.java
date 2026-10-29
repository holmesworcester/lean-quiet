package com.holmes.leanquiet;

import java.lang.ref.WeakReference;

/** Lean's last choice survives recreation; an Activity does not. */
final class BarState {
  record Choice(int top, int bottom, boolean lightTop, boolean lightBottom) {}
  interface Window {
    void postBars(Runnable work);
    void paintBars(Choice choice);
  }

  private volatile WeakReference<Window> window = new WeakReference<>(null);
  private volatile Choice choice;

  void attach(Window next) {
    window = new WeakReference<>(next);
    apply(next);
  }

  void detach(Window old) {
    if (window.get() == old) window.clear();
  }

  void set(Choice next) {
    if (next.equals(choice)) return;
    choice = next;
    Window current = window.get();
    if (current != null) current.postBars(() -> {
      if (window.get() == current) apply(current);
    });
  }

  private void apply(Window current) {
    Choice latest = choice;
    if (latest != null) current.paintBars(latest);
  }
}
