package com.holmes.lifecycle;

import android.app.Activity;
import android.app.Application;
import android.app.Instrumentation;
import android.content.Intent;
import android.os.Bundle;
import android.os.Process;
import android.os.SystemClock;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

/** Drives the real target Activity. Host assertions observe the actual native
 * control socket, displayed UI, PID and OS input-method state. */
public final class LifecycleProbe extends Instrumentation {
  static { System.loadLibrary("lifecycle_probe"); }
  private static native void installExitProbe();
  private volatile Activity current;
  private Activity previous;
  private android.app.Dialog focusGate;
  private volatile int generation;
  private File command, state;
  private String runToken;

  private void state(String phase) {
    try {
      Files.write(state.toPath(), (phase + " " + generation + " " + Process.myPid() + " " + runToken + "\n").getBytes(StandardCharsets.UTF_8));
      android.util.Log.i("LifecycleProbe", phase + " generation=" + generation + " pid=" + Process.myPid());
    } catch (Exception e) { throw new RuntimeException(e); }
  }

  @Override public void onCreate(Bundle args) {
    super.onCreate(args);
    runToken = args.getString("runToken");
    if (runToken == null) throw new IllegalArgumentException("missing run token");
    File dir = getTargetContext().getFilesDir();
    command = new File(dir, "lifecycle-command");
    state = new File(dir, "lifecycle-state");
    command.delete(); state.delete();
    Application app = (Application)getTargetContext().getApplicationContext();
    app.registerActivityLifecycleCallbacks(new Application.ActivityLifecycleCallbacks() {
      public void onActivityCreated(Activity a, Bundle b) { current = a; generation++; }
      public void onActivityResumed(Activity a) { current = a; }
      public void onActivityStarted(Activity a) {}
      public void onActivityPaused(Activity a) {}
      public void onActivityStopped(Activity a) {}
      public void onActivitySaveInstanceState(Activity a, Bundle b) {}
      public void onActivityDestroyed(Activity a) {}
    });
    start();
  }

  @Override public void onStart() {
    try {
      Intent intent = new Intent().setClassName("com.holmes.leanquiet", "com.holmes.leanquiet.LeanActivity")
          .addFlags(Intent.FLAG_ACTIVITY_NEW_TASK);
      startActivitySync(intent);
      waitForIdleSync();
      state("ready");
      String last = "";
      long until = SystemClock.elapsedRealtime() + 90000;
      while (SystemClock.elapsedRealtime() < until) {
        String next = command.exists() ? new String(Files.readAllBytes(command.toPath()), StandardCharsets.UTF_8).trim() : "";
        if (!next.equals(last) && !next.isEmpty()) {
          last = next;
          if (next.startsWith("recreate")) {
            previous = current;
            int before = generation;
            runOnMainSync(previous::recreate);
            long deadline = SystemClock.elapsedRealtime() + 5000;
            while (generation == before && SystemClock.elapsedRealtime() < deadline) SystemClock.sleep(10);
            if (generation == before || current == previous) throw new AssertionError("Activity did not recreate");
            waitForIdleSync();
            state("recreated");
          } else if (next.equals("stale")) {
            if (previous == null) throw new AssertionError("missing destroyed Activity");
            runOnMainSync(() -> {
              try {
                var owner = current.getClass().getDeclaredField("editorOwner");
                var revision = current.getClass().getDeclaredField("editorRevision");
                owner.setAccessible(true); revision.setAccessible(true);
                var method = previous.getClass().getDeclaredMethod("nText", long.class, long.class, String.class,
                    int.class, int.class, int.class, int.class, boolean.class);
                method.setAccessible(true);
                method.invoke(previous, owner.getLong(current), revision.getLong(current) + 1,
                    "stale-callback", 14, 14, 14, 14, false);
              } catch (Exception e) { throw new RuntimeException(e); }
            });
            state("stale-delivered");
          } else if (next.startsWith("hold-focus")) {
            runOnMainSync(() -> {
              focusGate = new android.app.Dialog(current);
              android.widget.TextView label = new android.widget.TextView(current);
              label.setText("Lifecycle focus gate");
              focusGate.setContentView(label);
              focusGate.show();
            });
            boolean[] focused = {true};
            long deadline = SystemClock.elapsedRealtime() + 5000;
            do {
              runOnMainSync(() -> focused[0] = current.hasWindowFocus());
              if (!focused[0]) break;
              SystemClock.sleep(10);
            } while (SystemClock.elapsedRealtime() < deadline);
            if (focused[0]) throw new AssertionError("dialog did not take actual window focus");
            state("focus-held");
          } else if (next.equals("show-pending") || next.equals("hide-pending")) {
            final boolean show = next.equals("show-pending");
            runOnMainSync(() -> {
              if (current.hasWindowFocus()) throw new AssertionError("focus gate lost ownership");
              try { current.getClass().getMethod("showIme", boolean.class).invoke(current, show); }
              catch (Exception e) { throw new RuntimeException(e); }
            });
            state(show ? "pending-show" : "pending-hide");
          } else if (next.startsWith("release-focus")) {
            runOnMainSync(() -> focusGate.dismiss());
            state("focus-released");
          } else if (next.equals("finish")) {
            // Installed last, after real rendering/IME activity. If the app
            // incorrectly runs exit destructors, report before their teardown
            // can race live Android workers, then end this test process.
            installExitProbe();
            state("finishing");
            runOnMainSync(() -> current.finish());
          } else throw new AssertionError("unknown command " + next);
        }
        SystemClock.sleep(10);
      }
      throw new AssertionError("lifecycle fixture exceeded its total deadline");
    } catch (Throwable error) {
      android.util.Log.e("LifecycleProbe", "fixture failed", error);
      state("failed");
      Bundle result = new Bundle(); result.putString("error", error.toString()); finish(1, result);
    }
  }
}
