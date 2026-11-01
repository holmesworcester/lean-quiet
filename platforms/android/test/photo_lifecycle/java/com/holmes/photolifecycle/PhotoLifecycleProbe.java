package com.holmes.photolifecycle;

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
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;

/** Only the real Activity, its real executor and actual instance JNI callbacks. */
public final class PhotoLifecycleProbe extends Instrumentation {
  private volatile Activity current;
  private Activity previous;
  private volatile boolean previousDestroyed;
  private volatile int generation;
  private File command, state;
  private String runToken;
  private CountDownLatch decodeGate;

  private void state(String phase) {
    try {
      Files.write(state.toPath(), (phase+" "+generation+" "+Process.myPid()+" "+runToken+"\n").getBytes(StandardCharsets.UTF_8));
      android.util.Log.i("PhotoLifecycleProbe",phase+" generation="+generation+" pid="+Process.myPid());
    } catch (Exception e) { throw new RuntimeException(e); }
  }

  private Object field(Activity owner, String name) throws Exception {
    var field=owner.getClass().getDeclaredField(name);
    field.setAccessible(true); return field.get(owner);
  }

  @Override public void onCreate(Bundle args) {
    super.onCreate(args);
    runToken=args.getString("runToken");
    if (runToken==null) throw new IllegalArgumentException("missing run token");
    command=new File(getTargetContext().getFilesDir(),"photo-lifecycle-command");
    state=new File(getTargetContext().getFilesDir(),"photo-lifecycle-state");
    command.delete(); state.delete();
    ((Application)getTargetContext().getApplicationContext()).registerActivityLifecycleCallbacks(new Application.ActivityLifecycleCallbacks() {
      public void onActivityCreated(Activity a,Bundle b) { current=a;generation++; }
      public void onActivityResumed(Activity a) { current=a; }
      public void onActivityStarted(Activity a) {}
      public void onActivityPaused(Activity a) {}
      public void onActivityStopped(Activity a) {}
      public void onActivitySaveInstanceState(Activity a,Bundle b) {}
      public void onActivityDestroyed(Activity a) { if (a==previous) previousDestroyed=true; }
    });
    start();
  }

  @Override public void onStart() {
    try {
      startActivitySync(new Intent().setClassName("com.holmes.leanquiet","com.holmes.leanquiet.LeanActivity").addFlags(Intent.FLAG_ACTIVITY_NEW_TASK));
      waitForIdleSync(); state("ready");
      String last="";
      long deadline=SystemClock.elapsedRealtime()+180000;
      while (SystemClock.elapsedRealtime()<deadline) {
        String next=command.exists()?new String(Files.readAllBytes(command.toPath()),StandardCharsets.UTF_8).trim():"";
        if (!next.isEmpty() && !next.equals(last)) {
          last=next;
          if (next.equals("gate-decode")) {
            decodeGate=new CountDownLatch(1);
            CountDownLatch entered=new CountDownLatch(1);
            ((ExecutorService)field(current,"photoWorker")).execute(() -> {
              entered.countDown();
              boolean interrupted=false;
              for (;;) {
                try { decodeGate.await(); break; }
                catch (InterruptedException e) { interrupted=true; }
              }
              if (interrupted) Thread.currentThread().interrupt();
            });
            if (!entered.await(2,java.util.concurrent.TimeUnit.SECONDS)) throw new AssertionError("actual photo executor did not enter gate");
            state("decode-gated");
          } else if (next.startsWith("recreate")) {
            previous=current;
            previousDestroyed=false;
            int before=generation;
            runOnMainSync(previous::recreate);
            long until=SystemClock.elapsedRealtime()+5000;
            while (!previousDestroyed && SystemClock.elapsedRealtime()<until) SystemClock.sleep(10);
            if (!previousDestroyed) throw new AssertionError("old Activity did not destroy");
            state("owner-destroyed");
            while (generation==before && SystemClock.elapsedRealtime()<until) SystemClock.sleep(10);
            if (generation==before || current==previous) throw new AssertionError("Activity did not recreate");
            waitForIdleSync(); state("recreated");
          } else if (next.equals("release-decode")) {
            decodeGate.countDown(); state("decode-released");
          } else if (next.equals("stale-photo")) {
            if (previous==null) throw new AssertionError("no old Activity");
            runOnMainSync(() -> {
              try {
                int token=(Integer)field(current,"photoToken");
                if (token==0) throw new AssertionError("replacement has no real outstanding request");
                // Deliberately match the current finite token, as after reuse:
                // owner identity must still reject this destroyed instance.
                var method=previous.getClass().getDeclaredMethod("nPhoto",int.class,int.class,int.class,int.class,byte[].class);
                method.setAccessible(true);
                method.invoke(previous,token,1,1,1,new byte[]{0,0,0,(byte)255});
              } catch (Exception e) { throw new RuntimeException(e); }
            });
            state("stale-photo-delivered");
          } else if (next.equals("done")) { state("done"); return; }
          else throw new AssertionError("unknown command "+next);
        }
        SystemClock.sleep(10);
      }
      throw new AssertionError("photo lifecycle total deadline");
    } catch (Throwable error) {
      android.util.Log.e("PhotoLifecycleProbe","fixture failed",error);
      state("failed");
    } finally {
      if (decodeGate!=null) decodeGate.countDown();
    }
  }
}
