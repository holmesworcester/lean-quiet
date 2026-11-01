package com.holmes.ownedinput;

import android.app.Activity;
import android.app.Application;
import android.app.Instrumentation;
import android.content.Intent;
import android.os.Bundle;
import android.os.Process;
import android.os.SystemClock;
import android.view.inputmethod.EditorInfo;
import android.view.KeyEvent;
import android.view.MotionEvent;
import android.view.WindowInsets;
import android.widget.EditText;
import java.io.File;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

/** Test-only gating; text and send callbacks are the real Activity's listeners. */
public final class OwnedInputProbe extends Instrumentation {
  static { System.loadLibrary("input_probe"); }
  private static native void attach(String path);
  private static native void hold(boolean value);
  private static native long blocked();
  private static native void holdView(boolean value);
  private static native void failCopy(int site);
  private static native long failedCopies(int site);
  private volatile Activity current;
  private volatile boolean resumed;
  private File command, state;
  private String token;
  private void onUi(Runnable action) {
    java.util.concurrent.atomic.AtomicReference<Throwable> failure=new java.util.concurrent.atomic.AtomicReference<>();
    super.runOnMainSync(() -> {try{action.run();}catch(Throwable error){failure.set(error);}});
    if(failure.get()!=null)throw new AssertionError("actual UI probe assertion",failure.get());
  }
  private void state(String phase) {
    try { Files.write(state.toPath(), (phase+" "+Process.myPid()+" "+token+"\n").getBytes(StandardCharsets.UTF_8)); }
    catch (Exception e) { throw new RuntimeException(e); }
    android.util.Log.i("OwnedInputProbe",phase+" pid="+Process.myPid());
  }
  private EditText editor() throws Exception {
    var f=current.getClass().getDeclaredField("edit"); f.setAccessible(true);
    return (EditText)f.get(current);
  }
  @Override public void onCreate(Bundle args) {
    super.onCreate(args); token=args.getString("runToken");
    if (token==null) throw new IllegalArgumentException("missing token");
    command=new File(getTargetContext().getFilesDir(),"input-race-command");
    state=new File(getTargetContext().getFilesDir(),"input-race-state");
    command.delete(); state.delete();
    ((Application)getTargetContext().getApplicationContext()).registerActivityLifecycleCallbacks(new Application.ActivityLifecycleCallbacks() {
      public void onActivityCreated(Activity a, Bundle b) { current=a; }
      public void onActivityResumed(Activity a) { current=a;resumed=true; }
      public void onActivityStarted(Activity a) {}
      public void onActivityPaused(Activity a) { if(current==a)resumed=false; }
      public void onActivityStopped(Activity a) {}
      public void onActivitySaveInstanceState(Activity a,Bundle b) {}
      public void onActivityDestroyed(Activity a) {}
    }); start();
  }
  private long fieldLong(String name) throws Exception {
    var f=current.getClass().getDeclaredField(name);f.setAccessible(true);return f.getLong(current);
  }
  private int fieldInt(String name) throws Exception {
    var f=current.getClass().getDeclaredField(name);f.setAccessible(true);return f.getInt(current);
  }
  private void capture(String name) {
    onUi(() -> {
      try {Files.write(new File(getTargetContext().getFilesDir(),name+".txt").toPath(),
        ("editor="+editor().getText()+"\nowner="+fieldLong("editorOwner")+
         "\nrevision="+fieldLong("editorRevision")+"\nrefusal="+fieldInt("lastActionRefusal")+
         "\nclear="+fieldLong("pendingClearTicket")+"\nreceipt="+fieldLong("lastActionTicket")+
         ":"+fieldInt("lastActionDisposition")+"\n").getBytes(StandardCharsets.UTF_8));
      }catch(Exception e){throw new RuntimeException(e);}
    });
  }
  private void readyEditor() {
    boolean[] ready={false};long end=SystemClock.elapsedRealtime()+3000;
    while(!ready[0]&&SystemClock.elapsedRealtime()<end) {
      onUi(() -> {try{ready[0]=fieldLong("editorOwner")!=0&&fieldLong("editorRevision")!=0&&editor().isEnabled();}
        catch(Exception e){throw new RuntimeException(e);}});
      if(!ready[0])SystemClock.sleep(5);
    }
    if(!ready[0])throw new AssertionError("actual Field never installed an owned editor");
  }
  private void gate() {
    readyEditor();long before=blocked();hold(true);long end=SystemClock.elapsedRealtime()+2000;
    while(blocked()==before&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(2);
    if(blocked()==before)throw new AssertionError("actual pump did not observe gate");
  }
  private void submit(String name,boolean newer,boolean busy,boolean hardware) {
    gate();onUi(() -> {
      try {
        faultPreviousReceipt=fieldLong("lastActionTicket");
        EditText e=editor();String a=name+"_A";e.setText(a);e.setSelection(a.length());
        if(hardware) {
          if(!e.dispatchKeyEvent(new KeyEvent(KeyEvent.ACTION_DOWN,KeyEvent.KEYCODE_ENTER))||
             !e.dispatchKeyEvent(new KeyEvent(KeyEvent.ACTION_UP,KeyEvent.KEYCODE_ENTER)))
            throw new AssertionError("actual physical Enter gesture was not consumed");
        }else e.onEditorAction(EditorInfo.IME_ACTION_SEND);
        if(fieldInt("lastActionRefusal")!=0)throw new AssertionError("first action refused");
        if(newer||busy){e.setText(name+"_B");e.setSelection(e.length());}
        if(busy) {
          e.onEditorAction(EditorInfo.IME_ACTION_SEND);
          if(fieldInt("lastActionRefusal")!=1)throw new AssertionError("second action must explicitly refuse busy");
        }
        if(e.getText().toString().contains("\n"))throw new AssertionError("Enter inserted fallback newline");
      }catch(Exception e){throw new RuntimeException(e);}
    });capture(name+"-queued");
  }
  private void delayedClear(String name) {
    gate();onUi(() -> {
      try {
        EditText e=editor();e.setText(name+"_A");e.setSelection(e.length());
        e.onEditorAction(EditorInfo.IME_ACTION_SEND);hold(false);
        long end=SystemClock.elapsedRealtime()+2500;
        while(fieldLong("pendingClearTicket")==0&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(2);
        if(fieldLong("pendingClearTicket")==0)throw new AssertionError("actual App did not issue async compare-clear");
        e.setText(name+"_B");e.setSelection(e.length());
      }catch(Exception e){throw new RuntimeException(e);}
    });capture(name+"-released");
  }
  private float[] sendPoint() {
    float[] p=new float[2];onUi(() -> {
      int dpi=current.getResources().getDisplayMetrics().densityDpi;
      android.graphics.Rect b=current.getWindowManager().getCurrentWindowMetrics().getBounds();
      android.graphics.Insets in=current.getWindow().getDecorView().getRootWindowInsets().getInsets(WindowInsets.Type.navigationBars());
      p[0]=b.width()-32*dpi/160;p[1]=b.height()-in.bottom-32*dpi/160;
    });return p;
  }
  private void pointer(float[] p,boolean longPress) {
    long down=SystemClock.uptimeMillis();
    sendPointerSync(MotionEvent.obtain(down,down,MotionEvent.ACTION_DOWN,p[0],p[1],0));
    SystemClock.sleep(longPress?750:70);
    sendPointerSync(MotionEvent.obtain(down,SystemClock.uptimeMillis(),MotionEvent.ACTION_UP,p[0],p[1],0));
  }
  private float[] pendingPoint;
  private long pendingDown;
  private void touchUp() {
    gate();sendPointerSync(MotionEvent.obtain(pendingDown,SystemClock.uptimeMillis(),MotionEvent.ACTION_UP,pendingPoint[0],pendingPoint[1],0));
    onUi(() -> {try{EditText e=editor();e.setText("touch_B");e.setSelection(e.length());}
      catch(Exception e){throw new RuntimeException(e);}});
    capture("touch-queued");
  }
  private void touch(String name,boolean longPress) {
    readyEditor();onUi(() -> {try{
      current.getClass().getMethod("showIme",boolean.class).invoke(current,false);
      EditText e=editor();e.setText(name+"_A");e.setSelection(e.length());
    }catch(Exception e){throw new RuntimeException(e);}});
    SystemClock.sleep(350);
    if(longPress){pointer(sendPoint(),true);capture(name+"-queued");}
    else {
      pendingPoint=sendPoint();pendingDown=SystemClock.uptimeMillis();
      sendPointerSync(MotionEvent.obtain(pendingDown,pendingDown,MotionEvent.ACTION_DOWN,pendingPoint[0],pendingPoint[1],0));
    }
  }
  private void gateField(String name,boolean value) throws Exception {
    var field=current.getClass().getDeclaredField(name);field.setAccessible(true);field.setBoolean(null,value);
  }
  private Object gateValue(String name) throws Exception {
    var field=current.getClass().getDeclaredField(name);field.setAccessible(true);return field.get(null);
  }
  private void holdClear(String name) throws Exception {
    readyEditor();gateField("ownedTestHoldClear",true);
    onUi(() -> {try{
      EditText e=editor();e.setText(name+"_A");e.setSelection(e.length());e.onEditorAction(EditorInfo.IME_ACTION_SEND);
      if(fieldInt("lastActionRefusal")!=0)throw new AssertionError("clear-gated Send refused");
    }catch(Exception e){throw new RuntimeException(e);}});
    long end=SystemClock.elapsedRealtime()+2500;
    while(gateValue("ownedTestClear")==null&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(2);
    if(gateValue("ownedTestClear")==null||fieldLong("pendingClearTicket")==0)
      throw new AssertionError("actual clear Runnable was not retained");
    capture(name+"-held");
  }
  private void type(String text) {
    onUi(() -> {try{EditText e=editor();e.setText(text);e.setSelection(e.length());}
      catch(Exception e){throw new RuntimeException(e);}});
  }
  private void awaitResumed(boolean expected) {
    long end=SystemClock.elapsedRealtime()+3000;
    while(resumed!=expected&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
    if(resumed!=expected)throw new AssertionError("actual Activity lifecycle state not reached");
  }
  private void recreate() {
    Activity previous=current;onUi(previous::recreate);
    long end=SystemClock.elapsedRealtime()+5000;
    while((current==previous||!resumed)&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
    if(current==previous||!resumed)throw new AssertionError("actual Activity was not replaced");
    readyEditor();
  }
  private long faultPreviousReceipt;
  private void recreateUninstalled() throws Exception {
    gateField("ownedTestHoldInstall",true);Activity previous=current;onUi(previous::recreate);
    long end=SystemClock.elapsedRealtime()+5000;
    while((current==previous||!resumed||gateValue("ownedTestInstall")==null)&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
    if(current==previous||!resumed||gateValue("ownedTestInstall")==null)throw new AssertionError("ownerless replacement interval not established");
    onUi(() -> {try{
      EditText e=editor();String before=e.getText().toString();
      if(fieldLong("editorOwner")!=0||e.isEnabled())throw new AssertionError("ownerless Field accepted editing");
      if(e.onCreateInputConnection(new EditorInfo())!=null)throw new AssertionError("ownerless Field exposes an InputConnection");
      e.dispatchKeyEvent(new KeyEvent(KeyEvent.ACTION_DOWN,KeyEvent.KEYCODE_A));
      e.dispatchKeyEvent(new KeyEvent(KeyEvent.ACTION_UP,KeyEvent.KEYCODE_A));
      if(!e.getText().toString().equals(before))throw new AssertionError("ownerless physical typing was silently accepted");
    }catch(Exception e){throw new RuntimeException(e);}});
  }
  private void focusTap() {
    onUi(() -> {try{current.getClass().getMethod("showIme",boolean.class).invoke(current,false);}
      catch(Exception e){throw new RuntimeException(e);}});
    SystemClock.sleep(350);float[] p=sendPoint();
    int dpi=current.getResources().getDisplayMetrics().densityDpi;
    p[0]=80*dpi/160;p[1]-=50*dpi/160;pointer(p,false);
  }
  private boolean wanted() throws Exception {
    var f=current.getClass().getDeclaredField("imeWanted");f.setAccessible(true);return f.getBoolean(current);
  }
  private void awaitFocusRequest() throws Exception {
    long end=SystemClock.elapsedRealtime()+3000;
    while(!wanted()&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
    if(!wanted())throw new AssertionError("first actual App field tap lost its pending IME request");
    if(editor().isEnabled()||fieldLong("editorOwner")!=0)throw new AssertionError("focus request escaped ownerless fixture interval");
    if(fieldInt("lastActionRefusal")!=6)throw new AssertionError("not-ready editor did not report explicit disposition");
  }
  private void focusReady() {
    readyEditor();boolean[] complete={false};long end=SystemClock.elapsedRealtime()+3000;
    // The request bit can retire after Android starts its show animation.
    // Observe its actual effect; exercise.py separately requires real IME
    // height within the original three-second observation bound.
    while(!complete[0]&&SystemClock.elapsedRealtime()<end) {
      onUi(() -> {try{complete[0]=editor().isEnabled()&&editor().hasFocus()&&
        editor().onCreateInputConnection(new EditorInfo())!=null;
      }catch(Exception e){throw new RuntimeException(e);}});
      if(!complete[0])SystemClock.sleep(5);
    }
    if(!complete[0])throw new AssertionError("installed editor did not honor first pending focus request");
  }
  private final long[] priorCopyFailures=new long[3];
  private void faultAction(String name,boolean content) {
    gate();onUi(() -> {try {
      faultPreviousReceipt=fieldLong("lastActionTicket");
      EditText e=editor();e.setText(name+"_A");e.setSelection(e.length());
      e.onEditorAction(EditorInfo.IME_ACTION_SEND);
      if(fieldInt("lastActionRefusal")!=0)throw new AssertionError("fault action not admitted");
      priorCopyFailures[content?1:2]=failedCopies(content?1:2);failCopy(content?1:2);
      if(content){e.setText(name+"_B");e.setSelection(e.length());}
    }catch(Exception e){throw new RuntimeException(e);}});
    capture(name+"-queued");
  }
  private void awaitCopyFailure(int site) throws Exception {
    long end=SystemClock.elapsedRealtime()+3000;
    while(failedCopies(site)==priorCopyFailures[site]&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
    if(failedCopies(site)==priorCopyFailures[site])throw new AssertionError("actual allocation site never failed");
    Files.write(new File(getTargetContext().getFilesDir(),"copy-failure-"+site+".txt").toPath(),
      ("site="+site+" failures="+failedCopies(site)+"\n").getBytes(StandardCharsets.UTF_8));
  }
  private void enqueue(boolean race) {
    readyEditor();long before=blocked(); hold(true);
    long until=SystemClock.elapsedRealtime()+2000;
    while (blocked()==before && SystemClock.elapsedRealtime()<until) SystemClock.sleep(2);
    if (blocked()==before) throw new AssertionError("actual native pump did not observe gate");
    onUi(() -> {
      try {
        EditText edit=editor();
        String a=race?"race_A_20261031":"control_A_20261031";
        edit.setText(a); edit.setSelection(a.length());
        edit.onEditorAction(EditorInfo.IME_ACTION_SEND);
        if(race) { edit.setText("race_B_20261031"); edit.setSelection(edit.length()); }
        String expected=race?"race_B_20261031":a;
        if (!edit.getText().toString().equals(expected)) throw new AssertionError("real editor did not retain expected text");
        Files.write(new File(getTargetContext().getFilesDir(),race?"race-enqueued.txt":"control-enqueued.txt").toPath(),
          ("TEXT("+a+") SEND"+(race?" TEXT(race_B_20261031)":"")+"\neditor="+edit.getText()+"\nblocked="+blocked()+"\n").getBytes(StandardCharsets.UTF_8));
      } catch(Exception e) {throw new RuntimeException(e);}
    });
  }
  @Override public void onStart() {
    try {
      startActivitySync(new Intent().setClassName("com.holmes.leanquiet","com.holmes.leanquiet.LeanActivity").addFlags(Intent.FLAG_ACTIVITY_NEW_TASK));
      waitForIdleSync();
      attach(current.getApplicationInfo().nativeLibraryDir+"/libleanapp.so");
      state("ready"); String last="";
      long deadline=SystemClock.elapsedRealtime()+180000;
      while(SystemClock.elapsedRealtime()<deadline) {
        String next=command.exists()?new String(Files.readAllBytes(command.toPath()),StandardCharsets.UTF_8).trim():"";
        if(!next.isEmpty()&&!next.equals(last)) {
          last=next;
          if(next.equals("control")) { enqueue(false); state("control-queued"); }
          else if(next.equals("race")) { enqueue(true); state("race-queued"); }
          else if(next.equals("community")||next.equals("profile")||next.equals("createdpost")) {submit(next,true,false,next.equals("profile"));state(next+"-queued");}
          else if(next.equals("hardware")) {submit("hardware",false,false,true);state("hardware-queued");}
          else if(next.equals("busy")) {submit("busy",true,true,false);state("busy-queued");}
          else if(next.equals("geometry")) {submit("geometry",false,false,false);holdView(true);state("geometry-queued");}
          else if(next.equals("stale")) {submit("stale",false,false,false);state("stale-queued");}
          else if(next.equals("lateclear")) {delayedClear("lateclear");state("lateclear-released");}
          else if(next.equals("touch")) {touch("touch",false);state("touch-down");}
          else if(next.equals("touch-up")) {touchUp();state("touch-queued");}
          else if(next.equals("long")) {touch("long",true);state("long-queued");}
          else if(next.startsWith("holdclear")) {holdClear(next);state(next+"-held");}
          else if(next.startsWith("type-")) {type(next.substring(5));state(next);}
          else if(next.equals("await-paused")) {awaitResumed(false);state(next);}
          else if(next.equals("await-resumed")) {awaitResumed(true);readyEditor();state(next);}
          else if(next.equals("recreate")) {recreate();state(next);}
          else if(next.equals("release-clear")) {current.getClass().getMethod("ownedTestReleaseClear").invoke(current);state(next);}
          else if(next.equals("hold-install")) {gateField("ownedTestHoldInstall",true);state(next);}
          else if(next.equals("release-install")) {current.getClass().getMethod("ownedTestReleaseInstall").invoke(current);state(next);}
          else if(next.equals("await-install")) {
            long end=SystemClock.elapsedRealtime()+3000;
            while(gateValue("ownedTestInstall")==null&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
            if(gateValue("ownedTestInstall")==null)throw new AssertionError("actual install Runnable was not retained");state(next);
          }
          else if(next.equals("snapshotfault")) {faultAction(next,false);state(next+"-queued");}
          else if(next.equals("contentfault")) {faultAction(next,true);state(next+"-queued");}
          else if(next.equals("await-snapshot-fault")) {awaitCopyFailure(2);state(next);}
          else if(next.equals("await-latest-fault")) {awaitCopyFailure(1);state(next);}
          else if(next.equals("await-refused")) {
            long end=SystemClock.elapsedRealtime()+3000;
            while((fieldLong("lastActionTicket")==faultPreviousReceipt||fieldInt("lastActionDisposition")!=2)&&SystemClock.elapsedRealtime()<end)SystemClock.sleep(5);
            if(fieldLong("lastActionTicket")==faultPreviousReceipt||fieldInt("lastActionDisposition")!=2)throw new AssertionError("actual App did not explicitly refuse new action");state(next);
          }
          else if(next.equals("hold-latest-copy")) {priorCopyFailures[1]=failedCopies(1);failCopy(1);state(next);}
          else if(next.equals("recover-copy")) {failCopy(-1);state(next);}
          else if(next.equals("resend")) {onUi(() -> {try {editor().onEditorAction(EditorInfo.IME_ACTION_SEND);}
            catch(Exception e){throw new RuntimeException(e);}});state(next);}
          else if(next.equals("clearthrow")) {
            readyEditor();gateField("ownedTestFailClear",true);
            onUi(() -> {try{EditText e=editor();e.setText("clearthrow_A");e.setSelection(e.length());
              e.onEditorAction(EditorInfo.IME_ACTION_SEND);
              if(fieldInt("lastActionRefusal")!=0)throw new AssertionError("clear-throw initial action refused");
            }catch(Exception e){throw new RuntimeException(e);}});state(next);
          }
          else if(next.equals("repeat-consumed")) {
            onUi(() -> {try{
              if(!editor().getText().toString().equals("clearthrow_A"))throw new AssertionError("throw fixture did not retain raw consumed text");
              editor().onEditorAction(EditorInfo.IME_ACTION_SEND);
              if(fieldInt("lastActionRefusal")!=2)throw new AssertionError("already consumed revision was admitted again after clear-post failure");
            }catch(Exception e){throw new RuntimeException(e);}});state(next);
          }
          else if(next.equals("home")) {submit("home",false,false,true);state("home-queued");}
          else if(next.startsWith("recreate-uninstalled")) {recreateUninstalled();state(next);}
          else if(next.startsWith("focus-tap")) {focusTap();awaitFocusRequest();state(next);}
          else if(next.equals("focus-ready")) {focusReady();state(next);}
          else if(next.equals("hide-ime")) {onUi(() -> {try{current.getClass().getMethod("showIme",boolean.class).invoke(current,false);}
            catch(Exception e){throw new RuntimeException(e);}});state(next);}
          else if(next.equals("focus-cancelled")) {readyEditor();if(wanted())throw new AssertionError("installation resurrected cancelled focus request");state(next);}
          else if(next.startsWith("capture-")) {capture(next);state(next);}
          else if(next.startsWith("release-")) { hold(false); state(next); }
          else if(next.equals("done")) { state("done"); return; }
          else throw new AssertionError("unknown command "+next);
        }
        SystemClock.sleep(5);
      }
      throw new AssertionError("instrumentation deadline");
    } catch(Throwable error) { android.util.Log.e("OwnedInputProbe","fixture failed",error);state("failed"); }
    finally {hold(false);}
  }
}
