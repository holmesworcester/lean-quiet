package com.holmes.leanquiet;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Service;
import android.content.Context;
import android.content.Intent;
import android.content.pm.ServiceInfo;
import android.os.IBinder;

/**
 * Sync in the background: a foreground service that keeps Quiet's process
 * (Lean's node, reader and notifications) running while the app is off
 * screen, after libquiet's SyncService.kt: a dataSync service, not sticky,
 * no wake lock, an ongoing "Quiet is syncing" notification on a quiet
 * channel that opens the app. Lean turns it on and off with the setting
 * (You > On this device > Sync in the background); it changes nothing else.
 */
public final class SyncService extends Service {
  static final String CHANNEL = "sync";

  /** On or off. Started while the app is in front (Android forbids
   *  starting a foreground service from the background). */
  static void set(Context ctx, boolean on) {
    Context c = ctx.getApplicationContext();
    Intent i = new Intent(c, SyncService.class);
    try {
      if (on) c.startForegroundService(i);
      else c.stopService(i);
    } catch (RuntimeException e) {
      android.util.Log.e("lean", "sync service: " + e.getMessage());
    }
  }

  @Override public int onStartCommand(Intent intent, int flags, int startId) {
    NotificationManager nm = getSystemService(NotificationManager.class);
    NotificationChannel ch = new NotificationChannel(CHANNEL, "Syncing", NotificationManager.IMPORTANCE_LOW);
    ch.setDescription("Shown while Quiet keeps syncing in the background.");
    ch.setShowBadge(false);
    nm.createNotificationChannel(ch);
    Intent open = new Intent(this, LeanActivity.class)
        .setAction(Intent.ACTION_MAIN).addCategory(Intent.CATEGORY_LAUNCHER);
    PendingIntent tap = PendingIntent.getActivity(this, 1, open,
        PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
    Notification n = new Notification.Builder(this, CHANNEL)
        .setSmallIcon(android.R.drawable.stat_notify_sync)
        .setContentTitle("Quiet is syncing")
        .setCategory(Notification.CATEGORY_SERVICE)
        .setOngoing(true).setShowWhen(false).setContentIntent(tap).build();
    startForeground(1, n, ServiceInfo.FOREGROUND_SERVICE_TYPE_DATA_SYNC);
    return START_NOT_STICKY;
  }

  /** Android 15's daily dataSync limit: stop, as libquiet does. */
  public void onTimeout(int startId, int fgsType) { stopSelf(); }

  @Override public IBinder onBind(Intent intent) { return null; }
}
