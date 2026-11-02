package com.holmes.leanquiet;

import android.app.Notification;
import android.app.NotificationChannel;
import android.app.NotificationManager;
import android.app.PendingIntent;
import android.app.Person;
import android.content.Context;
import android.content.Intent;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.drawable.Icon;
import android.net.Uri;
import android.os.Handler;
import android.os.HandlerThread;
import java.io.FileOutputStream;
import java.io.IOException;
import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

/**
 * Renders Lean's notification cards (app/community/Screen.lean, Notify.packet):
 * one card per conversation, grouped by community, as libquiet's
 * Notifications.kt and ConversationNotifications.kt do. Lean decides what
 * alerts, what stands and what is withdrawn; nothing here keeps a ledger.
 * Packets are applied in order on one thread of their own, so Lean's turn
 * never waits on NotificationManager.
 */
public final class Notifications {
  static final String CHANNEL = "messages";
  private static Handler handler;

  private static synchronized Handler handler() {
    if (handler == null) {
      HandlerThread t = new HandlerThread("notifications");
      t.start();
      handler = new Handler(t.getLooper());
    }
    return handler;
  }

  private static boolean started;

  /** Once per process, before Lean posts: message cards standing from a
   *  process that died are withdrawn. Lean's tracker is per process, so
   *  it could not withdraw them when their messages are read. */
  static synchronized void start(Context context) {
    if (started) return;
    started = true;
    final Context c = context.getApplicationContext();
    handler().post(() -> {
      NotificationManager nm = c.getSystemService(NotificationManager.class);
      for (android.service.notification.StatusBarNotification n : nm.getActiveNotifications()) {
        if (CHANNEL.equals(n.getNotification().getChannelId())) nm.cancel(n.getTag(), n.getId());
      }
    });
  }

  /** From Lean's thread: queue one packet and return. */
  static void post(Context context, String json) {
    final Context c = context.getApplicationContext();
    handler().post(() -> apply(c, json));
  }

  private static Icon icon(JSONObject p) throws JSONException {
    Bitmap b = Bitmap.createBitmap(96, 96, Bitmap.Config.ARGB_8888);
    Canvas c = new Canvas(b);
    Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
    paint.setColor(Color.parseColor(p.getString("color")));
    c.drawCircle(48, 48, 48, paint);
    paint.setColor(Color.WHITE);
    String mark = p.getString("mark");
    paint.setTextSize(mark.length() > 1 ? 32 : 44);
    paint.setTextAlign(Paint.Align.CENTER);
    c.drawText(mark, 48, 48 - (paint.ascent() + paint.descent()) / 2, paint);
    return Icon.createWithBitmap(b);
  }

  static void channel(NotificationManager nm) {
    NotificationChannel ch = new NotificationChannel(CHANNEL, "Messages", NotificationManager.IMPORTANCE_HIGH);
    ch.setDescription("New messages in channels you are not reading.");
    nm.createNotificationChannel(ch);
  }

  static void apply(Context ctx, String json) {
    try {
      JSONObject p = new JSONObject(json);
      NotificationManager nm = ctx.getSystemService(NotificationManager.class);
      String tag = p.getString("tag");
      if (p.getString("action").equals("cancel")) {
        nm.cancel(tag, 0);
        NotificationImages.file(ctx, tag).delete();
        return;
      }
      boolean alert = p.getBoolean("alert");
      if (!alert) {
        // a read or a removal re-renders only a card that still stands
        boolean standing = false;
        for (android.service.notification.StatusBarNotification n : nm.getActiveNotifications()) {
          if (tag.equals(n.getTag())) standing = true;
        }
        if (!standing) return;
      }
      channel(nm);
      Intent open = new Intent(ctx, LeanActivity.class).setAction(Intent.ACTION_VIEW)
          .setData(Uri.parse(p.getString("link")))
          .addFlags(Intent.FLAG_ACTIVITY_NEW_TASK | Intent.FLAG_ACTIVITY_SINGLE_TOP);
      PendingIntent tap = PendingIntent.getActivity(ctx, tag.hashCode(), open,
          PendingIntent.FLAG_UPDATE_CURRENT | PendingIntent.FLAG_IMMUTABLE);
      Person me = new Person.Builder().setName("You").build();
      Notification.MessagingStyle style = new Notification.MessagingStyle(me)
          .setConversationTitle(p.getString("title")).setGroupConversation(true);
      Uri photo = null;
      if (!p.getString("photo").isEmpty()) {
        int w = p.getInt("photoW"), h = p.getInt("photoH");
        byte[] rgba = android.util.Base64.decode(p.getString("photo"), android.util.Base64.DEFAULT);
        if (w > 0 && h > 0 && w <= 128 && h <= 128 && rgba.length == w * h * 4) {
          int[] colors = new int[w * h];
          for (int i = 0; i < colors.length; i++)
            colors[i] = Color.argb(255, rgba[4 * i] & 255, rgba[4 * i + 1] & 255, rgba[4 * i + 2] & 255);
          Bitmap bitmap = Bitmap.createBitmap(colors, w, h, Bitmap.Config.ARGB_8888);
          try (FileOutputStream file = new FileOutputStream(NotificationImages.file(ctx, tag))) {
            bitmap.compress(Bitmap.CompressFormat.PNG, 100, file);
          }
          photo = Uri.parse("content://" + ctx.getPackageName() + ".notifications/" + tag);
        }
      } else NotificationImages.file(ctx, tag).delete();
      JSONArray messages = p.getJSONArray("messages");
      for (int i = 0; i < messages.length(); i++) {
        JSONObject m = messages.getJSONObject(i);
        Person sender = new Person.Builder().setName(m.getString("sender"))
            .setKey(m.getString("senderId")).setIcon(icon(m)).build();
        long time = m.getLong("time");
        if (photo != null && i == messages.length() - 1)
          style.addMessage(new Notification.MessagingStyle.Message("Photo", time, sender).setData("image/png", photo));
        style.addMessage(new Notification.MessagingStyle.Message(m.getString("body"), time, sender));
      }
      Icon communityIcon = icon(p);
      android.content.pm.ShortcutInfo shortcut = new android.content.pm.ShortcutInfo.Builder(ctx, tag)
          .setShortLabel(p.getString("title")).setIntent(open).setLongLived(true).setIcon(communityIcon).build();
      ctx.getSystemService(android.content.pm.ShortcutManager.class).pushDynamicShortcut(shortcut);
      Notification.Builder b = new Notification.Builder(ctx, CHANNEL)
          .setSmallIcon(android.R.drawable.stat_notify_chat).setStyle(style)
          .setContentTitle(p.getString("title")).setContentText(p.getString("body"))
          .setGroup(p.getString("group")).setCategory(Notification.CATEGORY_MESSAGE)
          .setVisibility(Notification.VISIBILITY_PRIVATE)
          .setNumber(p.getInt("count")).setContentIntent(tap).setAutoCancel(true)
          .setLargeIcon(communityIcon).setShortcutId(tag)
          .setOnlyAlertOnce(!alert);
      nm.notify(tag, 0, b.build());
    } catch (JSONException | SecurityException | IOException | IllegalArgumentException e) {
      android.util.Log.e("lean", "notification: " + e.getMessage());
    }
  }
}
