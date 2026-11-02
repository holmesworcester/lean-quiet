package com.holmes.leanquiet;

import android.content.ContentProvider;
import android.content.ContentValues;
import android.content.Context;
import android.database.Cursor;
import android.net.Uri;
import android.os.ParcelFileDescriptor;
import java.io.File;
import java.io.FileNotFoundException;

/** Read-only inline photo previews handed to NotificationManager: one PNG per card. */
public final class NotificationImages extends ContentProvider {
  @Override public boolean onCreate() { return true; }

  static File file(Context c, String tag) { return new File(c.getCacheDir(), "notify-" + tag + ".png"); }

  @Override public String getType(Uri uri) { return "image/png"; }

  @Override public ParcelFileDescriptor openFile(Uri uri, String mode) throws FileNotFoundException {
    String tag = uri.getLastPathSegment();
    if (!"r".equals(mode) || tag == null || !tag.matches("[0-9a-f]{64}")) throw new FileNotFoundException();
    return ParcelFileDescriptor.open(file(getContext(), tag), ParcelFileDescriptor.MODE_READ_ONLY);
  }

  @Override public Cursor query(Uri u, String[] p, String s, String[] a, String o) { return null; }
  @Override public Uri insert(Uri u, ContentValues v) { throw new UnsupportedOperationException(); }
  @Override public int update(Uri u, ContentValues v, String s, String[] a) { throw new UnsupportedOperationException(); }
  @Override public int delete(Uri u, String s, String[] a) { throw new UnsupportedOperationException(); }
}
