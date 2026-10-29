import Quiet

namespace App

def Io.platform : Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs,
   do return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, (← Platform.tzMin).toInt),
   Platform.scan, Platform.luma, Platform.log, (fun t => Platform.setText t), Platform.poll, Platform.links, Platform.motion, Platform.appearance, Platform.bars, Platform.pickPhoto, Platform.photoResult⟩

end App
