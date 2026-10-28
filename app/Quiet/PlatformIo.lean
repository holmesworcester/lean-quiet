/- The platform effects as the running app's Io, shared with seam tests. -/
import Quiet.App

namespace App

def Io.platform : Io :=
  ⟨Platform.screen, Platform.scroll, Platform.scrollBy, Platform.scrollTo, Platform.frame, Platform.text,
   Platform.ime, Platform.textClear, fun t => Platform.copy t, Platform.ctlPoll, fun s => Platform.ctlReply s, Platform.nowUs,
   Platform.scan, Platform.luma, Platform.appearance⟩

end App
