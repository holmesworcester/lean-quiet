import app.community.caughtUp.Op

namespace Community
open Engine Codec

namespace CaughtUp

/-- Local, citing nothing: this device's own mark. -/
def check : Body → Option Fact
  | ⟨c, mark⟩ => some ⟨c, mark⟩

end CaughtUp

end Community
