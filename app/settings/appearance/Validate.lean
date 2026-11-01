import app.settings.appearance.Op

namespace Settings
open Engine Codec

namespace Appearance

/-- It cites nothing; its number must name a setting. -/
def check (o : Op) : Body → Option Fact
  | ⟨rev, choice⟩ => if o.reqs = [] then (ofCode choice).map (⟨rev, ·⟩) else none

end Appearance

end Settings
