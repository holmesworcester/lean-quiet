import app.community.channel.message.draft.Op

namespace Community
open Engine Codec

namespace Draft

/-- It cites nothing: any text is a draft. -/
def check (o : Op) : Body → Option Fact
  | ⟨acc, gen, text, pics⟩ => if o.reqs = [] then some ⟨acc, gen, text, pics⟩ else none

end Draft

end Community
