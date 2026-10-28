/-
UX laws over the running home page. Stored connection sessions must
not be presented as a person's presence (`sessions_not_presence`).
Anchor and Label carry their own laws; these imports audit them too.
-/
import Quiet.Pages
import Quiet.Anchor

namespace UxLaws

theorem sessions_not_presence (f : Font.Font) (dm : Row.Dim) (W h waiting : Nat)
    (channels : Array String) (people : Array (String × Bool)) (sessions : Array Bool) :
    Pages.home f dm W h waiting channels people sessions =
      Pages.home f dm W h waiting channels people #[] := rfl

end UxLaws
