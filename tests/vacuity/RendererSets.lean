import ops.community.Screen
import ops.Screen
import engine.renderer.Data
import engine.renderer.LiveLaws
import ops.community.channel.message.draft.View
import engine.renderer.bidi.Laws

set_option linter.defProp false
namespace Vacuity.RendererSets
open Engine Community Data

def c : Id := ByteArray.mk #[1]
def u : Id := ByteArray.mk #[2]
def profileA : Fact := .profile c u (ByteArray.mk #[65, 108, 105, 99, 101]) 10
def profileB : Fact := .profile c (ByteArray.mk #[3]) (ByteArray.mk #[66, 111, 98]) 11
def rows : List (Pos × Fact) := [((.empty, ByteArray.mk #[1]), profileA),
  ((.empty, ByteArray.mk #[2]), profileA), ((.empty, ByteArray.mk #[3]), profileB)]
def author : Fact → Option Id
  | .profile _ id _ _ => some id
  | _ => none
attribute [local instance] LiveLaws.byteArray_lawful

def setMembers := Data.projectSet_mem rows author u
def setUnique := Data.projectSet_nodup rows author
example : (Data.projectSet rows author).length = 2 := by decide

-- Two entries have the same display name/community, then one acceptance repeats.
def entry (a community : UInt8) : Kinds.Accepted.Me :=
  { acc := ByteArray.mk #[a], dev := Device.ofSeed (ByteArray.mk #[17]),
    seed := ByteArray.mk #[17], dev_ok := rfl, c := ByteArray.mk #[community],
    adm := ByteArray.mk #[0xAD], name := "Same name" }
def entries := #[entry 1 7, entry 2 7, entry 3 8, entry 1 9]
def acceptanceUnique := Switch.dedupe_nodup entries
def communityUnique := Switch.dedupe_one_per_community entries
private theorem hasSecond : 1 < (Kinds.Accepted.dedupe entries).size := by decide
def tapped := Switch.select_tapped_dedupe entries 1 hasSecond
example : (Kinds.Accepted.dedupe entries).size = 2 := by decide

def pages : Array Pages.Entry := #[⟨"Pending", "00000001", 0, false, true⟩,
  ⟨"Current", "00000002", 3, true, false⟩, ⟨"Other", "00000003", 1, false, false⟩]
def switcherSound := Pages.switcherOrder_sound pages (p := (1, pages[1])) (by
  simp [Pages.switcherOrder, pages])
def switcherComplete := Pages.switcherOrder_complete pages 0 (by decide)
example : (Pages.switcherOrder pages).map (·.1) = [1, 2, 0] := by decide

def dim : Row.Dim := default
def chipsApart := Composer.chips_apart dim 180 (i := 0) (j := 1) (by decide)
def closeClear := Composer.x_clear dim 180 (i := 0) (j := 1) (by decide)
def chipsFit := Composer.chips_fit dim 180 1280 (i := 3) (by decide) (by decide)

-- Numeric-run membership is concrete and nonempty at the shared bidi layer.
def digits : List (UInt32 × Text.Bidi.Class) := [(65, .l), (49, .en), (50, .en), (66, .l)]
def numberRun := Text.Bidi.run_contiguous .en false digits [49, 50] (by decide)

end Vacuity.RendererSets
