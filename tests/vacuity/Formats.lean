import engine.renderer.qr.SegLaws
import engine.renderer.qr.Laws
import engine.renderer.qr.Format
import engine.wire.mdns.Laws

namespace Vacuity.Formats
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.defProp false
open Qr

def segments : List Seg := [.numeric [49, 50, 51], .alnum [81, 85, 73, 69, 84], .bytes [0, 254, 255]]
theorem segmentsValid : ∀ s ∈ segments, s.Valid 1 := by
  simp [segments, Seg.Valid, isDigit, alnumIdx, countWidth]

def tailBits := [false, false, false, false]
theorem ended : Ended tailBits := Or.inr ⟨[], rfl⟩
theorem segmentRound : parse 1 (segsBits 1 segments ++ tailBits) = some segments :=
  parse_segsBits segments tailBits segmentsValid ended

def segmentSound := parse_valid (v := 1) (segsBits 1 segments ++ tailBits).length
  (segsBits 1 segments ++ tailBits) rfl segmentRound

-- Exactly 19 data bytes in a version-1 L symbol.
def stream := (dataStream 1 19 segments).getD []
theorem encoded : dataStream 1 19 segments = some stream := by decide +kernel
theorem streamRound : parse 1 (bytesBits stream) = some segments := parse_dataStream segmentsValid encoded
example : stream.length = 19 := by decide +kernel
example : dataStream 1 1 segments = none := by decide +kernel
example : ¬ (Seg.numeric [65]).Valid 1 := by simp [Seg.Valid, isDigit]

def formatDamaged := (formatBits .M 3) ^^^ 7
theorem formatRound : decodeFormat formatDamaged = some (.M, 3) :=
  decodeFormat_correct (by decide) (by decide +kernel)
def versionDamaged := (bchVersion 7) ^^^ 7
theorem versionRound : decodeVersion versionDamaged = some 7 :=
  decodeVersion_correct (by decide) (by decide) (by decide +kernel)
example : hd 15 (formatBits .M 3) formatDamaged = 3 := by decide +kernel
example : ¬ hd 15 (formatBits .M 3) ((formatBits .M 3) ^^^ 15) ≤ 3 := by decide +kernel

-- Two parity symbols, three nonzero payload bytes, one corrupted symbol.
def rsData : Array UInt8 := #[65, 66, 67]
def rsClean : Array UInt8 := rsData ++ RS.encode 2 rsData
theorem rsSyndromes : ∀ j < 2, RS.eval rsClean (RS.exp j) = 0 := by decide +kernel
theorem rsUnchanged : RS.correct 2 rsClean = some rsClean := RS.correct_clean rsSyndromes
def rsDamaged := rsClean.set! 0 64
theorem rsCorrects : RS.correct 2 rsDamaged = some rsClean := by decide +kernel
def rsSound := RS.correct_sound rsCorrects
example : RS.dist rsDamaged rsClean = 1 := by decide +kernel

open Mdns

def host : Mdns.Name := ["alice".toUTF8.toList, "local".toUTF8.toList]
def service : Mdns.Name := ["_quiet".toUTF8.toList, "_tcp".toUTF8.toList, "local".toUTF8.toList]
def announcement : Mdns.Msg := {
  flags := 0x8400
  questions := [⟨service, tPTR, 1⟩]
  answers := [⟨host, 0x8001, 120, .a [192, 0, 2, 10]⟩,
              ⟨service, 1, 120, .srv 0 0 7447 host⟩]
}
theorem announcementValid : announcement.Valid := by
  simp [Mdns.Msg.Valid, announcement, Mdns.Question.Valid, Mdns.Record.Valid, Mdns.Name.Valid, Mdns.RData.Valid, service, host]
  all_goals decide +kernel

theorem announcementRound : Mdns.decode (Mdns.encode announcement) = some announcement :=
  Mdns.decode_encode announcement announcementValid
theorem announcementSound : announcement.Valid := Mdns.decode_valid announcementRound
theorem decodedRound : Mdns.decode (Mdns.encode announcement) = some announcement :=
  Mdns.decode_roundtrip announcementRound
example : ¬ (Mdns.RData.a [192, 0, 2]).Valid := by simp [Mdns.RData.Valid]
example : Mdns.decode ⟨#[0, 0, 0]⟩ = none := by decide +kernel

end Vacuity.Formats
