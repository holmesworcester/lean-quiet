import app.community.Family

namespace Community
open Engine Codec

/-- An attachment of file f to message `msg` of c, by `by_` (admitted
as `adm`), its meta sealed under content key k; and the file's chunks
(`attach_chunks`: chunk i is `fileChunk`). The root and every proof
come from one pass over the file (`Merkle.rootAndProofs`). -/
def attach (c adm msg : Id) (by_ : Device) (k : Key32) (f : NewFile) : Op × List Op :=
  let ct := fileCipher f
  let tree := Merkle.rootAndProofs sha256 ct
  let root := tree.1
  let kid := kidOf cryptoSeal k
  let m := encode (f.info.name, f.info.kind, f.info.w, f.info.h, f.info.preview, f.key.1, f.nonce.1)
  let sealed := f.metaNonce ++ sealBody cryptoSeal k f.metaNonce c kid m
  let reqs := [c, adm, msg]
  let a := mkOp reqs (.attach root ct.size kid sealed (sig by_.sk reqs (.attach root ct.size kid sealed .empty)))
  let chunks := (List.range (Merkle.nChunks ct.size)).map fun i =>
    mkOp [c, a.id] (.chunk root ct.size i (Merkle.slice ct i) (tree.2.getD i []))
  (a, chunks)
open Engine
section
variable {s : DB Fact} {C : Crypto}

/-- The key of an attachment's chunk list. -/
def chunkKey (c att : Id) : ByteArray := chunk.byAttachment.key [c, att]

/-- How many of an attachment's chunks this device holds (Valid), and
how many its file has (len is the attachment's). -/
def progress (c att : Id) (len : Nat) : View Fact (Nat × Nat) := do
  let a ← chunk.byAttachment.read [c, att] (limit := some 0)
  pure (a.total, Merkle.nChunks len)

end
end Community
