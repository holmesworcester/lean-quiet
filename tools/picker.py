#!/usr/bin/env python3
"""Builds assets/picker.txt, the reaction catalogue, from libquiet's own
emoji list (app/src/emoji-data.json: emojibase, capped at the Emoji
version libquiet's platforms draw, components dropped).

One line per emoji, in libquiet's order:
  group TAB emoji TAB its five single-tone variants (space-separated, or
  empty) TAB label TAB tags (space-separated)
Multi-person emoji keep only their five same-tone variants, as libquiet's
`toned` picks.

    git -C ~/libquiet show origin/main:app/src/emoji-data.json > data.json
    python3 tools/picker.py data.json assets/picker.txt
"""
import json, re, sys

TONES = [chr(c) for c in range(0x1F3FB, 0x1F400)]

def main(src, dst):
    out = []
    for e in json.load(open(src, encoding="utf-8")):
        skins = []
        for t in TONES:
            pick = next((s["unicode"] for s in e.get("skins", [])
                         if (m := re.findall("[\U0001F3FB-\U0001F3FF]", s["unicode"]))
                         and all(x == t for x in m)), "")
            skins.append(pick)
        sk = " ".join(skins) if all(skins) else ""
        out.append("\t".join([str(e.get("group", 0)), e["unicode"], sk, e["label"],
                              " ".join(e.get("tags", []))]))
    open(dst, "w", encoding="utf-8").write("\n".join(out) + "\n")
    print(f"{dst}: {len(out)} emoji")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
