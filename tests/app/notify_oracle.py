#!/usr/bin/env python3
"""Rebuild tests/app/notify-policy.txt by running libquiet's own policy
(crates/quiet-core/src/notify/policy.rs at ab3d244cf, serde derives stripped)
over every message-policy input, from the read-only libquiet clone, without
Cargo or the network. The notify headless test checks Notify.policy against it."""
from pathlib import Path
import re
import subprocess
import tempfile

reference = "ab3d244cf"
source = subprocess.check_output([
    "git", "-C", "/home/holmes/libquiet", "show",
    reference + ":crates/quiet-core/src/notify/policy.rs",
], text=True)
# Remove only external serialization derives/attributes and the test submodule.
source = re.sub(r"^use serde[^\n]*\n", "", source, flags=re.M)
source = re.sub(r", (?:serde::)?(?:Serialize|Deserialize)", "", source)
source = re.sub(r"^#\[serde[^\n]*\n", "", source, flags=re.M)
source = source.replace("#[cfg(test)]\nmod tests;", "")
main = r"""
fn main() {
 let levels = [None, Some(Level::All), Some(Level::MentionsAndDirect), Some(Level::Off)];
 let choices = [None, Some(false), Some(true)];
 for community in levels { for channel in levels {
 for cr in choices { for r in choices {
 for conversation in [Conversation::Channel, Conversation::GroupDirect, Conversation::OneToOne] {
 for manual in choices { for reply in [false,true] { for mentioned in [false,true] {
 for root_author in [false,true] { for replied in [false,true] {
  let settings = Settings { community: ScopeValues {level:community, thread_replies:cr, pending_admissions:None}, channel: ScopeValues {level:channel, thread_replies:r, pending_admissions:None}};
  let following = follow(conversation, FollowInputs {manual,root_author,replied});
  let subject = Subject::Post {conversation,reply:if reply {Some(following)} else {None},mentioned};
  print!("{}", if decide(&settings, subject) {'1'} else {'0'});
 }}}}}}}}}}
 println!();
}
"""
with tempfile.TemporaryDirectory(prefix="notify-oracle-") as directory:
    path = Path(directory)
    (path / "oracle.rs").write_text(source + main)
    subprocess.run(["rustc", "--edition=2021", str(path / "oracle.rs"), "-o", str(path / "oracle")], check=True)
    output = subprocess.check_output([str(path / "oracle")])
    assert len(output.strip()) == 20736
    Path(__file__).with_name("notify-policy.txt").write_bytes(output)
print("20736 cases from libquiet " + reference)
