import Lake
open Lake DSL System

package quiet where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0",
    "/usr/lib/x86_64-linux-gnu/libsodium.so.23"]

require engine from ".." / "lean-engine"

lean_lib Quiet

lean_lib QTests

lean_exe host where
  root := `QTests.Host
