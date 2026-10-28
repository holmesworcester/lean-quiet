import Lake
open Lake DSL

package net where
  moreLinkArgs := #["-Wl,--allow-shlib-undefined", "/usr/lib/x86_64-linux-gnu/libsqlite3.so.0", "/usr/lib/x86_64-linux-gnu/libsodium.so.23"]

require engine from "../engine"

@[default_target]
lean_lib Net

lean_exe scene_check where
  root := `Tests.SceneCheck
