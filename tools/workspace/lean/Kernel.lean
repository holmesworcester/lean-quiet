/-
A deliberately small executable slice of the proposed workspace.
The browser calls these exact exported definitions. No cryptography, network
membership, full engine validation, or production painting is claimed here.
-/
namespace Workspace

/-- 0 waiting, 1 accepted, 2 rejected. Inputs are fixture facts, not signatures. -/
@[export quiet_validate]
def validate (present valid member sameCommunity strict : UInt32) : UInt32 :=
  if present == 0 then 0
  else if valid == 0 || member == 0 then 2
  else if strict != 0 && sameCommunity == 0 then 2
  else 1

/-- Explicit user choices override the external OS input. -/
@[export quiet_theme]
def theme (preference osDark : UInt32) : UInt32 :=
  if preference == 1 then 0 else if preference == 2 then 1 else osDark

@[export quiet_color]
def color (token dark : UInt32) : UInt32 :=
  if dark == 0 then
    if token == 0 then 0xffffff else if token == 1 then 0xffffff
    else if token == 2 then 0x1f2328 else if token == 3 then 0x59636e
    else if token == 4 then 0x0969da else if token == 5 then 0xd1d9e0 else 0xcf222e
  else
    if token == 0 then 0x0d1117 else if token == 1 then 0x161b22
    else if token == 2 then 0xe6edf3 else if token == 3 then 0x919ba6
    else if token == 4 then 0x79c0ff else if token == 5 then 0x30363d else 0xff7b72

/-- A bounded scalar rounded rectangle, compiled with Lean's ordinary C backend. -/
def inside (x y left top width height radius : UInt32) : Bool :=
  if x < left || y < top || x >= left + width || y >= top + height then false
  else
    let xx := x - left
    let yy := y - top
    let dx := if xx < radius then radius - xx else if xx >= width - radius then xx - (width - radius - 1) else 0
    let dy := if yy < radius then radius - yy else if yy >= height - radius then yy - (height - radius - 1) else 0
    dx * dx + dy * dy <= radius * radius

/-- Paint the client surfaces. Text and accessible controls are DOM overlays. -/
@[export quiet_pixel]
def pixel (x y dark accent : UInt32) : UInt32 :=
  let bg := color 0 dark
  let surface := color 1 dark
  let border := color 5 dark
  if y == 57 || y == 335 then border
  else if inside x y 16 73 28 28 3 then (if dark == 0 then 0xeaeef2 else 0x30363d)
  else if inside x y 16 172 28 28 3 then (if dark == 0 then 0xeaeef2 else 0x30363d)
  else if inside x y 52 135 65 27 3 then (if dark == 0 then 0xddf4ff else 0x152c46)
  else if inside x y 52 234 65 27 3 then (if dark == 0 then 0xddf4ff else 0x152c46)
  else if inside x y 266 357 22 22 3 then accent
  else if inside x y 16 350 272 35 3 then surface
  else bg

theorem waits_for_dependency (v m c s : UInt32) : validate 0 v m c s = 0 := by
  simp [validate]

theorem rejects_invalid_dependency (m c s : UInt32) : validate 1 0 m c s = 2 := by
  simp [validate]

theorem rejects_nonmember (c s : UInt32) : validate 1 1 0 c s = 2 := by
  simp [validate]

theorem rejects_wrong_community : validate 1 1 1 0 1 = 2 := by
  decide

theorem accepts_valid_reaction : validate 1 1 1 1 1 = 1 := by
  decide

theorem explicit_dark_overrides_os (os : UInt32) : theme 2 os = 1 := by
  simp [theme]

end Workspace

#print axioms Workspace.waits_for_dependency
#print axioms Workspace.rejects_invalid_dependency
#print axioms Workspace.rejects_nonmember
#print axioms Workspace.rejects_wrong_community
#print axioms Workspace.accepts_valid_reaction
#print axioms Workspace.explicit_dark_overrides_os
