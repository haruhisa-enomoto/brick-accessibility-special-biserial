module

public import BrickAccessibility
public import Solution

/-! Scan every declaration of the `BrickAccessibility` modules and `Solution` for axioms
other than `propext`, `Classical.choice` and `Quot.sound`.
Run with `lake env lean scripts/ScanAxioms.lean`. -/

@[expose] public section

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut bad : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`BrickAccessibility).isPrefixOf mod || mod == `Solution do continue
    count := count + 1
    for ax in ← collectAxioms name do
      unless allowed.contains ax do bad := bad.push (name, ax)
  IO.println s!"scanned {count} declarations; {bad.size} use other axioms"
  for (name, ax) in bad do IO.println s!"{name}: {ax}"
