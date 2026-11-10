import Kahn
import Kafka
import Acquisition
import Warehousing
import Visualization
import MarketModelEngine
import Workspace
import Wiring
import Lean

/-!
# The axiom audit

A check, not a definition: `make lean` runs it after the build, from `lean/`
(`cd lean && lake env lean ../dev/axioms.lean`). A proof of `lean/` rests on Lean's own axioms only,
`propext`, `Classical.choice` and `Quot.sound`; this is what checks it.

It covers every file of `lean/`: each `.lean` file under the directory it runs in (Lake's `.lake`
left out) has to be one of the modules imported above, or the audit fails, naming it. Of those
modules it takes every constant, definitions and what Lean makes for them included, not theorems
alone, and collects the axioms it rests on by `Lean.collectAxioms`, which is what `#print axioms`
prints. Any other axiom fails it, `sorryAx` (a proof left as `sorry`) and `Lean.ofReduceBool` (a
proof by `native_decide`) among them.
-/

open Lean

/-- Lean's own axioms: the only ones a constant of `lean/` may rest on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show CoreM Unit from do
  let env ← getEnv
  let imported := env.allImportedModuleNames
  -- the modules of lean/: its .lean files, by their paths
  let root ← IO.currentDir
  unless ← (root / "lakefile.toml").pathExists do
    throwError "AXIOMS ERROR: no lakefile.toml in {root}: the audit runs from lean/"
  let files ← root.walkDir fun d => pure (d.fileName != some ".lake")
  let mut modules : Array Name := #[]
  for f in files do
    if f.extension == some "lean" then
      modules := modules.push (← moduleNameOfFileName f (some root))
  modules := modules.qsort fun a b => toString a < toString b
  if modules.isEmpty then
    throwError "AXIOMS ERROR: no .lean file under {root}"
  let missing := modules.filter fun m => !imported.contains m
  unless missing.isEmpty do
    throwError "AXIOMS FAIL: not imported by dev/axioms.lean, so not audited: {missing.toList}"
  -- every constant of those modules
  let consts := env.constants.fold (init := (#[] : Array (Name × Name × Bool))) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := imported[idx.toNat]!
      if modules.contains m then acc.push (m, n, ci matches .thmInfo _) else acc
    | none => acc
  let consts := consts.qsort fun a b =>
    (toString a.1 ++ " " ++ toString a.2.1) < (toString b.1 ++ " " ++ toString b.2.1)
  let mut used : NameSet := {}
  let mut bad : Array (Name × Array Name) := #[]
  let mut theorems := 0
  for (m, n, isTheorem) in consts do
    let axioms ← collectAxioms n
    for a in axioms do
      used := used.insert a
    let other := axioms.filter fun a => !standardAxioms.contains a
    unless other.isEmpty do
      bad := bad.push (n, other)
    if isTheorem then
      theorems := theorems + 1
      IO.println s!"theorem {m}: {n}: {axioms.toList}"
  IO.println s!"modules: {modules.toList}"
  IO.println s!"constants: {consts.size}, theorems among them (Lean's own included): {theorems}"
  IO.println s!"axioms used: {used.toArray.toList}"
  unless bad.isEmpty do
    for (n, other) in bad do
      IO.println s!"AXIOMS FAIL: {n} rests on {other.toList}"
    throwError "AXIOMS FAIL: {bad.size} constants rest on an axiom other than Lean's three"
  IO.println <| s!"AXIOMS PASS: {modules.size} modules, {consts.size} constants, " ++
    "none resting on an axiom but propext, Classical.choice, Quot.sound"
