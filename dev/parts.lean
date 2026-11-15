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
# The open parts

Not a definition: what makes the export of the definition's open parts, `export/parts.json`, whose
form `README.md` gives (The open parts). `make parts` runs it from `lean/`
(`cd lean && lake env lean ../dev/parts.lean`), with the release's version in `PARTS_VERSION` and
the file to write in `PARTS_OUT`; `make parts-check` makes it again and compares.

It covers every file of `lean/`, as the axiom audit does (`dev/axioms.lean`): each `.lean` file under
the directory it runs in (Lake's `.lake` left out) has to be one of the modules imported above, or
it fails, naming it. Of those modules it takes every structure, classes among them, and each of the
structure's own fields (`getStructureFields`, a parent's `toPoset` among them): one entry for each.
-/

open Lean Meta

namespace Parts

/-- The modules of `lean/`: its `.lean` files, by their paths, each imported here. -/
def modules : CoreM (Array Name) := do
  let imported := (← getEnv).allImportedModuleNames
  let root ← IO.currentDir
  unless ← (root / "lakefile.toml").pathExists do
    throwError "PARTS ERROR: no lakefile.toml in {root}: it runs from lean/"
  let files ← root.walkDir fun d => pure (d.fileName != some ".lake")
  let mut modules : Array Name := #[]
  for f in files do
    if f.extension == some "lean" then
      modules := modules.push (← moduleNameOfFileName f (some root))
  if modules.isEmpty then
    throwError "PARTS ERROR: no .lean file under {root}"
  let missing := modules.filter fun m => !imported.contains m
  unless missing.isEmpty do
    throwError "PARTS FAIL: not imported by dev/parts.lean, so not exported: {missing.toList}"
  return modules

/-- The projection of each of a structure's own fields, in their order. -/
def fieldProjs (env : Environment) (s : Name) : CoreM (Array Name) :=
  (getStructureFields env s).mapM fun f => do
    let some p := getProjFnForField? env s f
      | throwError "PARTS ERROR: no projection for the field {f} of {s}"
    pure p

/-- What a type uses, so far: the expressions already visited, and the parts found. -/
structure State where
  visited : Std.HashSet Expr := {}
  found : NameSet := {}

/-- The parts `e` uses (`README.md`, The open parts): a projection of a structure of `lean/` is its
field; such a structure, or its constructor, each of its fields; a definition of `lean/` is unfolded
where it is used, its value applied to the arguments it is given, and what that comes to is visited
in its place; anything else, a theorem or a constant from outside `lean/`, adds nothing, and its
arguments are visited. It ends: Lean's kernel takes a definition's value only of constants declared
before it, so no unfolding comes back to the definition it started from; a value that names its own
definition fails it. -/
partial def visit (ours : Name → Bool) (e : Expr) :
    StateRefT State CoreM Unit := do
  if (← get).visited.contains e then return
  modify fun s => { s with visited := s.visited.insert e }
  let env ← getEnv
  let addAll (s : Name) : StateRefT State CoreM Unit := do
    for p in ← fieldProjs env s do
      modify fun st => { st with found := st.found.insert p }
  match e with
  | .app .. | .const .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := f then
      if ours c then
        if (env.getProjectionFnInfo? c).isSome then
          modify fun st => { st with found := st.found.insert c }
        else
          match env.find? c with
          | some (.inductInfo _) => if isStructure env c then addAll c
          | some (.ctorInfo v) => if isStructure env v.induct then addAll v.induct
          | some (.defnInfo v) =>
            if (v.value.find? (·.isConstOf c)).isSome then
              throwError "PARTS ERROR: the value of {c} names {c}"
            visit ours (v.value.beta args)
            return
          | some (.thmInfo _) | some (.recInfo _) => pure ()
          | some _ =>
            throwError "PARTS ERROR: {c} is a constant of lean/ of a kind not provided for"
          | none => throwError "PARTS ERROR: no constant {c}"
    else
      visit ours f
    for a in args do
      visit ours a
  | .lam _ t b _ | .forallE _ t b _ =>
    visit ours t
    visit ours b
  | .letE _ t v b _ =>
    visit ours t
    visit ours v
    visit ours b
  | .mdata _ b => visit ours b
  | .proj s i b =>
    if ours s then
      let some p := (← fieldProjs env s)[i]?
        | throwError "PARTS ERROR: no field {i} of {s}"
      modify fun st => { st with found := st.found.insert p }
    visit ours b
  | _ => pure ()

/-- One entry: the field's full name, its structure, its type as `#print` shows it in its structure
(`self` and the structure's parameters free, on one line), its doc comment or empty, and its uses. -/
def entry (ours : Name → Bool) (s : Name) (levels : List Level) (params : Array Expr) (self : Expr)
    (p : Name) : MetaM Json := do
  let t ← inferType (mkApp (mkAppN (.const p levels) params) self)
  let printed ← withTheReader Core.Context
    (fun c => { c with currNamespace := .anonymous, openDecls := [] }) (ppExpr t)
  let type := printed.pretty (width := 1000000)
  if type.contains '\n' then
    throwError "PARTS ERROR: the type of {p} is not printed on one line"
  let doc := ((← findDocString? (← getEnv) p).getD "").trimAscii.copy
  let (_, st) ← (visit ours t).run {}
  let uses := (st.found.erase p).toArray.map toString |>.qsort (· < ·)
  return Json.mkObj [
    ("name", toString p), ("structure", toString s), ("type", type), ("doc", doc),
    ("uses", Json.arr (uses.map Json.str))]

end Parts

open Parts in
#eval show MetaM Unit from do
  let some version ← IO.getEnv "PARTS_VERSION"
    | throwError "PARTS ERROR: no PARTS_VERSION: make parts gives it, from flake.nix"
  let some out ← IO.getEnv "PARTS_OUT"
    | throwError "PARTS ERROR: no PARTS_OUT: make parts gives it"
  if version.isEmpty then throwError "PARTS ERROR: PARTS_VERSION is empty"
  let env ← getEnv
  let mods ← modules
  let imported := env.allImportedModuleNames
  let ours (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => mods.contains imported[idx.toNat]!
    | none => false
  let structs := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if ours n && isStructure env n then acc.push n else acc
  let structs := structs.qsort fun a b => toString a < toString b
  let mut entries : Array (String × Json) := #[]
  for s in structs do
    let ci ← getConstInfoInduct s
    let levels := ci.levelParams.map Level.param
    let projs ← fieldProjs env s
    let es ← forallBoundedTelescope ci.type ci.numParams fun params _ => do
      unless params.size == ci.numParams do
        throwError "PARTS ERROR: {s} has {ci.numParams} parameters, {params.size} found"
      withLocalDeclD `self (mkAppN (.const s levels) params) fun self =>
        projs.mapM fun p => do pure (toString p, ← entry ours s levels params self p)
    entries := entries ++ es
  let sorted := entries.qsort fun a b => a.1 < b.1
  let json := Json.mkObj [("version", version), ("parts", Json.arr (sorted.map (·.2)))]
  IO.FS.writeFile out (json.pretty ++ "\n")
  IO.println s!"PARTS: {structs.size} structures, {entries.size} fields, written to {out}"
