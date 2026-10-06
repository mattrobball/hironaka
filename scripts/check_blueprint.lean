/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Lean
import Hironaka

/-!
# Blueprint coverage check

Run as `lake lean scripts/check_blueprint.lean` from the library's package directory, the one
holding `lakefile.toml` and `comparator.json` (the parent of `blueprint/`): Lake builds the library
this file imports and hands it to Lean. The blueprint (`blueprint/`) embeds Lean
declarations at its nodes through the field `(lean := "…")`, a comma-separated list of full names.
The script checks that these names are exactly

* the main theorems that the blueprint presents: the names of `comparator.json`, and
* the declarations of `Hironaka` a reader must read to understand their statements: every
  definition, structure, class, inductive type and instance reachable from the type of such a main
  theorem, following the type and value of each definition and the coercion instances declared
  beside them. Theorems are not followed: a proof does not change what a definition means. What
  Lean generates from a declaration is read with it and is not required at a node: constructors,
  recursors and the auxiliary recursors (`casesOn`, `brecOn`, `below`), matchers (`match_1`),
  auxiliary proofs (`proof_1`), equation lemmas, `noConfusion`, and the projections of a
  structure (its fields, shown with the structure); a node may still name a projection.

It prints each declaration that the statements need and no node names, and each name that a node
gives and that is neither, and exits with a nonzero status if there is one.

`coeClasses` and `uses` repeat `scripts/check_defs.lean` (scripts run by `lake lean` cannot import
one another); unlike that check, which follows the types of theorems to place every definition
they mention in a `Defs` module, this one does not follow theorems.
-/

open Lean

namespace CheckBlueprint

/-- The classes whose instances elaboration unfolds. -/
def coeClasses : List Name :=
  [``CoeFun, ``CoeSort, ``Coe, ``CoeTail, ``CoeHead, ``CoeOut, ``CoeDep, ``CoeTC, ``CoeOTC,
    ``CoeHTC, ``CoeHTCT, ``CoeT]

/-- The constants a constant mentions: its type, its value unless it is a theorem, and the
constructors and recursors tied to an inductive type. -/
def uses (env : Environment) (ci : ConstantInfo) : Array Name := Id.run do
  let mut s := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => s := s ++ v.value.getUsedConstants
  | .opaqueInfo v => s := s ++ v.value.getUsedConstants
  | .inductInfo d =>
    for c in d.ctors do
      s := s.push c
      if let some cc := env.find? c then s := s ++ cc.type.getUsedConstants
  | .ctorInfo d => s := s.push d.induct
  | .recInfo d => s := s ++ d.all.toArray
  | _ => pure ()
  return s

/-- Declarations Lean generates from another one, read with it and not required at a node. -/
def generated (env : Environment) (n : Name) : Bool :=
  n.isInternal || env.isConstructor n || (env.find? n matches some (.recInfo _)) ||
    isAuxRecursor env n || isNoConfusion env n || Meta.isMatcherCore env n ||
    (env.getProjectionFnInfo? n).isSome ||
    match n with
    | .str p last =>
      last.startsWith "match_" || last.startsWith "proof_" || last.startsWith "eq_" ||
        last.startsWith "_" || (last == "go" && (p matches .str _ "brecOn"))
    | _ => false

/-- Walk up from a directory to the library's package directory, the first one containing both
`lakefile.toml` and `comparator.json` (so not the blueprint's own package). -/
partial def findRoot (dir : System.FilePath) : IO System.FilePath := do
  if (← (dir / "lakefile.toml").pathExists) && (← (dir / "comparator.json").pathExists) then
    return dir
  match dir.parent with
  | some p => findRoot p
  | none => throw <| IO.userError <|
      "check_blueprint: no directory with lakefile.toml and comparator.json above the working " ++
        "directory"

/-- The names given in the `(lean := "…")` fields of a blueprint file. -/
def namesIn (text : String) : Array String := Id.run do
  let mut out := #[]
  for piece in (text.splitOn "(lean := \"").drop 1 do
    let field := (piece.splitOn "\"").headD ""
    for n in field.splitOn "," do
      let n := n.trimAscii.toString
      if !n.isEmpty then out := out.push n
  return out

/-- The Lean files of the blueprint: `blueprint/Blueprint.lean` and every file under
`blueprint/Blueprint/`. -/
def blueprintFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut fs : Array System.FilePath := #[root / "blueprint" / "Blueprint.lean"]
  for f in ← (root / "blueprint" / "Blueprint").walkDir do
    if f.extension == some "lean" then fs := fs.push f
  return fs

/-- The check, on the environment `env` of this file. -/
def check (env : Environment) (root : System.FilePath) : IO UInt32 := do
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "comparator.json"))
  let allMains ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let mains := allMains
  let moduleNames := env.header.moduleNames
  let libModule? (n : Name) : Option Name := do
    let m := moduleNames[(← env.getModuleIdxFor? n).toNat]!
    if m.getRoot == `Hironaka then some m else none
  let coeInstances := env.constants.map₁.toList.filterMap fun (n, ci) =>
    if (libModule? n).isSome && Meta.isInstanceCore env n &&
        ci.type.getForallBody.getAppFn.constName?.any coeClasses.contains then some n else none
  let mut errors : Array String := #[]
  -- the statement vocabulary
  let mut stack : Array Name := #[]
  for t in mains do
    match env.find? t.toName with
    | some ci => stack := stack ++ ci.type.getUsedConstants
    | none => errors := errors.push s!"comparator.json names {t}, which is not in the library"
  let mut vocab : NameSet := {}
  let mut done := false
  while !done do
    while h : stack.size > 0 do
      let n := stack.back
      stack := stack.pop
      if vocab.contains n then continue
      let some _ := libModule? n | continue
      if allMains.contains n.toString then continue
      let some ci := env.find? n | continue
      -- a theorem is not read: a proof does not change what a definition means
      if ci matches .thmInfo _ then continue
      vocab := vocab.insert n
      stack := stack ++ uses env ci
    let modules : NameSet := vocab.foldl (fun s n => s.insert (libModule? n).get!) {}
    stack := (coeInstances.filter fun n =>
      !vocab.contains n && modules.contains (libModule? n).get!).toArray
    done := stack.isEmpty
  let needed : NameSet := vocab.foldl (init := {}) fun s n =>
    if generated env n then s else s.insert n
  -- the names of the blueprint
  let mut given : NameSet := {}
  for f in ← blueprintFiles root do
    for n in namesIn (← IO.FS.readFile f) do
      given := given.insert n.toName
  for t in mains do
    if !given.contains t.toName then
      errors := errors.push s!"main theorem at no node: {t}"
  for n in needed.toList do
    if !given.contains n then
      errors := errors.push s!"statement declaration at no node: {n} ({(libModule? n).get!})"
  for n in given.toList do
    -- a node may name a field of a structure the statements need
    let isNeededField := match env.getProjectionFnInfo? n with
      | some info => match env.find? info.ctorName with
        | some (.ctorInfo c) => needed.contains c.induct
        | _ => false
      | none => false
    if !needed.contains n && !mains.contains n.toString && !isNeededField then
      errors := errors.push s!"node names a declaration no statement needs: {n}"
  for e in errors.qsort (· < ·) do IO.println e
  IO.println s!"check_blueprint: {mains.size} main theorems, {needed.size} statement \
    declarations, {given.size} names at nodes, {errors.size} violations"
  return if errors.isEmpty then 0 else 1

end CheckBlueprint

open Lean Elab Command CheckBlueprint in
run_cmd do
  let root ← findRoot (← IO.currentDir)
  if (← check (← getEnv) root) != 0 then throwError "check_blueprint: violations found"
