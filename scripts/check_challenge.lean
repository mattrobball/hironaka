/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Lean
import Challenge

/-!
# Challenge check

Run as `lake lean scripts/check_challenge.lean` from the directory of `lakefile.toml`. The
comparator checks only the theorems that `comparator.json` names, so a theorem stated in a
Challenge file but missing from `comparator.json` would go unchecked, and a name in
`comparator.json` without a Challenge statement would make the comparator fail. The script checks
that

* the theorems declared in the modules of `Challenge` are exactly the names of `comparator.json`;
* every Lean file under `Challenge/` is imported by `Challenge.lean`, so that it is part of the
  `challenge_module` the comparator builds.

It prints each violation and exits with a nonzero status if there is one.
-/

open Lean

namespace CheckChallenge

/-- Walk up from a directory to the directory containing `lakefile.toml`. -/
partial def findRoot (dir : System.FilePath) : IO System.FilePath := do
  if ← (dir / "lakefile.toml").pathExists then return dir
  match dir.parent with
  | some p => findRoot p
  | none =>
    throw <| IO.userError "check_challenge: lakefile.toml not found above the working directory"

/-- The check, on the environment `env` of this file. -/
def check (env : Environment) (root : System.FilePath) : IO UInt32 := do
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "comparator.json"))
  let names ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let listed : NameSet := names.foldl (fun s n => s.insert n.toName) {}
  let mut stated : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if env.header.moduleNames[idx.toNat]!.getRoot == `Challenge && ci matches .thmInfo _ &&
        !n.isInternal then
      stated := stated.insert n
  let mut errors : Array String := #[]
  for f in ← (root / "Challenge").walkDir do
    if f.extension == some "lean" then
      let rel := (f.toString.drop (root.toString.length + 1)).toString
      let m := (System.FilePath.mk rel).withExtension "" |>.components.foldl Name.mkStr .anonymous
      unless env.header.moduleNames.contains m do
        errors := errors.push s!"{rel} is not imported by Challenge.lean"
  for n in stated.toList do
    unless listed.contains n do
      errors := errors.push s!"{n} is stated in Challenge but not named by comparator.json"
  for n in listed.toList do
    unless stated.contains n do
      errors := errors.push s!"{n} is named by comparator.json but not stated in Challenge"
  for e in errors.qsort (· < ·) do IO.println e
  IO.println s!"check_challenge: {stated.size} Challenge theorems, {listed.size} comparator \
    names, {errors.size} violations"
  return if errors.isEmpty then 0 else 1

end CheckChallenge

open Lean Elab Command CheckChallenge in
run_cmd do
  let root ← findRoot (← IO.currentDir)
  if (← check (← getEnv) root) != 0 then throwError "check_challenge: violations found"
