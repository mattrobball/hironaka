import Lean

/-!
# Long conjunctions, one conjunct per line

Lean prints `a ∧ b ∧ c ∧ d` as the right-nested `a ∧ (b ∧ (c ∧ d))` that it is, so that a long
conjunction, broken over several lines, has each conjunct indented one step further than the one
before. The signatures of the blueprint's nodes are printed with the delaborator below in scope:
it prints a conjunction of three or more conjuncts that does not fit on one line with one conjunct
per line, all at the same indentation. Shorter conjunctions are printed as usual.

The syntax `conjChain` exists only for printing. It has no elaborator, so in Lean source the
ordinary notation `∧` is the only reading of `a ∧ b ∧ c`.
-/

namespace Blueprint.ConjunctionChains

open Lean PrettyPrinter Delaborator SubExpr

/-- A conjunction of several conjuncts, one per line; printing only. -/
syntax:35 (name := conjChain) term:36 (" ∧" ppLine term:36)+ : term

/-- The conjuncts of the right-nested conjunction at the current position, delaborated. -/
partial def delabConjuncts : DelabM (Array Term) := do
  if (← getExpr).isAppOfArity ``And 2 then
    let first ← withAppFn (withAppArg delab)
    return #[first] ++ (← withAppArg delabConjuncts)
  else
    return #[← delab]

/-- Prints a conjunction of three or more conjuncts whose flat form is long with one conjunct per
line (`conjChain`); fails, leaving the ordinary notation, otherwise. -/
@[delab app.And]
def delabConjChain : Delab := do
  let parts ← delabConjuncts
  if parts.size < 3 then failure
  let flat ← parts.foldlM (fun n p => return n + (toString (← ppTerm p)).length) 0
  if flat < 60 then failure
  let rest := parts.extract 1 parts.size |>.map fun p => mkNode groupKind #[mkAtom " ∧", p.raw]
  return ⟨mkNode ``conjChain #[parts[0]!.raw, mkNullNode rest]⟩

end Blueprint.ConjunctionChains
