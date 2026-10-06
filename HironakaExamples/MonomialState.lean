/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.State
import HironakaExamples.Monomial.Examples  -- shake: keep (used only by `example`s)
import Hironaka.Resolution.Algebraic.Monomial.Step3Phases  -- shake: keep (used only by `example`s)

/-!
# The monomial order-reduction run on the combinatorial state: worked examples

Examples of the run `step3` of [Kol07, Theorem 107, Step 3 of the proof] (order reduction for a
monomial ideal supported on a simple normal crossing divisor with ordered components) on the
combinatorial state `MonomialState`, decided by `decide` (never `native_decide`) through the
fuelled copies `step3Fuel`/`maxMultRun` and the agreement theorem `step3_map_eq_of_step3Fuel`.

* [Kol07, Example 112]: two curves meeting at a point, `a₁ = a₂ = m + 1`. The
  maximal-multiplicity procedure ("look for the highest multiplicity locus and blow it up … does
  not work, not even for surfaces", [Kol07, Theorem 107, Step 3 of the proof]) blows up the point,
  then `E² ∩ E³`, `E³ ∩ E⁴`, …, and the exceptional exponents are `m + p_i` with `p_i` the
  Fibonacci numbers (`3, 4, 6, 9` for `m = 1`): unbounded. Kollár's Step 3 blows up `E¹`, then
  `E²` (trivial blow-ups: the components die and the exceptional components carry `1`), and is
  done with `max-ord = 2` for `m ≥ 3`; for `m = 2` phase 2 blows up the remaining double point
  once; for `m = 1` phase 1 takes two steps per curve: `4, 3, 2, 2, 2` blow-ups for
  `m = 1, 2, 3, 5, 10`.
* A three-phase instance: `n = 3`, `m = 8`, `a = (4, 9, 3, 6)`, maximal faces `{0}` and
  `{1, 2, 3}`; phase 1 blows up `{1}`, phase 2 `{2, 3}`, phase 3 `{3, 4, 5}`, final
  `max-ord = 7 < 8`; the measure vectors `((m_s, n_s))_{s = 1, 2, 3}` are
  `((9,1), (15,1), (18,1))`, `((6,1), (9,1), (10,1))`, `((6,1), (7,2), (8,1))`,
  `((6,1), (7,2), (7,2))`: no pair ever increases.
* The split example: `E¹ = V(x(x-1))`, `E² = V(y(y-1))`, `I = (xy)`, `m = 1`, exponents
  `1, 0, 1, 0` on the four lines; Step 3 blows up `V(x)` then `V(y)` on `X` and on
  `U = D((x-1)(y-1))` alike.
* The nerve rule: three lines in `𝔸²` blown up at a double point; the coordinate planes of `𝔸³`
  blown up at the origin and then along the transform of a line.
-/

@[expose] public section

namespace Hironaka.Monomial.Examples

open Hironaka.Monomial MonomialState Hironaka.Monomial.Examples

/-! ### Example 112 -/

/-- The maximal-multiplicity procedure on Example 112 with `m = 1`: four steps blow up the point,
then the double points `E² ∩ E³`, `E³ ∩ E⁴`, `E⁴ ∩ E⁵`. -/
example : (maxMultRun 4 (example112 1 (by decide))).2 =
    [{{0, 1}}, {{1, 2}}, {{2, 3}}, {{3, 4}}] := by
  decide

/-- The exceptional exponents of that procedure are `m + p_i = 3, 4, 6, 9` (Fibonacci
`2, 3, 5, 8`), unbounded. -/
example : (List.range 6).map (maxMultRun 4 (example112 1 (by decide))).1.a =
    [2, 2, 3, 4, 6, 9] := by
  decide

/-- Kollár's Step 3 on Example 112, `m = 1`: phase 1 blows up `E¹`, `E²` and then their exceptional
components again — four blow-ups. -/
example : (step3 (example112 1 (by decide))).2 = [{{0}}, {{1}}, {{2}}, {{3}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- Example 112, `m = 1`: the final nerve is the two exceptional curves `4, 5` meeting at a point,
all exponents `0`; the original components `0, 1` and the first exceptional components `2, 3` are
dead. -/
example : (step3 (example112 1 (by decide))).1.nerve = {{4}, {5}, {4, 5}} :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide)

example : (List.range 6).map (step3 (example112 1 (by decide))).1.a = [2, 2, 1, 1, 0, 0] :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 6).map r.1.a) (by decide)

/-- Example 112, `m = 2`: phase 1 blows up `E¹`, `E²` (exponents `3 → 1`), phase 2 blows up the
double point `{2, 3}` of the exceptional components (sum `2 ≥ 2`) once — three blow-ups. -/
example : (step3 (example112 2 (by decide))).2 = [{{0}}, {{1}}, {{2, 3}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

example : (step3 (example112 2 (by decide))).1.nerve = {{2}, {3}, {4}, {2, 4}, {3, 4}} :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide)

/-- Example 112, `m = 3`: two blow-ups, done with `max-ord = 2 < 3`. -/
example : (step3 (example112 3 (by decide))).2 = [{{0}}, {{1}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

example : (step3 (example112 3 (by decide))).1.nerve = {{2}, {3}, {2, 3}} :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide)

example : (List.range 4).map (step3 (example112 3 (by decide))).1.a = [4, 4, 1, 1] :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 4).map r.1.a) (by decide)

example : (step3 (example112 5 (by decide))).2 = [{{0}}, {{1}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

example : (step3 (example112 10 (by decide))).2 = [{{0}}, {{1}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-! ### A three-phase instance -/

/-- Phase 1 blows up `{1}`, phase 2 blows up `{2, 3}`, phase 3 blows up `{3, 4, 5}`. -/
example : (step3 threePhase).2 = [{{1}}, {{2, 3}}, {{3, 4, 5}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The exceptional exponents `1, 1, 0`; the final `max-ord` is `7 < 8`. -/
example : (List.range 7).map (step3 threePhase).1.a = [4, 9, 3, 6, 1, 1, 0] :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => (List.range 7).map r.1.a) (by decide)

example : (step3 threePhase).1.nerve.sup (step3 threePhase).1.total = 7 :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve.sup r.1.total) (by decide)

/-- The measure vectors `((m_s, n_s))_{s = 1, 2, 3}` along the run: no pair increases, and the pair
of the current phase drops. -/
example : [1, 2, 3].map (fun s => ofLex (threePhase.measure s)) = [(9, 1), (15, 1), (18, 1)] := by
  decide

example : [1, 2, 3].map (fun s => ofLex ((threePhase.blowUp {{1}}).measure s)) =
    [(6, 1), (9, 1), (10, 1)] := by
  decide

example : [1, 2, 3].map (fun s => ofLex (((threePhase.blowUp {{1}}).blowUp {{2, 3}}).measure s)) =
    [(6, 1), (7, 2), (8, 1)] := by
  decide

example : [1, 2, 3].map (fun s =>
    ofLex ((((threePhase.blowUp {{1}}).blowUp {{2, 3}}).blowUp {{3, 4, 5}}).measure s)) =
    [(6, 1), (7, 2), (7, 2)] := by
  decide

/-! ### The split example -/

/-- Step 3 blows up `V(x)` then `V(y)` on `X` … -/
example : (step3 splitX).2 = [{{0}}, {{2}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- … and on `U` alike (functoriality under restriction,
`HironakaExamples/MonomialRestrict.lean`). -/
example : (step3 splitU).2 = [{{0}}, {{2}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-! ### The nerve rule -/

/-- Three lines `E⁰ = V(x)`, `E¹ = V(y)`, `E² = V(x + y - 1)` in `𝔸²`. -/
def threeLines : MonomialState :=
  ofValid 2 1 3 3 (fun c => c) (fun _ => 0) {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}} (by decide)

/-- Blowing up the double point `{0, 1}`: the exceptional component `3` meets only the transforms of
`E⁰` and `E¹`. -/
example : (threeLines.blowUp {{0, 1}}).nerve =
    {{0}, {1}, {2}, {0, 2}, {1, 2}, {3}, {0, 3}, {1, 3}} := by
  decide

/-- The coordinate planes of `𝔸³`: the nerve is the full simplex on `{0, 1, 2}`. -/
def planes : MonomialState :=
  ofValid 3 1 3 3 (fun c => c) (fun _ => 0)
    {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} (by decide)

/-- Blowing up the origin `{0, 1, 2}`: the faces other than `{0, 1, 2}`, plus the faces with the
exceptional component `3` over every proper face. -/
example : (planes.blowUp {{0, 1, 2}}).nerve =
    {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {3}, {0, 3}, {1, 3}, {2, 3}, {0, 1, 3}, {0, 2, 3},
      {1, 2, 3}} := by
  decide

/-- Then blowing up the line `{0, 1}` removes `{0, 1}`, `{0, 1, 3}` and adds `{4}`, `{0, 4}`,
`{1, 4}`, `{3, 4}`, `{0, 3, 4}`, `{1, 3, 4}`. -/
example : ((planes.blowUp {{0, 1, 2}}).blowUp {{0, 1}}).nerve =
    {{0}, {1}, {2}, {0, 2}, {1, 2}, {3}, {0, 3}, {1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {4}, {0, 4},
      {1, 4}, {3, 4}, {0, 3, 4}, {1, 3, 4}} := by
  decide

end Hironaka.Monomial.Examples
