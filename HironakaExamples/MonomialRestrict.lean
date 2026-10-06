/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
public import HironakaExamples.Monomial.Examples
import Hironaka.Resolution.Algebraic.Monomial.Restrict.RefinePhase  -- shake: keep (used only by `example`s)
import HironakaExamples.MonomialState  -- shake: keep (used only by `example`s)

/-!
# Functoriality of the monomial run under restriction: worked examples

Examples, decided by `decide` through the fuelled copies of the algorithm, of the restriction and
refinement properties of the monomial order-reduction run `step3` on the combinatorial state
`MonomialState` (`Hironaka/Resolution/Algebraic/Monomial/Restrict/RefinePhase.lean`):

* the split example (`splitX`, `splitU` of `HironakaExamples/Monomial/Examples.lean`): the run on
  the `U`-nerve `{0}, {2}, {0, 2}` is the run on the `X`-nerve with the empty faces deleted; here
  every center meets `U`, so `restrictRun` keeps both centers and the renumbering is the identity;
* a subnerve pair in which the run on `N` blows up a center disjoint from `L` first (the
  component `0` of exponent `5 ≥ m = 4`, absent from `L`) and then the double point `{1, 2}`
  common to both (exponents `2 + 2 = 4 ≥ m`): `restrictRun` drops the first center, the direct
  run on `L` has the single center `{1, 2}`, and the exceptional component is numbered `3` in the
  direct run but `4` in the pulled-back run (the empty blow-up allocated the dead component `3`):
  the order-preserving correspondence `3 ↦ 4` of `step3_restrict`;
* a refinement pair: `Y = X ⊔ X`, two copies of the two-component state `L` (`ρ` the fold),
  refines `L`; the run on `Y` blows up both copies of each center of `L` at once (one center of
  `Y` with twice the faces): it is the preimage run `refineRun` of the run on `L`, with `ρ`
  extended by `4, 5 ↦ 2` and `6, 7 ↦ 3`.
-/

@[expose] public section

namespace Hironaka.Monomial.Examples

open Hironaka.Monomial MonomialState Hironaka.Monomial.Examples

/-- The centers of the split example on `X`. -/
theorem splitX_centers : (step3 splitX).2 = [{{0}}, {{2}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The centers of the split example on `U`. -/
theorem splitU_centers : (step3 splitU).2 = [{{0}}, {{2}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

example : Sub splitU splitX := ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- The pulled-back run of the split example on `U`: both centers of the `X`-run meet `U`, and they
are the centers of the direct run on `U`. -/
example : restrictRun splitU (step3 splitX).2 = (step3 splitU).2 := by
  rw [splitX_centers, splitU_centers]
  decide

/-- `N`: components `0, 1, 2` (labels `0, 1, 2`), exponents `5, 2, 2`, `m = 4`, nerve
`{0}, {1}, {2}, {1, 2}`. -/
def bigN : MonomialState :=
  ofValid 2 4 3 3 (fun c => c) (fun c => [5, 2, 2].getD c 0) {{0}, {1}, {2}, {1, 2}} (by decide)

/-- `L`: the subnerve without the component `0`. -/
def subL : MonomialState :=
  ofValid 2 4 3 3 (fun c => c) (fun c => [5, 2, 2].getD c 0) {{1}, {2}, {1, 2}} (by decide)

example : Sub subL bigN := ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- The run on `N`: phase 1 blows up `{0}`, phase 2 blows up `{1, 2}`. -/
theorem bigN_centers : (step3 bigN).2 = [{{0}}, {{1, 2}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The run on `L`: only `{1, 2}`. -/
theorem subL_centers : (step3 subL).2 = [{{1, 2}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The pulled-back run drops the empty blow-up along `{0}`. -/
example : restrictRun subL (step3 bigN).2 = (step3 subL).2 := by
  rw [bigN_centers, subL_centers]
  decide

/-- The pulled-back state numbers the exceptional component `4` (the empty blow-up allocated the
dead component `3`) … -/
example : ((step3 bigN).2.foldl MonomialState.blowUp subL).nerve =
    {{1}, {2}, {4}, {1, 4}, {2, 4}} := by
  rw [bigN_centers]
  decide

/-- … while the direct run on `L` numbers it `3`: the correspondence `3 ↦ 4`. -/
example : (step3 subL).1.nerve = {{1}, {2}, {3}, {1, 3}, {2, 3}} :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide)

/-- Exponents agree along the correspondence (`2 + 2 - 4 = 0`). -/
example : ((step3 bigN).2.foldl MonomialState.blowUp subL).a 4 = 0 := by
  rw [bigN_centers]
  decide

example : (step3 subL).1.a 3 = 0 :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.a 3) (by decide)

/-- The pulled-back final state is `Sub` the final state of `N`: its nerve lies in `N`'s. -/
example : ((step3 bigN).2.foldl MonomialState.blowUp subL).nerve ⊆ (step3 bigN).1.nerve := by
  rw [bigN_centers, step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve)
    (x := {{1}, {2}, {3}, {4}, {1, 4}, {2, 4}}) (by decide)]
  decide

/-! ### A refinement pair -/

/-- `L`: two components `0, 1` (labels `0, 1`) meeting at a point, exponents `1`, `m = 1`. -/
def baseL : MonomialState :=
  ofValid 2 1 2 2 (fun c => c) (fun _ => 1) {{0}, {1}, {0, 1}} (by decide)

/-- `Y = X ⊔ X`: two copies `0, 1` and `2, 3` of the components of `L`, with their labels. -/
def doubleY : MonomialState :=
  ofValid 2 1 4 2 (fun c => [0, 1, 0, 1].getD c 0) (fun _ => 1)
    {{0}, {1}, {0, 1}, {2}, {3}, {2, 3}} (by decide)

/-- The fold `X ⊔ X → X` on components. -/
def fold : ℕ → ℕ := fun c => [0, 1, 0, 1].getD c 0

example : Refines fold doubleY baseL :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem baseL_centers : (step3 baseL).2 = [{{0}}, {{1}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The run on `Y` blows up both copies of `E⁰` at once, then both copies of `E¹`. -/
theorem doubleY_centers : (step3 doubleY).2 = [{{0}, {2}}, {{1}, {3}}] :=
  step3_map_eq_of_step3Fuel (fuel := 20) Prod.snd (by decide)

/-- The extension of the fold: the new components `4, 5` (over `{0}`, `{2}`) go to `2`, the new
components `6, 7` to `3`. -/
def fold' : ℕ → ℕ := fun c => [0, 1, 0, 1, 2, 2, 3, 3].getD c 0

/-- The run on `Y` is the preimage run of the run on `L` … -/
example : refineRun fold' doubleY (step3 baseL).2 = (step3 doubleY).2 := by
  rw [baseL_centers, doubleY_centers]
  decide

/-- … and the run on `L` is its image. -/
example : (step3 baseL).2 = (step3 doubleY).2.map fun S => S.image (Finset.image fold') := by
  rw [baseL_centers, doubleY_centers]
  decide

/-- The final nerves correspond: two copies of `{2}, {3}, {2, 3}`. -/
example : (step3 doubleY).1.nerve = {{4}, {6}, {4, 6}, {5}, {7}, {5, 7}} :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide)

example : (step3 baseL).1.nerve = {{2}, {3}, {2, 3}} :=
  step3_map_eq_of_step3Fuel (fuel := 20) (fun r => r.1.nerve) (by decide)

end Hironaka.Monomial.Examples
