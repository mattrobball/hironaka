/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/

module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Functor
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.AllNFam
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.InstancesFamTheorem107
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialTransformMod
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The order-reduction tower at the library's constructions

The order-reduction tower on the compatible-family structures (`Stage/Family.lean`) takes the two
reduction steps of [Kol07, 70] as parameters. This module instantiates it at the steps the library
constructs, over any field `K` with `RCLike K`: Theorem 103 as `theorem103FamStar`
(`Stage/InstancesFam.lean`), and Theorem 107 as `theorem107FamStarOf`
(`Stage/InstancesFamTheorem107.lean`) applied to the monomial procedure `BMO.monomialStep3Fam` of
Step 3 of the proof of Theorem 107 (`BMO/Step3Monomial/Functor.lean`) and to the two transform
identities for the nonmonomial part proved in `Modified/NonmonomialTransformMod.lean`.

* `nonmonomialTransformIdentity_refl K n` — the transform identity for the nonmonomial part at the
  standard model of dimension `n`;
* `concreteTheorem107FamStar K : BMOanFamStep K` — Theorem 107 as the second reduction step, at the
  library's constructions;
* `concreteOrderReductionTower K n` — the tower along the two steps;
* `concreteBOanFam K n d : BOanFam K n d` — order reduction for ideals in every dimension and at
  every mark ([Kol07, Theorem 68]), and `concreteBMOanFam K n : BMOanFam K n 1` — order reduction
  for marked ideals at the mark `1` ([Kol07, Theorem 69]), both read off the tower;
* `concreteBOanFamReal n m : BOanFam ℝ n m` — the same order-reduction family over `ℝ`, written as
  `BOanFamAllOf` at the second step.

These are the order-reduction functors the analytic main theorems apply: `concreteBOanFam` and
`concreteBMOanFam` enter the embedded desingularization
(`Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`).
-/

@[expose] public section

universe u

open scoped Manifold ContDiff
open TopologicalSpace Hironaka.Manifold

namespace Hironaka

variable (K : Type) [RCLike K]


/-- The transform identity for the nonmonomial part (`BMOmod.NonmonomialTransformIdentity`) at the
standard model `Fin n → K` of every dimension: `nonmonomialTransformIdentity_inhabitant` at that
model. -/
theorem nonmonomialTransformIdentity_refl (n : ℕ) :
    BMOmod.NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl K (Fin n → K)) :=
  BMOmod.nonmonomialTransformIdentity_inhabitant (ContinuousLinearEquiv.refl K (Fin n → K))

/-- Order reduction for marked ideals from order reduction for ideals in the same dimension
([Kol07, Theorem 107]), as the second reduction step of the tower: `theorem107FamStarOf` at the
monomial procedure `BMO.monomialStep3Fam` and the two transform identities for the nonmonomial
part, in every dimension. -/
noncomputable def concreteTheorem107FamStar : BMOanFamStep.{u} K :=
  theorem107FamStarOf K (fun n m => BMO.monomialStep3Fam K n m)
    (fun n => BMOmod.nonmonomialTransformIdentity_inhabitant
      (ContinuousLinearEquiv.refl K (Fin n → K)))
    (fun n => BMOmod.nonmonomialTransformIdentityMod_inhabitant
      (ContinuousLinearEquiv.refl K (Fin n → K)))

/-- The order-reduction tower on the compatible-family structures along Theorem 103
(`theorem103FamStar`) and Theorem 107 (`concreteTheorem107FamStar`). -/
noncomputable def concreteOrderReductionTower : ∀ n : ℕ, OrderReductionStageAnFam.{u} K n :=
  orderReductionTowerAnFamStarOf K (concreteTheorem107FamStar K)

/-- Order reduction for ideals in dimension `n` at the mark `d` ([Kol07, Theorem 68]), in the
compatible-family form: the component `bo` of the tower `concreteOrderReductionTower`. -/
noncomputable def concreteBOanFam (n d : ℕ) : BOanFam.{u} K n d :=
    (concreteOrderReductionTower K n).bo d

/-- Order reduction for marked ideals in dimension `n` at the mark `1` ([Kol07, Theorem 69]), in
the compatible-family form: the component `bmo` of the tower `concreteOrderReductionTower` at the
mark `1`. -/
noncomputable def concreteBMOanFam (n : ℕ) : BMOanFam.{u} K n 1 :=
    (concreteOrderReductionTower K n).bmo 1

end Hironaka

open Set Filter Topology TopologicalSpace Hironaka.Manifold Analytic
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka

/-- Order reduction for ideals over `ℝ` in dimension `n` at the mark `m`, in the compatible-family
form: `BOanFamAllOf` at the second reduction step `theorem107FamStarOf` applied to the library's
constructions, which unfolds to `concreteBOanFam ℝ n m`. -/
def concreteBOanFamReal (n m : ℕ) : BOanFam.{0} ℝ n m :=
  BOanFamAllOf ℝ
    (theorem107FamStarOf ℝ (fun n m => BMO.monomialStep3Fam ℝ n m)
      (fun n => BMOmod.nonmonomialTransformIdentity_inhabitant
        (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)))
      (fun n => BMOmod.nonmonomialTransformIdentityMod_inhabitant
        (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))))
    n m

end Hironaka

end
