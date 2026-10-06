/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Stage.Family
public import Hironaka.Resolution.Analytic.OrderReduction.BOanFamOfInput
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Theorem 103 as the first reduction step

The order-reduction tower on the compatible-family structures (`Stage/Family.lean`) takes the two
reduction steps of [Kol07, 70] as parameters. This module supplies the first one, order reduction
for ideals from order reduction for marked ideals one dimension down ([Kol07, Theorem 103]), and
the tower along it:

* `theorem103FamStar 𝕜 : BOanFamStep 𝕜` — the construction `BO.BOanFamOfInput` of
  `BOanFamOfInput.lean`, which assembles the order-reduction family in dimension `n` from the
  marked families in dimension `n - 1` following the three steps of the proof of Theorem 103, taken
  in dimension `n + 1` (so that the input dimension `(n + 1) - 1 = n` holds by definition);
* `orderReductionTowerAnFamStarOf 𝕜 h107` — the tower along `theorem103FamStar 𝕜` and an arbitrary
  second reduction step `h107 : BMOanFamStep 𝕜`.

The second reduction step is constructed in `Stage/InstancesFamTheorem107.lean`; the tower at both,
`Stage/Concrete.lean`, provides the order-reduction functors used by the analytic main theorems.
`Stage/AllNFam.lean` reads the families in every dimension off the tower along `theorem103FamStar`
and an arbitrary second step.
-/

@[expose] public section

noncomputable section

universe u

namespace Hironaka.Manifold

/-- Order reduction for ideals from order reduction for marked ideals one dimension down
([Kol07, Theorem 103]), as the first reduction step of the tower on the compatible-family
structures: `BO.BOanFamOfInput` in dimension `n + 1`. -/
def theorem103FamStar (𝕜 : Type) [RCLike 𝕜] : BOanFamStep.{u} 𝕜 :=
  ⟨fun n bmo m => BO.BOanFamOfInput 𝕜 (n + 1) bmo m⟩

/-- The order-reduction tower on the compatible-family structures along Theorem 103
(`theorem103FamStar`) and a given second reduction step `h107`. -/
def orderReductionTowerAnFamStarOf (𝕜 : Type) [RCLike 𝕜] (h107 : BMOanFamStep.{u} 𝕜) :
    ∀ n : ℕ, OrderReductionStageAnFam.{u} 𝕜 n :=
  orderReductionTowerAnFam (theorem103FamStar 𝕜) h107

/-- The tower along `theorem103FamStar` unfolds to `orderReductionTowerAnFam` at that step. -/
theorem orderReductionTowerAnFamStarOf_eq (𝕜 : Type) [RCLike 𝕜] (h107 : BMOanFamStep.{u} 𝕜) :
    orderReductionTowerAnFamStarOf 𝕜 h107 = orderReductionTowerAnFam (theorem103FamStar 𝕜) h107 :=
  rfl

end Hironaka.Manifold

end
