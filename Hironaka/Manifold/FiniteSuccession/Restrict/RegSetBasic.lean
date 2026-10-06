/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.CenterComponents
import Hironaka.AnalyticSpace.ClosedSubspace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The simple locus of a closed subspace of a manifold, read in the ambient

`CenterComponents.lean` reads the simple points of the closed subspace `V(J) = Sp(A)/J` of a
manifold `A` (`IdealSheaf.toAnalyticSpace`) as the subset `regSet J ⊆ A`, the image of
`Reg (V(J))` under the canonical inclusion. This module supplies the elementary facts about that
reading:

* the stalk of `V(J)` at a point `y` is the quotient `𝒪_{A,y} / J_y` of the ambient stalk
  (`QuotientSpace.stalkEquiv`), so `V(J)` is reduced when `J` has radical stalks
  (`isReduced_toAnalyticSpace_of_isRadical`; a space is reduced when its local rings have no
  nilpotent elements, [Hir64, Introduction]); the simple points themselves are read through
  `mem_reg_toAnalyticSpace_iff` (`Hironaka/Resolution/Analytic/Wlo09/Clauses`);
* the inclusion `V(J) → A` is continuous with range the support `|J|` (the underlying space of a
  local analytic space `(S(𝓘), 𝒜_G/𝓘)` is the support of `𝒜_G/𝓘`, [Hir64, Ch. 0, §1, p. 119]),
  so `regSet J ⊆ |J|`.
-/

@[expose] public section

open Set TopologicalSpace

universe u

noncomputable section

namespace Manifold

variable {K : Type} [RCLike K] {n : ℕ} {A : AnalyticManifold.{u} K (Fin n → K)}
  (J : AnalyticManifold.IdealSheaf A)

/-- The closed subspace `V(J)` is reduced when `J` has radical stalks: its stalks are the
quotients `𝒪_{A,y} / J_y` (`QuotientSpace.stalkEquiv`), and reducedness means that the local
rings have no nilpotent elements [Hir64, Introduction]. -/
theorem isReduced_toAnalyticSpace_of_isRadical (hJ : ∀ x, (J.stalkIdeal x).IsRadical) :
    (AnalyticManifold.IdealSheaf.toAnalyticSpace J).IsReduced := by
  intro y
  have : IsReduced (AnalyticSpace.QuotientSpace.fiber
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K))
        A).toLocallyRingedSpace J y) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (hJ y.1)
  exact isReduced_of_injective
    (AnalyticSpace.QuotientSpace.stalkEquiv
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K))
        A).toLocallyRingedSpace J y)
    (AnalyticSpace.QuotientSpace.stalkEquiv
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K))
        A).toLocallyRingedSpace J y).injective

/-- The range of the inclusion `V(J) → A` is the support `|J|` (`range_toFun_closedSubspaceι`, in
the form of `regSet`); the underlying space of a local analytic space is the support of its
structure sheaf [Hir64, Ch. 0, §1, p. 119]. -/
theorem range_toFun_toAnalyticSpaceι :
    Set.range (fun y => (J.toAnalyticSpaceι y : A)) = J.support :=
  AnalyticSpace.range_toFun_closedSubspaceι
    (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K)) A) J

/-- The simple locus of `V(J)`, read in `A`, lies in the support `|J|`. -/
theorem regSet_subset_cosupport : AnalyticManifold.IdealSheaf.regSet J ⊆ J.support := by
  rintro _ ⟨y, -, rfl⟩
  rw [← range_toFun_toAnalyticSpaceι J]
  exact ⟨y, rfl⟩

/-- The inclusion `V(J) → A` is continuous (the base map of the canonical morphism). -/
theorem continuous_toFun_toAnalyticSpaceι :
    Continuous (Y := A)
      (fun y => (J.toAnalyticSpaceι y : A)) :=
  (AnalyticManifold.IdealSheaf.toAnalyticSpaceι J).1.base.hom.continuous

end Manifold

end
