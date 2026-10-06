/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.StratumIso
public import Hironaka.AnalyticSpace.Sigma
import Hironaka.AnalyticSpace.SigmaLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A non-singular analytic space as the coproduct of its strata

For a non-singular analytic `K`-space `X`, the strata `X_d = {x | dim 𝒪_{X,x} = d}` (`dimOpens`) are
open, pairwise disjoint and cover `X`, and each is `K`-isomorphic to the space of the manifold
`stratumManifold X hX d` modelled on `K^d` (`stratumKIso`,
`Hironaka.AnalyticSpace.Manifold.StratumIso`). The morphisms `stratumIncl d : Sp(X_d) ⟶ X` (the
isomorphism followed by the open immersion `X | X_d ⟶ X`) are therefore open immersions with
pairwise disjoint images covering `X`, so their descent `∐ d, Sp(X_d) ⟶ X` is an isomorphism
(`isIso_sigmaDesc_of_isOpenImmersion`); `stratumSigmaIso : X ≅ ∐ d, Sp(X_d)` is its inverse, and a
point has local dimension `d` exactly when its image lies in the `d`-th summand
(`ringKrullDim_eq_iff_exists`).

This is the disjoint-union form of Hironaka's description of a non-singular analytic space as
locally the space of an open subset of some `K^d` [Hir64, Ch. 0, §1, p. 121]: a non-singular
analytic space is the space of a manifold whose components may have different dimensions. It is used
to apply results proved for the spaces of manifolds of one dimension to arbitrary non-singular
analytic spaces (`Hironaka.AnalyticSpace.SigmaCoproductLemmas`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Manifold ContDiff

universe u

noncomputable section

namespace AnalyticSpace

variable {K : Type} [RCLike K] (X : AnalyticSpace.{u} K) (hX : X.IsNonsingular)

/-- `Sp` of the `d`-th stratum, with the identity coordinates on `K^d`. -/
abbrev stratumSpaceOf (d : ℕ) : AnalyticSpace.{u} K :=
  toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) (stratumManifold X hX d)

/-- The morphism `Sp(X_d) ⟶ X`: the isomorphism `Sp(X_d) ≅ X | X_d` followed by the open immersion
`X | X_d ⟶ X`. -/
def stratumIncl (d : ℕ) : stratumSpaceOf X hX d ⟶ X :=
  (((stratumKIso X hX d).hom :
    (stratumSpaceOf X hX d).toKLocallyRingedSpace ⟶ stratumRestrict X hX d) ≫
    KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (dimOpens X hX d) :
      (stratumSpaceOf X hX d).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace)

/-- `Sp(X_d) ⟶ X` is an open immersion (an isomorphism followed by an open immersion). -/
instance isOpenImmersion_stratumIncl (d : ℕ) :
    LocallyRingedSpace.IsOpenImmersion (stratumIncl X hX d).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion ((stratumKIso X hX d).hom.1 ≫
    (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace (dimOpens X hX d)).1))

/-- The image of `Sp(X_d) ⟶ X` lies in the stratum `X_d`. -/
theorem toFun_stratumIncl_mem (d : ℕ) (m : stratumSpaceOf X hX d) :
    Hom.toFun (stratumIncl X hX d) m ∈ dimSet X d :=
  (KLocallyRingedSpace.Hom.toFun (stratumKIso X hX d).hom m).2

/-- Every point of the stratum `X_d` is in the image of `Sp(X_d) ⟶ X`. -/
theorem exists_toFun_stratumIncl_eq {d : ℕ} {x : X} (hx : x ∈ dimSet X d) :
    ∃ m : stratumSpaceOf X hX d, Hom.toFun (stratumIncl X hX d) m = x := by
  obtain ⟨m, hm⟩ : ∃ m, KLocallyRingedSpace.Hom.toFun (stratumKIso X hX d).hom m =
      (⟨x, hx⟩ : dimOpens X hX d) :=
    ⟨KLocallyRingedSpace.Hom.toFun (stratumKIso X hX d).inv ⟨x, hx⟩,
      congrArg (fun g : stratumRestrict X hX d ⟶ stratumRestrict X hX d =>
        KLocallyRingedSpace.Hom.toFun g (⟨x, hx⟩ : dimOpens X hX d))
        (stratumKIso X hX d).inv_hom_id⟩
  exact ⟨m, congrArg Subtype.val hm⟩

/-- The descent `∐ d, Sp(X_d) ⟶ X` of the inclusions of the strata. -/
def stratumDesc : sigma (fun d => stratumSpaceOf X hX d) ⟶ X :=
  sigmaDesc (stratumIncl X hX)

/-- The descent of the strata is an isomorphism: the `Sp(X_d) ⟶ X` are open immersions with pairwise
disjoint images (a point has one local dimension) covering `X` (`iUnion_dimSet_eq_univ`). -/
theorem isIso_stratumDesc : IsIso (stratumDesc X hX) := by
  refine isIso_sigmaDesc_of_isOpenImmersion _ ?_ ?_
  · intro d d' hdd' a b h
    apply hdd'
    have ha := toFun_stratumIncl_mem X hX d a
    have hb := toFun_stratumIncl_mem X hX d' b
    rw [h] at ha
    have : ((d : ℕ) : WithBot ℕ∞) = d' := ha.symm.trans hb
    exact_mod_cast this
  · intro x
    have hx : x ∈ ⋃ d, dimSet X d := by
      rw [iUnion_dimSet_eq_univ X hX]
      trivial
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hx
    obtain ⟨m, hm⟩ := exists_toFun_stratumIncl_eq X hX hd
    exact ⟨d, m, hm⟩

/-- **A non-singular analytic `K`-space is the coproduct of its pure-dimensional strata**,
`X ≅ ∐ d, Sp(X_d)` [Hir64, Ch. 0, §1, p. 121]. -/
def stratumSigmaIso : X ≅ sigma (fun d => stratumSpaceOf X hX d) :=
  have := isIso_stratumDesc X hX
  (asIso (stratumDesc X hX)).symm

/-- Under `X ≅ ∐ d, Sp(X_d)`, a point of `X` goes to the point `m` of the `d`-th summand exactly
when it is the image of `m` under `Sp(X_d) ⟶ X`. -/
theorem toFun_stratumSigmaIso_hom_eq_iff (d : ℕ) (x : X) (m : stratumSpaceOf X hX d) :
    Hom.toFun (stratumSigmaIso X hX).hom x =
        Hom.toFun (sigmaι (fun d => stratumSpaceOf X hX d) d) m ↔
      x = Hom.toFun (stratumIncl X hX d) m := by
  have := isIso_stratumDesc X hX
  have h₁ : ∀ y, Hom.toFun (stratumDesc X hX) (Hom.toFun (stratumSigmaIso X hX).hom y) = y :=
    fun y => congrArg (fun g : X ⟶ X => Hom.toFun g y) (IsIso.inv_hom_id (stratumDesc X hX))
  have h₂ : ∀ z, Hom.toFun (stratumSigmaIso X hX).hom (Hom.toFun (stratumDesc X hX) z) = z :=
    fun z => congrArg (fun g : sigma (fun d => stratumSpaceOf X hX d) ⟶ _ => Hom.toFun g z)
      (IsIso.hom_inv_id (stratumDesc X hX))
  rw [← toFun_sigmaDesc_toFun_sigmaι (stratumIncl X hX) d m]
  constructor
  · intro h
    rw [← h₁ x, h]
    rfl
  · intro h
    rw [h]
    exact h₂ _

/-- Under `X ≅ ∐ d, Sp(X_d)`, the points of local dimension `d` are exactly the points of the `d`-th
summand. -/
theorem ringKrullDim_eq_iff_exists (d : ℕ) (x : X) :
    ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞) ↔
      ∃ m : stratumManifold X hX d, Hom.toFun (stratumSigmaIso X hX).hom x =
        Hom.toFun (sigmaι (fun d => stratumSpaceOf X hX d) d) m := by
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := exists_toFun_stratumIncl_eq X hX (d := d) hx
    exact ⟨m, (toFun_stratumSigmaIso_hom_eq_iff X hX d x m).mpr hm.symm⟩
  · rintro ⟨m, hm⟩
    rw [(toFun_stratumSigmaIso_hom_eq_iff X hX d x m).mp hm]
    exact toFun_stratumIncl_mem X hX d m

end AnalyticSpace
