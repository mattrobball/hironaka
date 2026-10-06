/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.Principalization.MonomialStep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial predicate along the assembly of the value

`BlowUpSequence.PullbackIsMonomialAtLast L F I`: at every point `x` of the last stage of `L`, the
pull-back of `I` along the composite blow-down is a monomial in the vanishing ideals of finitely
many members of the final total transform of `F` through `x` — the chart-free monomial clause of
Kollár's explicit formula [Kol07, 72], as a predicate on a list of centres. It is transported along
the constructions that assemble the principalization:

* `cons` (`pullbackIsMonomialAtLast_cons`): the head blow-up pulls `I` and `F` back, the tail
  carries the predicate (`cons_totalTransformSeqFrom_last`, `stageMapAux_cons_succ`);
* `concat` (`pullbackIsMonomialAtLast_concat`, by induction through `cons`): the predicate for the
  appended list with the boundary and the pulled-back ideal at the junction gives it for the
  concatenation — the shrink-and-append step is a `concat` of a pulled-back list;
* `eraseEmpty` (`pullbackIsMonomialAtLast_eraseEmpty`): along the diffeomorphism `eraseEmptyLast`
  of the last stages (the deletion of the empty blow-ups, [Kol07, 32]) the composites agree
  (`stageMap_last_eraseEmptyLast`), the boundary members correspond with the members of the list's
  boundary outside the range of the empty ones (`boundaryCorr_eraseEmpty`), and the vanishing
  ideals transport along the bijective germ map (`vanishingStalk_preimage_diffeomorph`);
* the order clause `ord I_r < 1` of the input ([Kol07, Theorem 107 (1)]) along the pull-back of a
  list by a local isomorphism (`ord_markedTransformSeq_pullback_last_lt_one`, via
  `markedTransformSeqAux_pullback`): `ord < 1` is "the stalk is the unit ideal", which pulls back.

Used for the monomial clause at general mark (`MonomialSeqMark.lean`).
-/

@[expose] public section

universe u

open TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Order `< 1` at a point means the stalk is the unit ideal (`ord_eq_zero_iff`). -/
theorem IdealSheaf.ord_lt_one_iff_stalkIdeal_eq_top {M : AnalyticManifold.{u} 𝕜 E}
    (J : AnalyticManifold.IdealSheaf M) (x : M) :
    J.ord x < ((1 : ℕ) : ℕ∞) ↔ J.stalkIdeal x = ⊤ := by
  rw [Nat.cast_one, Order.lt_one_iff, IdealSheaf.ord_eq_zero_iff, mem_support,
    not_not]

/-- Order `< 1` pulls back along any analytic map (the unit stalk maps to the unit ideal). -/
theorem IdealSheaf.ord_comap_lt_one {M N : AnalyticManifold.{u} 𝕜 E} (f : AnalyticMap N M)
    (J : AnalyticManifold.IdealSheaf M) {x : N} (h : J.ord (f x) < ((1 : ℕ) : ℕ∞)) :
    (J.pullback f f.contMDiff).ord x < ((1 : ℕ) : ℕ∞) := by
  rw [IdealSheaf.ord_lt_one_iff_stalkIdeal_eq_top] at h ⊢
  rw [IdealSheaf.stalkIdeal_pullback, h, Ideal.map_top]

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The chart-free reading of Kollár's formula [Kol07, 72] as a predicate on a list: at every point
`x` of the last stage, the pull-back of `I` along the composite blow-down is a monomial in the
vanishing ideals of finitely many members of the final total transform of `F` through `x`. -/
def PullbackIsMonomialAtLast {X : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ X)
    (F : HypersurfaceFamily X) (I : IdealSheaf X) : Prop :=
  ∀ x : L.stage (Fin.last _),
    ∃ (s : Finset (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι)
      (α : (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).ι → ℕ),
      (∀ j ∈ s, x ∈ (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp j) ∧
      (I.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff).stalkIdeal x
          =
        ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E)
          ((L.toSuccession.totalTransformSeqFrom F (Fin.last _)).hyp j) x ^ α j

/-- The composite blow-down of `cons hY rest` is the head blow-up after the tail's composite, as
ideal-sheaf pull-backs. -/
theorem comap_stageMap_last_cons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (R : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
    (I : IdealSheaf M) :
    I.pullback _ ((cons hY R).toSuccession.stageMap (Fin.last _)).contMDiff =
      (I.pullback _ (blowUpπ ψ₀ hY).contMDiff).pullback _ (R.toSuccession.stageMap (Fin.last
          _)).contMDiff := by
  rw [IdealSheaf.pullback_comp]
  refine congrArg (fun f : AnalyticMap _ _ => I.pullback f f.contMDiff)
      (ContMDiffMap.ext fun p => ?_)
  exact stageMapAux_cons_succ hY R R.length (Nat.lt_succ_self _) p

/-- The predicate for `cons hY rest` from the predicate for the tail with the pulled-back boundary
and ideal. -/
theorem pullbackIsMonomialAtLast_cons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (R : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
        (F : HypersurfaceFamily M)
    (I : IdealSheaf M)
    (hR : R.PullbackIsMonomialAtLast (F.totalTransform (blowUpπ ψ₀ hY) Y)
      (I.pullback _ (blowUpπ ψ₀ hY).contMDiff)) :
    (cons hY R).PullbackIsMonomialAtLast F I := by
  intro x
  have eF : (cons hY R).toSuccession.totalTransformSeqFrom F (Fin.last _) =
      R.toSuccession.totalTransformSeqFrom (F.totalTransform (blowUpπ ψ₀ hY) Y) (Fin.last _) :=
    FiniteSuccession.cons_totalTransformSeqFrom_last hY R.toSuccession F
  rw [comap_stageMap_last_cons hY R I, eF]
  exact hR x

/-- The predicate for a concatenation from the predicate for the appended list with the boundary
and the pulled-back ideal at the junction. -/
theorem pullbackIsMonomialAtLast_concat :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (A : BlowUpSequence ψ₀ M)
      (B : BlowUpSequence ψ₀ (A.stage (Fin.last _))) (F : HypersurfaceFamily M)
      (I : IdealSheaf M),
      B.PullbackIsMonomialAtLast (A.toSuccession.totalTransformSeqFrom F (Fin.last _))
        (I.pullback _ (A.toSuccession.stageMap (Fin.last _)).contMDiff) →
      (A.concat B).PullbackIsMonomialAtLast F I
  | _, nil M, B, F, I, hB => by
    have eI :
        Manifold.IdealSheaf.pullback _ ((nil (ψ₀ := ψ₀) M).toSuccession.stageMap (Fin.last
            _)).contMDiff
        I = I := by
      change IdealSheaf.pullback (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id I = I
      exact IdealSheaf.pullback_id_eq_self I
    rw [eI] at hB
    exact hB
  | _, cons hY rest, B, F, I, hB => by
    rw [concat_cons]
    refine pullbackIsMonomialAtLast_cons hY _ F I ?_
    refine pullbackIsMonomialAtLast_concat rest B _ _ ?_
    rw [← FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.toSuccession F,
      ← comap_stageMap_last_cons hY rest I]
    exact hB

/-- The predicate is preserved by the deletion of the empty blow-ups ([Kol07, 32]): along the
diffeomorphism `eraseEmptyLast` of the last stages the composites agree and the boundary members
correspond (`boundaryCorr_eraseEmpty`), the vanishing ideals transporting along the bijective
germ map. -/
theorem pullbackIsMonomialAtLast_eraseEmpty {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    {F : HypersurfaceFamily M} (hF : ∀ j, IsClosed (F.hyp j))
        (I : IdealSheaf M)
    (hL : L.PullbackIsMonomialAtLast F I) : L.eraseEmpty.PullbackIsMonomialAtLast F I := by
  classical
  intro x'
  obtain ⟨s, α, hs, hx⟩ := hL (L.eraseEmptyLast.symm x')
  obtain ⟨e', he₁, he₂, -⟩ := boundaryCorr_eraseEmpty L F F (RelEmbedding.refl (· ≤ ·))
    ⟨fun _ => rfl, fun b hb => absurd ⟨b, rfl⟩ hb⟩ hF
  have hrange : ∀ j ∈ s, j ∈ Set.range e' := fun j hj => by
    by_contra hj'
    have := hs j hj
    rw [he₂ j hj'] at this
    exact this
  have eI :
      I.pullback _ (L.eraseEmpty.toSuccession.stageMap (Fin.last _)).contMDiff =
      (I.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff).pullback _
          (Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm).contMDiff := by
    rw [IdealSheaf.pullback_comp]
    refine congrArg (fun f : AnalyticMap _ _ => I.pullback f f.contMDiff)
        (ContMDiffMap.ext fun p => ?_)
    change L.eraseEmpty.toSuccession.stageMap (Fin.last _) p =
      L.toSuccession.stageMap (Fin.last _) (L.eraseEmptyLast.symm p)
    rw [← stageMap_last_eraseEmptyLast L (L.eraseEmptyLast.symm p), Diffeomorph.apply_symm_apply]
  refine ⟨s.preimage e' e'.injective.injOn, fun i => α (e' i), fun i hi => ?_, ?_⟩
  · rw [← he₁ i]
    exact hs _ (Finset.mem_preimage.mp hi)
  · rw [eI]
    change (IdealSheaf.pullback (⇑L.eraseEmptyLast.symm) L.eraseEmptyLast.symm.contMDiff
      (I.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff)).stalkIdeal
          x' = _
    rw [IdealSheaf.stalkIdeal_pullback, hx, Hironaka.Manifold.Ideal.map_finset_prod]
    symm
    refine Finset.prod_bij (fun a _ => e' a) (fun a ha => Finset.mem_preimage.mp ha)
      (fun _ _ _ _ h => e'.injective h) (fun b hb => ?_) fun a _ => ?_
    · obtain ⟨i, rfl⟩ := hrange b hb
      exact ⟨i, Finset.mem_preimage.mpr hb, rfl⟩
    · rw [Ideal.map_pow, ← he₁ a, vanishingStalk_preimage_diffeomorph]

/-- The order clause of [Kol07, Theorem 107 (1)] along the pull-back of a list by a local analytic
isomorphism: the last marked transform of the pulled-back list is the pull-back of the last marked
transform (`markedTransformSeqAux_pullback`), so `ord < 1` — the unit stalk — pulls back. -/
theorem ord_markedTransformSeq_pullback_last_lt_one {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (I E₀ : IdealSheaf M)
    (hge : L.toSuccession.IsOfOrderGe I 1 E₀)
    (hlt : ∀ x : L.stage (Fin.last _),
      (L.toSuccession.markedTransformSeq I 1 (Fin.last _)).ord x < ((1 : ℕ) : ℕ∞))
    (q : (L.pullback h hh).stage (Fin.last _)) :
    ((L.pullback h hh).toSuccession.markedTransformSeq (I.pullback h h.contMDiff) 1
      (Fin.last _)).ord q < ((1 : ℕ) : ℕ∞) := by
  have := finiteDimensional_of_chartIso ψ₀
  have key : ∀ (a : ℕ) (ha : a < (L.pullback h hh).length + 1), a = L.length →
      ∀ x : (L.pullback h hh).toSuccession.stage ⟨a, ha⟩,
        ((L.pullback h hh).toSuccession.markedTransformSeqAux
            (I.pullback h h.contMDiff) 1
          a ha).ord x < ((1 : ℕ) : ℕ∞) := by
    intro a ha hal x
    subst hal
    rw [markedTransformSeqAux_pullback L h hh I E₀ 1 hge L.length (Nat.lt_succ_self _) ha]
    exact IdealSheaf.ord_comap_lt_one _ _ (hlt _)
  exact key _ (Fin.last _).2 (length_pullback L h hh) q

end AnalyticManifold.BlowUpSequence

