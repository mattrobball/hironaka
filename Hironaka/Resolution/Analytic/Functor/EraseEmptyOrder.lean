/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# [Kol07, Definition 66] survives the deletion of empty blow-ups

For the boundary of the main theorems, the reduced ideal sheaf `F.idealSheaf` of a simple normal
crossings family `F`, a list of order `≥ m` for `(I, m, F.idealSheaf)` [Kol07, Definition 66]
stays of order `≥ m` after the deletion of its empty blow-ups ([Kol07, 34.1];
`BlowUpSequence.isOfOrderGe_eraseEmpty`): a kept step contributes the same two clauses on both
sides, with the boundary transformed to the reduced ideal sheaf of the total transform of `F`
(`reducedTransform_eq_idealSheaf_totalTransform`), so that the recursion runs over simple normal
crossings families; a deleted step is an isomorphism `Bl_∅ M ≃ M` along which [Kol07, Definition
66] pulls back (`isOfOrderGe_map`, from the descent `isOfOrderGe_of_pullback`), the marked
transform being the pull-back (`cons_markedTransformSeq_one_of_eq_empty`) and the boundary the
pull-back of `F.idealSheaf` (`reducedTransform_blowUpπ_idealSheaf_of_eq_empty`: the total transform
of `F` along the empty blowing-up has the support of `π⁻¹(F)`, and the reduced ideal sheaf depends
only on the support).

The statement is for the boundary `F.idealSheaf` and not for an arbitrary ideal sheaf `E₀`: at a
deleted step the boundary becomes `red(π⁻¹E₀)`, not `π⁻¹E₀`, and identifying the normal-crossings
clause for `E₀` with that for its reduction would need a Nullstellensatz, which is not done here.
The counterpart for schemes is in `Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced`.
-/

public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The reduced ideal sheaf of a family depends only on its support. -/
theorem HypersurfaceFamily.idealSheaf_congr_support {M : AnalyticManifold.{u} 𝕜 E}
    {F G : HypersurfaceFamily M} (h : F.support = G.support) :
    F.idealSheaf (𝕜 := 𝕜) (E := E) = G.idealSheaf := by
  unfold HypersurfaceFamily.idealSheaf
  rw [h]

/-- Along the chosen blowing-up of an empty centre, the reduced transform of the reduced ideal
sheaf of an snc family is the pull-back of that reduced ideal sheaf: by dictionary it is
the reduced ideal sheaf of the total transform, whose support is `π⁻¹(|F|)`. -/
theorem _root_.Hironaka.Manifold.reducedTransform_blowUpπ_idealSheaf_of_eq_empty
    {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ₀) :
    IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) F.idealSheaf hY.idealSheaf =
      F.idealSheaf.pullback _ (blowUpπ ψ₀ hY).contMDiff := by
  subst hY₀
  have hsnc : F.HasSncWith ψ₀ (∅ : Set M) c := fun a ha => absurd ha (Set.notMem_empty a)
  have h1 :
      IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) F.idealSheaf hY.idealSheaf =
      (F.totalTransform (blowUpπ ψ₀ hY) ∅).idealSheaf :=
    reducedTransform_eq_idealSheaf_totalTransform hY (isBlowUp_blowUpπ ψ₀ hY) hF hsnc
  have hloc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (blowUpπ ψ₀ hY) := by
    rw [← toAnalyticMap_emptyBlowUpDiffeomorph hY rfl]
    exact (BlowUpSequence.emptyBlowUpDiffeomorph hY rfl).isLocalDiffeomorph
  have hsurj : Function.Surjective (blowUpπ ψ₀ hY) := by
    rw [← toAnalyticMap_emptyBlowUpDiffeomorph hY rfl]
    exact (BlowUpSequence.emptyBlowUpDiffeomorph hY rfl).toEquiv.surjective
  have h2 : (F.totalTransform (blowUpπ ψ₀ hY) ∅).support = (F.comap (blowUpπ ψ₀ hY)).support := by
    rw [HypersurfaceFamily.support_totalTransform _ _ _ (blowUpπ ψ₀ hY).contMDiff.continuous
      (fun j => (hF.1 j).isClosed), HypersurfaceFamily.support_comap, Set.preimage_empty,
      Set.union_empty]
  rw [h1, HypersurfaceFamily.idealSheaf_congr_support h2,
    HypersurfaceFamily.idealSheaf_comap_of_surjective (blowUpπ ψ₀ hY) hloc hsurj F]

end Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold
open Manifold Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- [Kol07, Definition 66] pulls back along a diffeomorphism: the transport of a list of order `≥
m` for the pull-backs of `(I, E₀)` is of order `≥ m` for `(I, E₀)` (descent
`isOfOrderGe_of_pullback` along `φ`, the transport being the pull-back along `φ⁻¹`). -/
theorem isOfOrderGe_map (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (Z : BlowUpSequence ψ₀ M) (I E₀ : IdealSheaf N) (m : ℕ)
    (h :
        Z.toSuccession.IsOfOrderGe
            (I.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff) m
      (E₀.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff)) :
    (Z.map φ).toSuccession.IsOfOrderGe I m E₀ := by
  have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
  have hid : (Diffeomorph.toAnalyticMap φ.symm).comp (Diffeomorph.toAnalyticMap φ) =
      ContMDiffMap.id :=
    ContMDiffMap.ext fun x => φ.symm_apply_apply x
  refine isOfOrderGe_of_pullback _ (Diffeomorph.toAnalyticMap φ) φ.isLocalDiffeomorph
    φ.toEquiv.surjective I E₀ m ?_
  rw [map_eq_pullback_symm, pullback_comp, pullback_congr _ hid _ (isLocalDiffeomorph_id _),
    pullback_id]
  exact h

/-- [Kol07, 34.1] for [Kol07, Definition 66] with the boundary: **a list of order
`≥ m` for `(I, m, red F)`, `F` an snc family, stays of order `≥ m` after the deletion of its empty
blow-ups** — so the erased list's induced triple lies in the class. -/
theorem isOfOrderGe_eraseEmpty : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (I : IdealSheaf M) (m : ℕ)
        {F : HypersurfaceFamily M},
    F.IsSnc ψ₀ → L.toSuccession.IsOfOrderGe I m F.idealSheaf →
    L.eraseEmpty.toSuccession.IsOfOrderGe I m F.idealSheaf
  | _, nil _, I, m, F, _, _ => FiniteSuccession.isOfOrderGe_nil I F.idealSheaf m
  | _, @cons _ _ _ _ _ _ _ _ Y _ hY rest, I, m, F, hF, hge => by
    have : FiniteDimensional 𝕜 E := ψ₀.symm.toLinearEquiv.finiteDimensional
    obtain ⟨⟨hnc, hm⟩, hrest⟩ := (FiniteSuccession.isOfOrderGe_cons_iff (I := I) (m := m)
      (E₀ := F.idealSheaf) hY rest.toSuccession).mp hge
    have hsnc : F.HasSncWith ψ₀ Y _ := (hasOnlyNormalCrossingsWith_idealSheaf_iff hF hY).mp hnc
    have hF₁ : (F.totalTransform (blowUpπ ψ₀ hY) Y).IsSnc ψ₀ :=
      HypersurfaceFamily.isSnc_totalTransform hY (isBlowUp_blowUpπ ψ₀ hY) hF hsnc
    have hred : IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) F.idealSheaf hY.idealSheaf =
        (F.totalTransform (blowUpπ ψ₀ hY) Y).idealSheaf :=
      reducedTransform_eq_idealSheaf_totalTransform hY (isBlowUp_blowUpπ ψ₀ hY) hF hsnc
    rw [hred] at hrest
    have ih := isOfOrderGe_eraseEmpty rest _ m hF₁ hrest
    by_cases hY₀ : Y = ∅
    · rw [eraseEmpty_cons_of_eq_empty hY rest hY₀]
      refine isOfOrderGe_map (emptyBlowUpDiffeomorph hY hY₀) rest.eraseEmpty I F.idealSheaf m ?_
      rw [toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀,
        ← FiniteSuccession.cons_markedTransformSeq_one_of_eq_empty hY hY₀ rest.toSuccession I m,
        (reducedTransform_blowUpπ_idealSheaf_of_eq_empty hY hY₀ hF).symm.trans hred]
      exact ih
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀]
      refine (FiniteSuccession.isOfOrderGe_cons_iff (I := I) (m := m) (E₀ := F.idealSheaf) hY
        rest.eraseEmpty.toSuccession).mpr ⟨⟨hnc, hm⟩, ?_⟩
      rw [hred, FiniteSuccession.cons_markedTransformSeq_one]
      rw [FiniteSuccession.cons_markedTransformSeq_one] at ih
      exact ih

end AnalyticManifold.BlowUpSequence

end
