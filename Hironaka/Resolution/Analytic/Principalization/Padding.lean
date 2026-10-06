/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Assembly
public import Hironaka.Resolution.Analytic.Principalization.DisjoinedNatural
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.Principalization.DisjoinBoundary
import Hironaka.Resolution.Analytic.Principalization.DisjoinLemmas
import Hironaka.Resolution.Analytic.Principalization.DisjoinNatural
import Hironaka.Resolution.Analytic.Principalization.ShrinkAppendLemmas
import Hironaka.Resolution.Analytic.Principalization.ValueNatural
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Padding the disjoining list by empty blow-ups

Kollár's empty-blow-up convention [Kol07, 32] for the disjoining list: when the `(m+2)`-fold locus
of `E` is already empty, the first round of `disjoinList (m+2)` blows up the empty centre and the
rest is the pull-back of `disjoinList (m+1)` along the blow-down `Bl_∅ M → M` (the strict
transform along an empty blow-up is the preimage, `strictTransformSet_empty_of_isClosed`). The
value built from the padded list is the value built from the unpadded one:

* the empty first round is erased (`eraseEmpty_cons_of_eq_empty`) and its blow-down carried
  through the shrink-and-append step (`shrinkAppend_pullback_eraseEmpty`, with the compatibility
  of the input family on the two reading opens) — `valueOf_cons_of_eq_empty`;
* the pulled-back list is compared with the list itself by `valueOf_pullback`, the disjoined
  triple of the padded list being an empty extension of the pull-back of the disjoined triple
  (`isEmptyExtensionOfPullback_disjoinedTripleOf_cons_of_eq_empty`) — the padded exceptional
  divisor is empty and the input family is indifferent to it.

Iterating, the value built from `disjoinList k` for the disjoined triple does not depend on the
admissible bound `k` (`valueOf_disjoinList_eq`) — the first half of the canonicity of the
shrinking chain (the disjoining bounds over two shrinking opens differ), completed in
`Canonicity.lean`. This realises Kollár's functoriality for smooth morphisms [Kol07, 34.1], where
a pull-back is compared with the value "by deleting every blow-up whose center is empty".
-/

public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

section General

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The padded disjoining list -/

/-- The empty-blow-up convention [Kol07, 32] for the disjoining list: when the `(m+2)`-fold locus
is already empty, the first round of `disjoinList (m+2)` blows up the empty centre and the rest is
the pull-back of `disjoinList (m+1)` along the blow-down. -/
theorem disjoinList_succ_succ_eq_cons_pullback {M : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) {m : ℕ} (hm₂ : F.meetLocus (m + 2 + 1) = ∅)
    (hm₁ : F.meetLocus (m + 2) = ∅) :
    disjoinList (ψ₀ := ψ₀) (m + 2) F hF hm₂ =
      AnalyticManifold.BlowUpSequence.cons (hF.isClosedSubmanifold_meetLocus hm₂)
        ((disjoinList (m + 1) F hF hm₁).pullback
          (Manifold.blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm₂))
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_blowUpπ_of_eq_empty _ hm₁)) := by
  have hnext : disjoinNext F hF hm₂ =
      F.comap (Manifold.blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm₂)) := by
    unfold disjoinNext HypersurfaceFamily.strictTransforms HypersurfaceFamily.comap
    congr 1
    funext j
    have h1 : F.hyp j \ F.meetLocus (m + 2) = F.hyp j := by rw [hm₁, Set.sdiff_empty]
    unfold strictTransformSet
    rw [h1, ((hF.isClosedSubmanifold j).isClosed.preimage
      (Manifold.blowUpπ ψ₀ (hF.isClosedSubmanifold_meetLocus hm₂)).contMDiff.continuous).closure_eq]
  rw [disjoinList_succ_succ, disjoinList_pullback]
  exact congrArg (AnalyticManifold.BlowUpSequence.cons _) (disjoinList_congr hnext (m + 1) _ _ _ _)

/-- Transport of the snc hypothesis on the boundary along an equality of lists. -/
theorem isSnc_totalTransformSeqFrom_last_congr {M : AnalyticManifold.{u} 𝕜 E}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (e : L₁ = L₂) (F : HypersurfaceFamily M)
    (h : (L₁.toSuccession.totalTransformSeqFrom F (Fin.last _)).IsSnc ψ₀) :
    (L₂.toSuccession.totalTransformSeqFrom F (Fin.last _)).IsSnc ψ₀ := by
  subst e
  exact h

/-- Transport of the disjointness hypothesis on the original members along an equality of lists. -/
theorem meetLocus_two_subfamily_original_congr {M : AnalyticManifold.{u} 𝕜 E}
    {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (e : L₁ = L₂) (F : HypersurfaceFamily M)
    (h : ((L₁.toSuccession.totalTransformSeqFrom F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₁.toSuccession.originalIdx F (Fin.last _)))).meetLocus 2 = ∅) :
    ((L₂.toSuccession.totalTransformSeqFrom F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L₂.toSuccession.originalIdx F (Fin.last _)))).meetLocus 2 = ∅ := by
  subst e
  exact h

/-- A map with relatively compact range, composed with an analytic isomorphism: the range of the
other factor is relatively compact. -/
theorem isCompact_closure_range_of_comp_diffeomorph {A B N : AnalyticManifold.{u} 𝕜 E}
    (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) A B ω) (ι₁ : AnalyticMap N A) (ι : AnalyticMap N B)
    (h : ∀ p, φ (ι₁ p) = ι p) (hc : IsCompact (closure (Set.range ι))) :
    IsCompact (closure (Set.range ι₁)) := by
  have hr : Set.range ι₁ = ⇑φ.toHomeomorph ⁻¹' Set.range ι := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, (h p).symm⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, φ.toEquiv.injective ?_⟩
      change φ (ι₁ p) = φ x
      rw [h p]
      exact hp
  rw [hr, ← φ.toHomeomorph.preimage_closure]
  exact φ.toHomeomorph.isCompact_preimage.mpr hc

namespace CenterList

open AnalyticManifold.BlowUpSequence _root_.Manifold

/-- The shrink-and-append step of a list whose first round is empty over the reading map: the empty
round is erased and its blow-down carried through the step along the corestricted lift
(`eraseEmpty_cons_of_eq_empty`, `shrinkAppend_pullback_eraseEmpty`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.eraseEmpty_cons_shrinkAppend_of_eq_empty
    {X N : AnalyticManifold.{u} 𝕜 E} {Y : Set X}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (R : AnalyticManifold.BlowUpSequence ψ₀
        (Manifold.blowUp ψ₀ hY))
    (ι : AnalyticMap N X) (hι : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ι) (hY₀' : ⇑ι ⁻¹' Y = ∅)
    (B : AnalyticManifold.BlowUpSequence ψ₀ ((R.stage (Fin.last _)).restrict
      (R.liftRange (liftStep ι hι hY) (isLocalDiffeomorph_liftStep ι hι hY))))
    (ι₁ : AnalyticMap N (Manifold.blowUp ψ₀ hY)) (hι₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ι₁)
    (hcomp : (liftStep ι hι hY).comp (Diffeomorph.toAnalyticMap
      (emptyBlowUpDiffeomorph (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm) = ι₁)
    (B₁ : AnalyticManifold.BlowUpSequence ψ₀ ((R.stage (Fin.last _)).restrict (R.liftRange ι₁ hι₁)))
    (hle : R.liftRange ι₁ hι₁ ≤
      R.liftRange (liftStep ι hι hY) (isLocalDiffeomorph_liftStep ι hι hY))
    (hB : B₁.eraseEmpty = (B.pullback ((R.stage (Fin.last _)).restrictLE hle)
      (isLocalDiffeomorph_restrictLE hle)).eraseEmpty) :
    ((cons hY R).shrinkAppend ι hι B).eraseEmpty = (R.shrinkAppend ι₁ hι₁ B₁).eraseEmpty := by
  have h1 : ((cons hY R).shrinkAppend ι hι B).eraseEmpty =
      ((R.shrinkAppend (liftStep ι hι hY) (isLocalDiffeomorph_liftStep ι hι hY) B).pullback
        (Diffeomorph.toAnalyticMap
          (emptyBlowUpDiffeomorph (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm)
        (emptyBlowUpDiffeomorph (hY.preimage_of_isLocalDiffeomorph hι)
          hY₀').symm.isLocalDiffeomorph).eraseEmpty := by
    change (cons (hY.preimage_of_isLocalDiffeomorph hι)
      (R.shrinkAppend (liftStep ι hι hY) (isLocalDiffeomorph_liftStep ι hι hY) B)).eraseEmpty = _
    rw [eraseEmpty_cons_of_eq_empty _ _ hY₀', map_eq_pullback_symm,
      eraseEmpty_pullback _ _ _ (emptyBlowUpDiffeomorph _ hY₀').symm.toEquiv.surjective]
  rw [h1]
  exact shrinkAppend_pullback_eraseEmpty R (liftStep ι hι hY) (isLocalDiffeomorph_liftStep ι hι hY)
    _ _ ι₁ hι₁ hcomp B B₁ hle hB

end CenterList

end General

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-! ### The value of a list whose first round is empty -/

/-- The value built from a list whose first centre is empty over the reading map `ι` is the value
built from its tail, read along the lift of `ι` composed with the inverse of the empty blow-up. -/
theorem valueOf_cons_of_eq_empty (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {Y : Set X} {c : ℕ}
    (hY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y c)
    (R : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (Manifold.blowUp _ hY))
    (T₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((AnalyticManifold.BlowUpSequence.cons hY R).stage (Fin.last _)))
    (hT₂ : AnalyticTriple.BMOClass 1 T₂) (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) (hY₀' : ⇑ι ⁻¹' Y = ∅)
    (ι₁ : AnalyticMap N (Manifold.blowUp _ hY))
    (hι₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι₁)
    (hc₁ : IsCompact (closure (Set.range ι₁)))
    (hcomp : (AnalyticManifold.BlowUpSequence.liftStep ι hι hY).comp (Diffeomorph.toAnalyticMap
      (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
          (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm) = ι₁) :
    valueOf bmo (AnalyticManifold.BlowUpSequence.cons hY R) T₂ hT₂ ι hι hc = valueOf bmo R T₂ hT₂
        ι₁ hι₁ hc₁ := by
  have hle : R.liftRange ι₁ hι₁ ≤ R.liftRange (AnalyticManifold.BlowUpSequence.liftStep ι hι hY)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ι hι hY) :=
    AnalyticManifold.BlowUpSequence.range_pullbackLiftLast_subset_of_comp R _ _ _
      (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph _ hY₀').symm.isLocalDiffeomorph _ _
          hcomp
  unfold valueOf
  refine AnalyticManifold.BlowUpSequence.eraseEmpty_cons_shrinkAppend_of_eq_empty hY R ι hι hY₀' _
      ι₁ hι₁ hcomp _ hle ?_
  have e := (bmo.functor.fam T₂ hT₂).compat _ _ (R.isCompact_closure_liftRange ι₁ hι₁ hc₁)
    ((AnalyticManifold.BlowUpSequence.cons hY R).isCompact_closure_liftRange ι hι hc) hle
  exact (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty e).trans
      (AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _)

/-! ### One padding step -/

/-- The empty-blow-up convention [Kol07, 32] for the value: the value built from the list padded by
an empty first round, `cons h∅ (π^* L)`, and its disjoined triple is the value built from `L` and
its disjoined triple. -/
theorem valueOf_disjoinedTripleOf_cons_pullback_of_eq_empty (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) {Y : Set X}
        {c : ℕ}
    (hY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y c) (hY₀ : Y = ∅)
    (h₁ : (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc _)
    (h₁' : ((L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅)
    (h₂ : ((AnalyticManifold.BlowUpSequence.cons hY (L.pullback (Manifold.blowUpπ _ hY)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_blowUpπ_of_eq_empty hY
        hY₀))).toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc _)
    (h₂' : (((AnalyticManifold.BlowUpSequence.cons hY (L.pullback (Manifold.blowUpπ _ hY)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_blowUpπ_of_eq_empty hY
        hY₀))).toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
        (fun k => k ∈ Set.range
          ((AnalyticManifold.BlowUpSequence.cons hY (L.pullback (Manifold.blowUpπ _ hY)
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_blowUpπ_of_eq_empty hY
                hY₀))).toSuccession.originalIdx
              T.F (Fin.last _)))).meetLocus 2 = ∅)
    (ι : AnalyticMap N X) (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) :
    valueOf bmo (AnalyticManifold.BlowUpSequence.cons hY (L.pullback (Manifold.blowUpπ _ hY)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_blowUpπ_of_eq_empty hY hY₀)))
      (disjoinedTripleOf T _ h₂ h₂') (disjoinedTripleOf_bmoClass T _ h₂ h₂') ι hι hc =
      valueOf bmo L (disjoinedTripleOf T L h₁ h₁') (disjoinedTripleOf_bmoClass T L h₁ h₁') ι hι
        hc := by
  have hY₀' : ⇑ι ⁻¹' Y = ∅ := by rw [hY₀, Set.preimage_empty]
  have hι₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((AnalyticManifold.BlowUpSequence.liftStep ι hι hY).comp (Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
            (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep ι hι hY)
      (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph _ hY₀').symm.isLocalDiffeomorph
  have hcomp₁ : (Manifold.blowUpπ _ hY).comp ((AnalyticManifold.BlowUpSequence.liftStep ι hι
      hY).comp (Diffeomorph.toAnalyticMap
      (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
          (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm)) =
      ι := by
    refine ContMDiffMap.ext fun p => ?_
    change Manifold.blowUpπ _ hY (AnalyticManifold.BlowUpSequence.liftStep ι hι hY
      ((AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
          (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm p)) =
      ι p
    rw [AnalyticManifold.BlowUpSequence.blowUpπ_liftStep,
      ← AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph_apply
          (hY.preimage_of_isLocalDiffeomorph hι) hY₀',
      Diffeomorph.apply_symm_apply]
  have hc₁ : IsCompact (closure (Set.range ((AnalyticManifold.BlowUpSequence.liftStep ι hι hY).comp
      (Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph
            (hY.preimage_of_isLocalDiffeomorph hι) hY₀').symm)))) :=
    isCompact_closure_range_of_comp_diffeomorph
        (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph hY hY₀) _ ι
      (fun p => (AnalyticManifold.BlowUpSequence.emptyBlowUpDiffeomorph_apply hY hY₀ _).trans
        (congrArg (fun f : AnalyticMap N X => f p) hcomp₁)) hc
  refine (valueOf_cons_of_eq_empty bmo hY _ _ _ ι hι hc hY₀' _ hι₁ hc₁ rfl).trans ?_
  exact valueOf_pullback bmo L (Manifold.blowUpπ _ hY) _ _ hι₁ ι hι hcomp₁ hc₁ hc _ _ _ _
    (AnalyticManifold.BlowUpSequence.isEmptyExtensionOfPullback_disjoinedTripleOf_cons_of_eq_empty
        T L hY hY₀ _ h₁ h₁'
      h₂ h₂')

/-! ### Independence of the disjoining bound -/

/-- One padding step for the disjoining list of a triple: the value at the bound `k + 1` is the
value at the bound `k` (both admissible). -/
theorem valueOf_disjoinList_succ (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) :
    ∀ (k : ℕ) (hk : T.F.meetLocus (k + 1) = ∅) (hk' : T.F.meetLocus (k + 1 + 1) = ∅),
    valueOf bmo (disjoinList (k + 1) T.F T.isSnc hk') (disjoinedTriple T hk')
        (disjoinedTriple_bmoClass T hk') ι hι hc =
      valueOf bmo (disjoinList k T.F T.isSnc hk) (disjoinedTriple T hk)
        (disjoinedTriple_bmoClass T hk) ι hι hc
  | 0, _, _ => rfl
  | k + 1, hk, hk' => by
    have e := disjoinList_succ_succ_eq_cons_pullback T.F T.isSnc hk' hk
    refine (valueOf_disjoinedTripleOf_congr bmo T e _ _
      (isSnc_totalTransformSeqFrom_last_congr e T.F
        (disjoinList_isSnc_totalTransformSeqFrom (k + 2) T.F T.isSnc hk' (Fin.last _)))
      (meetLocus_two_subfamily_original_congr e T.F
        (meetLocus_two_subfamily_original_eq_empty (k + 2) T.F T.isSnc hk')) ι hι hc).trans ?_
    exact valueOf_disjoinedTripleOf_cons_pullback_of_eq_empty bmo T _ _ hk _ _ _ _ ι hι hc

/-- Iterated padding: the value at the bound `k + d` is the value at the bound `k`. -/
theorem valueOf_disjoinList_add (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) :
    ∀ (d k : ℕ) (hk : T.F.meetLocus (k + 1) = ∅) (hkd : T.F.meetLocus (k + d + 1) = ∅),
    valueOf bmo (disjoinList (k + d) T.F T.isSnc hkd) (disjoinedTriple T hkd)
        (disjoinedTriple_bmoClass T hkd) ι hι hc =
      valueOf bmo (disjoinList k T.F T.isSnc hk) (disjoinedTriple T hk)
        (disjoinedTriple_bmoClass T hk) ι hι hc
  | 0, _, _, _ => rfl
  | d + 1, k, hk, hkd => by
    have hkd' : T.F.meetLocus (k + d + 1) = ∅ :=
      Set.eq_empty_of_subset_empty fun x hx =>
        hk ▸ HypersurfaceFamily.meetLocus_antitone (F := T.F) (by omega : k + 1 ≤ k + d + 1) hx
    exact (valueOf_disjoinList_succ bmo T ι hι hc (k + d) hkd' hkd).trans
      (valueOf_disjoinList_add bmo T ι hι hc d k hk hkd')

/-- **The value does not depend on the admissible disjoining bound** ([Kol07, 32]): for two bounds
`k₁`, `k₂` with `E` having no `(kᵢ+1)`-fold points, the values built from `disjoinList k₁` and
`disjoinList k₂` with their disjoined triples agree. -/
theorem valueOf_disjoinList_eq (bmo : BMOanFam.{u} 𝕜 n 1)
    {X N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X) (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
    (hc : IsCompact (closure (Set.range ι))) (k₁ k₂ : ℕ) (hk₁ : T.F.meetLocus (k₁ + 1) = ∅)
    (hk₂ : T.F.meetLocus (k₂ + 1) = ∅) :
    valueOf bmo (disjoinList k₁ T.F T.isSnc hk₁) (disjoinedTriple T hk₁)
        (disjoinedTriple_bmoClass T hk₁) ι hι hc =
      valueOf bmo (disjoinList k₂ T.F T.isSnc hk₂) (disjoinedTriple T hk₂)
        (disjoinedTriple_bmoClass T hk₂) ι hι hc := by
  rcases le_total k₁ k₂ with h | h
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    exact (valueOf_disjoinList_add bmo T ι hι hc d k₁ hk₁ hk₂).symm
  · obtain ⟨d, rfl⟩ := Nat.le.dest h
    exact valueOf_disjoinList_add bmo T ι hι hc d k₂ hk₂ hk₁

end Hironaka.Manifold
