/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.Canonicity
public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Hironaka.Resolution.Analytic.Principalization.Padding
import Hironaka.Resolution.Analytic.Principalization.ValueNatural
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Clause (5) of the principalization family: closed embeddings with `F = ∅`

Clause (5) of [Kol07, Theorem 35] ([Kol07, 34.3]; [Kol07, Claim 71.2], proved in [Kol07, 108]),
per open, in the form `CommutesWithClosedEmbeddingsOfEmptyDivisorFam`: for `F = ∅` the value of
the principalization functor in dimension `n` on `U` is the restricted push-forward of the value
in dimension `n − s` on `U ∩ S`, for a closed submanifold `S` of codimension `s`. The route:
**for `F = ∅` the principalization value is the input's value** (`principalizationValue_empty`) —
the disjoining bound is `0` (no nonempty member, `Nat.card_of_isEmpty`), the disjoining list is
`nil` (`valueOf_disjoinList_eq` moves the value to the bound `0`), the disjoined triple has the
restricted ideal (`pullback_id_eq_self`) and a boundary whose members are all empty (the collapse
of the empty family), so the input's `indifferentToEmptyMembers` reads it on the empty family, its
`commutesWithLocalIsos` along the inclusion of the shrinking open and its `compat` along
`U ≤ image` bring the value back to `U`, the `eraseEmpty`s collapsing by
`eraseEmpty_pullback_eraseEmpty` and `eraseEmpty_of_noEmptyCenters`. Clause (5) is then the input
family's commutation `hbmo` rewritten on both sides (`principalizationFam_closedEmbedding`).
Kollár's remark that (71.2) only makes sense for the marking `m = 1` [Kol07, Claim 71.2] is why
the input is taken at mark `1`.
-/

@[expose] public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The triple `(M, 𝓘, ∅)`. -/
noncomputable abbrev emptyTriple (I : AnalyticManifold.IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
  ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩

/-- `(M, 𝓘, ∅)` lies in the marked class at mark `1`. -/
theorem emptyTriple_bmoClass (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere) :
    AnalyticTriple.BMOClass 1 (emptyTriple I hI) :=
  AnalyticTriple.bmoClass_one_empty I hI

/-- With no member, the disjoining bound is `0`. -/
theorem disjoinBound_emptyTriple (I : AnalyticManifold.IdealSheaf M)
    (hI : I.IsNonzeroEverywhere)
    (W : Opens M) : disjoinBound (emptyTriple I hI) W = 0 := by
  have : IsEmpty {j // (restrictTriple (emptyTriple I hI) W).F.hyp j ≠ ∅} :=
    ⟨fun j => PEmpty.elim j.1⟩
  exact Nat.card_of_isEmpty

/-- The one-point locus of the restricted empty family is empty. -/
theorem meetLocus_one_restrictTriple_emptyTriple (I : AnalyticManifold.IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) (W : Opens M) :
    (restrictTriple (emptyTriple I hI) W).F.meetLocus (0 + 1) = ∅ := by
  rw [HypersurfaceFamily.meetLocus_one]
  refine Set.eq_empty_of_subset_empty fun x hx => ?_
  obtain ⟨j, -⟩ := Set.mem_iUnion.mp hx
  exact PEmpty.elim j

/-- The order embedding of the empty family into any family. -/
def emptyOrderEmbedding {X : Type u} (G : HypersurfaceFamily X) :
    (HypersurfaceFamily.empty X).ι ↪o G.ι :=
  ⟨⟨fun j => j.elim, fun j => j.elim⟩, fun {j} => j.elim⟩

/-- Every member of the collapse of a memberless family along the empty disjoining list is
empty. -/
theorem collapsedFamilyOf_nil_hyp_eq_empty (X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜))
    (F : HypersurfaceFamily X) (hF : IsEmpty F.ι)
    (k : (collapsedFamilyOf (AnalyticManifold.BlowUpSequence.nil (ψ₀ :=
        ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      F).ι) :
    (collapsedFamilyOf (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜
        (Fin n → 𝕜)) X) F).hyp
      k = ∅ := by
  obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
  unfold collapsedFamilyOf
  rcases k' with _ | ⟨j, -⟩
  · rw [HypersurfaceFamily.collapse_hyp_inl]
    refine Set.eq_empty_of_subset_empty fun x hx => ?_
    obtain ⟨j, -⟩ := Set.mem_iUnion.mp hx
    exact (hF.false j.1).elim
  · exact (hF.false j).elim

/-- **For the empty divisor the principalization value on `U` is the input's value on `U`**
([Kol07, 72] with `E = ∅`: no disjoining blow-up): the disjoined triple is the restricted triple up
to an empty boundary member, and the input's `indifferentToEmptyMembers`, `commutesWithLocalIsos`
(along the inclusion of the shrinking open) and `compat` (along `U ≤ image`) bring its value on the
reading open back to `U`. -/
theorem principalizationValue_empty (bmo : BMOanFam.{u} 𝕜 n 1)
    (I : AnalyticManifold.IdealSheaf M)
    (hI : I.IsNonzeroEverywhere) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hT : AnalyticTriple.BMOClass 1 (emptyTriple I hI)) :
    principalizationValue bmo (emptyTriple I hI) U hU =
      (bmo.functor.fam (emptyTriple I hI) hT).seqOn U hU := by
  have hUW : U ≤ shrinkOpen U hU := subset_closure.trans (closure_subset_shrinkOpen U hU)
  have hW := isCompact_closure_shrinkOpen U hU
  have hι := isLocalDiffeomorph_restrictLE hUW
  have hc : IsCompact (closure (Set.range (M.restrictLE hUW))) :=
    isCompact_closure_range_restrictLE hUW hU (closure_subset_shrinkOpen U hU)
  -- the disjoining bound is irrelevant: read the value at the bound `0`, i.e. the list `nil`
  unfold principalizationValue principalizationValueOn
  rw [valueOf_disjoinList_eq bmo (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)) _ _ _
    (disjoinBound (emptyTriple I hI) (shrinkOpen U hU)) 0
    (meetLocus_disjoinBound_eq_empty (emptyTriple I hI) (shrinkOpen U hU) hW)
    (meetLocus_one_restrictTriple_emptyTriple I hI (shrinkOpen U hU))]
  -- the reading open of `nil`: the range of the restriction map
  have hU' := (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (M.restrict (shrinkOpen U hU))).isCompact_closure_liftRange (M.restrictLE hUW) hι hc
  -- the disjoined triple reads on the empty triple of the shrinking open
  have hemptyι : IsEmpty (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).F.ι :=
    ⟨fun j => PEmpty.elim j⟩
  have hT'' : AnalyticTriple.BMOClass 1
      (emptyTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).I
        (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).isNonzeroEverywhere) :=
    emptyTriple_bmoClass _ _
  have hseq : (bmo.functor.fam
        (disjoinedTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU))
          (meetLocus_one_restrictTriple_emptyTriple I hI (shrinkOpen U hU)))
        (disjoinedTriple_bmoClass _ _)).seqOn _ hU' =
      (bmo.functor.fam (emptyTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).I
        (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).isNonzeroEverywhere) hT'').seqOn
        _ hU' := by
    have e := bmo.indifferentToEmptyMembers
      (disjoinedTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU))
        (meetLocus_one_restrictTriple_emptyTriple I hI (shrinkOpen U hU)))
      (HypersurfaceFamily.empty (M.restrict (shrinkOpen U hU)))
      HypersurfaceFamily.isSnc_empty
      (emptyOrderEmbedding (disjoinedTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU))
        (meetLocus_one_restrictTriple_emptyTriple I hI (shrinkOpen U hU))).F) (fun i => i.elim)
      (fun b _ => collapsedFamilyOf_nil_hyp_eq_empty (M.restrict (shrinkOpen U hU))
        (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).F hemptyι b)
      (disjoinedTriple_bmoClass _ _)
      (AnalyticTriple.bmoClass_one_of_isEmpty _ ⟨fun j => PEmpty.elim j⟩)
      ((AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict (shrinkOpen U hU))).liftRange (M.restrictLE hUW) hι) hU'
    refine e.trans (bmo.functor.seqOn_congr ?_ _ hT'' _ hU')
    refine AnalyticTriple.ext' ?_ rfl
    change (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).I.pullback ContMDiffMap.id
        ContMDiffMap.id.contMDiff =
      (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).I
    exact IdealSheaf.pullback_id_eq_self _
  -- the empty triple on the shrinking open is the pull-back of the empty triple along the inclusion
  have hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (M.inclusion (shrinkOpen U hU)) :=
    isLocalDiffeomorph_inclusion M (shrinkOpen U hU)
  have hpull : (emptyTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).I
      (restrictTriple (emptyTriple I hI) (shrinkOpen U hU)).isNonzeroEverywhere).IsPullbackOf
        (emptyTriple I hI) (M.inclusion (shrinkOpen U hU)) :=
    ⟨rfl, (HypersurfaceFamily.empty_comap ⇑(M.inclusion (shrinkOpen U hU))).symm⟩
  have hcomm := bmo.commutesWithLocalIsos (emptyTriple I hI) _ (M.inclusion (shrinkOpen U hU)) hg
    hpull hT hT'' _ hU'
  -- the image of the reading open contains `U`
  have hUV : U ≤ AnalyticMap.imageOpens (M.inclusion (shrinkOpen U hU)) hg
      ((AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict (shrinkOpen U hU))).liftRange (M.restrictLE hUW) hι) :=
    fun x hx => ⟨M.restrictLE hUW ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hcompat := (bmo.functor.fam (emptyTriple I hI) hT).compat U _ hU
    (AnalyticMap.isCompact_closure_image (M.inclusion (shrinkOpen U hU)) hU') hUV
  -- assemble
  unfold valueOf
  change (((bmo.functor.fam
      (disjoinedTriple (restrictTriple (emptyTriple I hI) (shrinkOpen U hU))
        (meetLocus_one_restrictTriple_emptyTriple I hI (shrinkOpen U hU)))
      (disjoinedTriple_bmoClass _ _)).seqOn _ hU').pullback
    ((AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict (shrinkOpen U hU))).liftCorestrict (M.restrictLE hUW) hι)
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)).eraseEmpty = _
  rw [hseq, hcomm]
  refine (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ _).trans ?_
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
      (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).trans ?_
  refine (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
      (AnalyticManifold.BlowUpSequence.pullback_congr _ ?_ _ _)).trans hcompat.symm
  exact ContMDiffMap.ext fun q => Subtype.ext rfl

/-- Clause (5) of [Kol07, Theorem 35] ([Kol07, 34.3; Claim 71.2; 108]): the principalization
functors commute with closed embeddings of empty divisor between the models `𝕜ⁿ` and `𝕜^{n−s}`
whenever the input family does (`hbmo`) — for `F = ∅` both values are the input's values
(`principalizationValue_empty`). -/
theorem principalizationFam_closedEmbedding (bmo : ∀ n : ℕ, BMOanFam.{u} 𝕜 n 1)
    (hbmo : ∀ (n s : ℕ),
      (bmo n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) (bmo (n - s)).functor)
    (n s : ℕ) :
    (principalizationFam (bmo n)).CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
      (principalizationFam (bmo (n - s))) := by
  intro M S hS I hI J hJ hle hJ' _ _ U hU
  rw [principalizationFam_seqOn, principalizationFam_seqOn]
  change principalizationValue (bmo n) (emptyTriple I hI) U hU =
    AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U (principalizationValue (bmo (n - s))
        (emptyTriple J hJ)
      (hS.preimageOpens U) (hS.isCompact_closure_preimageOpens U hU))
  rw [principalizationValue_empty (bmo n) I hI U hU (emptyTriple_bmoClass I hI),
    principalizationValue_empty (bmo (n - s)) J hJ _ _ (emptyTriple_bmoClass J hJ)]
  exact hbmo n s hS I hI J hJ hle hJ' (emptyTriple_bmoClass I hI) (emptyTriple_bmoClass J hJ) U hU

end Hironaka.Manifold
