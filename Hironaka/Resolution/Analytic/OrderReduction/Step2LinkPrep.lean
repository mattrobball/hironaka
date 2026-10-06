/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ValueTransport
public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamFunctoriality
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The value of Step 2.2 under deletion of empty blow-ups and under pull-back

The value of Step 2.2 on an open is the family functor of Step 2.2 (`Step22Fam.lean`) at the
triple of Step 2.2 over the sequence of Step 2.1, read on the lifted range of the last
restriction. To transport this value along the restrictions of the chain and along local analytic
isomorphisms (`Step2LinkTransport.lean`), exactly as `ChainTransport.lean` transports Lemma 102's
family at the induced triple, three facts about the value are needed:

* `BO.hfStep22Fam_seqOn_eraseEmpty` — the value over a sequence `L` is its value over the sequence
  with the empty blow-ups deleted, transported along the identification of the last stages
  (`eraseEmptyLast`). The tuned triple of Step 2.2 over `L` is the pull-back of the tuned triple of
  Step 2.2 over the cleaned sequence along `eraseEmptyLast`, up to the empty exceptional members
  (the appended member `H_r` is kept), so the indifference of the data to empty boundary members
  ([Kol07, 32]) and their commutation with local analytic isomorphisms ([Kol07, 34.1]) at the
  re-tuned mark give the value.
* `BO.hfStep22Fam_seqOn_pullback`, `BO.hfStep22Fam_seqOn_pullback_liftRange` — the value over the
  pull-back of `L` along a local analytic isomorphism is the pull-back of the value over `L`
  along the lift, with empty blow-ups deleted: the triple of Step 2.2 over the pulled-back
  sequence is the pull-back of the triple of Step 2.2 along the lift
  (`step22TripleOf_isPullbackOf`, `Step22Pullback.lean`), and the family functor of Step 2.2
  commutes with local analytic isomorphisms (`Step22FamFunctoriality.lean`); with the
  compatibility of the family under inclusion, this gives the value on the lifted reading opens
  ([Kol07, 104, Step 2.3]).
* `BO.hfStep22Fam_seqOn_congr` — the value depends only on the sequence: a substitution along an
  equality of sequences.

The `hf…` declarations are the general forms over data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`); the plain forms are their instances at Lemma 102's data.
-/

public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ}

namespace BO

open _root_.Manifold

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s)

section Erase

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) {H : Set M}
  (hH : IsClosedSubmanifold ψ₀ H 1) (L : AnalyticManifold.BlowUpSequence ψ₀ M)
  (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
  (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)
  (hcls : stepHClass s (step22TripleOf T L hL hsnc))
  (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
  (hsnce : ((exceptionalOf L.eraseEmpty).append (transformHOf L.eraseEmpty H)).IsSnc ψ₀)
  (hclse : stepHClass s (step22TripleOf T L.eraseEmpty hLe hsnce))

include hH in
/-- The value of the family functor of Step 2.2 over a sequence `L` is its value over the sequence
with the empty blow-ups deleted, transported along the identification `eraseEmptyLast` of the last
stages, with empty blow-ups deleted ([Kol07, 32] and [Kol07, 34.1]; over data `d`). The tuned triple
of Step 2.2 over `L` is the pull-back of the tuned triple of Step 2.2 over the cleaned sequence
along `eraseEmptyLast`, up to the empty exceptional members of the deleted steps
(`markedTransformSeq_last_eraseEmpty`, `eraseEmptyIdx`; the appended member `H_r` is kept, both
greatest members being the appended one), so the indifference of the data to empty members at the
re-tuned mark and then their commutation with local analytic isomorphisms give the value. -/
theorem hfStep22Fam_seqOn_eraseEmpty (V : Opens (L.stage (Fin.last _)))
    (hV : IsCompact (closure (V : Set (L.stage (Fin.last _))))) :
    ((hfStep22Functor d.hf).fam (step22TripleOf T L hL hsnc) hcls).seqOn V hV =
      ((((hfStep22Functor d.hf).fam (step22TripleOf T L.eraseEmpty hLe hsnce) hclse).seqOn
          (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
            L.eraseEmptyLast.isLocalDiffeomorph V)
          (AnalyticMap.isCompact_closure_image _ hV)).pullback
        (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap L.eraseEmptyLast) V _ Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap L.eraseEmptyLast.isLocalDiffeomorph V _
          Set.Subset.rfl)).eraseEmpty := by
  have hFe : ∀ j, IsClosed ((HypersurfaceFamily.empty M).hyp j) := fun j => j.elim
  -- the erased exceptional family embeds into the exceptional family, the appended member kept
  let e₀ : (exceptionalOf L.eraseEmpty).ι ↪o (exceptionalOf L).ι :=
    AnalyticManifold.BlowUpSequence.eraseEmptyIdx L (HypersurfaceFamily.empty M) hFe
  let eZ : (step22TripleOf T L.eraseEmpty hLe hsnce).F.ι ↪o (step22TripleOf T L hL hsnc).F.ι :=
    Hironaka.Sequence.sumLexMapEmb (γ := PUnit.{u + 1}) e₀
  -- the tuned Step-2.2 triple of the cleaned list, pulled back along `eraseEmptyLast`
  have hpb : AnalyticTriple.BOClass (tuningParam s)
      (((step22TripleOf T L.eraseEmpty hLe hsnce).tuned s hclse.1.1).pullback
        (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph) :=
    AnalyticTriple.boClass_of_isPullbackOf (AnalyticTriple.boClass_tuned hclse.1)
      L.eraseEmptyLast.isLocalDiffeomorph (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hsnc' : ((step22TripleOf T L.eraseEmpty hLe hsnce).F.comap
      ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast)).IsSnc ψ₀ :=
    HypersurfaceFamily.isSnc_comap (step22TripleOf T L.eraseEmpty hLe hsnce).isSnc _
      L.eraseEmptyLast.isLocalDiffeomorph
  -- the tuned Step-2.2 triple of `L` is that pull-back up to the empty exceptional members
  have htriple : (⟨((step22TripleOf T L hL hsnc).tuned s hcls.1.1).I,
      ((step22TripleOf T L hL hsnc).tuned s hcls.1.1).isNonzeroEverywhere,
      (step22TripleOf T L.eraseEmpty hLe hsnce).F.comap
        ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast), hsnc'⟩ :
        AnalyticTriple ψ₀ (L.stage (Fin.last _))) =
      ((step22TripleOf T L.eraseEmpty hLe hsnce).tuned s hclse.1.1).pullback
        (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph := by
    refine AnalyticTriple.ext' ?_ rfl
    change (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).tuning s (tuningParam s) =
      ((L.eraseEmpty.toSuccession.markedTransformSeq T.I s (Fin.last _)).tuning s
          (tuningParam s)).pullback _ (Diffeomorph.toAnalyticMap L.eraseEmptyLast).contMDiff
    rw [comap_tuning (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
      L.eraseEmptyLast.isLocalDiffeomorph _ s (tuningParam s),
      AnalyticManifold.BlowUpSequence.markedTransformSeq_last_eraseEmpty L T.I T.F.idealSheaf s hL]
    exact congrArg
      (fun J : AnalyticManifold.IdealSheaf (L.stage (Fin.last _)) => J.tuning s (tuningParam s))
      (comap_symm_comap L.eraseEmptyLast.symm
        (L.toSuccession.markedTransformSeq T.I s (Fin.last _))).symm
  -- the members correspond along `eZ`, the exceptional divisors of the deleted steps being empty
  have he : ∀ i, (step22TripleOf T L hL hsnc).F.hyp (eZ i) =
      ((step22TripleOf T L.eraseEmpty hLe hsnce).F.comap
        ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast)).hyp i := by
    intro i
    obtain ⟨i', rfl⟩ : ∃ i', toLex i' = i := ⟨ofLex i, rfl⟩
    rcases i' with i₀ | u
    · change (L.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty M) (Fin.last _)).hyp
          (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L (HypersurfaceFamily.empty M) hFe i₀) =
        ⇑L.eraseEmptyLast ⁻¹'
          (L.eraseEmpty.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty M)
            (Fin.last _)).hyp i₀
      rw [← AnalyticManifold.BlowUpSequence.hyp_eraseEmptyIdx L (HypersurfaceFamily.empty M) hFe i₀]
      exact (L.eraseEmptyLast.toEquiv.preimage_symm_preimage _).symm
    · change L.toSuccession.strictTransformSeq H (Fin.last _) =
        ⇑L.eraseEmptyLast ⁻¹' L.eraseEmpty.toSuccession.strictTransformSeq H (Fin.last _)
      rw [AnalyticManifold.BlowUpSequence.strictTransformSeq_last_eraseEmpty L hH.isClosed]
      exact (L.eraseEmptyLast.toEquiv.preimage_symm_preimage _).symm
  have he' : ∀ b, b ∉ Set.range eZ → (step22TripleOf T L hL hsnc).F.hyp b = ∅ := by
    intro b hb
    obtain ⟨b', rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
    rcases b' with b₀ | u
    · have hb₀ : b₀ ∉ Set.range e₀ := fun ⟨a, ha⟩ =>
        hb ⟨toLex (Sum.inl a), congrArg (fun x => toLex (Sum.inl x)) ha⟩
      change (L.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty M) (Fin.last _)).hyp
        b₀ = ∅
      exact AnalyticManifold.BlowUpSequence.hyp_eq_empty_of_notMem_range_eraseEmptyIdx L
          (HypersurfaceFamily.empty M)
        hFe b₀ hb₀
    · exact absurd ⟨toLex (Sum.inr u), rfl⟩ hb
  have hT' : AnalyticTriple.BOClass (tuningParam s)
      (⟨((step22TripleOf T L hL hsnc).tuned s hcls.1.1).I,
        ((step22TripleOf T L hL hsnc).tuned s hcls.1.1).isNonzeroEverywhere,
        (step22TripleOf T L.eraseEmpty hLe hsnce).F.comap
          ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast), hsnc'⟩ : AnalyticTriple ψ₀ _) := by
    rw [htriple]
    exact hpb
  -- the data's indifference at the appended member, then its commutation along `eraseEmptyLast`
  have hind := d.hf.indifferentToEmptyMembers
    ((step22TripleOf T L hL hsnc).tuned s hcls.1.1) _ hsnc' eZ he he'
    (AnalyticTriple.boClass_tuned hcls.1) hT' (toLex (Sum.inr PUnit.unit)) V hV
  have hcomm := d.hf.commutesWithLocalIsos
    ((step22TripleOf T L.eraseEmpty hLe hsnce).tuned s hclse.1.1)
    (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph
    (AnalyticTriple.boClass_tuned hclse.1) hpb (toLex (Sum.inr PUnit.unit)) V hV
  -- both greatest members are the appended one
  have hg₁ : greatestIdx (stepHClass_tuned hcls) =
      (toLex (Sum.inr PUnit.unit) : (exceptionalOf L).ι ⊕ₗ PUnit.{u + 1}) :=
    greatestIdx_eq _ fun k => le_toLex_inr k
  have hg₂ : greatestIdx (stepHClass_tuned hclse) =
      (toLex (Sum.inr PUnit.unit) : (exceptionalOf L.eraseEmpty).ι ⊕ₗ PUnit.{u + 1}) :=
    greatestIdx_eq _ fun k => le_toLex_inr k
  refine (hfStep22Functor_fam_seqOn d.hf _ hcls V hV).trans ?_
  rw [hg₁]
  refine (hind.trans (d.hf.fam_congr_seqOn htriple hT' hpb _ _ HEq.rfl V hV)).trans
    ?_
  refine hcomm.trans ?_
  exact congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ ((L.eraseEmpty.stage
      (Fin.last _)).restrict
      (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
        L.eraseEmptyLast.isLocalDiffeomorph V)) => (X.pullback
      (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap L.eraseEmptyLast) V _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap L.eraseEmptyLast.isLocalDiffeomorph V _
        Set.Subset.rfl)).eraseEmpty)
    ((d.hf.fam_congr_seqOn rfl (AnalyticTriple.boClass_tuned hclse.1)
      (AnalyticTriple.boClass_tuned hclse.1) _ _ (heq_of_eq hg₂) _ _).symm.trans
      (hfStep22Functor_fam_seqOn d.hf _ hclse _ _).symm)

end Erase

section Pullback

variable {M N P Q : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) {H : Set M}
  (hW : AnalyticMap N M) (hhW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hW)
  (L : AnalyticManifold.BlowUpSequence ψ₀ M) (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
  (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)
  (hcls : stepHClass s (step22TripleOf T L hL hsnc))
  (hL' : (L.pullback hW hhW).toSuccession.IsOfOrderGe (T.pullback hW hhW).I s
    (T.pullback hW hhW).F.idealSheaf)
  (hsnc' : ((exceptionalOf (L.pullback hW hhW)).append
    (transformHOf (L.pullback hW hhW) (⇑hW ⁻¹' H))).IsSnc ψ₀)
  (hcls' : stepHClass s (step22TripleOf (T.pullback hW hhW) (L.pullback hW hhW) hL' hsnc'))

/-- The value of the family functor of Step 2.2 over the pull-back of a sequence along a local
analytic isomorphism is the pull-back of its value over the sequence, read at the image of the open
under the lift, with empty blow-ups deleted ([Kol07, 34.1]; over data `d`): the triple of Step 2.2
over the pulled-back sequence is the pull-back of the triple of Step 2.2 along the lift
(`step22TripleOf_isPullbackOf`), and the family functor of Step 2.2 commutes with local analytic
isomorphisms (`hfStep22Functor_commutesWithLocalIsos`). -/
theorem hfStep22Fam_seqOn_pullback (U' : Opens ((L.pullback hW hhW).stage (Fin.last _)))
    (hU' : IsCompact (closure (U' : Set ((L.pullback hW hhW).stage (Fin.last _))))) :
    ((hfStep22Functor d.hf).fam (step22TripleOf (T.pullback hW hhW) (L.pullback hW hhW) hL' hsnc')
        hcls').seqOn U' hU' =
      ((((hfStep22Functor d.hf).fam (step22TripleOf T L hL hsnc) hcls).seqOn
          (AnalyticMap.imageOpens (L.pullbackLiftLast hW hhW)
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L hW hhW) U')
          (AnalyticMap.isCompact_closure_image _ hU')).pullback
        (AnalyticMap.restrictMap (L.pullbackLiftLast hW hhW) U' _ Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L hW hhW) U' _
          Set.Subset.rfl)).eraseEmpty :=
  hfStep22Functor_commutesWithLocalIsos d.hf (step22TripleOf T L hL hsnc)
    (step22TripleOf (T.pullback hW hhW) (L.pullback hW hhW) hL' hsnc') (L.pullbackLiftLast hW hhW)
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L hW hhW)
    (step22TripleOf_isPullbackOf T hW hhW L hL hL' hsnc hsnc') hcls hcls' U' hU'

variable (ρ : AnalyticMap P M) (hρ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ)
  (ρ' : AnalyticMap Q N) (hρ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ρ')
  (hV : AnalyticMap Q P) (hhV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω hV)
  (hsq : ρ.comp hV = hW.comp ρ')

include hsq in
/-- The value over the sequence `L` on the lifted range of `ρ`, pulled back along the lift
restricted to the lifted range of `ρ'`, is the value over the pulled-back sequence on the lifted
range of `ρ'` (over data `d`): `hfStep22Fam_seqOn_pullback`, the compatibility of the family under
inclusion, and the fact that the lift carries the lifted range of `ρ'` into that of `ρ` by the
commuting square `hsq`. The analogue for Lemma 102's family at the induced triple is
`fam_seqOn_induced_pullback_liftRange` (`ChainTransport.lean`). -/
theorem hfStep22Fam_seqOn_pullback_liftRange
    (hO₁ : IsCompact (closure (L.liftRange ρ hρ : Set (L.stage (Fin.last _)))))
    (hOP : IsCompact (closure ((L.pullback hW hhW).liftRange ρ' hρ' :
      Set ((L.pullback hW hhW).stage (Fin.last _))))) :
    ((((hfStep22Functor d.hf).fam (step22TripleOf T L hL hsnc) hcls).seqOn (L.liftRange ρ hρ)
        hO₁).pullback
      (AnalyticMap.restrictMap (L.pullbackLiftLast hW hhW) ((L.pullback hW hhW).liftRange ρ' hρ')
        (L.liftRange ρ hρ)
        (AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L hW hhW ρ hρ ρ'
            hρ' hV hsq))
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L hW hhW) _ _
            _)).eraseEmpty =
    ((hfStep22Functor d.hf).fam (step22TripleOf (T.pullback hW hhW) (L.pullback hW hhW) hL' hsnc')
      hcls').seqOn ((L.pullback hW hhW).liftRange ρ' hρ') hOP := by
  have hB := hfStep22Fam_seqOn_pullback d T hW hhW L hL hsnc hcls hL' hsnc' hcls'
    ((L.pullback hW hhW).liftRange ρ' hρ') hOP
  have hle : AnalyticMap.imageOpens (L.pullbackLiftLast hW hhW)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L hW hhW)
      ((L.pullback hW hhW).liftRange ρ' hρ') ≤ L.liftRange ρ hρ := fun _ hx =>
    AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L hW hhW ρ hρ ρ' hρ' hV
        hsq hx
  have hC := ((hfStep22Functor d.hf).fam (step22TripleOf T L hL hsnc) hcls).compat _ _
    (AnalyticMap.isCompact_closure_image (L.pullbackLiftLast hW hhW) hOP) hO₁ hle
  have hmaps : ((L.stage (Fin.last _)).restrictLE hle).comp
      (AnalyticMap.restrictMap (L.pullbackLiftLast hW hhW)
        ((L.pullback hW hhW).liftRange ρ' hρ') _ Set.Subset.rfl) =
      AnalyticMap.restrictMap (L.pullbackLiftLast hW hhW) ((L.pullback hW hhW).liftRange ρ' hρ')
        (L.liftRange ρ hρ)
        (AnalyticManifold.BlowUpSequence.image_liftRange_pullbackLiftLast_subset L hW hhW ρ hρ ρ'
            hρ' hV hsq) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  rw [hB, hC, AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
    AnalyticManifold.BlowUpSequence.pullback_congr _ hmaps]

end Pullback

/-- The value of the family functor of Step 2.2 depends only on the sequence: for equal sequences
the values at the triples of Step 2.2, read on corresponding opens along `stageOfEq`, correspond
(a substitution; over data `d`). -/
theorem hfStep22Fam_seqOn_congr {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    {H : Set M} {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ M} (e : L₁ = L₂)
    (hL₁ : L₁.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL₂ : L₂.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hsnc₁ : ((exceptionalOf L₁).append (transformHOf L₁ H)).IsSnc ψ₀)
    (hsnc₂ : ((exceptionalOf L₂).append (transformHOf L₂ H)).IsSnc ψ₀)
    (hcls₁ : stepHClass s (step22TripleOf T L₁ hL₁ hsnc₁))
    (hcls₂ : stepHClass s (step22TripleOf T L₂ hL₂ hsnc₂))
    (U₁ : Opens (L₁.stage (Fin.last _))) (U₂ : Opens (L₂.stage (Fin.last _)))
    (hU₁ : IsCompact (closure (U₁ : Set (L₁.stage (Fin.last _)))))
    (hU₂ : IsCompact (closure (U₂ : Set (L₂.stage (Fin.last _)))))
    (hU : ∀ p, p ∈ U₁ ↔ AnalyticManifold.BlowUpSequence.stageOfEq e p ∈ U₂)
        {Z : AnalyticManifold.{u} 𝕜 E}
    (f₁ : AnalyticMap Z ((L₁.stage (Fin.last _)).restrict U₁))
    (f₂ : AnalyticMap Z ((L₂.stage (Fin.last _)).restrict U₂))
    (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₁)
    (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₂)
    (hf : ∀ z, AnalyticManifold.BlowUpSequence.stageOfEq e (f₁ z).1 = (f₂ z).1) :
    (((hfStep22Functor d.hf).fam (step22TripleOf T L₁ hL₁ hsnc₁) hcls₁).seqOn U₁ hU₁).pullback f₁
        hf₁ =
      (((hfStep22Functor d.hf).fam (step22TripleOf T L₂ hL₂ hsnc₂) hcls₂).seqOn U₂ hU₂).pullback f₂
        hf₂ := by
  subst e
  have hUU : U₁ = U₂ := by
    ext p
    have := hU p
    rw [AnalyticManifold.BlowUpSequence.stageOfEq_rfl] at this
    exact this
  subst hUU
  have hff : f₁ = f₂ := ContMDiffMap.ext fun z => Subtype.ext (by
    have := hf z
    rw [AnalyticManifold.BlowUpSequence.stageOfEq_rfl] at this
    exact this)
  subst hff
  rfl

end BO

end Hironaka.Manifold
