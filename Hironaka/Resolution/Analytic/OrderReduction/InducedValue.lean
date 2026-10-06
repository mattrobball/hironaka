/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyData
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.Step21Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The value of a compatible-family functor at the induced triple

Two transport identities for the value of the data `BDanFamData` of [Kol07, Lemma 102] in the
compatible-family form (`FamilyData.lean`), read at the triple induced by a sequence of centres at
its last stage (the triples `(X_j, I_j, E_j)` of [Kol07, 104, Step 2.1.j]).

* Deleting empty blow-ups ([Kol07, 32]; [Kol07, 34.1]): the triple induced by the sequence with
  its empty blow-ups deleted is the pull-back of the triple induced by the sequence along the
  isomorphism `eraseEmptyLast⁻¹` of the last stages (its controlled transform by
  `markedTransformSeq_last_eraseEmpty`), up to the empty members of the boundary (the order
  embedding `eraseEmptyIdx` of the kept indices), so the indifference of the data to empty members
  and its commutation with local analytic isomorphisms identify the two values
  (`fam_seqOn_induced_eraseEmpty`).
* Pulling back along a local analytic isomorphism (the functoriality argument in the proof of
  [Kol07, Lemma 102]): the triple induced by the pulled-back sequence is the pull-back of the
  induced triple along the lift to the last stage (`induced_pullback`), and the commutation of the
  data with local analytic isomorphisms applies (`fam_seqOn_induced_pullback`).

Not in the sources; bookkeeping for the assembly of Step 2.1 in the compatible-family form.
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ} (bd : BDanFamData ψ₀ s)

namespace BDanFamData

open _root_.Manifold

omit [FiniteDimensional 𝕜 E] in
/-- The value of the family depends only on the triple and the member. -/
theorem fam_seqOn_congr {X : AnalyticManifold.{u} 𝕜 E} {T₁ T₂ : AnalyticTriple ψ₀ X} (h : T₁ = T₂)
    (hT₁ : AnalyticTriple.BOClass s T₁) (hT₂ : AnalyticTriple.BOClass s T₂) (j₁ : T₁.F.ι)
    (j₂ : T₂.F.ι) (hj : HEq j₁ j₂) (U : Opens X) (hU : IsCompact (closure (U : Set X))) :
    (bd.fam T₁ hT₁ j₁).seqOn U hU = (bd.fam T₂ hT₂ j₂).seqOn U hU := by
  subst h
  cases hj
  rfl

variable {M N : AnalyticManifold.{u} 𝕜 E} (TW : AnalyticTriple ψ₀ M)
  (hTW : AnalyticTriple.BOClass s TW) (L : AnalyticManifold.BlowUpSequence ψ₀ M)
  (hL : L.toSuccession.IsOfOrderGe TW.I s TW.F.idealSheaf) (j : TW.F.ι)

/-- The value of the family at the triple induced by a pulled-back sequence is the value at the
triple induced by the sequence on the image, pulled back along the lift to the last stage (the
functoriality argument in the proof of [Kol07, Lemma 102]): `induced_pullback`,
`originalIdx_last_pullback_heq` and the commutation of the data with local analytic isomorphisms. -/
theorem fam_seqOn_induced_pullback (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hTW' : AnalyticTriple.BOClass s (TW.pullback h hh))
    (hL' : (L.pullback h hh).toSuccession.IsOfOrderGe (TW.pullback h hh).I s
      (TW.pullback h hh).F.idealSheaf)
    (U' : Opens ((L.pullback h hh).stage (Fin.last _)))
    (hU' : IsCompact (closure (U' : Set ((L.pullback h hh).stage (Fin.last _))))) :
    (bd.fam ((TW.pullback h hh).induced s (L.pullback h hh) hL')
        (AnalyticTriple.boClass_induced (TW.pullback h hh) s (L.pullback h hh) hL' hTW')
        ((L.pullback h hh).toSuccession.originalIdx (TW.pullback h hh).F (Fin.last _) j)).seqOn
      U' hU' =
    (((bd.fam (TW.induced s L hL) (AnalyticTriple.boClass_induced TW s L hL hTW)
          (L.toSuccession.originalIdx TW.F (Fin.last _) j)).seqOn
        (AnalyticMap.imageOpens (L.pullbackLiftLast h hh)
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh) U')
        (AnalyticMap.isCompact_closure_image _ hU')).pullback
      (AnalyticMap.restrictMap (L.pullbackLiftLast h hh) U' _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh) U' _
        Set.Subset.rfl)).eraseEmpty := by
  have hpull : AnalyticTriple.BOClass s ((TW.induced s L hL).pullback (L.pullbackLiftLast h hh)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh)) :=
    AnalyticTriple.boClass_of_isPullbackOf (AnalyticTriple.boClass_induced TW s L hL hTW)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh)
      (AnalyticTriple.isPullbackOf_pullback _ _ _)
  exact (bd.fam_seqOn_congr (AnalyticTriple.induced_pullback TW s L hL h hh hL').symm _ hpull _ _
    (AnalyticManifold.BlowUpSequence.originalIdx_last_pullback_heq L h hh TW.F j) U' hU').trans
    (bd.commutesWithLocalIsos (TW.induced s L hL) (L.pullbackLiftLast h hh)
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh)
      (AnalyticTriple.boClass_induced TW s L hL hTW) hpull
      (L.toSuccession.originalIdx TW.F (Fin.last _) j) U' hU')

/-- The value of the family at the triple induced by a sequence is the value at the triple induced
by the sequence with its empty blow-ups deleted, transported along the isomorphism `eraseEmptyLast`
of the last stages ([Kol07, 32]; [Kol07, 34.1]): the former triple is the pull-back of the latter
along `eraseEmptyLast⁻¹` up to empty boundary members (`markedTransformSeq_last_eraseEmpty`,
`eraseEmptyIdx`), so the indifference of the data to empty members and its commutation with local
analytic isomorphisms apply. -/
theorem fam_seqOn_induced_eraseEmpty (V : Opens (L.stage (Fin.last _)))
    (hV : IsCompact (closure (V : Set (L.stage (Fin.last _))))) :
    (bd.fam (TW.induced s L hL) (AnalyticTriple.boClass_induced TW s L hL hTW)
        (L.toSuccession.originalIdx TW.F (Fin.last _) j)).seqOn V hV =
    (((bd.fam (TW.induced s L.eraseEmpty (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L
        TW.I s TW.isSnc hL))
          (AnalyticTriple.boClass_induced TW s L.eraseEmpty
            (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L TW.I s TW.isSnc hL) hTW)
          (L.eraseEmpty.toSuccession.originalIdx TW.F (Fin.last _) j)).seqOn
        (AnalyticMap.imageOpens (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
          L.eraseEmptyLast.isLocalDiffeomorph V)
        (AnalyticMap.isCompact_closure_image _ hV)).pullback
      (AnalyticMap.restrictMap (Diffeomorph.toAnalyticMap L.eraseEmptyLast) V _ Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap L.eraseEmptyLast.isLocalDiffeomorph V _
        Set.Subset.rfl)).eraseEmpty := by
  have hLe := AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L TW.I s TW.isSnc hL
  have hF : ∀ k, IsClosed (TW.F.hyp k) := fun k => (TW.isSnc.1 k).isClosed
  have hTe : AnalyticTriple.BOClass s (TW.induced s L.eraseEmpty hLe) :=
    AnalyticTriple.boClass_induced TW s L.eraseEmpty hLe hTW
  have hpull : AnalyticTriple.BOClass s ((TW.induced s L.eraseEmpty hLe).pullback
      (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph) :=
    AnalyticTriple.boClass_of_isPullbackOf hTe L.eraseEmptyLast.isLocalDiffeomorph
      (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hsnc' : ((TW.induced s L.eraseEmpty hLe).F.comap
      ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast)).IsSnc ψ₀ :=
    HypersurfaceFamily.isSnc_comap (TW.induced s L.eraseEmpty hLe).isSnc _
      L.eraseEmptyLast.isLocalDiffeomorph
  -- the induced triple of `L` is the pull-back of the induced triple of the cleaned list along
  -- `eraseEmptyLast`, up to the empty boundary members
  have htriple : (⟨(TW.induced s L hL).I, (TW.induced s L hL).isNonzeroEverywhere,
      (TW.induced s L.eraseEmpty hLe).F.comap ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast),
      hsnc'⟩ : AnalyticTriple ψ₀ (L.stage (Fin.last _))) =
      (TW.induced s L.eraseEmpty hLe).pullback (Diffeomorph.toAnalyticMap L.eraseEmptyLast)
        L.eraseEmptyLast.isLocalDiffeomorph := by
    refine AnalyticTriple.ext' ?_ rfl
    change L.toSuccession.markedTransformSeq TW.I s (Fin.last _) =
      (L.eraseEmpty.toSuccession.markedTransformSeq TW.I s (Fin.last _)).pullback _
          (Diffeomorph.toAnalyticMap L.eraseEmptyLast).contMDiff
    rw [AnalyticManifold.BlowUpSequence.markedTransformSeq_last_eraseEmpty L TW.I TW.F.idealSheaf s
        hL]
    exact (comap_symm_comap L.eraseEmptyLast.symm
      (L.toSuccession.markedTransformSeq TW.I s (Fin.last _))).symm
  have he : ∀ i, (TW.induced s L hL).F.hyp (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F hF
      i) =
      ((TW.induced s L.eraseEmpty hLe).F.comap
        ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast)).hyp i := by
    intro i
    change (L.toSuccession.totalTransformSeqFrom TW.F (Fin.last _)).hyp
        (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F hF i) =
      ⇑L.eraseEmptyLast ⁻¹'
        (L.eraseEmpty.toSuccession.totalTransformSeqFrom TW.F (Fin.last _)).hyp i
    rw [← AnalyticManifold.BlowUpSequence.hyp_eraseEmptyIdx L TW.F hF i]
    exact (L.eraseEmptyLast.toEquiv.preimage_symm_preimage _).symm
  have he' : ∀ b, b ∉ Set.range (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F hF) →
      (TW.induced s L hL).F.hyp b = ∅ := fun b hb =>
    AnalyticManifold.BlowUpSequence.hyp_eq_empty_of_notMem_range_eraseEmptyIdx L TW.F hF b hb
  have hT' : AnalyticTriple.BOClass s (⟨(TW.induced s L hL).I,
      (TW.induced s L hL).isNonzeroEverywhere, (TW.induced s L.eraseEmpty hLe).F.comap
        ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast), hsnc'⟩ : AnalyticTriple ψ₀ _) := by
    rw [htriple]
    exact hpull
  have hind := bd.indifferentToEmptyMembers (TW.induced s L hL) _ hsnc'
    (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L TW.F hF) he he'
        (AnalyticTriple.boClass_induced TW s L hL hTW) hT'
    (L.eraseEmpty.toSuccession.originalIdx TW.F (Fin.last _) j) V hV
  have hcomm := bd.commutesWithLocalIsos (TW.induced s L.eraseEmpty hLe)
    (Diffeomorph.toAnalyticMap L.eraseEmptyLast) L.eraseEmptyLast.isLocalDiffeomorph hTe hpull
    (L.eraseEmpty.toSuccession.originalIdx TW.F (Fin.last _) j) V hV
  rw [← AnalyticManifold.BlowUpSequence.eraseEmptyIdx_originalIdx L TW.F hF j]
  exact hind.trans ((bd.fam_seqOn_congr htriple hT' hpull _ _ HEq.rfl V hV).trans hcomm)

end BDanFamData

end Hironaka.Manifold
