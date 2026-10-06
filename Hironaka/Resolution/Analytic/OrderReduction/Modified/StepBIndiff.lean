/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBCore
public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The modified first step: the modified core is indifferent to empty boundary members

The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the modified
first step of [Wlo09, Theorem 7.4.1]: deleting empty members of the boundary along an order
embedding `e : F'.ι ↪o E.ι` of the index types does not change the modified core at a kept member.
This is the counterpart of `BDan.coreFamOn_indifferentToEmptyMembers` **without** the first blow-up.

The stopped locus and `H⁺` of the member `e i` of `E` are those of the member `i` of `F'`
(`hplus_withBoundary`: the same set `E^{e i} = F'^i` and the same ideal), so the two modified cores
are read on the same closed hypersurface (`coreModOn_eq_of_eq`); the two restricted triples have the
same ideal (the pull-back of `𝓘` along the same inclusion) and boundaries, the traces of
`E − E^{e i}` and of `F' − F'^i`, which correspond along `e` with the deleted members empty, so the
indifference of the functor `R` one dimension down (a hypothesis here) identifies the two values on
the trace, and the push-forward and the deletion of empty blow-ups are the same.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
  (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (i : F'.ι)

include he in
/-- `H⁺` does not see the deleted members: the member `i` of `F'` is the member `e i` of `E`, and
the ideal is the same. -/
theorem hplus_withBoundary : hplus (BDan.withBoundary T F' hsnc') i = hplus T (e i) := by
  change F'.hyp i \ BD.Zminus1 T.I 1 (F'.hyp i) =
    T.F.hyp (e i) \ BD.Zminus1 T.I 1 (T.F.hyp (e i))
  rw [he i]

include he in
/-- The trace of `E − E^{e i}` at the member `e k` is the trace of `F' − F'^i` at `k` (both empty at
`k = i`; `E^{e k} = F'^k` otherwise). -/
theorem restrictedTripleModOf_F_hyp_apply {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (hSeq : S = hplus T (e i)) (hSeq' : S = hplus (BDan.withBoundary T F' hsnc') i) (k : F'.ι) :
    (restrictedTripleModOf T (e i) hS hSeq).F.hyp (e k) =
      (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i hS hSeq').F.hyp k := by
  change hS.preimageVal ((T.F.emptyMember (e i)).hyp (e k)) =
    hS.preimageVal ((F'.emptyMember i).hyp k)
  congr 1
  by_cases hk : k = i
  · subst hk
    rw [HypersurfaceFamily.emptyMember_hyp_self, HypersurfaceFamily.emptyMember_hyp_self]
  · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F fun h => hk (e.injective h),
      HypersurfaceFamily.emptyMember_hyp_of_ne F' hk, he k]

/-- The trace of `E − E^{e i}` at a member outside the range of `e` is empty. -/
theorem restrictedTripleModOf_F_hyp_eq_empty (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    {S : Set M} (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (hSeq : S = hplus T (e i)) (b : T.F.ι) (hb : b ∉ Set.range e) :
    (restrictedTripleModOf T (e i) hS hSeq).F.hyp b = ∅ := by
  change hS.preimageVal ((T.F.emptyMember (e i)).hyp b) = ∅
  have hb0 : (T.F.emptyMember (e i)).hyp b = ∅ := by
    by_cases hbi : b = e i
    · subst hbi
      exact HypersurfaceFamily.emptyMember_hyp_self T.F (e i)
    · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F hbi]
      exact he' b hb
  rw [hb0]
  exact Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp

include he in
/-- **The modified core is indifferent to empty boundary members** (the counterpart, for boundary
members, of [Kol07, 32]; the analogue of `BDan.coreFamOn_indifferentToEmptyMembers` without the
first blow-up): the modified core at the
member `e i` of `E` is the modified core at the member `i` of `F'`; the same `H⁺`, the same
restricted ideal, the boundaries corresponding along `e`, and the functor `R` one dimension down
indifferent (`hRi`). -/
theorem coreModOn_indifferentToEmptyMembers (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hRi : R.IndifferentToEmptyMembers) (hT : AnalyticTriple.BMOClass 1 T)
    (hT₂ : AnalyticTriple.BMOClass 1 (BDan.withBoundary T F' hsnc')) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    coreModOn R T (e i) hT U hU = coreModOn R (BDan.withBoundary T F' hsnc') i hT₂ U hU := by
  rw [coreModOn_eq_of_eq R T (e i) hT (isClosedSubmanifold_hplus T (e i)) rfl U hU,
    coreModOn_eq_of_eq R (BDan.withBoundary T F' hsnc') i hT₂ (isClosedSubmanifold_hplus T (e i))
      (hplus_withBoundary T F' hsnc' e he i).symm U hU]
  refine congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (congrArg (AnalyticManifold.BlowUpSequence.pushforwardRestrict (isClosedSubmanifold_hplus T
        (e i)) U) ?_)
  -- the two restricted triples: the same ideal, the boundaries corresponding along `e`
  have heq : (⟨(restrictedTripleModOf T (e i) (isClosedSubmanifold_hplus T (e i)) rfl).I,
      (restrictedTripleModOf T (e i) (isClosedSubmanifold_hplus T (e i)) rfl).isNonzeroEverywhere,
      (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
        (hplus_withBoundary T F' hsnc' e he i).symm).F,
      (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
        (hplus_withBoundary T F' hsnc' e he i).symm).isSnc⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) _) =
      restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
        (hplus_withBoundary T F' hsnc' e he i).symm :=
    AnalyticTriple.ext' rfl rfl
  have hD'' : AnalyticTriple.BMOClass 1
      (⟨(restrictedTripleModOf T (e i) (isClosedSubmanifold_hplus T (e i)) rfl).I,
        (restrictedTripleModOf T (e i) (isClosedSubmanifold_hplus T (e i)) rfl).isNonzeroEverywhere,
        (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
          (hplus_withBoundary T F' hsnc' e he i).symm).F,
        (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
          (hplus_withBoundary T F' hsnc' e he i).symm).isSnc⟩ :
          AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) _) := by
    rw [heq]
    exact bmoClass_restrictedTripleModOf (BDan.withBoundary T F' hsnc') i hT₂ _ _
  refine (hRi (restrictedTripleModOf T (e i) (isClosedSubmanifold_hplus T (e i)) rfl)
    (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
      (hplus_withBoundary T F' hsnc' e he i).symm).F
    (restrictedTripleModOf (BDan.withBoundary T F' hsnc') i (isClosedSubmanifold_hplus T (e i))
      (hplus_withBoundary T F' hsnc' e he i).symm).isSnc e
    (restrictedTripleModOf_F_hyp_apply T F' hsnc' e he i _ rfl _)
    (restrictedTripleModOf_F_hyp_eq_empty T F' e i he' _ rfl)
    (bmoClass_restrictedTripleModOf T (e i) hT _ rfl) hD'' _ _).trans ?_
  exact R.fam_seqOn_congr_triple heq hD'' _ _ _

include he in
/-- `coreModOn_indifferentToEmptyMembers` for the `CompatibleFamily` `coreModFam`. -/
theorem coreModFam_indifferentToEmptyMembers (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hRi : R.IndifferentToEmptyMembers) (hT : AnalyticTriple.BMOClass 1 T)
    (hT₂ : AnalyticTriple.BMOClass 1 (BDan.withBoundary T F' hsnc')) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (coreModFam R T (e i) hT).seqOn U hU =
      (coreModFam R (BDan.withBoundary T F' hsnc') i hT₂).seqOn U hU :=
  coreModOn_indifferentToEmptyMembers R T F' hsnc' e he i he' hRi hT hT₂ U hU

end Hironaka.Manifold.BMOmod

end
