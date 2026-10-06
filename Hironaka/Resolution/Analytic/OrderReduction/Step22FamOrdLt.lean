/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step22Fam
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.MaximalContactTheorem
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamPersist
import Hironaka.Resolution.Analytic.OrderReduction.Step22Persist
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# At the end of Step 2 on an open the transform has order `< s`

Step 2.2 of the proof of Theorem 103 ends by observing that the cosupport of the controlled
transform of `(I, m)` misses the transform of `H` while, `H` being a hypersurface of maximal
contact, it lies in that transform, so that it is empty ([Kol07, 104, Step 2.2]),
which is the conclusion (1) of [Kol07, Theorem 103]. This module proves it for the value of Step 2
on a relatively compact open (`Step22Fam.lean`).

* `BlowUpSequence.forall_ord_weakTransformSeq_last_pullback_lt`,
  `BlowUpSequence.forall_ord_weakTransformSeq_last_eraseEmpty_lt` — "the final weak transform has
  order `< m` everywhere" is carried along a pull-back and along the deletion of empty blow-ups,
  the order being read at the lift of the point.
* `BO.step22FamOn_ord_lt` — the value of Step 2.2 on its reading open has this property for the
  triple of Step 2.2 restricted to the open: for the tuned data, the cosupport of the controlled
  transform lies in the transform of `H_r` (maximal contact for the tuned ideal sheaf, by
  `maximalContact_persistsFam` restricted to the open and `iteratedDeriv_tuning`, carried along
  by [Kol07, Theorem 80 (1)]) and misses it (Lemma 102 (1) at the appended member `H_r`); then
  `ord_lt_of_tuned` carries the drop back through the tuning.
* `step2SeqFamOn_ord_lt` — for the value of Step 2 on `U`: the chain of Step 2.1 restricted to
  the next open is of order exactly `s`, so its final weak transform is the controlled one, which
  is the ideal sheaf of the triple of Step 2.2 pulled back along the lift of the restriction; the
  drop along the appended value of Step 2.2 carries through the concatenation, the restriction to
  `U` and the deletion of empty blow-ups.

This is the clause `ord_lt` of the family structure `BOanFam` for the local functor
(`LocalFunctorFam.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- Order `< m` everywhere of the final weak transform pulls back along a local analytic
isomorphism ([Kol07, 34.1]): the order of the pulled-back final weak transform at a point is the
order at its lift (`weakTransformSeq_pullback`, `ord_pullback_of_isLocalDiffeomorphAt`). -/
theorem forall_ord_weakTransformSeq_last_pullback_lt (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (J : IdealSheaf M) (m : ℕ)
    (hL : ∀ y, (L.toSuccession.weakTransformSeq J (Fin.last _)).ord y < (m : ℕ∞)) :
    ∀ z,
        ((L.pullback h hh).toSuccession.weakTransformSeq (J.pullback h h.contMDiff)
      (Fin.last _)).ord z < (m : ℕ∞) := by
  have hlast : (Fin.last (L.pullback h hh).length : Fin ((L.pullback h hh).length + 1)) =
      ⟨(Fin.last L.length).1, Nat.lt_of_lt_of_eq (Fin.last L.length).2
        (congrArg (· + 1) (length_pullback L h hh).symm)⟩ :=
    Fin.ext (length_pullback L h hh)
  rw [hlast, L.weakTransformSeq_pullback h hh J (Fin.last _)]
  intro z
  exact (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (L.isLocalDiffeomorph_pullbackLift h hh _ z)).trans_lt (hL _)

/-- Order `< m` everywhere of the final weak transform survives the deletion of empty blow-ups
([Kol07, 32]): the last stages are identified by `eraseEmptyLast`. -/
theorem forall_ord_weakTransformSeq_last_eraseEmpty_lt (L : BlowUpSequence ψ₀ M)
    (J : IdealSheaf M) (m : ℕ)
    (hL : ∀ y, (L.toSuccession.weakTransformSeq J (Fin.last _)).ord y < (m : ℕ∞)) :
    ∀ z, (L.eraseEmpty.toSuccession.weakTransformSeq J (Fin.last _)).ord z < (m : ℕ∞) := by
  intro z
  rw [weakTransformSeq_last_eraseEmpty L J]
  exact (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (Diffeomorph.isLocalDiffeomorph L.eraseEmptyLast.symm z)).trans_lt (hL _)

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

namespace BO

open _root_.Manifold

variable {s : ℕ} (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
  (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
  {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- At the end of the value of Step 2.2 on its reading open, the weak transform of the ideal sheaf
of the triple of Step 2.2 restricted to the open has order `< s` everywhere (the conclusion of
[Kol07, 104, Step 2.2], per open). For the tuned data, the cosupport of the controlled transform
lies in the transform of `H_r` (maximal contact for the tuned ideal sheaf by
`maximalContact_persistsFam` restricted to the open and `iteratedDeriv_tuning`, carried along the
sequence by [Kol07, Theorem 80 (1)]) and misses it (Lemma 102 (1) for the appended member, the
greatest member being `H_r`); then `ord_lt_of_tuned` carries the drop back through the tuning. -/
theorem step22FamOn_ord_lt
    (w : (step22FamOn bd T s hT U hU hH hle).toSuccession.stage (Fin.last _)) :
    ((step22FamOn bd T s hT U hU hH hle).toSuccession.weakTransformSeq
      ((step22TripleFam bd T s hT U hU hH hle).pullback
        (((step2FamChain bd T s hT U hU).L.stage (Fin.last _)).inclusion
          (step2ReadOpen bd T s hT U hU))
        (isLocalDiffeomorph_inclusion _ _)).I (Fin.last _)).ord w < (s : ℕ∞) := by
  set T₂₂ := step22TripleFam bd T s hT U hU hH hle with hT₂₂def
  have hT₂₂ : stepHClass s T₂₂ := stepHClass_step22TripleFam bd T s hT U hU hH hle
  set ι := ((step2FamChain bd T s hT U hU).L.stage (Fin.last _)).inclusion
    (step2ReadOpen bd T s hT U hU) with hιdef
  have hT₂ : AnalyticTriple.BOClass s (T₂₂.pullback ι (isLocalDiffeomorph_inclusion _ _)) :=
    boClass_pullback_inclusion_of_boClass T₂₂ _ hT₂₂.1
  -- the data's clauses at the tuned Step-2.2 triple, read on the open (the value is
  -- `step22FamOn` by definition)
  have hord : (step22FamOn bd T s hT U hU hH hle).toSuccession.IsOfOrder
      ((T₂₂.tuned s hT₂₂.1.1).pullback ι (isLocalDiffeomorph_inclusion _ _)).I
      ((T₂₂.tuned s hT₂₂.1.1).pullback ι (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf
      (tuningParam s) :=
    (bd (tuningParam s)).isOfOrder (T₂₂.tuned s hT₂₂.1.1) (AnalyticTriple.boClass_tuned hT₂₂.1)
      (greatestIdx (stepHClass_tuned hT₂₂)) _ (isCompact_closure_step2ReadOpen bd T s hT U hU)
  have hc : Disjoint
      {y | (tuningParam s : ℕ∞) ≤ ((step22FamOn bd T s hT U hU hH hle).toSuccession.weakTransformSeq
        ((T₂₂.tuned s hT₂₂.1.1).pullback ι (isLocalDiffeomorph_inclusion _ _)).I
        (Fin.last _)).ord y}
      ((step22FamOn bd T s hT U hU hH hle).toSuccession.strictTransformSeq
        (((T₂₂.tuned s hT₂₂.1.1).pullback ι (isLocalDiffeomorph_inclusion _ _)).F.hyp
          (greatestIdx (stepHClass_tuned hT₂₂) : (T₂₂.tuned s hT₂₂.1.1).F.ι)) (Fin.last _)) :=
    (bd (tuningParam s)).cosupp_disjoint (T₂₂.tuned s hT₂₂.1.1)
      (AnalyticTriple.boClass_tuned hT₂₂.1) (greatestIdx (stepHClass_tuned hT₂₂)) _
      (isCompact_closure_step2ReadOpen bd T s hT U hU)
  -- the tuned triple pulled back is the pulled-back triple tuned
  have eI : ((T₂₂.tuned s hT₂₂.1.1).pullback ι (isLocalDiffeomorph_inclusion _ _)).I =
      ((T₂₂.pullback ι (isLocalDiffeomorph_inclusion _ _)).tuned s hT₂.1).I :=
    congrArg AnalyticTriple.I (AnalyticTriple.tuned_pullback T₂₂ hT₂₂.1.1 ι _).symm
  rw [eI] at hord hc
  refine AnalyticTriple.ord_lt_of_tuned (T₂₂.pullback ι (isLocalDiffeomorph_inclusion _ _)) hT₂ _
    ((AnalyticTriple.orderReduction_tuned_iff _ hT₂ _).mp hord.isOfOrderGe) w ?_
  -- the order drop for the tuned data
  by_contra hcon
  rw [not_lt, ← hord.markedTransformSeq_eq_weakTransformSeq] at hcon
  -- the transform of `H`, restricted to the open, is of maximal contact for the tuned ideal
  have hH₂ := isClosedSubmanifold_transformHOf
    (T.pullback (M.inclusion (step2OpenW T s hT U hU)) (isLocalDiffeomorph_inclusion M _)) s
    (step2FamChain bd T s hT U hU).L (boClass_pullback_inclusion_of_boClass T _ hT)
    (step2FamChain bd T s hT U hU).hge
    (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
    (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle _)
  have hle₂ := maximalContact_persistsFam
    (T.pullback (M.inclusion (step2OpenW T s hT U hU)) (isLocalDiffeomorph_inclusion M _))
    (boClass_pullback_inclusion_of_boClass T _ hT) (step2FamChain bd T s hT U hU).L
    (step2FamChain bd T s hT U hU).hge
    (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
    (idealSheaf_preimage_le_iteratedDeriv_inclusion T s hH hle _)
  have hle₃ : (hH₂.preimage_of_isLocalDiffeomorph
      (isLocalDiffeomorph_inclusion _ (step2ReadOpen bd T s hT U hU))).idealSheaf ≤
      ((T₂₂.pullback ι (isLocalDiffeomorph_inclusion _ _)).tuned s hT₂.1).I.iteratedDeriv
        (tuningParam s - 1) := by
    rw [AnalyticTriple.tuned_I,
      IdealSheaf.iteratedDeriv_tuning _ _ _ hT₂.1 hT₂.2.1 (one_le_tuningParam s)]
    exact idealSheaf_preimage_le_iteratedDeriv_inclusion T₂₂ s hH₂ hle₂ _
  obtain ⟨hHi, hHle⟩ := hord.exists_isClosedSubmanifold_strictTransformSeq_idealSheaf_le
    (one_le_tuningParam s)
    (hH₂.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion _ _)) hle₃ (Fin.last _)
  have hderiv := hord.isOfOrderGe.markedTransformSeq_iteratedDeriv_le
    (Nat.sub_le (tuningParam s) 1) (Fin.last _)
  rw [Nat.sub_sub_self (one_le_tuningParam s)] at hderiv
  have hmem : w ∈ (((step22FamOn bd T s hT U hU hH hle).toSuccession.markedTransformSeq
      ((T₂₂.pullback ι (isLocalDiffeomorph_inclusion _ _)).tuned s hT₂.1).I (tuningParam s)
      (Fin.last _)).iteratedDeriv (tuningParam s - 1)).support := by
    rw [IdealSheaf.support_iteratedDeriv _ (one_le_tuningParam s)]
    exact hcon
  have hmemH : w ∈ hHi.idealSheaf.support := by
    rw [IdealSheaf.mem_support] at hmem ⊢
    intro htop
    exact hmem (top_le_iff.mp (htop ▸ (IdealSheaf.le_def.mp (hHle.trans hderiv) w)))
  rw [hHi.cosupport_idealSheaf] at hmemH
  rw [← hord.markedTransformSeq_eq_weakTransformSeq] at hc
  -- the greatest member of the tuned Step-2.2 triple is `H_r`
  have hset : ((T₂₂.tuned s hT₂₂.1.1).pullback ι (isLocalDiffeomorph_inclusion _ _)).F.hyp
      (greatestIdx (stepHClass_tuned hT₂₂) : (T₂₂.tuned s hT₂₂.1.1).F.ι) =
      ⇑ι ⁻¹' transformHOf (step2FamChain bd T s hT U hU).L
        (⇑(M.inclusion (step2OpenW T s hT U hU)) ⁻¹' H) := by
    rw [greatestIdx_eq (stepHClass_tuned hT₂₂) (fun k => le_toLex_inr k)]
    rfl
  rw [hset] at hc
  exact Set.disjoint_left.mp hc hcon hmemH

end BO

/-- At the end of the value of Step 2 on the open `U`, the weak transform of `𝓘|_U` has order `< s`
everywhere ([Kol07, Theorem 103 (1)] per open, by [Kol07, 104, Step 2.2]): the chain of Step 2.1
restricted to the next open is of order exactly `s`, so its final weak transform is the controlled
one (`isOfOrderOf`), which is the ideal sheaf of the triple of Step 2.2 pulled back along the lift
of the restriction (`markedTransformSeq_last_pullbackLiftLast`, `pullback_comp`); the drop along the
appended value of Step 2.2 (`step22FamOn_ord_lt`, pulled back along the corestricted lift) carries
through the concatenation (`forall_ord_lt_concat_of_forall`), the restriction to `U` and the
deletion of empty blow-ups. -/
theorem step2SeqFamOn_ord_lt {s : ℕ} (bd : ∀ s : ℕ, BDanFamData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))
    (x : (BO.step2SeqFamOn bd T s hT U hU hH hle).toSuccession.stage (Fin.last _)) :
    ((BO.step2SeqFamOn bd T s hT U hU hH hle).toSuccession.weakTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _)).ord x <
      (s : ℕ∞) := by
  -- the ideal of `𝓘|_U` is the ideal of `𝓘|_W` restricted twice
  have hI : (((T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
      (isLocalDiffeomorph_inclusion M _)).pullback (M.restrictLE (BO.step2OpenV_le T s hT U hU))
      (isLocalDiffeomorph_restrictLE _)).pullback (M.restrictLE (BO.le_step2OpenV T s hT U hU))
      (isLocalDiffeomorph_restrictLE _)).I =
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I := by
    rw [AnalyticTriple.pullback_inclusion_restrictLE T (BO.step2OpenV_le T s hT U hU),
      AnalyticTriple.pullback_inclusion_restrictLE T (BO.le_step2OpenV T s hT U hU)]
  unfold BO.step2SeqFamOn BO.hfStep2SeqFamOn
  rw [← hI]
  refine AnalyticManifold.BlowUpSequence.forall_ord_weakTransformSeq_last_eraseEmpty_lt _ _ s
    (AnalyticManifold.BlowUpSequence.forall_ord_weakTransformSeq_last_pullback_lt _ _ _ _ s ?_) x
  -- Step 2.1's chain restricted to the next open: of order exactly `s` for the restricted triple
  have hTV : AnalyticTriple.BOClass s
      ((T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).pullback
        (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)) :=
    AnalyticTriple.boClass_of_isPullbackOf (boClass_pullback_inclusion_of_boClass T _ hT)
      (isLocalDiffeomorph_restrictLE _) (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hPge := AnalyticTriple.isOfOrderGe_pullback
    (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU)) (isLocalDiffeomorph_inclusion M _)) s
    (BO.step2FamChain bd T s hT U hU).L (BO.step2FamChain bd T s hT U hU).hge
    (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)
  have hPord := BO.isOfOrderOf _ s _ hTV hPge
  -- its last controlled transform is the Step-2.2 triple's ideal pulled back along the lift
  have hPm : ((BO.step2FamChain bd T s hT U hU).L.pullback
      (M.restrictLE (BO.step2OpenV_le T s hT U hU))
      (isLocalDiffeomorph_restrictLE _)).toSuccession.markedTransformSeq
      ((T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).pullback
        (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)).I s
      (Fin.last _) =
      Manifold.IdealSheaf.pullback _ ((BO.step2FamChain bd T s hT U hU).L.pullbackLiftLast
          (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)).contMDiff
        ((BO.step2FamChain bd T s hT U hU).L.toSuccession.markedTransformSeq
          (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
            (isLocalDiffeomorph_inclusion M _)).I s (Fin.last _)) :=
    AnalyticManifold.BlowUpSequence.markedTransformSeq_last_pullbackLiftLast
      (BO.step2FamChain bd T s hT U hU).L (M.restrictLE (BO.step2OpenV_le T s hT U hU))
      (isLocalDiffeomorph_restrictLE _)
      (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU)) (isLocalDiffeomorph_inclusion M _)).I
      (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).F.idealSheaf s (BO.step2FamChain bd T s hT U hU).hge
  have hPm' : Manifold.IdealSheaf.pullback _ ((BO.step2FamChain bd T s hT U hU).L.pullbackLiftLast
        (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)).contMDiff
      ((BO.step2FamChain bd T s hT U hU).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
          (isLocalDiffeomorph_inclusion M _)).I s (Fin.last _)) =
      Manifold.IdealSheaf.pullback _ ((BO.step2FamChain bd T s hT U hU).L.liftCorestrict
          (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _)).contMDiff
        ((BO.step22TripleFam bd T s hT U hU hH hle).pullback
          (((BO.step2FamChain bd T s hT U hU).L.stage (Fin.last _)).inclusion
            (BO.step2ReadOpen bd T s hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I :=
    (AnalyticManifold.IdealSheaf.pullback_comp
      ((BO.step2FamChain bd T s hT U hU).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
          (isLocalDiffeomorph_inclusion M _)).I s (Fin.last _))
      (((BO.step2FamChain bd T s hT U hU).L.stage (Fin.last _)).inclusion
        (BO.step2ReadOpen bd T s hT U hU))
      ((BO.step2FamChain bd T s hT U hU).L.liftCorestrict
        (M.restrictLE (BO.step2OpenV_le T s hT U hU)) (isLocalDiffeomorph_restrictLE _))).symm
  -- `step2FamChain` unfolded once, to its general form over the data of Step 2
  unfold BO.step2FamChain at hPord hPm hPm'
  unfold AnalyticManifold.BlowUpSequence.shrinkAppend
  refine AnalyticManifold.BlowUpSequence.forall_ord_lt_concat_of_forall _ _ _ s ?_
  intro z
  rw [← hPord.markedTransformSeq_eq_weakTransformSeq (Fin.last _), hPm, hPm']
  exact AnalyticManifold.BlowUpSequence.forall_ord_weakTransformSeq_last_pullback_lt _ _ _ _ s
    (BO.step22FamOn_ord_lt bd T hT U hU hH hle) z

end Hironaka.Manifold
