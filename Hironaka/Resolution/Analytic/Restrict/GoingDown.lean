/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Restrict
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.Restrict.LemmaSixtyTwo
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Lemma 62 along a succession, and the going-down property of maximal contact

Kollár's Lemma 62 iterated along the restriction of a succession `Π` to a closed submanifold `S`
whose strict transforms contain the centres ([Kol07, Definition 30.2] and [Kol07, Lemma 62]): the
marked transforms of `(J|_S, m)` along `Π|_S` are the restrictions of the marked transforms of
`(J, m)` along `Π` (`markedTransformSeq_pullback_restrictIncl`, induction on the stage with
`birationalTransform_pullback_restrictMap` at each step). Hence the going-down property of maximal
contact [Kol07, 51.1]: the order clause (4′) of [Kol07, Definition 66] for `Π|_S` and `(J|_S, m)` —
the order can only go up under restriction (the opening remark of [Kol07, §9]), and the marked
transforms of `Π|_S` are restrictions (`le_ordAlong_restrictSubmanifold`).

Two bookkeeping facts make the induction typecheck on `FiniteSuccession`: the ideal sheaf of a
closed submanifold does not depend on the chart or the codimension of the submanifold predicate
(`IsClosedSubmanifold.idealSheaf_congr`; `idealSheaf_eq_of_set` below is its same-set corollary),
so the marked transform depends only on the centre as a set and on the blow-down
(`MarkedIdealSheaf.birationalTransform_congr`); and the centre of the restriction at step `i` is
the pull-back of `C_i` (`center_restrictSubmanifold`).
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology

universe u v

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n n' : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] {Y : Set M} {c c' : ℕ}

/-- The ideal sheaf of a closed submanifold depends neither on the chart `ψ` nor on the
codimension of the submanifold predicate: the same-set case of
`IsClosedSubmanifold.idealSheaf_congr`. -/
theorem IsClosedSubmanifold.idealSheaf_eq_of_set (hY : IsClosedSubmanifold ψ Y c)
    (hY' : IsClosedSubmanifold ψ' Y c') : hY.idealSheaf = hY'.idealSheaf :=
  hY.idealSheaf_congr hY' rfl

variable [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M}

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {N : Type v} [TopologicalSpace N]
  [ChartedSpace E' N]

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] in
/-- The order along a centre under pull-back: if `m ≤ ord_D K` at `φ b`, then
`m ≤ ord_{φ⁻¹D} (φ⁻¹K)` at `b` — pulling back is a ring map on stalks, so `K_{φ b} ⊆ D_{φ b}^m`
gives `(φ⁻¹K)_b ⊆ (φ⁻¹D)_b^m` (the order can only go up under restriction, the opening remark of
[Kol07, §9]). -/
theorem _root_.Hironaka.Manifold.le_ordAlongIdeal_pullback {D K : IdealSheaf
    (structureSheaf 𝕜 E M)} (φ : N → M)
    (hφ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ) {b : N} {m : ℕ}
    (hm : (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal D K (φ b)) :
    (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (D.pullback φ hφ) (K.pullback φ hφ) b := by
  rw [IdealSheaf.le_ordAlongIdeal_iff, IdealSheaf.stalkIdeal_pullback,
    IdealSheaf.stalkIdeal_pullback, ← Ideal.map_pow]
  exact Ideal.map_mono ((IdealSheaf.le_ordAlongIdeal_iff _ _ _ _).mp hm)

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) {H : Set M}
  {s : ℕ} (hH : IsClosedSubmanifold ψ H s) (hc : S.CentersIn H)

/-- Kollár's `Z_i ∩ S_i` as a closed submanifold of the stage `S_i` of the restriction, in the
induced chart and of codimension `c_i − s` (`restrictCenterSub'` typed on the stages of the
succession). -/
theorem isClosedSubmanifold_preimage_center (i : Fin S.length) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (S.restrictIncl hH hc i.castSucc ⁻¹' (S.center i).support) (S.codim i - s) := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact S.restrictCenterSub' hH hc 0 hi
  · exact S.restrictCenterSub' hH hc (_ + 1) hi

/-- The centre of the restriction at step `i`, at the recursion level: the pull-back of `C_i`
under the embedding `S_i ↪ M_i` (`idealSheaf_preimageVal_eq_pullback`). -/
theorem restrictCenterOf_eq_pullback (i : ℕ) (hi : i < S.length) :
    S.restrictCenterOf hH hc i hi =
      (S.center ⟨i, hi⟩).pullback ⇑(S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i
          (Nat.lt_succ_of_lt hi)).inclusionMap
        (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i
            (Nat.lt_succ_of_lt hi)).inclusionMap.contMDiff := by
  have h := idealSheaf_preimageVal_eq_pullback
      (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc i (Nat.lt_succ_of_lt hi))
    (S.restrictCenterSub i hi) (hc ⟨i, hi⟩)
  rw [(S.restrictCenterSub i hi).idealSheaf_eq_of_set (S.isClosedSubmanifold_center ⟨i, hi⟩),
    S.idealSheaf_center] at h
  exact h

/-- The centre of `Π|_S` at step `i` is the pull-back of the centre `C_i` of `Π` under the
embedding `S_i ↪ M_i` (Kollár's `Z_i ∩ S_i`, [Kol07, Definition 30.2]). -/
theorem center_restrictSubmanifold (i : Fin S.length) :
    (S.restrictSubmanifold hH hc).center i =
      (S.center i).pullback ⇑(S.restrictIncl hH hc i.castSucc)
        (S.restrictIncl hH hc i.castSucc).contMDiff := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact S.restrictCenterOf_eq_pullback hH hc 0 hi
  · exact S.restrictCenterOf_eq_pullback hH hc (_ + 1) hi

/-- The inductive step: Kollár's Lemma 62 at stage `i` of the succession, read on the stages of
the succession — the marked transform under `π_i|_{S_{i+1}}` of the restriction of `(K, m)` is the
restriction of the marked transform under `π_i`, for a mark `m` legitimate along `Z_i`
([Kol07, Lemma 62]). -/
theorem birationalTransform_restrict_step (i : Fin S.length) (K : IdealSheaf (S.stage i.castSucc))
    {m : ℕ}
    (hm : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i) K a) :
    (MarkedIdealSheaf.birationalTransform
        ((S.restrictSubmanifold hH hc).isClosedSubmanifold_center i)
        ((S.restrictSubmanifold hH hc).isBlowUp_map i)
        ⟨K.pullback ⇑(S.restrictIncl hH hc i.castSucc) (S.restrictIncl hH hc i.castSucc).contMDiff,
          m⟩).I =
      (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
        ⟨K, m⟩).I.pullback ⇑(S.restrictIncl hH hc i.succ)
          (S.restrictIncl hH hc i.succ).contMDiff := by
  have hm' : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      ((S.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf K a := by
    rwa [((S.isClosedSubmanifold_center i).congr_chart ψ).idealSheaf_eq_of_set
      (S.isClosedSubmanifold_center i), S.idealSheaf_center]
  rw [MarkedIdealSheaf.birationalTransform_congr
      ((S.restrictSubmanifold hH hc).isClosedSubmanifold_center i)
      (S.isClosedSubmanifold_preimage_center hH hc i) (S.support_center_restrictSubmanifold hH hc i)
      ((S.restrictSubmanifold hH hc).isBlowUp_map i) (S.isBlowUp_map_restrictSubmanifold hH hc i),
    MarkedIdealSheaf.birationalTransform_congr (S.isClosedSubmanifold_center i)
      ((S.isClosedSubmanifold_center i).congr_chart ψ) rfl (S.isBlowUp_map i)
      ((S.isBlowUp_map i).congr_chart ψ)]
  obtain ⟨i, hi⟩ := i
  cases i
  · exact birationalTransform_pullback_restrictMap
      (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc 0 _)
      (S.restrictCenterSub 0 hi) ((S.isBlowUp_map ⟨0, hi⟩).congr_chart ψ) (hc ⟨0, hi⟩) K hm'
  · exact birationalTransform_pullback_restrictMap
      (S.isClosedSubmanifold_strictTransformSeqAux _ hH hc (_ + 1) _)
      (S.restrictCenterSub (_ + 1) hi) ((S.isBlowUp_map ⟨_ + 1, hi⟩).congr_chart ψ) (hc ⟨_ + 1, hi⟩)
      K
      hm'

variable {J E₀ : IdealSheaf M} {m : ℕ}

/-- Kollár's Lemma 62 iterated along the restriction of a blow-up sequence ([Kol07, Lemma 62] and
[Kol07, Definition 30.2]): for `Π` of order `≥ m` for `(J, m)` with centres in the strict transforms
`S_i` of `S`, the marked transform of `(J|_S, m)` along `Π|_S` is, at every stage, the restriction
under `S_i ↪ M_i` of the marked transform of `(J, m)` along `Π`. Induction on the stage; the order
clause (4′) of `Π` makes the mark legitimate at each step. -/
theorem markedTransformSeq_pullback_restrictIncl (hge : S.IsOfOrderGe J m E₀)
    (i : Fin (S.length + 1)) :
    (S.restrictSubmanifold hH hc).markedTransformSeq
        (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m i =
      (S.markedTransformSeq J m i).pullback ⇑(S.restrictIncl hH hc i)
        (S.restrictIncl hH hc i).contMDiff := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    -- `markedTransformSeq_succ` is definitional on both successions
    have step := S.birationalTransform_restrict_step hH hc i (S.markedTransformSeq J m i.castSucc)
      fun a ha => hge.le_ordAlong i ha
    have e := congrArg (fun X : IdealSheaf ((S.restrictSubmanifold hH hc).stage i.castSucc) =>
      (MarkedIdealSheaf.birationalTransform
        ((S.restrictSubmanifold hH hc).isClosedSubmanifold_center i)
        ((S.restrictSubmanifold hH hc).isBlowUp_map i) ⟨X, m⟩).I) ih
    exact e.trans step

/-- The going-down property of maximal contact [Kol07, 51.1] — the order clause (4′) of
[Kol07, Definition 66] for `Π|_S`: the marked transforms of `(J|_S, m)` along `Π|_S` have order
`≥ m` along the centres `Z_i ∩ S_i` at every point — they are the restrictions of the marked
transforms of `Π` (`markedTransformSeq_pullback_restrictIncl`), the centres of `Π|_S` are the
restrictions of the centres of `Π`, and the order can only go up under restriction. -/
theorem le_ordAlong_restrictSubmanifold (hge : S.IsOfOrderGe J m E₀) (i : Fin S.length) :
    ∀ a ∈ ((S.restrictSubmanifold hH hc).center i).support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((S.restrictSubmanifold hH hc).center i)
        ((S.restrictSubmanifold hH hc).markedTransformSeq
          (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m i.castSucc) a := by
  intro a ha
  have ha' : S.restrictIncl hH hc i.castSucc a ∈ (S.center i).support := by
    rwa [S.support_center_restrictSubmanifold hH hc] at ha
  rw [S.markedTransformSeq_pullback_restrictIncl hH hc hge, S.center_restrictSubmanifold hH hc]
  exact le_ordAlongIdeal_pullback _ _ (hge.le_ordAlong i ha')

/-- The assembly of [Kol07, Definition 66] for `Π|_S` from its two clauses: given the
normal-crossings clause (3′) for the boundary of `Π|_S`, the restricted succession is of order
`≥ m` for `(J|_S, m)` with the empty boundary — the order clause (4′) is
`le_ordAlong_restrictSubmanifold`. -/
theorem isOfOrderGe_restrictSubmanifold_of_hasOnlyNormalCrossingsWith
    (hge : S.IsOfOrderGe J m (⊤))
    (hnc : ∀ i : Fin S.length,
      ((S.restrictSubmanifold hH hc).boundarySeq (⊤)
        i.castSucc).HasOnlyNormalCrossingsWith ((S.restrictSubmanifold hH hc).center i)) :
    (S.restrictSubmanifold hH hc).IsOfOrderGe
      (J.pullback ⇑hH.inclusionMap hH.inclusionMap.contMDiff) m
      (⊤) :=
  fun i => ⟨hnc i, S.le_ordAlong_restrictSubmanifold hH hc hge i⟩

end AnalyticManifold.FiniteSuccession

end
