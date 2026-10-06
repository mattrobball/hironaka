/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.ClosedEmbedding
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1EraseEmpty
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Tools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Subfamily
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep21Passage
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 along Step 2.2

Step 2.2 of the proof of [Kol07, Theorem 103] (item 104, Step 2.2) applies [Kol07, Lemma 102] at
the position of the strict transform `H_r` of the hypersurface of maximal contact to the triple
`(X_r, I_r, F_r + H_r)`, whose boundary is the EXCEPTIONAL sub-family `F_r` of the total transform
`E_r` of the original boundary, through the re-tuning at the mark `1` (the identity). The statement
CP1 of the embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`)
along it for `(I_r, E_r)` at a generic point `η` of `V(I_r)` off `E_r`: the value is the functor of
Lemma 102 at the mark `1` on the Step 2.2 triple (`step22Functor_seq_of_maxOrd_eq`,
`functor_seq_congr_mark`, `dataFunctor_seq_of_maxOrd_eq`, `functor_seq`), the raw output with its
empty blow-ups deleted; the core of Step 2.2 (`cp1For_rawSeq_of_cp1`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core`) gives CP1 along the raw output for the
tuned ideal (which is `I_r`: `W_tuningParam_one`, [Kol07, Remark 67]) and the family `(F_r + H_r) −
H_r`; `cp1For_eraseEmpty` deletes the empty blow-ups; and the family bridge `cp1For_of_embeds`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Subfamily`) passes to `E_r`, since the members of
`E_r` missing from `F_r` are the birational transforms of the original members, which miss `V(I_r)`
at the end of Step 2.1 (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep21Passage`) and hence miss
`c̃` at every later stage (the lifted generic point). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step2`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BO Hironaka.BD Hironaka.Local IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Step22

variable {N : ℕ} (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (N - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)
  (T : Triple k) (hn : T.HasDimLE N) (hmax : T.I.maxOrd ≤ 1) {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H) (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 H)

include hmax hH hle in
/-- CP1 along the re-tuned functor of Lemma 102 at the mark `1` on the Step 2.2 triple of an
arbitrary Step 2.1 run `S₁`, for `(I_r, E_r)` at a generic point `η` of `V(I_r)` off `E_r` — given
CP1 for the inductive input `B` at the mark `1` and the fact that the transforms of the original
members miss `V(I_r)`. -/
theorem cp1For_step22_aux (S₁ : BlowUpSequence T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E 1) (hne : S₁.NoEmptyCenters)
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hT₂ : Triple.BDClass N 1 (Fintype.card (S₁.exceptionalFamily T.E).ι)
      (step22TripleOfSeq T S₁ hS₁ hsnc))
    (hpass : ∀ (i : ℕ) (hi : i < Fintype.card T.E.ι),
      Disjoint (SetLike.coe (S₁.markedTransformSeq T.I 1 (Fin.last _)).support)
        (SetLike.coe (S₁.strictTransformSeq (T.E.nth ⟨i, hi⟩) (Fin.last _)).support))
    (hcp1 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 → ∀ η' : T'.X.left,
      η' ∈ T'.I.support.genericPoints → (∀ i, η' ∉ (T'.E.component i).support) →
      T'.I.stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' →
      CP1For ((B k).seq T' hT') T'.I T'.E η')
    {η : S₁.stage (Fin.last _)}
    (hη : η ∈ (S₁.markedTransformSeq T.I 1 (Fin.last _)).support.genericPoints)
    (hηE : ∀ i, η ∉ ((S₁.totalTransformSeq T.E (Fin.last _)).component i).support)
    (hIc : (S₁.markedTransformSeq T.I 1 (Fin.last _)).stalkIdeal η =
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η) :
    CP1For ((step22Functor (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) 1 _ le_rfl).seq
        (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂)
      (S₁.markedTransformSeq T.I 1 (Fin.last _)) (S₁.totalTransformSeq T.E (Fin.last _)) η := by
  classical
  -- standing facts on the Step 2.1 run
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hm1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞) :=
    maxOrd_eq_one_of_mem_support_markedTransformSeq (T.X.left ↘ Spec (.of k)) n' hS₁ hne hmax hη.1
  have hge : S₁.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n' hS₁
  have hmw : S₁.markedTransformSeq T.I 1 (Fin.last _) = S₁.weakTransformSeq T.I (Fin.last _) :=
    IsOrderGeSeq.markedTransformSeq_eq_weakTransformSeq (T.X.left ↘ Spec (.of k)) n' hm1 hge
      (Fin.last _)
  -- the Step 2.2 triple `T₂` (on `X_r`), its structure map and the mark
  set T₂ := step22TripleOfSeq T S₁ hS₁ hsnc with hT₂def
  obtain ⟨n₂, hn₂⟩ := T₂.smoothOfRelativeDimension
  have hsm₂ : SmoothOfRelativeDimension n₂ (T₂.X.left ↘ Spec (.of k)) := hn₂
  have hLN₂ : IsLocallyNoetherian T₂.X.left :=
    (T₂.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hT₂I : T₂.I = S₁.markedTransformSeq T.I 1 (Fin.last _) := hmw.symm
  have h1 : T₂.I.maxOrd = ((1 : ℕ) : ℕ∞) := by
    refine le_antisymm (maxOrd_induced_last_le T hmax hS₁ hne) ?_
    rw [hT₂I, Nat.cast_one]
    exact ((IdealSheafData.one_le_ord_iff _ η).mpr hη.1).trans (IdealSheafData.le_maxOrd _ η)
  -- Lemma 102's functor at the mark `1` on `T₂`, then the raw output with its empty blow-ups
  -- deleted on the tuned triple `T₃`
  have e2 : (((fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) (tuningParam 1)
        (Fintype.card (S₁.exceptionalFamily T.E).ι)).functor k).seq (T₂.tuned 1 le_rfl)
        (bdClass_tuned hT₂ h1 le_rfl) =
      ((bdData N 1 (Fintype.card (S₁.exceptionalFamily T.E).ι) Dom B (hDom 1) hB hsm
        hbc).functor k).seq T₂ hT₂ :=
    functor_seq_congr_mark (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) _ T₂
      (tuningParam 1) tuningParam_one _ (IdealSheafData.W_tuningParam_one _ _) _ _ hT₂
  rw [step22Functor_seq_of_maxOrd_eq _ 1 _ le_rfl T₂ hT₂ h1, e2]
  change CP1For ((dataFunctor N 1 _ le_rfl (B k) (hDom 1 k)).seq T₂ hT₂) _ _ _
  rw [dataFunctor_seq_of_maxOrd_eq N 1 _ le_rfl (B k) (hDom 1 k) T₂ hT₂ h1, functor_seq]
  set T₃ := T₂.tuned 1 le_rfl with hT₃
  have hdom₃ := domain_tuned (n := N) (m := 1) le_rfl hT₂ h1
  set j₃ := monoEquivOfFin T₃.E.ι rfl ⟨Fintype.card (S₁.exceptionalFamily T.E).ι, hdom₃.2.2.2⟩
    with hj₃
  have hsm₃ : SmoothOfRelativeDimension n₂ (T₃.X.left ↘ Spec (.of k)) := hn₂
  have hLN₃ : IsLocallyNoetherian T₃.X.left := hLN₂
  have hLN₁ : IsLocallyNoetherian (S₁.stage (Fin.last _)) := hLN₂
  have hI₃ : T₃.I = S₁.markedTransformSeq T.I 1 (Fin.last _) := by
    change IdealSheafData.W (T₂.X.left ↘ Spec (.of k)) T₂.I 1 (tuningParam 1) = _
    rw [IdealSheafData.W_tuningParam_one]
    exact hT₂I
  -- the member `H_r` at the appended position and the indices of `(F_r + H_r) − H_r`
  have hH₃ : T₃.E.component j₃ = S₁.strictTransformSeq H (Fin.last _) :=
    nth_append_last (S₁.exceptionalFamily T.E) (S₁.strictTransformSeq H (Fin.last _)) _
  have h7 : ∀ b : (T₃.E.erase j₃).ι, ∃ a : (S₁.exceptionalFamily T.E).ι,
      b.1 = toLex (Sum.inl a) :=
    exists_eq_inl_of_erase_append_last (S₁.exceptionalFamily T.E)
      (S₁.strictTransformSeq H (Fin.last _)) _
  -- the hypotheses at `η` for the tuned ideal and the family `(F_r + H_r) − H_r`
  have hη₃ : η ∈ T₃.I.support.genericPoints := by
    rw [hI₃]
    exact hη
  have hIc₃ : T₃.I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure
      {η})).stalkIdeal η := by
    rw [hI₃]
    exact hIc
  have hηE₃ : ∀ i, η ∉ ((T₃.E.erase j₃).component i).support := by
    intro i hi
    obtain ⟨a, ha⟩ := h7 i
    change η ∈ (T₃.E.component i.1).support at hi
    rw [ha] at hi
    exact hηE a.1 hi
  -- `H_r` is a smooth hypersurface of maximal contact for `I_r` at the end of Step 2.1
  have hle' : H ≤ IdealSheafData.MC (T.X.left ↘ Spec (.of k)) T.I 1 := hle
  have hHsm₃ : IsSmoothDivisor (T₃.E.component j₃) := by
    rw [hH₃]
    exact IsOrderSeq.isSmoothDivisor_strictTransformSeq (T.X.left ↘ Spec (.of k)) n' le_rfl hS₁ hH
      hle' (Fin.last _)
  have hHJ₃ : T₃.E.component j₃ ≤ T₃.I := by
    rw [hH₃, hI₃]
    exact IsOrderSeq.strictTransformSeq_le_markedTransformSeq_MC (T.X.left ↘ Spec (.of k)) n' le_rfl
      hS₁ hH hle' (Fin.last _)
  -- the raw output's order property for the family `(F_r + H_r) − H_r`, at the mark `1`
  have hS₃ : (rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
      (hDom 1 k)).IsOrderGeSeq (T₃.X.left ↘ Spec (.of k)) T₃.I 1 (T₃.E.erase j₃) := by
    have h := IsOrderSeq.isOrderGeSeq (T₃.X.left ↘ Spec (.of k)) n₂
      (isOrderSeq_rawSeq_erase T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
        (hDom 1 k))
    exact (congrArg (fun m => (rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1
      (B k) (hDom 1 k)).IsOrderGeSeq (T₃.X.left ↘ Spec (.of k)) T₃.I m (T₃.E.erase j₃))
      tuningParam_one).mp h
  -- the family bridge from `(F_r + H_r) − H_r` to the full `E_r`
  let e₀ : (T₃.E.erase j₃).ι → (S₁.totalTransformSeq T.E (Fin.last _)).ι :=
    fun b => (Classical.choose (h7 b)).1
  have he₀ : Function.Injective e₀ := by
    intro b b' hbb'
    have hb := Classical.choose_spec (h7 b)
    have hb' := Classical.choose_spec (h7 b')
    have h2 : Classical.choose (h7 b) = Classical.choose (h7 b') := Subtype.ext hbb'
    exact Subtype.ext (hb.trans (by rw [h2]; exact hb'.symm))
  have hcomp₀ : ∀ b, (S₁.totalTransformSeq T.E (Fin.last _)).component (e₀ b) =
      (T₃.E.erase j₃).component b := by
    intro b
    change _ = T₃.E.component b.1
    rw [Classical.choose_spec (h7 b)]
    rfl
  have hj₃inr : j₃ = toLex (Sum.inr PUnit.unit) := monoEquivOfFin_lex_inr_last _
  refine cp1For_of_embeds _ _ e₀ he₀ hcomp₀ ?_ ?_
  · -- the missing members are the originals' transforms; they miss `c̃` below the first
    -- containing stage
    intro i hmin a ha p hp
    -- `a` is not exceptional: it is the transform of an original member `t`
    have horig : ∃ t : T.E.ι, a = S₁.originalIdx T.E (Fin.last _) t := by
      by_contra hcon
      have hex : ∀ t, a ≠ S₁.originalIdx T.E (Fin.last _) t := fun t ht => hcon ⟨t, ht⟩
      have hne : toLex (Sum.inl (⟨a, hex⟩ : (S₁.exceptionalFamily T.E).ι)) ≠ j₃ := by
        rw [hj₃inr]
        intro h
        exact absurd (toLex_inj.mp h) Sum.inl_ne_inr
      set b₀ : (T₃.E.erase j₃).ι :=
        ⟨toLex (Sum.inl (⟨a, hex⟩ : (S₁.exceptionalFamily T.E).ι)), hne⟩ with hb₀
      refine ha (Set.mem_range.mpr ⟨b₀, ?_⟩)
      change (Classical.choose (h7 b₀)).1 = a
      have hsp := Classical.choose_spec (h7 b₀)
      change toLex (Sum.inl (⟨a, hex⟩ : (S₁.exceptionalFamily T.E).ι)) = toLex (Sum.inl _) at hsp
      exact (congrArg Subtype.val (Sum.inl.inj (toLex_inj.mp hsp))).symm
    obtain ⟨t, rfl⟩ := horig
    -- the point lies on `V(I_i)` (the generic lift), which misses the transform of `E^t`
    obtain ⟨ξ, hξ⟩ := exists_genericLift _ _ _ 1 hη hηE hIc i.castSucc hmin
    have hpI : p ∈ ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
        (hDom 1 k)).eraseEmpty.markedTransformSeq (S₁.markedTransformSeq T.I 1 (Fin.last _)) 1
        i.castSucc).support := by
      have hsp : ξ ⤳ p := hξ.isGenericPoint_strictTransformSeq.specializes hp
      exact hsp.mem_closed (Closeds.isClosed _) hξ.mem_genericPoints.1
    -- the transform of `E^t` misses `V(I_r)`, hence `V(I_i)`
    obtain ⟨idx, hidx, hnth⟩ : ∃ (idx : ℕ) (hidx : idx < Fintype.card T.E.ι),
        T.E.nth ⟨idx, hidx⟩ = T.E.component t :=
      ⟨((monoEquivOfFin T.E.ι rfl).symm t).val, ((monoEquivOfFin T.E.ι rfl).symm t).isLt, by
        change T.E.component (monoEquivOfFin T.E.ι rfl ⟨_, _⟩) = _
        rw [Fin.eta, OrderIso.apply_symm_apply]⟩
    have hD : Disjoint (SetLike.coe (S₁.markedTransformSeq T.I 1 (Fin.last _)).support)
        (SetLike.coe (S₁.strictTransformSeq (T.E.component t) (Fin.last _)).support) := by
      rw [← hnth]
      exact hpass idx hidx
    have hdisj := disjoint_support_markedTransformSeq_strictTransformSeq _ _ _ hD i.castSucc
    rw [component_originalIdx ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
      (hDom 1 k)).eraseEmpty) (S₁.totalTransformSeq T.E (Fin.last _)) i.castSucc
      (S₁.originalIdx T.E (Fin.last _) t), component_originalIdx S₁ T.E (Fin.last _) t]
    exact Set.disjoint_left.mp hdisj hpI
  · -- CP1 along the raw output for the tuned data, then the empty blow-ups deleted
    rw [← hI₃]
    refine cp1For_eraseEmpty (T₃.X.left ↘ Spec (.of k)) n₂ _ T₃.I (T₃.E.erase j₃) hη₃ hηE₃ hIc₃ hS₃
      ?_
    exact cp1For_rawSeq_of_cp1 (B k) T₃ (tuningParam 1) tuningParam_one j₃ hdom₃.2.1
      hdom₃.2.2.1 hdom₃.1 (hDom 1 k) hcp1 hHsm₃ hHJ₃ hη₃ hηE₃ hIc₃

/-- **CP1 along Step 2.2** ([Kol07, 104, Step 2.2]; the proof of [Kol07, Lemma 102]) with the data
`bdData`, given CP1 for the inductive input `B` at the mark `1` (`hcp1`): for a point `η` of the
input of Step 2.2 — a generic point of `V(I_r)` off the boundary `E_r` (the FULL total transform of
`E`) with `I_r` the reduced ideal of its closure there — CP1 holds along Step 2.2 for
`(I_r, E_r)`. -/
theorem cp1For_step22
    (hcp1 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 → ∀ η' : T'.X.left,
      η' ∈ T'.I.support.genericPoints → (∀ i, η' ∉ (T'.E.component i).support) →
      T'.I.stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure {η'})).stalkIdeal η' →
      CP1For ((B k).seq T' hT') T'.I T'.E η')
    {η : (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1.stage (Fin.last _)}
    (hη : η ∈ ((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1.markedTransformSeq T.I 1 (Fin.last _)).support.genericPoints)
    (hηE : ∀ i, η ∉ (((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1.totalTransformSeq T.E (Fin.last _)).component i).support)
    (hIc : ((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1.markedTransformSeq T.I 1 (Fin.last _)).stalkIdeal η =
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η) :
    CP1For (step22 T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH hle)
      ((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
        (Fintype.card T.E.ι)).1.markedTransformSeq T.I 1 (Fin.last _))
      ((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
        (Fintype.card T.E.ι)).1.totalTransformSeq T.E (Fin.last _)) η := by
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hm1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞) :=
    maxOrd_eq_one_of_mem_support_markedTransformSeq (T.X.left ↘ Spec (.of k)) n'
      (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
        (Fintype.card T.E.ι)).2.1
      (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
        (Fintype.card T.E.ι)).2.2 hmax hη.1
  have hm1' : T.I.maxOrd = 1 := by rwa [Nat.cast_one] at hm1
  exact cp1For_step22_aux Dom B hDom hB hsm hbc T hmax hH hle
    (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1
    (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).2.1
    (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).2.2
    (step22Triple T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH
      hle).isSnc
    (bdClass_step22Triple T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH
      hle)
    (fun i hi => disjoint_support_markedTransformSeq_step21_final T hn hmax _ hm1' hi)
    hcp1 hη hηE hIc

end Step22

end Hironaka.Resolution
