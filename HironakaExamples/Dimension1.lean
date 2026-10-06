/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Resolution.Algebraic.Kol07.Globalize
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import HironakaExamples.Sequence.CosuppForcing
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Order reduction on a curve: the general step blows up the cosupport once

Kollár's outline of the induction, [Kol07, 70], dismisses dimension one: on a curve the cosupport
of an ideal sheaf is a Cartier divisor, "our algorithm tells us to blow up `Z := cosupp(I, m)`",
and after that one blow-up the transform `I ⊗ O_X(Z)` has order `< m`. In this library dimension
one is not a base case of the recursion: the stage `tower S0 1` is produced from any base stage
`S0 : OrderReductionStage 0` by the general step, the construction of [Kol07, Theorem 103]. This
file checks that the general step does what Kollár says (`stage1_BO_eq_blowUp_cosupp`): on a
smooth curve `X` with `E = ∅` and `max-ord I = m ≥ 1`, the value of the unmarked functor
`(tower S0 1).bo m` is the single blow-up of the reduced cosupport, `cons X Z nil` with
`Z = vanishingIdeal Z.support` and `Z.support = {x | m ≤ ord_x I}`. It is a check of the
construction: the axioms of a smooth blow-up sequence functor of order `m` alone do not determine
the sequence (on a curve with two points `p ≠ q` of order `m`, "blow up `{p}`, then `{q}`" is also
a smooth blow-up sequence of order `m` without empty centres whose end has maximal order `< m`).

**The argument** has two halves.

1. *The value has at most one member*, read off the construction through the descent identity of
   the global case. `(tower S0 1).bo m = boOfBMO S0.bmo m`, whose functor is the glued functor
   `BO.functor 1 m bd` of [Kol07, Theorem 103, Step 3] for the data `bd m j = bdData 1 m j …` of
   [Kol07, Lemma 102], fed with the amalgam of `S0.bmo`. Over a local cover `g : T' → T`
   (`Triple.exists_isLocalCover`), the pull-back of the value is the maximal-contact case
   `maxContactCase` on `T'` (`functor_seq_pullback_localCover`), and pulling back preserves the
   length. At the mark, `maxContactCase` is Step 2 of [Kol07, 104] on the tuned triple: Step 2.1
   is empty since `E = ∅` (`step21Seq_zero`), and Step 2.2 is the re-tuned `BD_{1,·,0}` at the
   hypersurface of maximal contact, whose raw output (`rawSeq`) is `π_{-1}` followed by the
   pushed-forward value of the inductive marked functor on the restricted triple, of dimension
   `0`, where every marked functor is `nil` (`seq_eq_nil_of_hasDimLE_zero`; this is where the base
   enters, and it enters for every base, so neither the base stage nor the amalgam is unfolded).
   Each tuning layer (`maxContactCase`, `step22Functor`, `dataFunctor`) returns `nil` below its
   mark, so every layer is covered by a two-case lemma `… .length ≤ 1`.
2. *The centre is forced.* Clause (1) of the data, `max-ord I_r < m`, excludes the empty sequence
   (its weak transform is `I`, of maximal order `m`), so the value is `cons X Z nil`; `Z` is
   reduced by `center_eq_vanishingIdeal_support_of_isOrderSeq`; every generic point of `Z` has
   order `m` ([Kol07, Definition 66]) and `{x | m ≤ ord_x I}` is closed (`isClosed_setOf_le_ord`),
   so `Z.support ⊆ cosupp(I, m)`; conversely a point `x` of order `≥ m` off `Z` has a preimage
   `x'` on the blow-up, which is an isomorphism off the centre (`exists_π_eq_of_notMem_support`),
   where the weak transform keeps the order (`ord_weakTransform_of_notMem`), against clause (1).

At `n = 1` the hypothesis `I|_H ≠ 0` of [Kol07, Theorem 80 (1)] fails for `H = {p}`, so the
maximal-contact property of `H` cannot come from that theorem; it enters here only through the
local existence of a hypersurface of maximal contact built into the construction
(`globalizationData_localClass`, valid in every dimension), and no global hypersurface is built.
The marked iteration of Kollár's remark is not part of the check.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme
  IdealSheafData Scheme.Hom BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence Hironaka.Stage
  Hironaka.BO Hironaka.BD IsLocalRing

namespace Hironaka.Examples.Dimension1

section Helpers

variable {k : Type u} [Field k]

/-- A marked functor's value on a marked triple of dimension `≤ 0` has length `0` (the
dimension-zero case, `OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero`). -/
theorem length_seq_eq_zero_of_hasDimLE_zero {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom) (T : MarkedTriple k) (hT : Dom T) (h0 : T.toTriple.HasDimLE 0)
    (hm : 1 ≤ T.m) : (B.seq T hT).length = 0 := by
  rw [OrderGeSeqAssignment.seq_eq_nil_of_hasDimLE_zero B T hT h0 hm]
  rfl

variable [CharZero k]

/-- The output of [Kol07, Lemma 102] is the first blow-up followed by
`τ_* BMO_{n−1,m}(S, I_0|_S, m, E_S)`; at `n = 1` this tail is empty: it is the pushed-forward
value of the marked functor on the restricted triple, which has dimension `≤ 0`. -/
theorem length_tailSeq_eq_zero (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) (hn : T.HasDimLE 1)
    (hm : 1 ≤ m) {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (1 - 1) → T'.m = m → Dom T') :
    (Hironaka.BD.tailSeq T m j hI hmax hn B hDom).length = 0 := by
  have h0 := length_seq_eq_zero_of_hasDimLE_zero B (Hironaka.BD.restrictedTriple T m j hI hmax)
    (hDom _ (Hironaka.BD.hasDimLE_restrictedTriple T m j hI hmax hn) rfl)
    (Hironaka.BD.hasDimLE_restrictedTriple T m j hI hmax hn)
    (by rw [Hironaka.BD.restrictedTriple_m]; exact hm)
  have hinst : IsClosedImmersion
      (pushforwardBlowUp (T.E.component j).subschemeι (Hironaka.BD.centerS T m j)) :=
    inferInstance
  have hlen := @length_pushforward _ _ (B.seq (Hironaka.BD.restrictedTriple T m j hI hmax)
    (hDom _ (Hironaka.BD.hasDimLE_restrictedTriple T m j hI hmax hn) rfl))
    (pushforwardBlowUp (T.E.component j).subschemeι (Hironaka.BD.centerS T m j)) hinst
  exact hlen.trans h0

/-- The functor of [Kol07, Lemma 102] in dimension `1` has at most one member: the raw output is
`π_{-1}` followed by the empty tail, and the empty-blow-up convention [Kol07, 32] deletes empty
blow-ups. -/
theorem length_bdFunctor_seq_le_one (m j : ℕ) (hm : 1 ≤ m) {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (1 - 1) → T'.m = m → Dom T')
    (T : Triple k) (hT : Hironaka.BD.Domain 1 m j T) :
    ((Hironaka.BD.functor 1 m j B hDom).seq T hT).length ≤ 1 := by
  have h0 := length_tailSeq_eq_zero T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1
    hT.1 hm B hDom
  have h3 := length_eraseEmpty_le (Hironaka.BD.rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩)
    hT.2.1 hT.2.2.1 hT.1 B hDom)
  have e2 : (Hironaka.BD.rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B
      hDom).length =
      (Hironaka.BD.tailSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B
        hDom).length + 1 := rfl
  change (Hironaka.BD.rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B
    hDom).eraseEmpty.length ≤ 1
  omega

/-- The tuned `BD_{1,m,j}` (the tuning of [Kol07, Theorem 103, Step 1] applied to the functor of
Lemma 102) has at most one member: it is the functor of Lemma 102 on the tuned triple at the mark,
and `nil` below it. -/
theorem length_dataFunctor_seq_le_one (m j : ℕ) (hm : 1 ≤ m) {Dom : MarkedTriple k → Prop}
    (B : OrderGeSeqAssignment k Dom)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (1 - 1) → T'.m = tuningParam m → Dom T')
    (T : Triple k) (hT : T.BDClass 1 m j) :
    ((Hironaka.BD.dataFunctor 1 m j hm B hDom).seq T hT).length ≤ 1 := by
  by_cases h : T.I.maxOrd = m
  · rw [Hironaka.BD.dataFunctor_seq_of_maxOrd_eq 1 m j hm B hDom T hT h]
    exact length_bdFunctor_seq_le_one (tuningParam m) j (one_le_tuningParam m) B hDom _ _
  · rw [Hironaka.BD.dataFunctor_seq_of_maxOrd_lt 1 m j hm B hDom T hT (lt_of_le_of_ne hT.2.1 h)]
    exact Nat.zero_le _

/-- The functor of the data of [Kol07, Lemma 102] in dimension `1` has at most one member, at
every mark (at the mark `0` the data are the erasure of empty blow-ups from `zeroFunctor`). -/
theorem length_bdData_seq_le_one (m j : ℕ)
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (1 - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (T : Triple k) (hT : T.BDClass 1 m j) :
    (((Hironaka.BD.bdData 1 m j Dom B hDom hB hsm hbc).functor k).seq T hT).length ≤ 1 := by
  cases m with
  | zero =>
    change ((Hironaka.BD.zeroFunctor 1 j).seq T hT).length ≤ 1
    rw [Hironaka.BD.zeroFunctor_seq]
    exact length_eraseEmpty_le _
  | succ p =>
    exact length_dataFunctor_seq_le_one (p + 1) j (Nat.le_add_left 1 p) (B k) (hDom k) T hT

/-- [Kol07, 104, Step 2.2]: the re-tuned functor of Step 2.2 has at most one member when the data
of Lemma 102 do. -/
theorem length_step22Functor_seq_le_one {n m j : ℕ} (bd : ∀ m j : ℕ, BDData.{u} n m j)
    (hm : 1 ≤ m)
    (hbd : ∀ (m' j' : ℕ) (T : Triple k) (hT : T.BDClass n m' j'),
      (((bd m' j').functor k).seq T hT).length ≤ 1)
    (T : Triple k) (hT : T.BDClass n m j) :
    ((Hironaka.BO.step22Functor bd m j hm).seq T hT).length ≤ 1 := by
  by_cases h : T.I.maxOrd = m
  · unfold Hironaka.BO.step22Functor
    rw [ofTunedClass_seq_of_maxOrd_eq _ _ _ T hT h]
    exact hbd _ _ _ _
  · unfold Hironaka.BO.step22Functor
    rw [ofTunedClass_seq_of_maxOrd_lt _ _ _ T hT (lt_of_le_of_ne hT.2.1 h)]
    exact Nat.zero_le _

/-- [Kol07, 104, Step 2.1] with `E = ∅`: Step 2.1 with no boundary members is empty. -/
theorem length_step21Seq_eq_zero {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
    (hmax : T.I.maxOrd ≤ m) (bd : ∀ j : ℕ, BDData.{u} n m j) (hE : Fintype.card T.E.ι = 0) :
    (Hironaka.BO.step21Seq T hn hmax bd (Fintype.card T.E.ι)).1.length = 0 := by
  rw [hE, Hironaka.BO.step21Seq_zero]
  rfl

/-- [Kol07, 104] (Step 2 of the proof of Theorem 103) with `E = ∅`: Step 2 on a triple without
boundary members has at most one member, since Step 2.1 is empty and Step 2.2 has at most one. -/
theorem length_step2Seq_le_one {n m : ℕ} (T : Triple k) (hn : T.HasDimLE n)
    (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m j) (hm : 1 ≤ m)
    {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
    (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)
    (hbd : ∀ (m' j' : ℕ) (T : Triple k) (hT : T.BDClass n m' j'),
      (((bd m' j').functor k).seq T hT).length ≤ 1)
    (hE : Fintype.card T.E.ι = 0) :
    (Hironaka.BO.step2Seq T hn hmax bd hm hH hle).length ≤ 1 := by
  have e : ((Hironaka.BO.step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.concat
      (Hironaka.BO.step22 T hn hmax bd hm hH hle)).length =
      (Hironaka.BO.step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.length +
        (Hironaka.BO.step22 T hn hmax bd hm hH hle).length :=
    length_concat _ _
  have h21 := length_step21Seq_eq_zero T hn hmax (bd m) hE
  have h22 : (Hironaka.BO.step22 T hn hmax bd hm hH hle).length ≤ 1 :=
    length_step22Functor_seq_le_one bd hm hbd _ _
  change ((Hironaka.BO.step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.concat
    (Hironaka.BO.step22 T hn hmax bd hm hH hle)).length ≤ 1
  omega

/-- [Kol07, Theorem 103, Steps 1 and 2] with `E = ∅`: the maximal-contact case `maxContactCase`
on a triple without boundary members has at most one member (`nil` below the mark). -/
theorem length_maxContactCase_le_one {n m : ℕ} (T : Triple k) (hT : T.BOClass n m)
    {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
    (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H) (bd : ∀ m j : ℕ, BDData.{u} n m j)
    (hbd : ∀ (m' j' : ℕ) (T : Triple k) (hT : T.BDClass n m' j'),
      (((bd m' j').functor k).seq T hT).length ≤ 1)
    (hE : Fintype.card T.E.ι = 0) :
    (Hironaka.BO.maxContactCase T hT hH hle bd).length ≤ 1 := by
  by_cases h : T.I.maxOrd = m
  · rw [Hironaka.BO.maxContactCase_of_maxOrd_eq T hT hH hle bd h]
    exact length_step2Seq_le_one (T.tuned m hT.1) _ _ bd _ hH _ hbd hE
  · rw [Hironaka.BO.maxContactCase_of_maxOrd_lt T hT hH hle bd (lt_of_le_of_ne hT.2.2 h)]
    exact Nat.zero_le _

/-- [Kol07, Theorem 103, Step 3]: `BO_{1,m}` on a triple without boundary members has at most one
member; over a local cover the value is Step 2's, and pulling back preserves the length. -/
theorem length_functor_seq_le_one (m : ℕ) (bd : ∀ m j : ℕ, BDData.{u} 1 m j)
    (hbd : ∀ (m' j' : ℕ) (T : Triple k) (hT : T.BDClass 1 m' j'),
      (((bd m' j').functor k).seq T hT).length ≤ 1)
    (T : Triple k) (hT : T.BOClass 1 m) (hE : IsEmpty T.E.ι) [Nonempty T.X.left] :
    ((Hironaka.BO.functor 1 m bd).seq T hT).length ≤ 1 := by
  obtain ⟨T', g, hc⟩ :=
    Triple.exists_isLocalCover (Hironaka.BO.globalizationData_localClass 1 m) hT
  rw [← length_pullback _ g, Hironaka.BO.functor_seq_pullback_localCover 1 m bd hc]
  have hEι : T'.E.ι = T.E.ι := congrArg DivisorFamily.ι hc.2.2.2.2.2.2
  have : IsEmpty T'.E.ι := by rw [hEι]; exact hE
  have hE' : Fintype.card T'.E.ι = 0 := Fintype.card_eq_zero
  change (Hironaka.BO.maxContactCase T' hc.2.1.1 (Classical.choose_spec hc.2.1.2).1
    (Classical.choose_spec hc.2.1.2).2 bd).length ≤ 1
  exact length_maxContactCase_le_one T' hc.2.1.1 _ _ bd hbd hE'

omit [CharZero k] in
/-- A blow-up sequence of length at most one that is not empty is a single blow-up. -/
theorem exists_eq_cons_nil {X : Scheme.{u}} (S : BlowUpSequence X) (h1 : S.length ≤ 1)
    (h2 : S ≠ nil X) : ∃ Z : X.IdealSheafData, S = cons X Z (nil _) := by
  cases S with
  | nil _ => exact absurd rfl h2
  | cons X Z rest =>
    refine ⟨Z, ?_⟩
    cases rest with
    | nil _ => rfl
    | cons _ _ r =>
      exfalso
      change r.length + 1 + 1 ≤ 1 at h1
      omega

end Helpers

/-- **Order reduction on a curve** ([Kol07, 70]): on a smooth curve with `E = ∅` and
`max-ord I = m ≥ 1`, the unmarked functor of the stage produced from any base by the general step
is the single blow-up of the reduced `cosupp(I, m)`. The value has at most one member by the
construction (`length_functor_seq_le_one` at the data that `boOfBMO S0.bmo m` exposes), is not
empty by clause (1), and its centre is forced (the centre of an order sequence is reduced, the
order is upper semicontinuous, and the blow-up is an isomorphism off the centre). -/
theorem stage1_BO_eq_blowUp_cosupp (S0 : OrderReductionStage.{u} 0) {k : Type u} [Field k]
    [CharZero k] {m : ℕ} (T : Triple k) (h1 : T.HasDim 1) (hE : IsEmpty T.E.ι) (hm : 1 ≤ m)
    (hmax : T.I.maxOrd = (m : ℕ∞)) (hT : T.BOClass 1 m) :
    ∃ Z : T.X.left.IdealSheafData,
      (((Hironaka.Stage.tower S0 1).bo m).functor k).seq T hT =
          BlowUpSequence.cons T.X.left Z (BlowUpSequence.nil _) ∧
        Z = vanishingIdeal Z.support ∧
        (Z.support : Set T.X.left) = {x | (m : ℕ∞) ≤ T.I.ord x} := by
  have hS := (((Hironaka.Stage.tower S0 1).bo m).functor k).isOrderSeq T hT
  have hend := ((Hironaka.Stage.tower S0 1).bo m).maxOrd_lt k T hT
  -- `X` is nonempty: the maximal order `m ≥ 1` is not `0`
  have hX : Nonempty T.X.left := by
    by_contra hX'
    have : IsEmpty T.X.left := not_nonempty_iff.mp hX'
    have h0 := Hironaka.BO.maxOrd_eq_zero_of_isEmpty T.I
    rw [hmax] at h0
    have : m = 0 := by exact_mod_cast h0
    omega
  -- at most one member, by the construction
  have hlen : ((((Hironaka.Stage.tower S0 1).bo m).functor k).seq T hT).length ≤ 1 := by
    rw [show (Hironaka.Stage.tower S0 1).bo m = boOfBMO S0.bmo m from rfl, boOfBMO_functor]
    exact length_functor_seq_le_one m _
      (fun m' j' T' hT' => length_bdData_seq_le_one m' j' _ _ _ _ _ _ T' hT') T hT hE
  -- not empty: clause (1)
  have hne : (((Hironaka.Stage.tower S0 1).bo m).functor k).seq T hT ≠ nil T.X.left := by
    intro hnil
    rw [hnil] at hend
    change T.I.maxOrd < (m : ℕ∞) at hend
    rw [hmax] at hend
    exact lt_irrefl _ hend
  obtain ⟨Z, hZ⟩ := exists_eq_cons_nil _ hlen hne
  rw [hZ] at hS hend
  refine ⟨Z, hZ, ?_, ?_⟩
  · have := T.smooth
    exact center_eq_vanishingIdeal_support_of_isOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m Z
      (nil _) hS
  · have h0 := hS.2 ⟨0, Nat.succ_pos _⟩
    change T.E.HasSncWith Z ∧ T.I.OrdAlongEq Z.support (m : ℕ∞) at h0
    change (T.I.weakTransform Z).maxOrd < (m : ℕ∞) at hend
    have : SmoothOfRelativeDimension 1 (T.X.left ↘ Spec (.of k)) := h1
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨η, hη, hηx⟩ := Closeds.exists_mem_genericPoints_specializes Z.support hx
      exact hηx.mem_closed (isClosed_setOf_le_ord (T.X.left ↘ Spec (.of k)) 1 T.I m) (h0.2 η hη).ge
    · intro x hx
      by_contra hxZ
      obtain ⟨x', hx'⟩ := exists_π_eq_of_notMem_support Z hxZ
      have hx'E : x' ∉ Z.exceptionalDivisor.support := by
        intro h
        apply hxZ
        have := (mem_support_comap_iff_apply Z Z.blowUpπ x').mp h
        rwa [hx'] at this
      have hord := ord_weakTransform_of_notMem Z T.I hx'E
      have h2 : (T.I.weakTransform Z).ord x' ≤ (T.I.weakTransform Z).maxOrd :=
        le_maxOrdAlong _ (Set.mem_univ x')
      rw [hord, hx'] at h2
      exact absurd (hx.trans h2) (not_le.mpr hend)

end Hironaka.Examples.Dimension1
