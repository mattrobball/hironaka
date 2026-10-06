/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Kol07.Warning63
import Hironaka.Resolution.Algebraic.Stage.DimZero
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Split
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step3
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Transport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Weak
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainLift
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimTools
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 through Step 1, and the Step 1 reduction along the tower

Step 1 of the proof of [Kol07, Theorem 107] (item 111, Step 1): `BMO_{n,1}` on `(X, I, 1, E)`
runs rounds of `BO_{n,d}` on the nonmonomial part `N(I)` for `d = max-ord N(I)` descending to `1`,
then Steps 2 and 3. Along a round of order `d` the ideal of the round is the weak transform of
`N(I)`, which is the nonmonomial part of the marked transform of `I` at every stage
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Weak`). For the statement CP3 of the embedded
desingularization (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): at a point of a
centre of a round of order `≥ 2` no chain shape of the current ideal exists, since its nonmonomial
part would have order `≤ 1` there while the centre has order `≥ 2`; the round of order `1` is
`BO_{n,1}` on the nonmonomial triple, and the classification for `N(K)` given by the hypothesis
`CP3BOFor` is one for `K` (`centerClassifiedAt_of_nonmonomialPart`, the fine split of [Kol07,
Definition–Lemma 110] with top monomial `1`, and `stratumIn_of_stratumIn_zero`). The loop is the
well-founded recursion `step1` of
`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart` (`cp3For_concat`); at the
mark `1` Step 2 is empty; Step 3 is `cp3For_step3Seq`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step3`); the base of the tower and its Step 1
reduction follow (`cp3BMOAt_zero`, `cp3BMOAt_succ_of_cp3BOAt`; [Kol07, 70]). This argument is not in
the literature. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.IdealSheafData Scheme
  BlowUpSequence Hironaka.Sequence Hironaka.BMO Hironaka.Stage

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Algebra

variable {R : Type*} [CommRing R]

/-- A stratum in the coordinates with the zero exponents is a stratum for any exponents: the zero
exponents force a positive level, where the top exponents do not enter. -/
theorem stratumIn_of_stratumIn_zero {n : ℕ} {z : Fin n → R} {C : Set (Fin n)} {r : ℕ}
    {σ : Fin (r + 1) → Fin n} {a : Fin (r + 1) → Fin n → ℕ} (b : Fin n → ℕ) {Z : Ideal R}
    (h : StratumIn z C σ a (0 : Fin n → ℕ) Z) : StratumIn z C σ a b Z := by
  obtain ⟨l, hl, s, hsC, hZ, h0, hpos⟩ := h
  refine ⟨l, hl, s, hsC, hZ, fun hl0 => ?_, hpos⟩
  obtain ⟨_, -, hk⟩ := h0 hl0
  exact absurd rfl hk

end Algebra

section Scheme

variable {X : Scheme.{u}}

/-- The marked transform of the unit ideal is the unit ideal at every stage (by the definition of
the marked transform, `π⁻¹_*(I, m) = 𝒪(mF) · π^* I`). -/
theorem markedTransformSeq_top (S : BlowUpSequence X) (m : ℕ) (i : Fin (S.length + 1)) :
    S.markedTransformSeq ⊤ m i = ⊤ := by
  induction S with
  | nil Y => rfl
  | cons Y D rest ih =>
    rcases i with ⟨_ | j, hi⟩
    · rfl
    · change rest.markedTransformSeq (Scheme.IdealSheafData.markedTransform ⊤ D m) m ⟨j,
        Nat.lt_of_succ_lt_succ hi⟩ = ⊤
      rw [markedTransform_top]
      exact ih _

/-- The classification for the ideal from the classification for its nonmonomial part (the fine
split of [Kol07, Definition–Lemma 110] read as a transfer): a chain shape of `K` gives the same
shape with top monomial `1` of `N(K)` (`stalkIdeal_nonmonomialPart_of_kShape`,
`stalkIdeal_nonmonomialPart_of_iShape`), whose stratum is one for `K`. -/
theorem centerClassifiedAt_of_nonmonomialPart [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
    (n₀ : ℕ) [SmoothOfRelativeDimension n₀ f] {E : DivisorFamily X} (hE : E.IsSnc)
    {K Z : X.IdealSheafData} (hK0 : IsNonzeroEverywhere K) {q : X}
    (h : CenterClassifiedAt E (nonmonomialPart K E) Z q) : CenterClassifiedAt E K Z q := by
  intro n z c r σ a b hfree hb
  have hb0 : ∀ κ, (0 : Fin n → ℕ) κ ≠ 0 → κ ∈ Set.range c := fun _ h0 => absurd rfl h0
  refine ⟨fun hK => ?_, fun hI => ?_⟩
  · have hN := stalkIdeal_nonmonomialPart_of_kShape f n₀ hE hK0 hfree hb hK
    refine stratumIn_of_stratumIn_zero b ((h z c σ a 0 hfree hb0).1 ?_)
    rw [hN, monomialOf_zero, Ideal.span_singleton_one, Ideal.top_mul]
  · have hN := stalkIdeal_nonmonomialPart_of_iShape f n₀ hE hK0 hfree hb hI
    rcases (h z c σ a 0 hfree hb0).2
        (by rw [hN, monomialOf_zero, Ideal.span_singleton_one, Ideal.top_mul]) with h1 | h2
    · exact Or.inl (stratumIn_of_stratumIn_zero b h1)
    · exact Or.inr h2

end Scheme

section Step1

variable {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d)

/-- The rounds of order `≥ 2` of Step 1 ([Kol07, 111, Step 1]): no point of their centres carries
a K- or I-shape of the current ideal, since the nonmonomial part has order `≤ 1` at such a point
(`ord_le_one_of_stalkIdeal_eq_chainKIdeal`, `ord_le_one_of_stalkIdeal_eq_chainIdeal`), it is the
ideal of the round (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Weak`), and the centre of the
round has order `≥ 2` (`notMem_of_leOrdAlong_two`); CP3 holds vacuously. -/
theorem cp3For_step1Round_of_two_le (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n 1 T)
    (hd : 1 ≤ roundOrder T) (h2 : 2 ≤ roundOrder T) :
    CP3For (step1Round bo T hT hd) T.I T.E := by
  obtain ⟨T, m⟩ := T
  obtain rfl : m = 1 := hT.2.2
  set f := T.X.left ↘ Spec (CommRingCat.of k) with hf
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  have hsm₀ : SmoothOfRelativeDimension n₀ f := hn₀
  have hLN : IsLocallyNoetherian T.X.left := f.isLocallyNoetherian_of_field
  have hS := step1Round_isOrderSeq bo ⟨T, 1⟩ hT hd
  have hI : (step1Round bo ⟨T, 1⟩ hT hd).IsOrderGeSeq f T.I 1 T.E :=
    step1Round_isOrderGeSeq bo ⟨T, 1⟩ hT hd
  set S := step1Round bo ⟨T, 1⟩ hT hd with hSdef
  intro i q hq
  have hW := weakTransformSeq_eq_nonmonomialPart_markedTransformSeq ⟨T, 1⟩ rfl hS hI i.castSucc
  -- the instances at stage `i`
  set fi := S.stageMap i.castSucc ≫ f with hfi
  have hsmi : SmoothOfRelativeDimension n₀ fi :=
    IsSmooth.smoothOfRelativeDimension_stageMap hI.1 i.castSucc
  have hsm : Smooth fi := SmoothOfRelativeDimension.smooth n₀ fi
  have hprop : IsProper (S.stageMap i.castSucc) := isProper_stageMap S i.castSucc
  have hNi : IsNoetherian (S.stage i.castSucc) := fi.isNoetherian_of_field
  have hreg := isRegularLocalRing_stalk fi q
  have hEi : (S.totalTransformSeq T.E i.castSucc).IsSnc :=
    IsOrderGeSeq.isSnc_totalTransformSeq f n₀ hI T.isSnc i.castSucc
  have hK0 : IsNonzeroEverywhere (S.markedTransformSeq T.I 1 i.castSucc) :=
    IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq f n₀ hI T.isNonzeroEverywhere i.castSucc
  -- the centre has order `≥ 2` for the round's ideal
  have hD : (S.weakTransformSeq (nonmonomialPart T.I T.E) i.castSucc).LeOrdAlong
      (S.center i).support ((2 : ℕ) : ℕ∞) := by
    intro η hη
    rw [(hS.2 i).2 η hη]
    exact_mod_cast h2
  intro nq z c r σ a b hfree hb
  obtain ⟨hz, -, -, -, -, -⟩ := id hfree
  refine ⟨fun hK => ?_, fun hI' => ?_⟩
  · exfalso
    have hN := stalkIdeal_nonmonomialPart_of_kShape fi n₀ hEi hK0 hfree hb hK
    have hle := ord_le_one_of_stalkIdeal_eq_chainKIdeal hz _ hN
    rw [← hW] at hle
    exact notMem_of_leOrdAlong_two fi n₀ _ _ hD hle hq
  · exfalso
    have hN := stalkIdeal_nonmonomialPart_of_iShape fi n₀ hEi hK0 hfree hb hI'
    have hle := ord_le_one_of_stalkIdeal_eq_chainIdeal hz _ hN
    rw [← hW] at hle
    exact notMem_of_leOrdAlong_two fi n₀ _ _ hD hle hq

/-- The round of order `1` of Step 1 ([Kol07, 111, Step 1] at `d = 1`) is `BO_{n,1}` on the
nonmonomial triple; its classification (the hypothesis `CP3BOFor`) is for the marked transform of
`N(I)` = the weak transform ([Kol07, Remark 67]) = the nonmonomial part of the marked transform
of `I` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Weak`), and a classification for `N(K)` is
one for `K` (`centerClassifiedAt_of_nonmonomialPart`). -/
theorem cp3For_step1Round_of_roundOrder_eq_one (hbo : CP3BOFor k bo) (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n 1 T) (hd : 1 ≤ roundOrder T) (h1 : roundOrder T = 1) :
    CP3For (step1Round bo T hT hd) T.I T.E := by
  obtain ⟨T, m⟩ := T
  obtain rfl : m = 1 := hT.2.2
  set f := T.X.left ↘ Spec (CommRingCat.of k) with hf
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  have hsm₀ : SmoothOfRelativeDimension n₀ f := hn₀
  have hLN : IsLocallyNoetherian T.X.left := f.isLocallyNoetherian_of_field
  have key : ∀ (d : ℕ), d = 1 →
      ∀ (hcls : Triple.BOClass n d (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k))),
        CP3For (((bo d).functor k).seq (nonmonomialTriple (⟨T, 1⟩ : MarkedTriple k)) hcls)
          (nonmonomialPart T.I T.E) T.E := by
    intro d e hcls
    subst e
    exact hbo _ hcls
  have hN : CP3For (step1Round bo ⟨T, 1⟩ hT hd) (nonmonomialPart T.I T.E) T.E :=
    key _ h1 (boClass_nonmonomialTriple ⟨T, 1⟩ hT hd)
  have hS := step1Round_isOrderSeq bo ⟨T, 1⟩ hT hd
  have hI : (step1Round bo ⟨T, 1⟩ hT hd).IsOrderGeSeq f T.I 1 T.E :=
    step1Round_isOrderGeSeq bo ⟨T, 1⟩ hT hd
  set S := step1Round bo ⟨T, 1⟩ hT hd with hSdef
  intro i q hq
  have hW := weakTransformSeq_eq_nonmonomialPart_markedTransformSeq ⟨T, 1⟩ rfl hS hI i.castSucc
  have hmw : S.markedTransformSeq (nonmonomialPart T.I T.E) 1 i.castSucc =
      S.weakTransformSeq (nonmonomialPart T.I T.E) i.castSucc := by
    have h := IsOrderSeq.markedTransformSeq_eq_weakTransformSeq f n₀ hS i.castSucc
    rwa [h1] at h
  -- the instances at stage `i`
  set fi := S.stageMap i.castSucc ≫ f with hfi
  have hsmi : SmoothOfRelativeDimension n₀ fi :=
    IsSmooth.smoothOfRelativeDimension_stageMap hI.1 i.castSucc
  have hsm : Smooth fi := SmoothOfRelativeDimension.smooth n₀ fi
  have hprop : IsProper (S.stageMap i.castSucc) := isProper_stageMap S i.castSucc
  have hNi : IsNoetherian (S.stage i.castSucc) := fi.isNoetherian_of_field
  have hEi : (S.totalTransformSeq T.E i.castSucc).IsSnc :=
    IsOrderGeSeq.isSnc_totalTransformSeq f n₀ hI T.isSnc i.castSucc
  have hK0 : IsNonzeroEverywhere (S.markedTransformSeq T.I 1 i.castSucc) :=
    IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq f n₀ hI T.isNonzeroEverywhere i.castSucc
  have hcls : CenterClassifiedAt (S.totalTransformSeq T.E i.castSucc)
      (S.markedTransformSeq (nonmonomialPart T.I T.E) 1 i.castSucc) (S.center i) q := hN i q hq
  rw [hmw, hW] at hcls
  intro nq z c r σ a b hfree hb
  exact centerClassifiedAt_of_nonmonomialPart fi n₀ hEi hK0 hcls z c σ a b hfree hb

/-- The induction behind `cp3For_step1` ([Kol07, 111, Step 1], the loop on `d = max-ord N(I)`),
on a bound for the loop variable: a round of order `≥ 2`, or the round of order `1`, then the
rest of Step 1 on the induced marked triple (`cp3For_concat`). -/
theorem cp3For_step1_aux (hbo : CP3BOFor k bo) (l : ℕ) :
    ∀ (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n 1 T), roundOrder T ≤ l →
      CP3For (step1 bo T hT).1 T.I T.E := by
  induction l with
  | zero =>
    intro T hT hl
    have hlt : roundOrder T < 1 := lt_of_le_of_lt hl Nat.zero_lt_one
    rw [step1_of_lt bo T hT hlt]
    intro i
    exact i.elim0
  | succ l ih =>
    intro T hT hl
    obtain ⟨T, m⟩ := T
    obtain rfl : m = 1 := hT.2.2
    by_cases hd : 1 ≤ roundOrder (⟨T, 1⟩ : MarkedTriple k)
    · rw [step1_of_le bo _ hT hd]
      refine cp3For_concat _ _ T.I T.E ?_ ?_
      · by_cases h2 : 2 ≤ roundOrder (⟨T, 1⟩ : MarkedTriple k)
        · exact cp3For_step1Round_of_two_le bo ⟨T, 1⟩ hT hd h2
        · exact cp3For_step1Round_of_roundOrder_eq_one bo hbo ⟨T, 1⟩ hT hd (by omega)
      · exact ih (roundTriple bo ⟨T, 1⟩ hT hd) (bmoClass_roundTriple bo ⟨T, 1⟩ hT hd)
          (Nat.lt_succ_iff.mp (lt_of_lt_of_le (roundOrder_roundTriple_lt bo ⟨T, 1⟩ hT hd) hl))
    · rw [step1_of_lt bo _ hT (not_le.mp hd)]
      intro i
      exact i.elim0

/-- CP3 along the whole Step 1 ([Kol07, 111, Step 1]; recursion on the order of the round,
`cp3For_concat`). -/
theorem cp3For_step1 (hbo : CP3BOFor k bo) (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n 1 T) : CP3For (step1 bo T hT).1 T.I T.E :=
  cp3For_step1_aux bo hbo (roundOrder T) T hT le_rfl

/-- At the mark `1` Step 2 is empty ([Kol07, 111, Steps 1–2]): after Step 1 the nonmonomial part
is the unit ideal (`roundOrder_afterStep1_lt`), so the separation order is `0`
(`sepOrder_eq_zero_iff`, `step2_of_eq_zero`). -/
theorem step2_afterStep1_eq_nil (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n 1 T) :
    (step2 bo (afterStep1 bo T hT) (bmoClass_afterStep1 bo T hT)).1 =
      BlowUpSequence.nil (afterStep1 bo T hT).X.left := by
  apply step2_of_eq_zero
  rw [sepOrder_eq_zero_iff]
  have hlt := roundOrder_afterStep1_lt bo T hT
  have h0 : roundOrder (afterStep1 bo T hT) = 0 := by omega
  have hmax : (nonmonomialPart (afterStep1 bo T hT).I (afterStep1 bo T hT).E).maxOrd = 0 := by
    rw [← coe_roundOrder, h0, Nat.cast_zero]
  refine Set.disjoint_right.mpr fun x hx _ => ?_
  have hord : (nonmonomialPart (afterStep1 bo T hT).I (afterStep1 bo T hT).E).ord x = 0 :=
    nonpos_iff_eq_zero.mp (hmax ▸ le_maxOrd _ x)
  rw [ord_eq_zero_iff] at hord
  exact hord hx

/-- CP3 along `BMO_{n,1}` from CP3 along `BO_{n,1}` ([Kol07, 111]): the three steps concatenated
(`cp3For_concat`; Step 2 empty, Step 3 by `cp3For_step3Seq`). -/
theorem cp3For_bmoSeq (hbo : CP3BOFor k bo) (T : MarkedTriple k)
    (hT : MarkedTriple.BMOClass n 1 T) : CP3For (bmoSeq bo T hT) T.I T.E := by
  obtain ⟨T, m⟩ := T
  obtain rfl : m = 1 := hT.2.2
  unfold bmoSeq
  refine cp3For_concat _ _ T.I T.E (cp3For_step1 bo hbo ⟨T, 1⟩ hT) ?_
  refine cp3For_concat _ _ _ _ ?_
    (cp3For_step3Seq (afterStep2 bo ⟨T, 1⟩ hT) (bmoClass_afterStep2 bo ⟨T, 1⟩ hT))
  rw [step2_afterStep1_eq_nil]
  intro i
  exact i.elim0

end Step1

/-- The base of the tower ([Kol07, 70]): in dimension `0` the ideal is the unit ideal
(`Triple.I_eq_top_of_hasDimLE_zero`), so the marked transforms are the unit ideal and no centre
of order `≥ 1` has a point. -/
theorem cp3BMOAt_zero : CP3BMOAt k 0 := by
  intro T hT i q hq
  exfalso
  have hI := Triple.I_eq_top_of_hasDimLE_zero T.toTriple hT.2.1
  have hge : (bmoRun k 0 T hT).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E :=
    (((tower stage0 0).bmo 1).functor k).isOrderGeSeq T hT
  obtain ⟨ζ, hζ, -⟩ := Closeds.exists_mem_genericPoints_specializes _ hq
  have h1 := (hge.2 i).2 ζ hζ
  rw [hI, markedTransformSeq_top, ord_top, hT.2.2] at h1
  exact absurd h1 (by norm_num)

/-- The Step 1 reduction along the tower ([Kol07, 70, (70.2)]: (68) in dimension `n` gives (69) in
dimension `n`): CP3 for `BMO_{n+1,1}` from CP3 for `BO_{n+1,1}` (`bmoRun` is `bmoSeq` on the data
`boOfBMO` of the tower). -/
theorem cp3BMOAt_succ_of_cp3BOAt (n : ℕ) (hbo : CP3BOAt k (n + 1)) : CP3BMOAt k (n + 1) := by
  intro T hT
  have hbo' : CP3BOFor k (boOfBMO (tower stage0 n).bmo) := fun T' hT' => hbo T' hT'
  exact cp3For_bmoSeq _ hbo' T hT

end Hironaka.Resolution
