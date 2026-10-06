/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TuningParam
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.IdealSheaf.Tuning
import Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra
import Hironaka.Manifold.BlowUp.Transform.TuningTransform
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Tuning of ideals along blow-up sequences on manifolds

Kollár's tuning theorems, on analytic manifolds. Theorem 100 (Tuning of ideals, I)
[Kol07, Theorem 100]: for `m = max-ord I`, `s ≥ 1` and any ideal sheaf `J` with
`I^s ⊆ J ⊆ W_{ms}(I)`, a smooth blow-up sequence is of order `≥ m` starting with `(X, I, m)` iff
it is of order `≥ ms` starting with `(X, J, ms)`. Corollary 101 (Tuning of ideals, II)
[Kol07, Corollary 101]: for `s = r · lcm(2, …, m)` with `r ≥ m − 1`, the same holds for
`(X, I, m, E)` and `(X, W_s(I), s, E)`. Here `W_s(I)` is the tuning ideal `tuning`, the sequences
are `FiniteSuccession` with their marked transforms `markedTransformSeq`, and the sequences of
order `≥ m` are `IsOfOrderGe`; the one-blowing-up transform rules are those of
`Hironaka/Manifold/BlowUp/Transform/{MarkedAlgebra,TuningTransform}.lean`. The algebraic
counterparts are the modules `Hironaka/Resolution/Algebraic/Tuning/` and
`Hironaka/Resolution/Algebraic/Kol07/Tuning.lean`.

## The argument

* Along a sequence (Kollár's induction on the length `r`): every stage `i` has `ord_{Z_i} I_i ≥ m`
  at the points of its centre (clause (4′) of `IsOfOrderGe`), so the marked transform of
  `(I_i, m)` is defined there and the one-blowing-up rules apply. The sequence forms of the
  product and power rules (`IsOfOrderGe.markedTransformSeq_mul`,
  `IsOfOrderGe.markedTransformSeq_pow`, `IsOfOrderGe.pow_markedTransformSeq_le`) and the tuning
  bounds `J_i ⊆ W_s(I_i)` for `J ⊆ W_s(I)` (`IsOfOrderGe.markedTransformSeq_le_tuning`, from
  `birationalTransform_tuning_le` at each step with the monotonicity of the marked transform,
  `birationalTransform_mono`, the transforms being defined by `le_ordAlong_tuning`) are inductions
  on the stage through the recursion `markedTransformSeq_succ`.
* Direction "order `≥ m` for `(I, m)` implies order `≥ ms` for `(J, ms)`" (`tuning_mp`): at every
  stage `J_i ⊆ W_{ms}(I_i)`, and `ord_{Z_i} I_i ≥ m` gives `ord_{Z_i} W_{ms}(I_i) ≥ ms`, so
  `ord_{Z_i} J_i ≥ ms` (the order is antitone in the ideal); the normal-crossings clause (3′) does
  not mention the ideal.
* Direction "order `≥ ms` for `(J, ms)` implies order `≥ m` for `(I, m)`" (`tuning_mpr`): for
  `I^s ⊆ J`, `I_i^s ⊆ J_i` at every stage, by induction, the transform of `(I_i, m)` being defined
  because `ord_{Z_i} J_i ≥ ms` and `I_i^s ⊆ J_i` give `ord_{Z_i} I_i ≥ m` (the order of a power,
  [Kol07, Definition 59], along the centre: `le_ordAlong_of_pow_le`); the same bound closes the
  order clause.
* Theorem 100 (`tuning_iff`) is the two directions; its bounds `J = I^s` (`tuning_iff_pow`) and
  `J = W_{ms}(I)` (`tuning_iff_tuning`) use `pow_le_tuning`. The sequence clause of Corollary 101
  (`tuning_iff_tuning_of_dvd`, `tuning_iff_lcm`) is Theorem 100 at `J = W_s(I)` for `s = m s'`
  (Kollár's "everything follows from (99) and (100)"), `s = r · lcm(2, …, m)` being divisible by
  `m` and positive. The form used by the order-reduction algorithm, at the parameter
  `s(m) = tuningParam m = max (m − 1) 1 · lcm(2, …, m)` (`tuning_orderReduction_equiv`), is the
  case `r = max (m − 1) 1`.
* The role of `E` (Kollár's remark in the proof of Corollary 101): both sides have the same
  sequence, the same centres and the same boundary, so clause (3′) is literally the same clause
  on both sides; every boundary `E₀` is allowed and no normal-crossings hypothesis enters.

Conventions: Kollár's `m = max-ord I` is the hypothesis `hI : ∀ y, I.ord y ≤ m` of `tuning_iff`
and of the theorems built on it; it is part of Kollár's statement of Theorem 100 and is kept so
that the theorems read as printed (the algebraic version carries it too); the proofs do not need
it, because both directions follow from the rules for the marked transforms of products and powers
and the containments `I^s ⊆ W_s(I)`, which hold whatever the order of `I`. `(J, ms)` is the mark
`m * s`; `lcm(2, …, m)` is `IsLocalRing.Lcm m` and `s(m)` is `IsLocalRing.tuningParam m`.

Tuning replaces an ideal by a D-balanced and `MC`-invariant one with the same blow-up sequences
of order `≥ m`; it is the first step of the order-reduction algorithm.
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M}
  {I J E₀ : IdealSheaf M} {m k s : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- Clause (4′) of `IsOfOrderGe` at stage `i`, read on the ideal sheaf `idealSheaf` of the centre
(through `idealSheaf_center`): the form in which the one-blowing-up rules take their divisibility
hypothesis. -/
theorem IsOfOrderGe.le_ordAlong_center (h : S.IsOfOrderGe I m E₀) (i : Fin S.length) :
    ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq I m i.castSucc) a := by
  intro a ha
  rw [S.idealSheaf_center i]
  exact h.le_ordAlong i ha

/-! ### The tuning ideal along the sequence -/

/-- For `J ⊆ W_s(I)` and a smooth blow-up sequence of order `≥ m` for `(I, m, E₀)`,
`J_i ⊆ W_s(I_i)` at every stage (Kollár's "since `J ⊂ W_{ms}(I)`, we know that
`J_{r−1} = (Π_{r−1})_*^{-1}(J, ms) ⊂ … = W_{ms}(I_{r−1})`" in the proof of
[Kol07, Theorem 100]). Induction on the stage:
`J_{i+1} = π_*^{-1}(J_i, s) ⊆ π_*^{-1}(W_s(I_i), s) ⊆ W_s(π_*^{-1}(I_i, m)) = W_s(I_{i+1})`
(`birationalTransform_mono` with the divisibility `le_ordAlong_tuning`, then
`birationalTransform_tuning_le`). -/
theorem IsOfOrderGe.markedTransformSeq_le_tuning (h : S.IsOfOrderGe I m E₀) (hJ : J ≤ I.tuning m s)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq J s i ≤ (S.markedTransformSeq I m i).tuning m s := by
  induction i using Fin.induction with
  | zero => exact hJ
  | succ i ih =>
    rw [markedTransformSeq_succ, markedTransformSeq_succ]
    have hmI := h.le_ordAlong_center i
    have hT : ∀ a ∈ (S.center i).support, (s : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf
        ((S.markedTransformSeq I m i.castSucc).tuning m s) a :=
      fun a ha => le_ordAlong_tuning _ _ m s ha (hmI a ha)
    exact (birationalTransform_mono (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) ih
      hT).trans (birationalTransform_tuning_le (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
        _ m s hmI)

/-- Along a smooth blow-up sequence of order `≥ m` for `(I, m, E₀)`, at every stage `i`,
`(Π_i)_*^{-1}(W_s(I), s) ⊆ W_s(I_i)` (the induction on `r` in the proof of
[Kol07, Theorem 100]): the case `J = W_s(I)` of `markedTransformSeq_le_tuning`. -/
theorem IsOfOrderGe.markedTransformSeq_tuning_le (h : S.IsOfOrderGe I m E₀) (s : ℕ)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq (I.tuning m s) s i ≤ (S.markedTransformSeq I m i).tuning m s :=
  h.markedTransformSeq_le_tuning le_rfl i

/-! ### Products and powers of marked transforms along the sequence -/

omit [FiniteDimensional 𝕜 E] in
/-- The product of marked ideal sheaves `(I_1, m_1) · (I_2, m_2) := (I_1 I_2, m_1 + m_2)`
[Kol07, Definition 59] along a sequence: along a smooth blow-up sequence of order `≥ m` for
`(I, m, E₀)` and of order `≥ k` for `(J, k, E₀)`, the marked transforms of `(IJ, m + k)` are the
products `I_i J_i`. At every stage the two transforms are defined (clause (4′)) and the
one-blowing-up product rule applies. -/
theorem IsOfOrderGe.markedTransformSeq_mul (hI : S.IsOfOrderGe I m E₀) (hJ : S.IsOfOrderGe J k E₀)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq (I * J) (m + k) i =
      S.markedTransformSeq I m i * S.markedTransformSeq J k i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [markedTransformSeq_succ, markedTransformSeq_succ, markedTransformSeq_succ, ih]
    exact birationalTransform_mul (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) _ _ m k
      (hI.le_ordAlong_center i) (hJ.le_ordAlong_center i)

omit [FiniteDimensional 𝕜 E] in
/-- Along a smooth blow-up sequence of order `≥ m` for `(I, m, E₀)`, the marked transforms of
`(I^s, ms)` are the powers `I_i^s` (Kollár's "`I_{r−1}^s = (Π_{r−1})_*^{-1} I^s`" in the proof of
[Kol07, Theorem 100]). -/
theorem IsOfOrderGe.markedTransformSeq_pow (h : S.IsOfOrderGe I m E₀) (s : ℕ)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq (I ^ s) (m * s) i = S.markedTransformSeq I m i ^ s := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [markedTransformSeq_succ, markedTransformSeq_succ, ih]
    exact birationalTransform_pow (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) _ m s
      (h.le_ordAlong_center i)

omit [FiniteDimensional 𝕜 E] in
/-- For `s ≥ 1`, `I^s ⊆ J` and a smooth blow-up sequence of order `≥ ms` for `(J, ms, E₀)`,
`I_i^s ⊆ J_i` at every stage (Kollár's "since `I^s ⊂ J`, we know that
`I_{r−1}^s = (Π_{r−1})_*^{-1} I^s ⊂ Π_{r−1 *}^{-1}(J, ms) = J_{r−1}`" in the proof of
[Kol07, Theorem 100]), the marked transforms of `(I, m)` being defined because the sequence has
order `≥ ms` for `(J, ms)`. By induction: `ord_{Z_i} I_i ≥ m` follows from `ord_{Z_i} J_i ≥ ms` and
`I_i^s ⊆ J_i` (`le_ordAlong_of_pow_le`), so that the power rule applies at the next step. -/
theorem IsOfOrderGe.pow_markedTransformSeq_le (h : S.IsOfOrderGe J (m * s) E₀) (hs : 1 ≤ s)
    (hIJ : I ^ s ≤ J) (i : Fin (S.length + 1)) :
    S.markedTransformSeq I m i ^ s ≤ S.markedTransformSeq J (m * s) i := by
  induction i using Fin.induction with
  | zero => exact hIJ
  | succ i ih =>
    rw [markedTransformSeq_succ, markedTransformSeq_succ]
    have hJi := h.le_ordAlong_center i
    have hIi : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq I m i.castSucc) a :=
      fun a ha => le_ordAlong_of_pow_le (S.isClosedSubmanifold_center i) hs ih ha (hJi a ha)
    rw [← birationalTransform_pow (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) _ m s hIi]
    exact birationalTransform_mono (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) ih hJi

/-! ### Theorem 100 and Corollary 101 -/

/-- The direction "order `≥ m` for `(I, m)` implies order `≥ ms` for `(J, ms)`" of
[Kol07, Theorem 100]: for `J ⊆ W_{ms}(I)`, a smooth blow-up sequence of order `≥ m` starting with
`(M, I, m, E₀)` is a smooth blow-up sequence of order `≥ ms` starting with `(M, J, ms, E₀)`. -/
theorem tuning_mp (hJW : J ≤ I.tuning m (m * s)) (h : S.IsOfOrderGe I m E₀) :
    S.IsOfOrderGe J (m * s) E₀ := fun i =>
  ⟨(h i).1, fun a ha => by
    have h1 := h.markedTransformSeq_le_tuning hJW i.castSucc
    have h2 : ((m * s : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i)
        ((S.markedTransformSeq I m i.castSucc).tuning m (m * s)) a := by
      rw [← S.idealSheaf_center i]
      exact le_ordAlong_tuning _ _ m (m * s) ha (h.le_ordAlong_center i a ha)
    exact IdealSheaf.le_ordAlongIdeal_of_le h1 h2⟩

omit [FiniteDimensional 𝕜 E] in
/-- The direction "order `≥ ms` for `(J, ms)` implies order `≥ m` for `(I, m)`" of
[Kol07, Theorem 100]: for `s ≥ 1` and `I^s ⊆ J`, a smooth blow-up sequence of order `≥ ms`
starting with `(M, J, ms, E₀)` is a smooth blow-up sequence of order `≥ m` starting with
`(M, I, m, E₀)`. -/
theorem tuning_mpr (hs : 1 ≤ s) (hIJ : I ^ s ≤ J) (h : S.IsOfOrderGe J (m * s) E₀) :
    S.IsOfOrderGe I m E₀ := fun i =>
  ⟨(h i).1, fun a ha => by
    rw [← S.idealSheaf_center i]
    exact le_ordAlong_of_pow_le (S.isClosedSubmanifold_center i) hs
      (h.pow_markedTransformSeq_le hs hIJ i.castSucc) ha (h.le_ordAlong_center i a ha)⟩

/-- **Tuning of ideals, I** [Kol07, Theorem 100], on analytic manifolds: for an ideal sheaf `I`
with `ord_y I ≤ m` at every point (Kollár's `m = max-ord I`, carried as printed), an integer
`s ≥ 1` and an ideal sheaf `J` with `I^s ⊆ J ⊆ W_{ms}(I)`, a smooth blow-up sequence `S` is of
order `≥ m` starting with `(M, I, m, E₀)` iff it is of order `≥ ms` starting with
`(M, J, ms, E₀)`. -/
theorem tuning_iff (hI : ∀ y, I.ord y ≤ m) (hs : 1 ≤ s) (hIJ : I ^ s ≤ J)
    (hJW : J ≤ I.tuning m (m * s)) :
    S.IsOfOrderGe I m E₀ ↔ S.IsOfOrderGe J (m * s) E₀ := by
  have _ := hI
  exact ⟨tuning_mp hJW, tuning_mpr hs hIJ⟩

/-- [Kol07, Theorem 100] at the lower bound `J = I^s`: `(M, I, m, E₀)` and `(M, I^s, ms, E₀)` have
the same smooth blow-up sequences of order `≥ m`, resp. `≥ ms` (`I^s ⊆ W_{ms}(I)` is
`pow_le_tuning`). -/
theorem tuning_iff_pow (hI : ∀ y, I.ord y ≤ m) (hs : 1 ≤ s) :
    S.IsOfOrderGe I m E₀ ↔ S.IsOfOrderGe (I ^ s) (m * s) E₀ :=
  tuning_iff hI hs le_rfl (I.pow_le_tuning m (m * s) le_rfl)

/-- [Kol07, Theorem 100] at the upper bound `J = W_{ms}(I)`, the form the proof of
[Kol07, Corollary 101] invokes: `(M, I, m, E₀)` and `(M, W_{ms}(I), ms, E₀)` have the same smooth
blow-up sequences of order `≥ m`, resp. `≥ ms`. -/
theorem tuning_iff_tuning (hI : ∀ y, I.ord y ≤ m) (hs : 1 ≤ s) :
    S.IsOfOrderGe I m E₀ ↔ S.IsOfOrderGe (I.tuning m (m * s)) (m * s) E₀ :=
  tuning_iff hI hs (I.pow_le_tuning m (m * s) le_rfl) le_rfl

/-- The sequence clause of [Kol07, Corollary 101] for any `s ≥ 1` divisible by `m` (Kollár's
"everything follows from (99) and (100)": Theorem 100 at `J = W_s(I)` for `s = m s'`):
`(M, I, m, E₀)` and `(M, W_s(I), s, E₀)` have the same smooth blow-up sequences of order `≥ m`,
resp. `≥ s`. -/
theorem tuning_iff_tuning_of_dvd (hI : ∀ y, I.ord y ≤ m) (hs : 1 ≤ s) (hdvd : m ∣ s) :
    S.IsOfOrderGe I m E₀ ↔ S.IsOfOrderGe (I.tuning m s) s E₀ := by
  obtain ⟨s', rfl⟩ := hdvd
  have hs' : 1 ≤ s' := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hs
  exact tuning_iff_tuning hI hs'

/-- **Tuning of ideals, II** [Kol07, Corollary 101], the equivalence of sequences, on analytic
manifolds: for `ord_y I ≤ m` at every point, `1 ≤ m`, and `s = r · lcm(2, …, m)` with `r ≥ m − 1`
and `r ≥ 1`, a smooth blow-up sequence is of order `≥ m` starting with `(M, I, m, E₀)` iff it is
of order `≥ s` starting with `(M, W_s(I), s, E₀)`, for every boundary `E₀`; `s` is divisible by
`m` (`dvd_Lcm`) and positive. Kollár's `r ≥ m − 1` is carried as printed; the equivalence does not
use it (it is what makes `W_s(I)` D-balanced, `isDBalanced_tuning`). -/
theorem tuning_iff_lcm (hI : ∀ y, I.ord y ≤ m) (hm : 1 ≤ m) {r : ℕ} (hr : m - 1 ≤ r)
    (hr1 : 1 ≤ r) :
    S.IsOfOrderGe I m E₀ ↔ S.IsOfOrderGe (I.tuning m (r * Lcm m)) (r * Lcm m) E₀ := by
  have _ := hr
  exact tuning_iff_tuning_of_dvd hI (Nat.mul_pos hr1 (Lcm_pos m)) ((dvd_Lcm hm le_rfl).mul_left r)

/-- [Kol07, Corollary 101] at the parameter `s(m) = tuningParam m = max (m − 1) 1 · lcm(2, …, m)`,
the value of `s` this library fixes once for all (where Kollár takes `s = m!` to avoid further
choices, [Kol07, Theorem 103, Step 1 of the proof]): order reduction for `(M, I, m, E₀)` is order
reduction for `(M, W_{s(m)}(I), s(m), E₀)`. -/
theorem tuning_orderReduction_equiv (hI : ∀ y, I.ord y ≤ m) (hm : 1 ≤ m) :
    S.IsOfOrderGe I m E₀ ↔ S.IsOfOrderGe (I.tuning m (tuningParam m)) (tuningParam m) E₀ :=
  tuning_iff_lcm hI hm (le_max_left _ _) (le_max_right _ _)

end AnalyticManifold.FiniteSuccession

end
