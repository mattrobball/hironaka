/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Balanced.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 106: the tuned ideal of `I = (x³ − y², x⁴ + xz² − w³)`

[Kol07, Example 106] considers the subvariety `X ⊂ 𝔸⁴` defined by the ideal
`I = (x³ − y², x⁴ + xz² − w³)` and notes that `ord I = 2` and that "`H = (y = 0)` is a hypersurface
of maximal contact". The tuning step of the order reduction on this example, computed exactly in
`ℚ[x, y, z, w]`:

* `D(I) = (x², y, z², xz, w²)` — the partial derivatives of `x³ − y²` are `3x²`, `−2y`, `0`, `0`,
  those of `x⁴ + xz² − w³` are `4x³ + z²`, `0`, `2xz`, `−3w²`, and `x³ ∈ (x²)`
  (`derivative_example106`);
* `I` and the tuned ideal `W(I) = I + D(I)²` have order exactly `2` at the origin
  (`ord_zero_example106`, `ord_zero_tuned_example106`): `I ⊆ 𝔪₀²`, `D(I) ⊆ 𝔪₀`, and `y² ∉ 𝔪₀³`;
* the order-2 locus `V(D(I))` has the origin as its only `ℚ`-point (`cosupport_example106`), and it
  is also `cosupp(W(I), 2)` since `D(W(I)) = D(I)` (`derivative_sup_derivative_sq`);
* `I` itself is neither D-balanced nor MC-invariant with respect to `2`
  (`not_isDBalanced_example106`, `not_mcInvariant_example106`): `y·y ∈ D(I)²`, but `y² ∉ I` — at the
  point `(1, 1, 0, 1)`, a common zero of the generators, `y²` evaluates to `1`.

The D-balance and MC-invariance of `W(I)` are the general facts `isDBalanced_sup_derivative_sq` and
`mcInvariant_sup_derivative_sq` of `HironakaExamples.Balanced.Tuned`; no explicit generators of this
`W(I)` are computed.
-/

@[expose] public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples.Example106

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1` in `ℚ[x, y, z, w]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2` in `ℚ[x, y, z, w]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3` in `ℚ[x, y, z, w]`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)

/-- Kollár's `I = (x³ − y², x⁴ + xz² − w³)`. -/
noncomputable abbrev I106 : Ideal (MvPolynomial (Fin 4) ℚ) :=
  Ideal.span {x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3}

/-- `D(I) = (x², y, z², xz, w²)`. -/
noncomputable abbrev D106 : Ideal (MvPolynomial (Fin 4) ℚ) :=
  Ideal.span {x ^ 2, y, z ^ 2, x * z, w ^ 2}

/-- The maximal ideal of the origin, `𝔪₀ = (x, y, z, w)`. -/
noncomputable abbrev m0 : Ideal (MvPolynomial (Fin 4) ℚ) := Ideal.span {x, y, z, w}

section Derivative

theorem pderiv_zero_gen1 : pderiv 0 (x ^ 3 - y ^ 2) = C 3 * x ^ 2 := by simp [map_ofNat]
theorem pderiv_one_gen1 : pderiv 1 (x ^ 3 - y ^ 2) = -(C 2 * y) := by simp [map_ofNat]
theorem pderiv_two_gen1 : pderiv 2 (x ^ 3 - y ^ 2) = 0 := by simp
theorem pderiv_three_gen1 : pderiv 3 (x ^ 3 - y ^ 2) = 0 := by simp

theorem pderiv_zero_gen2 : pderiv 0 (x ^ 4 + x * z ^ 2 - w ^ 3) = C 4 * x ^ 3 + z ^ 2 := by
  simp [map_ofNat]
theorem pderiv_one_gen2 : pderiv 1 (x ^ 4 + x * z ^ 2 - w ^ 3) = 0 := by simp
theorem pderiv_two_gen2 : pderiv 2 (x ^ 4 + x * z ^ 2 - w ^ 3) = C 2 * (x * z) := by
  simp [map_ofNat]
  ring
theorem pderiv_three_gen2 : pderiv 3 (x ^ 4 + x * z ^ 2 - w ^ 3) = -(C 3 * w ^ 2) := by
  simp [map_ofNat]

theorem x_sq_mem_D106 : x ^ 2 ∈ D106 := Ideal.subset_span (by simp)
theorem y_mem_D106 : y ∈ D106 := Ideal.subset_span (by simp)
theorem z_sq_mem_D106 : z ^ 2 ∈ D106 := Ideal.subset_span (by simp)
theorem xz_mem_D106 : x * z ∈ D106 := Ideal.subset_span (by simp)
theorem w_sq_mem_D106 : w ^ 2 ∈ D106 := Ideal.subset_span (by simp)

/-- `D(x³ − y², x⁴ + xz² − w³) = (x², y, z², xz, w²)`. -/
theorem derivative_example106 : Ideal.derivative ℚ I106 = D106 := by
  rw [I106, derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · have : x ^ 3 - y ^ 2 = x * x ^ 2 - y * y := by ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ x_sq_mem_D106)
          (Ideal.mul_mem_left _ _ y_mem_D106)
      · have : x ^ 4 + x * z ^ 2 - w ^ 3 = x ^ 2 * x ^ 2 + x * z ^ 2 - w * w ^ 2 := by ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ x_sq_mem_D106)
          (Ideal.mul_mem_left _ _ z_sq_mem_D106)) (Ideal.mul_mem_left _ _ w_sq_mem_D106)
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', hg', rfl⟩ := hg
      rcases hg' with rfl | rfl
      · match i with
        | 0 => rw [pderiv_zero_gen1]; exact Ideal.mul_mem_left _ _ x_sq_mem_D106
        | 1 => rw [pderiv_one_gen1]; exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ y_mem_D106)
        | 2 => rw [pderiv_two_gen1]; exact Ideal.zero_mem _
        | 3 => rw [pderiv_three_gen1]; exact Ideal.zero_mem _
      · match i with
        | 0 =>
          rw [pderiv_zero_gen2, show C 4 * x ^ 3 + z ^ 2 = C 4 * x * x ^ 2 + z ^ 2 by ring]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ x_sq_mem_D106) z_sq_mem_D106
        | 1 => rw [pderiv_one_gen2]; exact Ideal.zero_mem _
        | 2 => rw [pderiv_two_gen2]; exact Ideal.mul_mem_left _ _ xz_mem_D106
        | 3 => rw [pderiv_three_gen2]; exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ w_sq_mem_D106)
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ (f : MvPolynomial (Fin 4) ℚ), f ∈ ({x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3} :
        Set (MvPolynomial (Fin 4) ℚ)) → ∀ i : Fin 4, pderiv i f ∈
        Ideal.span (({x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3} : Set (MvPolynomial (Fin 4) ℚ)) ∪
          ⋃ i, pderiv i '' {x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3}) := fun f hf i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hf⟩))
    have h1 := hmem (x ^ 3 - y ^ 2) (by simp)
    have h2 := hmem (x ^ 4 + x * z ^ 2 - w ^ 3) (by simp)
    have hx2 : x ^ 2 ∈ Ideal.span (({x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3} :
        Set (MvPolynomial (Fin 4) ℚ)) ∪
          ⋃ i, pderiv i '' {x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3}) := by
      have h := h1 0
      rw [pderiv_zero_gen1] at h
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hx2
    · have h := h1 1
      rw [pderiv_one_gen1, neg_mem_iff] at h
      exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h
    · have h := h2 0
      rw [pderiv_zero_gen2] at h
      have h' := Ideal.sub_mem _ h (Ideal.mul_mem_left _ (C 4 * x) hx2)
      have e : C 4 * x ^ 3 + z ^ 2 - C 4 * x * x ^ 2 = z ^ 2 := by ring
      rwa [e] at h'
    · have h := h2 2
      rw [pderiv_two_gen2] at h
      exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h
    · have h := h2 3
      rw [pderiv_three_gen2, neg_mem_iff] at h
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h

end Derivative

section Order

theorem x_mem_m0_ex106 : x ∈ m0 := Ideal.subset_span (by simp)
theorem y_mem_m0_ex106 : y ∈ m0 := Ideal.subset_span (by simp)
theorem z_mem_m0_ex106 : z ∈ m0 := Ideal.subset_span (by simp)
theorem w_mem_m0_ex106 : w ∈ m0 := Ideal.subset_span (by simp)

/-- `y² ∉ 𝔪₀³`: differentiate twice in `y` and evaluate at the origin. -/
theorem y_sq_notMem_m0_cube : y ^ 2 ∉ m0 ^ 3 := by
  intro h
  have h1 := pderiv_mem_pow_of_mem_pow_succ 1 (a := 2) h
  have h2 := pderiv_mem_pow_of_mem_pow_succ 1 (a := 1) h1
  rw [pow_one] at h2
  have := eval_eq_zero_of_mem_span (![0, 0, 0, 0] : Fin 4 → ℚ) (by simp) h2
  simp at this

/-- `I ⊆ 𝔪₀²`. -/
theorem I106_le_m0_sq : I106 ≤ m0 ^ 2 := by
  rw [I106, Ideal.span_le]
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact Ideal.sub_mem _
      (mem_pow_of_mem_pow_of_le (k := 3) (by norm_num) (Ideal.pow_mem_pow x_mem_m0_ex106 3))
      (Ideal.pow_mem_pow y_mem_m0_ex106 2)
  · refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact mem_pow_of_mem_pow_of_le (k := 4) (by norm_num) (Ideal.pow_mem_pow x_mem_m0_ex106 4)
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow z_mem_m0_ex106 2)
    · exact mem_pow_of_mem_pow_of_le (k := 3) (by norm_num) (Ideal.pow_mem_pow w_mem_m0_ex106 3)

/-- `y² ∈ I + D(I)²`. -/
theorem y_sq_mem_tuned : y ^ 2 ∈ I106 ⊔ Ideal.derivative ℚ I106 ^ 2 := by
  rw [derivative_example106]
  exact Ideal.mem_sup_right
    (by rw [pow_two, pow_two]; exact Ideal.mul_mem_mul y_mem_D106 y_mem_D106)

/-- Kollár's "`ord I = 2`": `I` has order exactly `2` at the origin — `y² ≡ x³` modulo `I` and
`y² ∉ 𝔪₀³`. -/
theorem ord_zero_example106 : I106 ≤ m0 ^ 2 ∧ ¬ I106 ≤ m0 ^ 3 := by
  refine ⟨I106_le_m0_sq, fun h => ?_⟩
  have h0 : x ^ 3 - y ^ 2 ∈ m0 ^ 3 := h (Ideal.subset_span (by simp))
  have hx : x ^ 3 ∈ m0 ^ 3 := Ideal.pow_mem_pow x_mem_m0_ex106 3
  have : y ^ 2 = x ^ 3 - (x ^ 3 - y ^ 2) := by ring
  exact y_sq_notMem_m0_cube (this ▸ Ideal.sub_mem _ hx h0)

/-- `D(I) ⊆ 𝔪₀`. -/
theorem D106_le_m0 : D106 ≤ m0 := by
  rw [D106, Ideal.span_le]
  rintro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact Ideal.pow_mem_of_mem _ x_mem_m0_ex106 2 (by norm_num)
  · exact y_mem_m0_ex106
  · exact Ideal.pow_mem_of_mem _ z_mem_m0_ex106 2 (by norm_num)
  · exact Ideal.mul_mem_right _ _ x_mem_m0_ex106
  · exact Ideal.pow_mem_of_mem _ w_mem_m0_ex106 2 (by norm_num)

/-- The tuned ideal `W(I) = I + D(I)²` has order exactly `2` at the origin. -/
theorem ord_zero_tuned_example106 :
    I106 ⊔ Ideal.derivative ℚ I106 ^ 2 ≤ m0 ^ 2 ∧
      ¬ I106 ⊔ Ideal.derivative ℚ I106 ^ 2 ≤ m0 ^ 3 := by
  refine ⟨?_, fun h => y_sq_notMem_m0_cube (h y_sq_mem_tuned)⟩
  rw [derivative_example106]
  exact sup_le I106_le_m0_sq (Ideal.pow_right_mono D106_le_m0 2)

/-- `cosupp(I, 2) = V(D(I))` has the origin as its only `ℚ`-point. -/
theorem cosupport_example106 (a b c d : ℚ)
    (h : ∀ g ∈ Ideal.derivative ℚ I106, eval ![a, b, c, d] g = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  rw [derivative_example106] at h
  have ha : a ^ 2 = 0 := by simpa using h (x ^ 2) x_sq_mem_D106
  have hb : b = 0 := by simpa using h y y_mem_D106
  have hc : c ^ 2 = 0 := by simpa using h (z ^ 2) z_sq_mem_D106
  have hd : d ^ 2 = 0 := by simpa using h (w ^ 2) w_sq_mem_D106
  exact ⟨pow_eq_zero_iff two_ne_zero |>.mp ha, hb, pow_eq_zero_iff two_ne_zero |>.mp hc,
    pow_eq_zero_iff two_ne_zero |>.mp hd⟩

end Order

section Negative

/-- `y² ∉ I`: at `(1, 1, 0, 1)`, a common zero of `x³ − y²` and `x⁴ + xz² − w³`, `y²` evaluates
to `1`. -/
theorem y_sq_notMem_I106 : y ^ 2 ∉ I106 := by
  intro h
  have := eval_eq_zero_of_mem_span (![1, 1, 0, 1] : Fin 4 → ℚ) (by simp) h
  simp at this

/-- `I` is not D-balanced with respect to `2`. -/
theorem not_isDBalanced_example106 : ¬ Ideal.IsDBalanced ℚ I106 2 := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero,
    derivative_example106] at h1
  exact y_sq_notMem_I106
    (h1 (by rw [pow_two, pow_two]; exact Ideal.mul_mem_mul y_mem_D106 y_mem_D106))

/-- `I` is not MC-invariant with respect to `2`. -/
theorem not_mcInvariant_example106 :
    ¬ (Ideal.derivative ℚ I106 * Ideal.derivative ℚ I106 ≤ I106) := by
  intro h
  rw [derivative_example106] at h
  exact y_sq_notMem_I106 (h (by rw [pow_two]; exact Ideal.mul_mem_mul y_mem_D106 y_mem_D106))

end Negative

end Hironaka.Examples.Example106
