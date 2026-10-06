/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 106, the first blow-up: the restriction to `H` and the four charts

[Kol07, Example 106]: `I = (x³ − y², x⁴ + xz² − w³) ⊂ ℚ[x, y, z, w]`, `m = 2`, `H = (y = 0)` a
hypersurface of maximal contact (`y ∈ MC(I) = D(I)`, `derivative_example106` in
`HironakaExamples/Balanced/Example106.lean`), `H' = (y − x²)` a second one. Computed exactly in `ℚ`:

* `I|_H = (x³, xz² − w³)` in `ℚ[x, z, w]` has order `3` at the origin and `D²(I|_H) = (x, z, w)`,
  as Kollár says;
* on the `x`-chart of the blow-up of the origin, `I₁ = (x₁ − y₁², x₁(x₁ + z₁² − w₁³))`, Kollár's
  display, has no point of order `2` (`∂(x₁ − y₁²)/∂x₁ = 1`), and `I₁ + (x₁) = (x₁, y₁²)`, which
  gives Kollár's second centre `(x₁ = y₁ = 0)` of the order-`1` run;
* the `y`- and `w`-charts have no point of order `2`;
* on the `z`-chart, `I₁ = (x₁³z₁ − y₁², z₁(x₁⁴z₁ + x₁ − w₁³))` has order exactly `2` at the origin
  `q = [0:0:1:0] ∈ E₁`, which is its only `ℚ`-point of order `≥ 2`, and `y₁, y₁ − x₁²z₁ ∈ MC(I₁)`.
  This corrects Kollár's sentence "the order has dropped to 1", which holds on the `x`-chart but
  not on the `z`-chart: the order-`2` run of Example 106 continues at `q`
  (`HironakaExamples/MaximalContact/Example106Stages.lean`).

Tools: orders at a `ℚ`-point `p` are memberships in powers of `𝔪_p`; from `g ∈ 𝔪_p²` the value
and the first partials of `g` vanish at `p` (`pderiv_mem_pow_of_mem_pow_succ`,
`eval_eq_zero_of_mem_span`), and the resulting rational equations are solved by cases.
-/

public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples

section Tools

variable {σ : Type*} [Finite σ]

/-- `D(⟨S⟩) ≤ 𝔪^k` when every element of `S` lies in `𝔪^{k+1}`: the generators stay, the partials
drop one power (the Leibniz rule). -/
theorem derivative_span_le_pow {S : Set (MvPolynomial σ ℚ)} {N : Ideal (MvPolynomial σ ℚ)}
    {k : ℕ} (h : ∀ s ∈ S, s ∈ N ^ (k + 1)) : Ideal.derivative ℚ (Ideal.span S) ≤ N ^ k := by
  rw [derivative_span_pderiv, Ideal.span_le]
  rintro t (ht | ht)
  · exact mem_pow_of_mem_pow_of_le (Nat.le_succ k) (h t ht)
  · simp only [Set.mem_iUnion, Set.mem_image] at ht
    obtain ⟨i, s, hs, rfl⟩ := ht
    exact pderiv_mem_pow_of_mem_pow_succ i (h s hs)

/-- `D²(⟨S⟩) ≤ 𝔪^k` when every element of `S` lies in `𝔪^{k+2}`. -/
theorem derivativeIter_two_span_le_pow {S : Set (MvPolynomial σ ℚ)} {N : Ideal (MvPolynomial σ ℚ)}
    {k : ℕ} (h : ∀ s ∈ S, s ∈ N ^ (k + 2)) :
    Ideal.derivativeIter ℚ 2 (Ideal.span S) ≤ N ^ k := by
  change Ideal.derivativeIter ℚ (1 + 1) _ ≤ _
  rw [Ideal.derivativeIter_succ, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero,
    derivative_span_pderiv]
  refine derivative_span_le_pow ?_
  rintro t (ht | ht)
  · exact mem_pow_of_mem_pow_of_le (Nat.le_succ _) (h t ht)
  · simp only [Set.mem_iUnion, Set.mem_image] at ht
    obtain ⟨i, s, hs, rfl⟩ := ht
    exact pderiv_mem_pow_of_mem_pow_succ i (h s hs)

omit [Finite σ] in
/-- A partial derivative of a member of an ideal lies in its derivative ideal. -/
theorem pderiv_mem_derivative {J : Ideal (MvPolynomial σ ℚ)} (i : σ) {g : MvPolynomial σ ℚ}
    (hg : g ∈ J) : pderiv i g ∈ Ideal.derivative ℚ J :=
  Ideal.derivation_apply_mem_derivative ((pderiv i).restrictScalars ℚ) hg

end Tools

section ToolsFour

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)

/-- Members of `𝔪_p = (x − a, y − b, z − c, w − d)` vanish at `p = (a, b, c, d)`. -/
theorem eval_eq_zero_of_mem_m4 (a b c d : ℚ) {g : MvPolynomial (Fin 4) ℚ}
    (hg : g ∈ Ideal.span {x - C a, y - C b, z - C c, w - C d}) : eval ![a, b, c, d] g = 0 := by
  refine eval_eq_zero_of_mem_span _ ?_ hg
  rintro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl <;> simp

/-- Order `≥ 2` at `p`: the value and the four partial derivatives vanish at `p`. -/
theorem vanish_of_mem_m4_sq (a b c d : ℚ) {g : MvPolynomial (Fin 4) ℚ}
    (hg : g ∈ Ideal.span {x - C a, y - C b, z - C c, w - C d} ^ 2) :
    eval ![a, b, c, d] g = 0 ∧ ∀ i, eval ![a, b, c, d] (pderiv i g) = 0 := by
  refine ⟨eval_eq_zero_of_mem_m4 a b c d ?_, fun i => eval_eq_zero_of_mem_m4 a b c d ?_⟩
  · have := mem_pow_of_mem_pow_of_le one_le_two hg
    rwa [pow_one] at this
  · have := pderiv_mem_pow_of_mem_pow_succ i (a := 1) hg
    rwa [pow_one] at this

/-- Order `≥ 3` at the origin excluded by a nonzero second partial: if `g ∈ 𝔪₀³` then every second
partial derivative of `g` vanishes at `0`. -/
theorem eval_pderiv_pderiv_eq_zero_of_mem_m0_cube {g : MvPolynomial (Fin 4) ℚ}
    (hg : g ∈ Ideal.span {x, y, z, w} ^ 3) (i j : Fin 4) :
    eval ![(0 : ℚ), 0, 0, 0] (pderiv j (pderiv i g)) = 0 := by
  have h1 := pderiv_mem_pow_of_mem_pow_succ i (a := 2) hg
  have h2 := pderiv_mem_pow_of_mem_pow_succ j (a := 1) h1
  rw [pow_one] at h2
  have hgen : ∀ s ∈ ({x, y, z, w} : Set (MvPolynomial (Fin 4) ℚ)),
      eval ![(0 : ℚ), 0, 0, 0] s = 0 := by
    rintro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp
  exact eval_eq_zero_of_mem_span _ hgen h2

/-- `x ∈ (x, y, z, w)` in `ℚ[x, y, z, w]`. -/
theorem x_mem_m0_fin4 : x ∈ Ideal.span {x, y, z, w} := Ideal.subset_span (by simp)
/-- `y ∈ (x, y, z, w)`. -/
theorem y_mem_m0_fin4 : y ∈ Ideal.span {x, y, z, w} := Ideal.subset_span (by simp)
/-- `z ∈ (x, y, z, w)`. -/
theorem z_mem_m0_fin4 : z ∈ Ideal.span {x, y, z, w} := Ideal.subset_span (by simp)
/-- `w ∈ (x, y, z, w)`. -/
theorem w_mem_m0_fin4 : w ∈ Ideal.span {x, y, z, w} := Ideal.subset_span (by simp)

end ToolsFour

namespace Example106Charts

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z = X 2`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)
/-- The `x`-chart. -/
local notation "σx" => (aeval ![X 0, X 1 * X 0, X 2 * X 0, X 3 * X 0] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `y`-chart. -/
local notation "σy" => (aeval ![X 0 * X 1, X 1, X 2 * X 1, X 3 * X 1] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `z`-chart. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2, X 3 * X 2] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The `w`-chart. -/
local notation "σw" => (aeval ![X 0 * X 3, X 1 * X 3, X 2 * X 3, X 3] :
  MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 4) ℚ)
/-- The maximal ideal of the `ℚ`-point `(a, b, c, d)`. -/
local notation "𝔪(" a ", " b ", " c ", " d ")" =>
  Ideal.span {x - C a, y - C b, z - C c, w - C d}


/-! ### The restriction to `H = (y = 0)` -/

section Restriction

/-- `x = X 0` in `ℚ[x, z, w]`. -/
local notation "xR" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 1` in `ℚ[x, z, w]`. -/
local notation "zR" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `w = X 2` in `ℚ[x, z, w]`. -/
local notation "wR" => (X 2 : MvPolynomial (Fin 3) ℚ)

/-- Kollár's "`I|_H = (x³, xz² − w³)`": the image of `I` under `y ↦ 0`. -/
theorem map_example106_H :
    (Ideal.span {x ^ 3 - y ^ 2, x ^ 4 + x * z ^ 2 - w ^ 3}).map
        (aeval ![X 0, 0, X 1, X 2] : MvPolynomial (Fin 4) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ) =
      Ideal.span {xR ^ 3, xR * zR ^ 2 - wR ^ 3} := by
  rw [Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton, map_sub, map_add, map_mul, map_pow,
    aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, zero_pow two_ne_zero, sub_zero]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · have : xR ^ 4 + xR * zR ^ 2 - wR ^ 3 = xR * xR ^ 3 + (xR * zR ^ 2 - wR ^ 3) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · have : xR * zR ^ 2 - wR ^ 3 = (xR ^ 4 + xR * zR ^ 2 - wR ^ 3) - xR * xR ^ 3 := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.subset_span (by simp))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))


/-- Kollár's "`I|_H` has order `3`": order exactly `3` at the origin of `ℚ[x, z, w]`. -/
theorem ord_zero_map_example106_H :
    Ideal.span {xR ^ 3, xR * zR ^ 2 - wR ^ 3} ≤ Ideal.span {xR, zR, wR} ^ 3 ∧
      ¬ Ideal.span {xR ^ 3, xR * zR ^ 2 - wR ^ 3} ≤ Ideal.span {xR, zR, wR} ^ 4 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ideal.pow_mem_pow x_mem_m0 3
    · refine Ideal.sub_mem _ ?_ (Ideal.pow_mem_pow z_mem_m0 3)
      refine mem_pow_of_mem_pow_of_le (k := 1 + 2) le_rfl (mul_mem_pow_add ?_ ?_)
      · rw [pow_one]; exact x_mem_m0
      · exact Ideal.pow_mem_pow y_mem_m0 2
  · have h0 : xR * zR ^ 2 - wR ^ 3 ∈ Ideal.span {xR, zR, wR} ^ (3 + 1) :=
      h (Ideal.subset_span (by simp))
    have h1 := pderiv_mem_pow_of_mem_pow_succ 2 h0
    have h2 := pderiv_mem_pow_of_mem_pow_succ 2 h1
    have h3 := pderiv_mem_pow_of_mem_pow_succ 2 (a := 1) h2
    rw [pow_one] at h3
    have := eval_eq_zero_of_mem_span (![0, 0, 0] : Fin 3 → ℚ) (by simp) h3
    simp at this

/-- Kollár's "`MC(I|_H) = (x, z, w)`": `D²(I|_H) = (x, z, w)`. -/
theorem derivativeIter_map_example106_H :
    Ideal.derivativeIter ℚ 2 (Ideal.span {xR ^ 3, xR * zR ^ 2 - wR ^ 3}) =
      Ideal.span {xR, zR, wR} := by
  apply le_antisymm
  · have := derivativeIter_two_span_le_pow (N := Ideal.span {xR, zR, wR}) (k := 1)
      (S := {xR ^ 3, xR * zR ^ 2 - wR ^ 3}) (fun s hs => (ord_zero_map_example106_H.1
        (Ideal.subset_span hs)))
    rwa [pow_one] at this
  · have hD : ∀ (K : Ideal (MvPolynomial (Fin 3) ℚ)) (i : Fin 3) {g : MvPolynomial (Fin 3) ℚ},
        g ∈ K → pderiv i g ∈ Ideal.derivative ℚ K := fun K i g hg => pderiv_mem_derivative i hg
    change _ ≤ Ideal.derivativeIter ℚ (1 + 1) _
    rw [Ideal.derivativeIter_succ, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero]
    have hg1 : xR ^ 3 ∈ Ideal.span {xR ^ 3, xR * zR ^ 2 - wR ^ 3} := Ideal.subset_span (by simp)
    have hg2 : xR * zR ^ 2 - wR ^ 3 ∈ Ideal.span {xR ^ 3, xR * zR ^ 2 - wR ^ 3} :=
      Ideal.subset_span (by simp)
    have hxx : pderiv 0 (pderiv 0 (xR ^ 3)) = C 6 * xR := by simp [map_ofNat]; ring
    have hzx : pderiv 0 (pderiv 1 (xR * zR ^ 2 - wR ^ 3)) = C 2 * zR := by simp [map_ofNat]
    have hww : pderiv 2 (pderiv 2 (xR * zR ^ 2 - wR ^ 3)) = -(C 6 * wR) := by
      simp [map_ofNat]; ring
    rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · have h := hD _ 0 (hD _ 0 hg1)
      rw [hxx] at h
      exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h
    · have h := hD _ 0 (hD _ 1 hg2)
      rw [hzx] at h
      exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h
    · have h := hD _ 2 (hD _ 2 hg2)
      rw [hww, neg_mem_iff] at h
      exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h

end Restriction

/-! ### The `x`-chart -/

/-- The marked transforms on the `x`-chart. -/
theorem transform_example106_x :
    σx (x ^ 3 - y ^ 2) = x ^ 2 * (x - y ^ 2) ∧
      σx (x ^ 4 + x * z ^ 2 - w ^ 3) = x ^ 2 * (x * (x + z ^ 2 - w ^ 3)) ∧
      σx y = x * y ∧ σx (y - x ^ 2) = x * (y - x) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `x`-chart: `∂(x₁ − y₁²)/∂x₁ = 1`. -/
theorem empty_example106_x (a b c d : ℚ) :
    ¬ Ideal.span {x - y ^ 2, x * (x + z ^ 2 - w ^ 3)} ≤ 𝔪(a, b, c, d) ^ 2 := by
  intro h
  have h1 := (vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x - y ^ 2 ∈ _)).2 0
  simp at h1

/-- Kollár's "`I₁|_{E₁} = (x₁, y₁²)`": `I₁ + (x₁) = (x₁, y₁²)`. -/
theorem sup_example106_x_E :
    Ideal.span {x - y ^ 2, x * (x + z ^ 2 - w ^ 3)} ⊔ Ideal.span {x} =
      Ideal.span {x, y ^ 2} := by
  apply le_antisymm
  · refine sup_le ?_ ?_ <;> rw [Ideal.span_le] <;> rintro g hg <;>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    · rcases hg with rfl | rfl
      · exact Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · subst hg
      exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
    · have : y ^ 2 = x - (x - y ^ 2) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
        (Ideal.mem_sup_left (Ideal.subset_span (by simp)))

/-! ### The `y`-chart -/

/-- The marked transforms on the `y`-chart. -/
theorem transform_example106_y :
    σy (x ^ 3 - y ^ 2) = y ^ 2 * (x ^ 3 * y - 1) ∧
      σy (x ^ 4 + x * z ^ 2 - w ^ 3) = y ^ 2 * (y * (x ^ 4 * y + x * z ^ 2 - w ^ 3)) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `y`-chart: `x₁³y₁ − 1` and its `x₁`-partial `3x₁²y₁` cannot both
vanish. -/
theorem empty_example106_y (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 3 * y - 1, y * (x ^ 4 * y + x * z ^ 2 - w ^ 3)} ≤ 𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨hv, hd⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * y - 1 ∈ _)
  have hv' : a ^ 3 * b - 1 = 0 := by simpa using hv
  have h0 : b = 0 ∨ a = 0 := by simpa using hd 0
  rcases h0 with hb | ha
  · subst hb; simp at hv'
  · subst ha; simp at hv'

/-! ### The `z`-chart: the point of order `2` -/

/-- The marked transforms on the `z`-chart and the strict transforms of `H`, `H'`. -/
theorem transform_example106_z :
    σz (x ^ 3 - y ^ 2) = z ^ 2 * (x ^ 3 * z - y ^ 2) ∧
      σz (x ^ 4 + x * z ^ 2 - w ^ 3) = z ^ 2 * (z * (x ^ 4 * z + x - w ^ 3)) ∧
      σz y = z * y ∧ σz (y - x ^ 2) = z * (y - x ^ 2 * z) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- `ord_q I₁ = 2`: `I₁` has order exactly `2` at the origin of the `z`-chart. -/
theorem ord_zero_example106_z :
    Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)} ≤ Ideal.span {x, y, z, w} ^ 2 ∧
      ¬ Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)} ≤
        Ideal.span {x, y, z, w} ^ 3 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine Ideal.sub_mem _ ?_ (Ideal.pow_mem_pow y_mem_m0_fin4 2)
      refine mem_pow_of_mem_pow_of_le (k := 3 + 1) (by norm_num) (mul_mem_pow_add ?_ ?_)
      · exact Ideal.pow_mem_pow x_mem_m0_fin4 3
      · rw [pow_one]; exact z_mem_m0_fin4
    · have : z * (x ^ 4 * z + x - w ^ 3) = x ^ 4 * z ^ 2 + x * z - w ^ 3 * z := by ring
      rw [this]
      refine Ideal.sub_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · refine mem_pow_of_mem_pow_of_le (k := 4 + 2) (by norm_num) (mul_mem_pow_add ?_ ?_)
        · exact Ideal.pow_mem_pow x_mem_m0_fin4 4
        · exact Ideal.pow_mem_pow z_mem_m0_fin4 2
      · refine mem_pow_of_mem_pow_of_le (k := 1 + 1) le_rfl (mul_mem_pow_add ?_ ?_) <;>
          rw [pow_one]
        · exact x_mem_m0_fin4
        · exact z_mem_m0_fin4
      · refine mem_pow_of_mem_pow_of_le (k := 3 + 1) (by norm_num) (mul_mem_pow_add ?_ ?_)
        · exact Ideal.pow_mem_pow w_mem_m0_fin4 3
        · rw [pow_one]; exact z_mem_m0_fin4
  · have := eval_pderiv_pderiv_eq_zero_of_mem_m0_cube (h (Ideal.subset_span (by simp)) :
      x ^ 3 * z - y ^ 2 ∈ _) 1 1
    simp at this

/-- `cosupp(I₁, 2) = {q}`: the only `ℚ`-point of order `≥ 2` on the `z`-chart is its origin. -/
theorem cosupport_example106_z (a b c d : ℚ)
    (h : Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)} ≤ 𝔪(a, b, c, d) ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * z - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    z * (x ^ 4 * z + x - w ^ 3) ∈ _)
  have hb : b = 0 := by simpa using hd1 1
  have ha : a = 0 := by simpa using hd1 2
  subst ha hb
  have hc : c = 0 := by simpa using hd2 0
  subst hc
  have hd : d = 0 := by simpa using hd2 2
  exact ⟨rfl, rfl, rfl, hd⟩

/-- `q ∈ H₁`: `y₁ ∈ MC(I₁) = D(I₁)`, from `∂(x₁³z₁ − y₁²)/∂y₁ = −2y₁`. -/
theorem mem_derivative_example106_z_H :
    y ∈ Ideal.derivative ℚ (Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)}) := by
  have h := pderiv_mem_derivative (σ := Fin 4) 1
    (Ideal.subset_span (by simp) : x ^ 3 * z - y ^ 2 ∈ Ideal.span {x ^ 3 * z - y ^ 2,
      z * (x ^ 4 * z + x - w ^ 3)})
  have e : pderiv 1 (x ^ 3 * z - y ^ 2) = -(C 2 * y) := by simp [map_ofNat]
  rw [e, neg_mem_iff] at h
  exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h

/-- `q ∈ H₁'`: `y₁ − x₁²z₁ ∈ MC(I₁)`, with `∂(x₁³z₁ − y₁²)/∂x₁ = 3x₁²z₁`. -/
theorem mem_derivative_example106_z_H' :
    y - x ^ 2 * z ∈
      Ideal.derivative ℚ (Ideal.span {x ^ 3 * z - y ^ 2, z * (x ^ 4 * z + x - w ^ 3)}) := by
  refine Ideal.sub_mem _ mem_derivative_example106_z_H ?_
  have h := pderiv_mem_derivative (σ := Fin 4) 0
    (Ideal.subset_span (by simp) : x ^ 3 * z - y ^ 2 ∈ Ideal.span {x ^ 3 * z - y ^ 2,
      z * (x ^ 4 * z + x - w ^ 3)})
  have e : pderiv 0 (x ^ 3 * z - y ^ 2) = C 3 * (x ^ 2 * z) := by simp [map_ofNat]; ring
  rw [e] at h
  exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h

/-! ### The `w`-chart -/

/-- The marked transforms on the `w`-chart. -/
theorem transform_example106_w :
    σw (x ^ 3 - y ^ 2) = w ^ 2 * (x ^ 3 * w - y ^ 2) ∧
      σw (x ^ 4 + x * z ^ 2 - w ^ 3) = w ^ 2 * (w * (x ^ 4 * w + x * z ^ 2 - 1)) := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three]
    ring

/-- No point of order `2` on the `w`-chart: at a point of order `≥ 2`, `∂(x₁³w₁ − y₁²)/∂w₁ = x₁³`
forces `x₁ = 0`, and then `∂(w₁(x₁⁴w₁ + x₁z₁² − 1))/∂w₁ = 2x₁⁴w₁ + x₁z₁² − 1 = −1`. -/
theorem empty_example106_w (a b c d : ℚ) :
    ¬ Ideal.span {x ^ 3 * w - y ^ 2, w * (x ^ 4 * w + x * z ^ 2 - 1)} ≤ 𝔪(a, b, c, d) ^ 2 := by
  intro h
  obtain ⟨-, hd1⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    x ^ 3 * w - y ^ 2 ∈ _)
  obtain ⟨-, hd2⟩ := vanish_of_mem_m4_sq a b c d (h (Ideal.subset_span (by simp)) :
    w * (x ^ 4 * w + x * z ^ 2 - 1) ∈ _)
  have ha : a = 0 := by simpa using hd1 3
  subst ha
  have hw2 := hd2 3
  simp at hw2

end Example106Charts

end Hironaka.Examples
