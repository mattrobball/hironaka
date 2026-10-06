/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.Example11
import HironakaExamples.Balanced.PDeriv
import HironakaExamples.MaximalContact.Example106Charts
import HironakaExamples.MaximalContact.Example82
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 11: the two hypersurfaces of maximal contact and the first blow-up

[Kol07, Example 11]: `S = (x² + y³ − z⁶ = 0) ⊂ 𝔸³`, `m = 2`, `H = (x)`, and a second hypersurface
of maximal contact `H' = (x + y²)`. Computed exactly in `ℚ[x, y, z]` (`MC(I) = D(I) = (x, y², z⁵)`
and `cosupp(I, 2) = {0}` are `derivative_example11` and `cosupport_example11` of
`HironakaExamples/Balanced/Example11.lean`):

* `x`, `x + y² ∈ D(I)`; the restrictions `I|_H = (z⁶ − y³)` (Kollár's trace of multiplicity `3`)
  and `I|_{H'} = (z⁶ − y⁴ − y³)` have `MC = (y², z⁵)`, and the origin is their only point of
  order `2`;
* the blow-up of the origin: the `x`- and `y`-charts have no point of order `2`. The `z`-chart,
  which carries the whole locus of order `2`, and the second blow-up are in
  `HironakaExamples/MaximalContact/Example11Stages.lean`.

Tools: orders at a `ℚ`-point `p` of `𝔸²` or `𝔸³` are memberships in powers of `𝔪_p`, and from
`g ∈ 𝔪_p^{k+1}` the partial derivatives of `g` of order `≤ k` vanish at `p`
(`vanish_of_mem_m3_sq`, `vanish_of_mem_m3_cube` and the `𝔸²` versions); the resulting rational
equations are solved by cases.
-/

public section

open MvPolynomial Hironaka.Examples

namespace Hironaka.Examples

section ToolsThreeTwo

/-- Members of `𝔪_p = (X 0 − a, X 1 − b, X 2 − c)` vanish at `p`. -/
theorem eval_eq_zero_of_mem_m3 (a b c : ℚ) {g : MvPolynomial (Fin 3) ℚ}
    (hg : g ∈ Ideal.span {X 0 - C a, X 1 - C b, X 2 - C c}) : eval ![a, b, c] g = 0 := by
  refine eval_eq_zero_of_mem_span _ ?_ hg
  rintro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl <;> simp

/-- Order `≥ 2` at `p ∈ 𝔸³`: the value and the first partials vanish at `p`. -/
theorem vanish_of_mem_m3_sq (a b c : ℚ) {g : MvPolynomial (Fin 3) ℚ}
    (hg : g ∈ Ideal.span {X 0 - C a, X 1 - C b, X 2 - C c} ^ 2) :
    eval ![a, b, c] g = 0 ∧ ∀ i, eval ![a, b, c] (pderiv i g) = 0 := by
  refine ⟨eval_eq_zero_of_mem_m3 a b c ?_, fun i => eval_eq_zero_of_mem_m3 a b c ?_⟩
  · have := mem_pow_of_mem_pow_of_le one_le_two hg
    rwa [pow_one] at this
  · have := pderiv_mem_pow_of_mem_pow_succ i (a := 1) hg
    rwa [pow_one] at this

/-- Order `≥ 3` at `p ∈ 𝔸³`: the value, the first and the second partials vanish at `p`. -/
theorem vanish_of_mem_m3_cube (a b c : ℚ) {g : MvPolynomial (Fin 3) ℚ}
    (hg : g ∈ Ideal.span {X 0 - C a, X 1 - C b, X 2 - C c} ^ 3) :
    eval ![a, b, c] g = 0 ∧ (∀ i, eval ![a, b, c] (pderiv i g) = 0) ∧
      ∀ i j, eval ![a, b, c] (pderiv j (pderiv i g)) = 0 := by
  have h2 : g ∈ Ideal.span {X 0 - C a, X 1 - C b, X 2 - C c} ^ 2 :=
    mem_pow_of_mem_pow_of_le (by norm_num) hg
  refine ⟨(vanish_of_mem_m3_sq a b c h2).1, (vanish_of_mem_m3_sq a b c h2).2, fun i j => ?_⟩
  have h1 := pderiv_mem_pow_of_mem_pow_succ i (a := 2) hg
  have h0 := pderiv_mem_pow_of_mem_pow_succ j (a := 1) h1
  rw [pow_one] at h0
  exact eval_eq_zero_of_mem_m3 a b c h0

/-- Members of `𝔪_p = (X 0 − b, X 1 − c)` vanish at `p ∈ 𝔸²`. -/
theorem eval_eq_zero_of_mem_m2 (b c : ℚ) {g : MvPolynomial (Fin 2) ℚ}
    (hg : g ∈ Ideal.span {X 0 - C b, X 1 - C c}) : eval ![b, c] g = 0 := by
  refine eval_eq_zero_of_mem_span _ ?_ hg
  rintro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl <;> simp

/-- Order `≥ 2` at `p ∈ 𝔸²`: the value and the first partials vanish at `p`. -/
theorem vanish_of_mem_m2_sq (b c : ℚ) {g : MvPolynomial (Fin 2) ℚ}
    (hg : g ∈ Ideal.span {X 0 - C b, X 1 - C c} ^ 2) :
    eval ![b, c] g = 0 ∧ ∀ i, eval ![b, c] (pderiv i g) = 0 := by
  refine ⟨eval_eq_zero_of_mem_m2 b c ?_, fun i => eval_eq_zero_of_mem_m2 b c ?_⟩
  · have := mem_pow_of_mem_pow_of_le one_le_two hg
    rwa [pow_one] at this
  · have := pderiv_mem_pow_of_mem_pow_succ i (a := 1) hg
    rwa [pow_one] at this

/-- Order `≥ 3` at `p ∈ 𝔸²`: the value, the first and the second partials vanish at `p`. -/
theorem vanish_of_mem_m2_cube (b c : ℚ) {g : MvPolynomial (Fin 2) ℚ}
    (hg : g ∈ Ideal.span {X 0 - C b, X 1 - C c} ^ 3) :
    eval ![b, c] g = 0 ∧ (∀ i, eval ![b, c] (pderiv i g) = 0) ∧
      ∀ i j, eval ![b, c] (pderiv j (pderiv i g)) = 0 := by
  have h2 : g ∈ Ideal.span {X 0 - C b, X 1 - C c} ^ 2 :=
    mem_pow_of_mem_pow_of_le (by norm_num) hg
  refine ⟨(vanish_of_mem_m2_sq b c h2).1, (vanish_of_mem_m2_sq b c h2).2, fun i j => ?_⟩
  have h1 := pderiv_mem_pow_of_mem_pow_succ i (a := 2) hg
  have h0 := pderiv_mem_pow_of_mem_pow_succ j (a := 1) h1
  rw [pow_one] at h0
  exact eval_eq_zero_of_mem_m2 b c h0

/-- Order `≥ 3` at `p ∈ 𝔸²` excluded by a nonzero second partial at `p`, the origin version:
`g ∈ 𝔪₀³` kills every second partial at `0`. -/
theorem eval_pderiv_pderiv_eq_zero_of_mem_m2_zero_cube {g : MvPolynomial (Fin 2) ℚ}
    (hg : g ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ), X 1} ^ 3) (i j : Fin 2) :
    eval ![(0 : ℚ), 0] (pderiv j (pderiv i g)) = 0 := by
  have h : g ∈ Ideal.span {X 0 - C (0 : ℚ), X 1 - C (0 : ℚ)} ^ 3 := by simpa using hg
  exact (vanish_of_mem_m2_cube 0 0 h).2.2 i j

/-- The same for `𝔸³`. -/
theorem eval_pderiv_pderiv_eq_zero_of_mem_m3_zero_cube {g : MvPolynomial (Fin 3) ℚ}
    (hg : g ∈ Ideal.span {(X 0 : MvPolynomial (Fin 3) ℚ), X 1, X 2} ^ 3) (i j : Fin 3) :
    eval ![(0 : ℚ), 0, 0] (pderiv j (pderiv i g)) = 0 := by
  have h : g ∈ Ideal.span {X 0 - C (0 : ℚ), X 1 - C (0 : ℚ), X 2 - C (0 : ℚ)} ^ 3 := by
    simpa using hg
  exact (vanish_of_mem_m3_cube 0 0 0 h).2.2 i j

/-- `g ∈ 𝔪₀⁴` in `𝔸²` kills every third partial derivative of `g` at `0`. -/
theorem eval_pderiv3_eq_zero_of_mem_m2_zero_pow4 {g : MvPolynomial (Fin 2) ℚ}
    (hg : g ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ), X 1} ^ 4) (i j l : Fin 2) :
    eval ![(0 : ℚ), 0] (pderiv l (pderiv j (pderiv i g))) = 0 := by
  have h : g ∈ Ideal.span {X 0 - C (0 : ℚ), X 1 - C (0 : ℚ)} ^ 4 := by simpa using hg
  have h1 := pderiv_mem_pow_of_mem_pow_succ i (a := 3) h
  have h2 := pderiv_mem_pow_of_mem_pow_succ j (a := 2) h1
  have h3 := pderiv_mem_pow_of_mem_pow_succ l (a := 1) h2
  rw [pow_one] at h3
  exact eval_eq_zero_of_mem_m2 0 0 h3

/-- `X 0 ∈ (X 0, X 1)` in `ℚ[y, z]`, the coordinate ring of a hypersurface `H ⊂ 𝔸³`. -/
theorem yR_mem_m0_fin2 : (X 0 : MvPolynomial (Fin 2) ℚ) ∈ Ideal.span {X 0, X 1} :=
  Ideal.subset_span (by simp)

/-- `X 1 ∈ (X 0, X 1)` in `ℚ[y, z]`. -/
theorem zR_mem_m0_fin2 : (X 1 : MvPolynomial (Fin 2) ℚ) ∈ Ideal.span {X 0, X 1} :=
  Ideal.subset_span (by simp)

end ToolsThreeTwo

namespace Example11Charts

/-- `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 1`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- `z = X 2`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)
/-- `y = X 0` in `ℚ[y, z]`. -/
local notation "yR" => (X 0 : MvPolynomial (Fin 2) ℚ)
/-- `z = X 1` in `ℚ[y, z]`. -/
local notation "zR" => (X 1 : MvPolynomial (Fin 2) ℚ)
/-- The `x`-chart. -/
local notation "σx" => (aeval ![X 0, X 1 * X 0, X 2 * X 0] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- The `y`-chart. -/
local notation "σy" => (aeval ![X 0 * X 1, X 1, X 2 * X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- The `z`-chart. -/
local notation "σz" => (aeval ![X 0 * X 2, X 1 * X 2, X 2] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ)
/-- Restriction to `(x = 0)` into `ℚ[y, z]`. -/
local notation "ρH" => (aeval ![0, X 0, X 1] :
  MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)


/-! ### The two hypersurfaces and the restrictions -/

/-- `x ∈ D(I)`, from `∂f/∂x = 2x`: `H = (x)` is a hypersurface of maximal contact. -/
theorem mem_derivative_example11_H :
    x ∈ Ideal.derivative ℚ (Ideal.span {x ^ 2 + y ^ 3 - z ^ 6}) := by
  have h := pderiv_mem_derivative (σ := Fin 3) 0
    (Ideal.mem_span_singleton_self (x ^ 2 + y ^ 3 - z ^ 6))
  rw [Example11.pderiv_zero_ex11] at h
  exact mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero h

/-- `x + y² ∈ D(I)`, from `∂f/∂y = 3y²`: `H' = (x + y²)` is a hypersurface of maximal contact. -/
theorem mem_derivative_example11_H' :
    x + y ^ 2 ∈ Ideal.derivative ℚ (Ideal.span {x ^ 2 + y ^ 3 - z ^ 6}) := by
  refine Ideal.add_mem _ mem_derivative_example11_H ?_
  have h := pderiv_mem_derivative (σ := Fin 3) 1
    (Ideal.mem_span_singleton_self (x ^ 2 + y ^ 3 - z ^ 6))
  rw [Example11.pderiv_one_ex11] at h
  exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h

/-- `I|_H = (z⁶ − y³)`. -/
theorem map_example11_H :
    (Ideal.span {x ^ 2 + y ^ 3 - z ^ 6}).map ρH = Ideal.span {zR ^ 6 - yR ^ 3} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, zero_pow two_ne_zero, zero_add]
  rw [show zR ^ 6 - yR ^ 3 = -(yR ^ 3 - zR ^ 6) by ring, Ideal.span_singleton_neg]

/-- `MC(I|_H) = D(z⁶ − y³) = (y², z⁵)`. -/
theorem derivative_map_example11_H :
    Ideal.derivative ℚ (Ideal.span {zR ^ 6 - yR ^ 3}) = Ideal.span {yR ^ 2, zR ^ 5} := by
  have h0 : pderiv 0 (zR ^ 6 - yR ^ 3) = -(C 3 * yR ^ 2) := by simp [map_ofNat]
  have h1 : pderiv 1 (zR ^ 6 - yR ^ 3) = C 6 * zR ^ 5 := by simp [map_ofNat]
  rw [derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      have : zR ^ 6 - yR ^ 3 = zR * zR ^ 5 - yR * yR ^ 2 := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', rfl, rfl⟩ := hg
      match i with
      | 0 => rw [h0]; exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      | 1 => rw [h1]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ i : Fin 2, pderiv i (zR ^ 6 - yR ^ 3) ∈
        Ideal.span ({zR ^ 6 - yR ^ 3} ∪ ⋃ i, pderiv i '' {zR ^ 6 - yR ^ 3}) := fun i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ rfl⟩))
    rcases hg with rfl | rfl
    · have h := hmem 0
      rw [h0, neg_mem_iff] at h
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero h
    · have h := hmem 1
      rw [h1] at h
      exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h

/-- Kollár's "the trace `S ∩ H = (y³ − z⁶ = 0)` has multiplicity 3": order exactly `3` at the
origin (`∂³/∂y³ = −6`). -/
theorem ord_zero_map_example11_H :
    Ideal.span {zR ^ 6 - yR ^ 3} ≤ Ideal.span {yR, zR} ^ 3 ∧
      ¬ Ideal.span {zR ^ 6 - yR ^ 3} ≤ Ideal.span {yR, zR} ^ 4 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · refine Ideal.sub_mem _ ?_ (Ideal.pow_mem_pow yR_mem_m0_fin2 3)
    exact mem_pow_of_mem_pow_of_le (by norm_num) (Ideal.pow_mem_pow zR_mem_m0_fin2 6)
  · have := eval_pderiv3_eq_zero_of_mem_m2_zero_pow4 ((Ideal.span_singleton_le_iff_mem _).mp h)
      0 0 0
    norm_num at this

/-- `cosupp((I|_H, 2)) = {0}`: `z⁶ − y³ ∈ 𝔪₀²`, and a `ℚ`-point of order `≥ 2` has `−3y² = 0`,
`6z⁵ = 0`. -/
theorem cosupport_map_example11_H :
    Ideal.span {zR ^ 6 - yR ^ 3} ≤ Ideal.span {yR, zR} ^ 2 ∧
    ∀ b c : ℚ, Ideal.span {zR ^ 6 - yR ^ 3} ≤ Ideal.span {yR - C b, zR - C c} ^ 2 →
      b = 0 ∧ c = 0 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun b c h => ?_⟩
  · have : zR ^ 6 - yR ^ 3 = zR ^ 4 * zR ^ 2 - yR * yR ^ 2 := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow zR_mem_m0_fin2 2))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow yR_mem_m0_fin2 2))
  · obtain ⟨-, hd⟩ := vanish_of_mem_m2_sq b c ((Ideal.span_singleton_le_iff_mem _).mp h)
    have hb : b = 0 := by simpa using hd 0
    have hc : c = 0 := by simpa using hd 1
    exact ⟨hb, hc⟩

/-- `I|_{H'} = (z⁶ − y⁴ − y³)` (`x ↦ −y²`). -/
theorem map_example11_H' :
    (Ideal.span {x ^ 2 + y ^ 3 - z ^ 6}).map
        (aeval ![-(X 0) ^ 2, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      Ideal.span {zR ^ 6 - yR ^ 4 - yR ^ 3} := by
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [show zR ^ 6 - yR ^ 4 - yR ^ 3 = -((-yR ^ 2) ^ 2 + yR ^ 3 - zR ^ 6) by ring,
    Ideal.span_singleton_neg]

/-- `MC(I|_{H'}) = D(z⁶ − y⁴ − y³) = (y², z⁵)`: the partials are `−y²(4y + 3)` and `6z⁵`, and
`y³ = (4y + 3)y³ − 4y⁴ ∈ ⟨y²(4y + 3), z⁶ − y⁴ − y³, …⟩` shows `y² ∈ D`. -/
theorem derivative_map_example11_H' :
    Ideal.derivative ℚ (Ideal.span {zR ^ 6 - yR ^ 4 - yR ^ 3}) = Ideal.span {yR ^ 2, zR ^ 5} := by
  have h0 : pderiv 0 (zR ^ 6 - yR ^ 4 - yR ^ 3) = -(C 4 * yR ^ 3 + C 3 * yR ^ 2) := by
    simp [map_ofNat]; ring
  have h1 : pderiv 1 (zR ^ 6 - yR ^ 4 - yR ^ 3) = C 6 * zR ^ 5 := by simp [map_ofNat]
  rw [derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      have : zR ^ 6 - yR ^ 4 - yR ^ 3 = zR * zR ^ 5 - (yR ^ 2 + yR) * yR ^ 2 := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', rfl, rfl⟩ := hg
      match i with
      | 0 =>
        rw [h0]
        refine neg_mem_iff.mpr ?_
        have : C 4 * yR ^ 3 + C 3 * yR ^ 2 = (C 4 * yR + C 3) * yR ^ 2 := by ring
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      | 1 => rw [h1]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · set S : Set (MvPolynomial (Fin 2) ℚ) :=
      {zR ^ 6 - yR ^ 4 - yR ^ 3} ∪ ⋃ i, pderiv i '' {zR ^ 6 - yR ^ 4 - yR ^ 3} with hS
    have hf : zR ^ 6 - yR ^ 4 - yR ^ 3 ∈ Ideal.span S := Ideal.subset_span (Or.inl rfl)
    have hmem : ∀ i : Fin 2, pderiv i (zR ^ 6 - yR ^ 4 - yR ^ 3) ∈ Ideal.span S := fun i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ rfl⟩))
    have hz : zR ^ 5 ∈ Ideal.span S := by
      have h := hmem 1
      rw [h1] at h
      exact mem_of_C_mul_mem (q := (6 : ℚ)) (by norm_num) h
    have hp : C 4 * yR ^ 3 + C 3 * yR ^ 2 ∈ Ideal.span S := by
      have h := hmem 0
      rwa [h0, neg_mem_iff] at h
    -- `y⁴ + y³ = z⁶ − f ∈ ⟨S⟩`, so `y³ = (y⁴ + y³)·4 − (4y³ + 3y²)·y …`: eliminate `y⁴`
    have hy4 : yR ^ 4 + yR ^ 3 ∈ Ideal.span S := by
      have : yR ^ 4 + yR ^ 3 = zR * zR ^ 5 - (zR ^ 6 - yR ^ 4 - yR ^ 3) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hz) hf
    have hy3 : C 4 * yR ^ 3 ∈ Ideal.span S := by
      -- `4y³ = 4(y⁴ + y³) − y·(4y³ + 3y²) + 3y³`? use `y·(4y³ + 3y²) − 4(y⁴ + y³) = −y³`
      have hy3' : yR ^ 3 ∈ Ideal.span S := by
        have : yR ^ 3 = C 4 * (yR ^ 4 + yR ^ 3) - yR * (C 4 * yR ^ 3 + C 3 * yR ^ 2) := by
          simp only [map_ofNat]; ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hy4) (Ideal.mul_mem_left _ _ hp)
      exact Ideal.mul_mem_left _ _ hy3'
    have hy : yR ^ 2 ∈ Ideal.span S := by
      have : C 3 * yR ^ 2 = (C 4 * yR ^ 3 + C 3 * yR ^ 2) - C 4 * yR ^ 3 := by ring
      exact mem_of_C_mul_mem (q := (3 : ℚ)) three_ne_zero (this ▸ Ideal.sub_mem _ hp hy3)
    rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hy
    · exact hz

/-- `cosupp((I|_{H'}, 2)) = {0}`: `z⁶ − y⁴ − y³ ∈ 𝔪₀²`; at a `ℚ`-point of order `≥ 2` the partial
`6z⁵` gives `z = 0`, the partial `−y²(4y + 3)` gives `y ∈ {0, −3/4}`, and the value `−y³(y + 1)`
excludes `−3/4`. -/
theorem cosupport_map_example11_H' :
    Ideal.span {zR ^ 6 - yR ^ 4 - yR ^ 3} ≤ Ideal.span {yR, zR} ^ 2 ∧
    ∀ b c : ℚ, Ideal.span {zR ^ 6 - yR ^ 4 - yR ^ 3} ≤ Ideal.span {yR - C b, zR - C c} ^ 2 →
      b = 0 ∧ c = 0 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun b c h => ?_⟩
  · have : zR ^ 6 - yR ^ 4 - yR ^ 3 = zR ^ 4 * zR ^ 2 - (yR ^ 2 + yR) * yR ^ 2 := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow zR_mem_m0_fin2 2))
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow yR_mem_m0_fin2 2))
  · obtain ⟨hv, hd⟩ := vanish_of_mem_m2_sq b c ((Ideal.span_singleton_le_iff_mem _).mp h)
    have hc : c = 0 := by simpa using hd 1
    subst hc
    have hv' : b ^ 3 * (b + 1) = 0 := by
      have := hv
      simp at this
      linear_combination -this
    have hd0 : b ^ 2 * (4 * b + 3) = 0 := by
      have := hd 0
      simp at this
      linear_combination -this
    rcases mul_eq_zero.mp hd0 with hb | hb
    · exact ⟨pow_eq_zero_iff two_ne_zero |>.mp hb, rfl⟩
    · have hb' : b = -3 / 4 := by linarith
      subst hb'
      norm_num at hv'

/-! ### The blow-up of the origin: the `x`- and `y`-charts -/

/-- `σ f = x₁²(1 + x₁y₁³ − x₁⁴z₁⁶)` on the `x`-chart. -/
theorem transform_example11_x :
    σx (x ^ 2 + y ^ 3 - z ^ 6) = x ^ 2 * (1 + x * y ^ 3 - x ^ 4 * z ^ 6) := by
  simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- No point of order `2` on the `x`-chart: on `x₁ = 0` the transform equals `1`; off it,
`∂/∂y₁ = 3x₁y₁²` gives `y₁ = 0`, then `∂/∂x₁ = y₁³ − 4x₁³z₁⁶` gives `z₁ = 0`, and the value is `1`
again. -/
theorem empty_example11_x (a b c : ℚ) :
    ¬ Ideal.span {1 + x * y ^ 3 - x ^ 4 * z ^ 6} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 2 := by
  intro h
  obtain ⟨hv, hd⟩ := vanish_of_mem_m3_sq a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have hv' : 1 + a * b ^ 3 - a ^ 4 * c ^ 6 = 0 := by simpa using hv
  have h1 : a = 0 ∨ b = 0 := by simpa using hd 1
  rcases h1 with ha | hb
  · subst ha; norm_num at hv'
  · subst hb
    have h0 : c = 0 ∨ a = 0 := by simpa using hd 0
    rcases h0 with hc | ha
    · subst hc; norm_num at hv'
    · subst ha; norm_num at hv'

/-- `σ f = y₁²(x₁² + y₁ − y₁⁴z₁⁶)` on the `y`-chart. -/
theorem transform_example11_y :
    σy (x ^ 2 + y ^ 3 - z ^ 6) = y ^ 2 * (x ^ 2 + y - y ^ 4 * z ^ 6) := by
  simp only [map_sub, map_add, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- No point of order `2` on the `y`-chart: `∂/∂y₁ = 1 − 4y₁³z₁⁶` and `∂/∂z₁ = −6y₁⁴z₁⁵` cannot
both vanish. -/
theorem empty_example11_y (a b c : ℚ) :
    ¬ Ideal.span {x ^ 2 + y - y ^ 4 * z ^ 6} ≤ Ideal.span {x - C a, y - C b, z - C c} ^ 2 := by
  intro h
  obtain ⟨-, hd⟩ := vanish_of_mem_m3_sq a b c ((Ideal.span_singleton_le_iff_mem _).mp h)
  have h1 : 1 - 4 * b ^ 3 * c ^ 6 = 0 := by
    have := hd 1
    simp at this
    linear_combination this
  have h2 : b = 0 ∨ c = 0 := by simpa using hd 2
  rcases h2 with hb | hc
  · subst hb; norm_num at h1
  · subst hc; norm_num at h1

end Example11Charts

end Hironaka.Examples
