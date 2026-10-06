/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
import Hironaka.Algebra.Order.Cosupport
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import HironakaExamples.Balanced.Example52
import HironakaExamples.Balanced.PDeriv
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Example 82: going down is not onto, and a general `H` need not give an equivalence

[Kol07, Example 82] illustrates the two defects of going down along a hypersurface of maximal
contact. First part: for `I = (xy − zⁿ)` and `H = (x = 0)`, `(H, I|_H) ≅ (𝔸², (zⁿ))` has a
one-dimensional locus of order `n`, while `I` has an isolated point of order `2`, so a blow-up of
order `≥ n` of `(H, I|_H, 2)` centred at another point of that line has no counterpart of order
`2` on `(X, I)`; for the general `H_g = (x − y = 0)`, `(H_g, I|_{H_g}) ≅ (𝔸², (x² − zⁿ))` has the
same isolated point of order `2`. Second part: for `I = (x³ + xy⁵ + z⁴)` and the general
`H = (x + u₁xy³ + u₂y⁴ + u₃z² = 0)`, after two chart blow-ups the transform of `I` has order `2`
while its restriction to the transform of `H` still has order `3`.

All statements are computations in polynomial rings, in the vocabulary of
`Hironaka/Resolution/Algebraic/Balanced/`:

* Orders at a `ℚ`-point `p` are read as `𝔪_p`-adic orders ([Kol07, Definition 47] in the
  polynomial ring). Memberships `g ∈ 𝔪_p^k` are exhibited by witnesses; non-memberships
  `g ∉ 𝔪_p^k` follow uniformly from two tools, a partial derivative lowers the power of an ideal
  by one (`pderiv_mem_pow_of_mem_pow_succ`, the Leibniz rule) and evaluation at `p` kills `𝔪_p`
  (`eval_eq_zero_of_mem_span`; the simp lemma `pderiv_ofNat` of
  `Hironaka/Scheme/IdealSheaf/Order/AffineSpace.lean` handles the numerals), so a `(k−1)`-fold
  partial derivative of `g` that does not vanish at `p` shows `g ∉ 𝔪_p^k`.
* The derivative ideals are `Ideal.derivative`, computed from the partial derivatives of the
  generators (`derivative_span_pderiv`); `D(xy − zⁿ) = (x, y, z^{n−1})` is `derivative_example52`
  of `HironakaExamples/Balanced/Example52.lean` (the ideal of [Kol07, Example 52.2]).
* The chart blow-ups are the substitution `σ : x ↦ x₁y₁, y ↦ y₁, z ↦ z₁y₁`, and Kollár's rows are
  polynomial identities `σ g = y₁ᵐ · g'`; the elimination of `x₂` by the equation of `H₂` is
  stated with the unit `1 + u₁y₂³` cleared, as the identity `(1 + u₁y₂³)³ · f₂ = g + h₂ · q` with
  explicit `g`, `q`. -/

public section

open MvPolynomial

namespace Hironaka.Examples

/-! ### Two generic tools for orders at a point -/

section Tools

variable {σ R : Type*} [CommRing R]

/-- The Leibniz rule for a partial derivative: `g ∈ N^{a+1}` implies `∂ᵢ g ∈ N^a`. -/
theorem pderiv_mem_pow_of_mem_pow_succ (i : σ) {N : Ideal (MvPolynomial σ R)} {a : ℕ}
    {g : MvPolynomial σ R} (hg : g ∈ N ^ (a + 1)) : pderiv i g ∈ N ^ a :=
  IsLocalRing.derivation_mem_pow (pderiv i) N a hg

/-- Evaluation at a point kills every polynomial of an ideal whose generators vanish there. -/
theorem eval_eq_zero_of_mem_span {S : Set (MvPolynomial σ R)} (a : σ → R)
    (hS : ∀ s ∈ S, eval a s = 0) {g : MvPolynomial σ R} (hg : g ∈ Ideal.span S) : eval a g = 0 := by
  have hle : Ideal.span S ≤ RingHom.ker (eval a) :=
    Ideal.span_le.mpr fun s hs => RingHom.mem_ker.mpr (hS s hs)
  exact RingHom.mem_ker.mp (hle hg)

end Tools

/-! ### Example 82, first part, in `ℚ[x, y, z]` -/

section FirstPart

/-- Kollár's `x = X 0` in `ℚ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `y = X 1` in `ℚ[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℚ)
/-- Kollár's `z = X 2` in `ℚ[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℚ)

variable (n : ℕ)

/-- `x ∈ 𝔪₀ = (x, y, z)`. `HironakaExamples/MaximalContact/Example14.lean`, which names the
variables `x₁, x₂, y`, uses this statement and the next two for its own generators. -/
theorem x_mem_m0 : x ∈ Ideal.span {x, y, z} := Ideal.subset_span (by simp)
/-- `y ∈ 𝔪₀`. -/
theorem y_mem_m0 : y ∈ Ideal.span {x, y, z} := Ideal.subset_span (by simp)
/-- `z ∈ 𝔪₀`. -/
theorem z_mem_m0 : z ∈ Ideal.span {x, y, z} := Ideal.subset_span (by simp)

/-- `ord₀ (xy − zⁿ) = 2`. -/
theorem ord_zero_example82 (hn : 2 ≤ n) :
    Ideal.span {x * y - z ^ n} ≤ Ideal.span {x, y, z} ^ 2 ∧
      ¬ Ideal.span {x * y - z ^ n} ≤ Ideal.span {x, y, z} ^ 3 := by
  refine ⟨(Ideal.span_singleton_le_iff_mem _).mpr ?_, fun h => ?_⟩
  · refine Ideal.sub_mem _ ?_ ?_
    · rw [sq]
      exact Ideal.mul_mem_mul x_mem_m0 y_mem_m0
    · have hz : z ^ n = z ^ 2 * z ^ (n - 2) := by rw [← pow_add, Nat.add_sub_cancel' hn]
      rw [hz]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow z_mem_m0 2)
  · have h0 : x * y - z ^ n ∈ Ideal.span {x, y, z} ^ (2 + 1) :=
      (Ideal.span_singleton_le_iff_mem _).mp h
    have h1 := pderiv_mem_pow_of_mem_pow_succ 0 h0
    have h2 := pderiv_mem_pow_of_mem_pow_succ 1 (a := 1) h1
    rw [pow_one] at h2
    have := eval_eq_zero_of_mem_span (![0, 0, 0] : Fin 3 → ℚ) (by simp) h2
    simp at this

/-- `x, x − y ∈ MC(I) = D(I)`: `H = (x = 0)` and `H_g = (x − y = 0)` are of maximal contact. -/
theorem mem_derivative_example82 (hn : 2 ≤ n) :
    x ∈ Ideal.derivative ℚ (Ideal.span {x * y - z ^ n}) ∧
      x - y ∈ Ideal.derivative ℚ (Ideal.span {x * y - z ^ n}) := by
  rw [show Ideal.span {x * y - z ^ n} = Hironaka.Balanced.example52 n from rfl,
    Hironaka.Balanced.derivative_example52 n hn]
  exact ⟨Ideal.subset_span (by simp),
    Ideal.sub_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))⟩

/-- The locus of order `2`, `V(D(I))`, has the origin as its only `ℚ`-point. -/
theorem cosupport_example82 (hn : 2 ≤ n) (a b c : ℚ)
    (h : ∀ g ∈ Ideal.derivative ℚ (Ideal.span {x * y - z ^ n}), eval ![a, b, c] g = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [show Ideal.span {x * y - z ^ n} = Hironaka.Balanced.example52 n from rfl,
    Hironaka.Balanced.derivative_example52 n hn] at h
  have ha : a = 0 := by simpa using h x (Ideal.subset_span (by simp))
  have hb : b = 0 := by simpa using h y (Ideal.subset_span (by simp))
  have hc : c ^ (n - 1) = 0 := by simpa using h (z ^ (n - 1)) (Ideal.subset_span (by simp))
  exact ⟨ha, hb, pow_eq_zero_iff (by omega) |>.mp hc⟩

/-- `I|_H = (zⁿ)` for `H = (x = 0)`. -/
theorem map_example82_H (hn : 2 ≤ n) :
    (Ideal.span {x * y - z ^ n}).map
        (aeval ![0, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      Ideal.span {(X 1 : MvPolynomial (Fin 2) ℚ) ^ n} := by
  have _ := hn
  rw [Ideal.map_span, Set.image_singleton]
  have himg : (aeval ![0, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ)
      (x * y - z ^ n) = -(X 1 ^ n) := by
    simp
  rw [himg, Ideal.span_singleton_neg]

/-- `(zⁿ)` has order `≥ n` at every `ℚ`-point of the line `z = 0`: the one-dimensional locus of
order `n` on `H`. -/
theorem mem_pow_example82_H_line (hn : 2 ≤ n) (b : ℚ) :
    (X 1 : MvPolynomial (Fin 2) ℚ) ^ n ∈
      Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ) - C b, X 1} ^ n := by
  have _ := hn
  exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) n

/-- `I` has order `< 2` at `(0, 1, 0) ∈ H`, a point of the line of order `n` on `H`. -/
theorem notMem_pow_example82_at (hn : 2 ≤ n) :
    x * y - z ^ n ∉ Ideal.span {x, y - 1, z} ^ 2 := by
  have _ := hn
  intro h
  have h1 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h
  rw [pow_one] at h1
  have := eval_eq_zero_of_mem_span (![0, 1, 0] : Fin 3 → ℚ) (by simp) h1
  simp at this

/-- `I|_{H_g} = (x² − zⁿ)` for `H_g = (x − y = 0)`. -/
theorem map_example82_Hg (hn : 2 ≤ n) :
    (Ideal.span {x * y - z ^ n}).map
        (aeval ![X 0, X 0, X 1] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ) =
      Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n} := by
  have _ := hn
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, ← sq]

/-- `D(x² − zⁿ)` in `ℚ[x, z]`: the partial derivatives of the generator. -/
theorem pderiv_zero_Hg :
    pderiv 0 ((X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n) = 2 * X 0 := by
  rw [map_sub, pderiv_pow, pderiv_X_self, pderiv_pow, pderiv_X_of_ne (by decide)]
  ring

theorem pderiv_one_Hg :
    pderiv 1 ((X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n) =
      -((n : MvPolynomial (Fin 2) ℚ) * X 1 ^ (n - 1)) := by
  rw [map_sub, pderiv_pow, pderiv_X_of_ne (by decide), pderiv_pow, pderiv_X_self]
  ring

/-- `D(x² − zⁿ) = (x, z^{n−1})` in `ℚ[x, z]`. -/
theorem derivative_example82_Hg (hn : 2 ≤ n) :
    Ideal.derivative ℚ (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n}) =
      Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ), X 1 ^ (n - 1)} := by
  rw [derivative_span_pderiv]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro g (hg | hg)
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      have hz : (X 1 : MvPolynomial (Fin 2) ℚ) ^ n = X 1 ^ (n - 1) * X 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hz, sq]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff] at hg
      obtain ⟨i, g', rfl, rfl⟩ := hg
      match i with
      | 0 => rw [pderiv_zero_Hg]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      | 1 =>
        rw [pderiv_one_Hg]
        exact neg_mem_iff.mpr (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hmem : ∀ i : Fin 2, pderiv i ((X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n) ∈
        Ideal.span ({(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n} ∪
          ⋃ i, pderiv i '' {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n}) := fun i =>
      Ideal.subset_span (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ rfl⟩))
    rcases hg with rfl | rfl
    · have h := hmem 0
      rw [pderiv_zero_Hg] at h
      refine mem_of_C_mul_mem (q := (2 : ℚ)) two_ne_zero ?_
      rwa [map_ofNat]
    · have h := hmem 1
      rw [pderiv_one_Hg, neg_mem_iff] at h
      refine mem_of_C_mul_mem (q := (n : ℚ)) (Nat.cast_ne_zero.mpr (by omega)) ?_
      rwa [map_natCast]

/-- The locus of order `2` of `I|_{H_g}` has the origin as its only `ℚ`-point. -/
theorem cosupport_example82_Hg (hn : 2 ≤ n) (a c : ℚ)
    (h : ∀ g ∈ Ideal.derivative ℚ (Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ) ^ 2 - X 1 ^ n}),
      eval ![a, c] g = 0) :
    a = 0 ∧ c = 0 := by
  rw [derivative_example82_Hg n hn] at h
  have ha : a = 0 := by simpa using h (X 0) (Ideal.subset_span (by simp))
  have hc : c ^ (n - 1) = 0 := by simpa using h (X 1 ^ (n - 1)) (Ideal.subset_span (by simp))
  exact ⟨ha, pow_eq_zero_iff (by omega) |>.mp hc⟩

end FirstPart

/-! ### Example 82, second part, over a nontrivial commutative `ℚ`-algebra -/

section SecondPart

variable {R : Type*} [CommRing R] [Algebra ℚ R] [Nontrivial R] (u₁ u₂ u₃ : R)

/-- Kollár's `x = X 0` in `R[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) R)
/-- Kollár's `y = X 1` in `R[x, y, z]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 3) R)
/-- Kollár's `z = X 2` in `R[x, y, z]`. -/
local notation "z" => (X 2 : MvPolynomial (Fin 3) R)
/-- The chart `x = x₁y₁`, `y = y₁`, `z = z₁y₁` (pivot `y`), as a substitution. -/
local notation "σ" => (aeval ![X 0 * X 1, X 1, X 2 * X 1] :
  MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R)

omit [Algebra ℚ R] in
/-- `x ∈ 𝔪₀ = (x, y, z)` in `R[x, y, z]`. -/
theorem xR_mem_m0 : x ∈ Ideal.span {x, y, z} := Ideal.subset_span (by simp)
omit [Algebra ℚ R] in
/-- `y ∈ 𝔪₀` in `R[x, y, z]`. -/
theorem yR_mem_m0 : y ∈ Ideal.span {x, y, z} := Ideal.subset_span (by simp)
omit [Algebra ℚ R] in
/-- `z ∈ 𝔪₀` in `R[x, y, z]`. -/
theorem zR_mem_m0 : z ∈ Ideal.span {x, y, z} := Ideal.subset_span (by simp)

/-- A product of elements of `N^a` and `N^b` lies in `N^{a+b}`. -/
theorem mul_mem_pow_add {A : Type*} [CommRing A] {N : Ideal A} {a b : ℕ} {g g' : A}
    (hg : g ∈ N ^ a) (hg' : g' ∈ N ^ b) : g * g' ∈ N ^ (a + b) := by
  rw [pow_add]
  exact Ideal.mul_mem_mul hg hg'

/-- `N^k ⊆ N^l` for `l ≤ k`. -/
theorem mem_pow_of_mem_pow_of_le {A : Type*} [CommRing A] {N : Ideal A} {k l : ℕ} (h : l ≤ k)
    {g : A} (hg : g ∈ N ^ k) : g ∈ N ^ l :=
  Ideal.pow_le_pow_right h hg

/-- A nontrivial `ℚ`-algebra has characteristic zero. -/
theorem charZero_of_algebraRat : CharZero R :=
  charZero_of_injective_algebraMap (algebraMap ℚ R).injective

/-- `ord₀ f = 3` and `ord₀ h = 1`, for `f = x³ + xy⁵ + z⁴` and `h = x + u₁xy³ + u₂y⁴ + u₃z²`. -/
theorem ord_zero_example82_second :
    (x ^ 3 + x * y ^ 5 + z ^ 4 ∈ Ideal.span {x, y, z} ^ 3 ∧
        x ^ 3 + x * y ^ 5 + z ^ 4 ∉ Ideal.span {x, y, z} ^ 4) ∧
      (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 4 + C u₃ * z ^ 2 ∈ Ideal.span {x, y, z} ∧
        x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 4 + C u₃ * z ^ 2 ∉ Ideal.span {x, y, z} ^ 2) := by
  have := charZero_of_algebraRat (R := R)
  refine ⟨⟨?_, fun h => ?_⟩, ⟨?_, fun h => ?_⟩⟩
  · refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.pow_mem_pow xR_mem_m0 3) ?_) ?_
    · refine mem_pow_of_mem_pow_of_le (k := 1 + 5) (by norm_num) (mul_mem_pow_add ?_ ?_)
      · rw [pow_one]; exact xR_mem_m0
      · exact Ideal.pow_mem_pow yR_mem_m0 5
    · exact mem_pow_of_mem_pow_of_le (k := 4) (by norm_num) (Ideal.pow_mem_pow zR_mem_m0 4)
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 0 h
    have h2 := pderiv_mem_pow_of_mem_pow_succ 0 h1
    have h3 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h2
    rw [pow_one] at h3
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : R)) (by simp) h3
    norm_num [map_ofNat] at this
  · refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ xR_mem_m0 ?_) ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ xR_mem_m0)
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ yR_mem_m0 4 (by norm_num))
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ zR_mem_m0 2 (by norm_num))
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h
    rw [pow_one] at h1
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : R)) (by simp) h1
    norm_num [map_ofNat] at this

omit [Nontrivial R] in
/-- `h ∈ D²(f) = MC(I)`. Over the `ℚ`-algebra `R` the partial derivatives are `ℚ`-derivations, and
`6x = ∂ₓ∂ₓ f`, `5y⁴ = ∂_y∂ₓ f`, `20xy³ = ∂_y∂_y f`, `12z² = ∂_z∂_z f` lie in `D²(f)`; dividing by
the nonzero rationals gives the four monomials of `h`. -/
theorem mem_MC_example82_second :
    x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 4 + C u₃ * z ^ 2 ∈
      Ideal.derivativeIter ℚ 2 (Ideal.span {x ^ 3 + x * y ^ 5 + z ^ 4}) := by
  have hD : ∀ (K : Ideal (MvPolynomial (Fin 3) R)) (i : Fin 3) {g : MvPolynomial (Fin 3) R},
      g ∈ K → pderiv i g ∈ Ideal.derivative ℚ K := fun K i g hg =>
    Ideal.derivation_apply_mem_derivative ((pderiv i).restrictScalars ℚ) hg
  change _ ∈ Ideal.derivativeIter ℚ (1 + 1) _
  rw [Ideal.derivativeIter_succ, Ideal.derivativeIter_succ, Ideal.derivativeIter_zero]
  have hf : x ^ 3 + x * y ^ 5 + z ^ 4 ∈ Ideal.span {x ^ 3 + x * y ^ 5 + z ^ 4} :=
    Ideal.mem_span_singleton_self _
  have hxx : pderiv 0 (pderiv 0 (x ^ 3 + x * y ^ 5 + z ^ 4)) = 6 * x := by
    simp
    ring
  have hyx : pderiv 1 (pderiv 0 (x ^ 3 + x * y ^ 5 + z ^ 4)) = 5 * y ^ 4 := by
    simp
  have hyy : pderiv 1 (pderiv 1 (x ^ 3 + x * y ^ 5 + z ^ 4)) = 20 * (x * y ^ 3) := by
    simp
    ring
  have hzz : pderiv 2 (pderiv 2 (x ^ 3 + x * y ^ 5 + z ^ 4)) = 12 * z ^ 2 := by
    simp
    ring
  set D2 := Ideal.derivative ℚ (Ideal.derivative ℚ (Ideal.span {x ^ 3 + x * y ^ 5 + z ^ 4}))
  have hx : x ∈ D2 := by
    have h := hD _ 0 (hD _ 0 hf)
    rw [hxx] at h
    refine Ideal.mem_of_algebraMap_mul_mem (K := ℚ) (q := 6) (by norm_num) ?_
    rw [map_ofNat]
    exact h
  have hy : y ^ 4 ∈ D2 := by
    have h := hD _ 1 (hD _ 0 hf)
    rw [hyx] at h
    refine Ideal.mem_of_algebraMap_mul_mem (K := ℚ) (q := 5) (by norm_num) ?_
    rw [map_ofNat]
    exact h
  have hxy : x * y ^ 3 ∈ D2 := by
    have h := hD _ 1 (hD _ 1 hf)
    rw [hyy] at h
    refine Ideal.mem_of_algebraMap_mul_mem (K := ℚ) (q := 20) (by norm_num) ?_
    rw [map_ofNat]
    exact h
  have hz : z ^ 2 ∈ D2 := by
    have h := hD _ 2 (hD _ 2 hf)
    rw [hzz] at h
    refine Ideal.mem_of_algebraMap_mul_mem (K := ℚ) (q := 12) (by norm_num) ?_
    rw [map_ofNat]
    exact h
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ hx (Ideal.mul_mem_left _ _ hxy))
    (Ideal.mul_mem_left _ _ hy)) (Ideal.mul_mem_left _ _ hz)

omit [Algebra ℚ R] [Nontrivial R] in
/-- The first blow-up (Kollár's second row): `σ f = y₁³·f₁` and `σ h = y₁·h₁`. -/
theorem transform_example82_second_one :
    σ (x ^ 3 + x * y ^ 5 + z ^ 4) = y ^ 3 * (x ^ 3 + x * y ^ 3 + y * z ^ 4) ∧
      σ (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 4 + C u₃ * z ^ 2) =
        y * (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 3 + C u₃ * (y * z ^ 2)) := by
  constructor
  · simp only [map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  · simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

omit [Algebra ℚ R] [Nontrivial R] in
/-- The second blow-up (Kollár's third row): `σ f₁ = y₂³·f₂` and `σ h₁ = y₂·h₂`. -/
theorem transform_example82_second_two :
    σ (x ^ 3 + x * y ^ 3 + y * z ^ 4) = y ^ 3 * (x ^ 3 + x * y + y ^ 2 * z ^ 4) ∧
      σ (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 3 + C u₃ * (y * z ^ 2)) =
        y * (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 2 + C u₃ * (y ^ 2 * z ^ 2)) := by
  constructor
  · simp only [map_add, map_mul, map_pow, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  · simp only [map_add, map_mul, map_pow, aeval_X, aeval_C, algebraMap_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring

/-- `ord₀ f₂ = 2`: after two blow-ups the transform of `I` has order `2`, as Kollár says. -/
theorem ord_example82_second_two :
    x ^ 3 + x * y + y ^ 2 * z ^ 4 ∈ Ideal.span {x, y, z} ^ 2 ∧
      x ^ 3 + x * y + y ^ 2 * z ^ 4 ∉ Ideal.span {x, y, z} ^ 3 := by
  have := charZero_of_algebraRat (R := R)
  refine ⟨?_, fun h => ?_⟩
  · refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact mem_pow_of_mem_pow_of_le (k := 3) (by norm_num) (Ideal.pow_mem_pow xR_mem_m0 3)
    · rw [sq]
      exact Ideal.mul_mem_mul xR_mem_m0 yR_mem_m0
    · exact mem_pow_of_mem_pow_of_le (k := 2 + 4) (by norm_num)
        (mul_mem_pow_add (Ideal.pow_mem_pow yR_mem_m0 2) (Ideal.pow_mem_pow zR_mem_m0 4))
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 1 h
    have h2 := pderiv_mem_pow_of_mem_pow_succ 0 (a := 1) h1
    rw [pow_one] at h2
    have := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : R)) (by simp) h2
    norm_num [map_ofNat] at this

omit [Algebra ℚ R] [Nontrivial R] in
/-- The elimination identity: `(1 + u₁y₂³)³ · f₂ = g + h₂ · q` with `g` free of `x₂`, so `f₂`
restricted to `h₂ = 0` is `g` up to the unit `(1 + u₁y₂³)³`. -/
theorem restrict_example82_second_two :
    (1 + C u₁ * y ^ 3) ^ 3 * (x ^ 3 + x * y + y ^ 2 * z ^ 4) =
      (-(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
          (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
          (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4) +
        (x + C u₁ * (x * y ^ 3) + C u₂ * y ^ 2 + C u₃ * (y ^ 2 * z ^ 2)) *
          ((x * (1 + C u₁ * y ^ 3)) ^ 2 - x * (1 + C u₁ * y ^ 3) * y ^ 2 * (C u₂ + C u₃ * z ^ 2) +
            y ^ 4 * (C u₂ + C u₃ * z ^ 2) ^ 2 + (1 + C u₁ * y ^ 3) ^ 2 * y) := by
  ring

omit [Algebra ℚ R] [Nontrivial R] in
/-- Kollár's `I₂|_{H₂} ⊂ (y₂³, y₂²z₂⁴)`: `g ∈ (y₂³, y₂²z₂⁴)`. -/
theorem mem_span_example82_second_two :
    -(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) - (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
        (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4 ∈
      Ideal.span {y ^ 3, y ^ 2 * z ^ 4} := by
  have hg : -(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
        (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
        (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4 =
      y ^ 3 * (-(y ^ 3 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
          (1 + C u₁ * y ^ 3) ^ 2 * (C u₂ + C u₃ * z ^ 2)) +
        y ^ 2 * z ^ 4 * (1 + C u₁ * y ^ 3) ^ 3 := by
    ring
  rw [hg]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- Kollár's "its restriction to the birational transform `H₂` of `H` still has order 3": `g` has
order `≥ 3`, and exactly `3` when `u₂` is a unit (`∂_y³ g` at the origin is `−6u₂`). -/
theorem ord_restrict_example82_second_two :
    (-(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) - (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
        (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4 ∈ Ideal.span {x, y, z} ^ 3) ∧
      (IsUnit u₂ →
        -(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
            (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
            (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4 ∉ Ideal.span {x, y, z} ^ 4) := by
  have := charZero_of_algebraRat (R := R)
  refine ⟨?_, fun hu h => ?_⟩
  · have hg : -(y ^ 6 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
          (1 + C u₁ * y ^ 3) ^ 2 * y ^ 3 * (C u₂ + C u₃ * z ^ 2) +
          (1 + C u₁ * y ^ 3) ^ 3 * y ^ 2 * z ^ 4 =
        y ^ 3 * (-(y ^ 3 * (C u₂ + C u₃ * z ^ 2) ^ 3) -
            (1 + C u₁ * y ^ 3) ^ 2 * (C u₂ + C u₃ * z ^ 2)) +
          y ^ 2 * z ^ 4 * (1 + C u₁ * y ^ 3) ^ 3 := by
      ring
    rw [hg]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow yR_mem_m0 3)) ?_
    exact Ideal.mul_mem_right _ _ (mem_pow_of_mem_pow_of_le (k := 2 + 4) (by norm_num)
      (mul_mem_pow_add (Ideal.pow_mem_pow yR_mem_m0 2) (Ideal.pow_mem_pow zR_mem_m0 4)))
  · have h1 := pderiv_mem_pow_of_mem_pow_succ 1 h
    have h2 := pderiv_mem_pow_of_mem_pow_succ 1 h1
    have h3 := pderiv_mem_pow_of_mem_pow_succ 1 (a := 1) h2
    rw [pow_one] at h3
    have h0 := eval_eq_zero_of_mem_span (fun _ : Fin 3 => (0 : R)) (by simp) h3
    norm_num [map_ofNat, hu.mul_right_eq_zero] at h0

end SecondPart

end Hironaka.Examples
