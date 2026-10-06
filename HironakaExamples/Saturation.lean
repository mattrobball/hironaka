/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Germ.Coordinate
public import Mathlib.RingTheory.Ideal.Colon
import Hironaka.Analytic.ConvSeries.Units
import Hironaka.Analytic.Germ.Prime
import Hironaka.Analytic.Rueckert.UFD
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Bierstone–Milman's Example 3.16: the saturation computed

[BM97, Example 3.16] blows up the origin of `ℝ²` for `X = V(h)`, `h = x⁴(x−1)² + y²`, and reads
off in the chart `x = u`, `y = uv` the strict transform `X' = V(u²(u−1)² + v²)`, with support
`{(0,0), (1,0)}`, against the geometric strict transform `X''` ([BM97, Remark 3.15]) with support
`{(1,0)}`. The saturation lemma for `K`-analytic spaces, `K = ℝ` or `ℂ`
(`colonChain_locallyStationary`, `Hironaka.AnalyticSpace.Noether.Saturation`), says the colon chain
`(J : I_F^k)` of the total transform
`J` by the exceptional ideal `I_F` is stationary near every point; this module computes that
chain on the example, in the germ ring `Conv 2` of the chart (the stalk of the structure sheaf at
a point of the chart is `Conv 2` through the Taylor isomorphism `taylorEquivConv`, with
coordinates centred at the point):

* **Chart 1** (`x = u`, `y = uv`; `I_F = (u)`, `h ∘ π = u² h₁`, `h₁ = u²(u−1)² + v²`). At the point
  `(0, c)` of the exceptional divisor the centred equation is `bm316Chart1 c = u²(u−1)² + (c + v)²`;
  `u` is prime in the unique factorization domain `Conv 2` and does not divide `h₁`, because the
  coefficient of `v²` in `h₁` is `1` (`coeff_bm316Chart1`: `h₁(0, v) = v²` is not identically
  zero). Hence `(u² h₁ : u^k) = (u^(2−k) h₁)` for `k ≤ 2` and `= (h₁)` for `k ≥ 2`
  (`colon_bm316Chart1_of_le_two`, `colon_bm316Chart1_of_two_le`): the chain is stationary from
  `N = 2` on, uniformly in `c`, and not before (`colon_bm316Chart1_one_lt_two`). The saturation is
  the ideal-theoretic strict transform `(h₁)`.
* **Chart 2** (`x = u'v'`, `y = v'`; `I_F = (v')`, `h ∘ π = v'² h₂`, `h₂ = u'⁴v'²(u'v'−1)² + 1`).
  The computation is made at the origin of the chart only (`bm316Chart2` is the series centred
  there): `h₂` is a unit (constant coefficient `1`, `isUnit_bm316Chart2`), so the saturation is
  the unit ideal at that point, again from `N = 2` on (`colon_bm316Chart2_of_two_le`).
* **Supports**: the real zero set of `h₁` is `{(0,0), (1,0)}` (`zeroSet_bm316Chart1Fun`); it meets
  `F = {u = 0}` in `{(0,0)}` (`zeroSet_bm316Chart1Fun_inter_exceptional`); the closure of its part
  off `F` is `{(1,0)}` (`closure_zeroSet_bm316Chart1Fun_diff_exceptional`). [BM97, Example 3.16]
  states that `|X''| = {(1,0)}`, strictly smaller than the support of `X'`; the identification
  of `|X''|` with this closure is the source's statement and is not verified here.

The two general colon computations (`colon_span_pow_mul_of_le`, `colon_span_pow_mul_of_prime`)
are "`(h₁) : u^j = (h₁)` when `h₁` and `u` are coprime", in Mathlib's vocabulary: `u` prime and
`u ∤ h` give `IsRelPrime h (u^j)` (`Irreducible.isRelPrime_iff_not_dvd`), and a relatively prime
divisor of a product divides the other factor (`IsRelPrime.dvd_of_dvd_mul_right`, in any
`DecompositionMonoid`; a unique factorization domain is one). These are computations on concrete
data; `RealPlaneStrictTransform` proves the same failure of the closure inclusion on the
manifold-level blow-up.
-/

@[expose] public section

open MvPowerSeries

namespace Hironaka.Examples

section Colon

variable {R : Type*} [CommRing R] [IsDomain R]

/-- In a domain, for `u ≠ 0` and `k ≤ m`, `(u^m h : (u)^k) = (u^(m−k) h)` — cancel `u^k`. -/
theorem colon_span_pow_mul_of_le {u h : R} (hu : u ≠ 0) {m k : ℕ} (hk : k ≤ m) :
    Submodule.colon (Ideal.span {u ^ m * h}) (SetLike.coe (Ideal.span {u} ^ k)) =
      Ideal.span {u ^ (m - k) * h} := by
  have hmk : u ^ m = u ^ (m - k) * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk]
  ext x
  rw [Ideal.span_singleton_pow, Submodule.mem_colon, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hx' := hx (u ^ k) (Ideal.mem_span_singleton_self _)
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, ?_⟩
    apply mul_right_cancel₀ (pow_ne_zero k hu)
    rw [hy, hmk]
    ring
  · rintro ⟨y, rfl⟩ p hp
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨y * q, by rw [hmk]; ring⟩

/-- For `u` prime with `u ∤ h`, `(u^m h : (u)^k) = (h)` for `k ≥ m` — cancel `u^m`, then
`h ∣ x u^(k−m)` forces `h ∣ x` since `h` is relatively prime to every power of `u`. -/
theorem colon_span_pow_mul_of_prime [DecompositionMonoid R] {u h : R} (hu : Prime u)
    (hh : ¬ u ∣ h) {m k : ℕ} (hk : m ≤ k) :
    Submodule.colon (Ideal.span {u ^ m * h}) (SetLike.coe (Ideal.span {u} ^ k)) =
      Ideal.span {h} := by
  have hrel : ∀ j : ℕ, IsRelPrime h (u ^ j) := by
    intro j
    induction j with
    | zero => simpa using isRelPrime_one_right
    | succ j ih =>
      rw [pow_succ]
      exact ih.mul_right (hu.irreducible.isRelPrime_iff_not_dvd.mpr hh).symm
  have hkm : u ^ k = u ^ m * u ^ (k - m) := by rw [← pow_add, Nat.add_sub_of_le hk]
  ext x
  rw [Ideal.span_singleton_pow, Submodule.mem_colon, Ideal.mem_span_singleton]
  constructor
  · intro hx
    have hx' := hx (u ^ k) (Ideal.mem_span_singleton_self _)
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, hy⟩ := hx'
    have h2 : x * u ^ (k - m) = h * y := by
      apply mul_left_cancel₀ (pow_ne_zero m hu.ne_zero)
      have : u ^ m * (h * y) = x * u ^ k := by rw [hy]; ring
      rw [this, hkm]
      ring
    exact (hrel (k - m)).dvd_of_dvd_mul_right ⟨y, h2⟩
  · rintro ⟨y, rfl⟩ p hp
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hp
    obtain ⟨q, rfl⟩ := hp
    rw [smul_eq_mul, Ideal.mem_span_singleton]
    exact ⟨u ^ (k - m) * y * q, by rw [hkm]; ring⟩

end Colon

open Analytic

/-- [BM97, Example 3.16], chart 1 (`x = u`, `y = uv`), at the point `(0, c)` of the
exceptional divisor `F = {u = 0}`: the strict transform's equation `h₁ = u²(u−1)² + v²` in the
coordinates centred at the point, `u²(u−1)² + (c + v)²`, as a convergent series (`u = convX 0`,
`v = convX 1`). -/
noncomputable def bm316Chart1 (c : ℝ) : Conv ℝ 2 :=
  convX ℝ 0 ^ 2 * (convX ℝ 0 - 1) ^ 2 + (algebraMap ℝ (Conv ℝ 2) c + convX ℝ 1) ^ 2

/-- The coefficient of `v²` in `bm316Chart1 c` is `1`: `h₁(0, v) = v²` is not identically zero
near any `v₀`. -/
theorem coeff_bm316Chart1 (c : ℝ) :
    coeff (Finsupp.single 1 2) (bm316Chart1 c : MvPowerSeries (Fin 2) ℝ) = 1 := by
  have hcoe : (bm316Chart1 c : MvPowerSeries (Fin 2) ℝ) =
      X 0 ^ 2 * (X 0 - 1) ^ 2 + (C c + X 1) ^ 2 := rfl
  have h1 : coeff (Finsupp.single (1 : Fin 2) 2)
      ((X 0 : MvPowerSeries (Fin 2) ℝ) ^ 2 * (X 0 - 1) ^ 2) = 0 :=
    X_pow_dvd_iff.mp (dvd_mul_right _ _) _ (by simp)
  rw [hcoe, map_add, h1, zero_add, add_sq, map_add, map_add, ← map_pow C, coeff_C,
    ← map_ofNat C 2, ← map_mul, coeff_C_mul, coeff_X, coeff_X_pow]
  simp [Finsupp.single_eq_single_iff, Finsupp.single_eq_zero]

/-- `h₁ ≠ 0` in `Conv ℝ 2`. -/
theorem bm316Chart1_ne_zero (c : ℝ) : bm316Chart1 c ≠ 0 := by
  intro h
  have := coeff_bm316Chart1 c
  rw [h] at this
  simp at this

/-- `u ∤ h₁` in `Conv ℝ 2`: a multiple of `u` has no `u`-free monomial, but `h₁` has `v²`. -/
theorem not_convX_dvd_bm316Chart1 (c : ℝ) : ¬ convX ℝ (0 : Fin 2) ∣ bm316Chart1 c := by
  rintro ⟨g, hg⟩
  have hX : (X 0 : MvPowerSeries (Fin 2) ℝ) ∣ (bm316Chart1 c : MvPowerSeries (Fin 2) ℝ) :=
    ⟨g, congrArg Subtype.val hg⟩
  have := X_dvd_iff.mp hX (Finsupp.single 1 2) (by simp)
  rw [coeff_bm316Chart1] at this
  exact one_ne_zero this

/-- Chart 1, `k ≥ 2`: `(u² h₁ : u^k) = (h₁)` at every point `(0, c)` of `F` — the saturation is
the ideal-theoretic strict transform, with `N = 2` uniformly. -/
theorem colon_bm316Chart1_of_two_le (c : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    Submodule.colon (Ideal.span {convX ℝ (0 : Fin 2) ^ 2 * bm316Chart1 c})
        (SetLike.coe (Ideal.span {convX ℝ (0 : Fin 2)} ^ k)) =
      Ideal.span {bm316Chart1 c} :=
  colon_span_pow_mul_of_prime (R := Conv ℝ 2) (prime_convX 0) (not_convX_dvd_bm316Chart1 c) hk

/-- Chart 1, `k ≤ 2`: `(u² h₁ : u^k) = (u^(2−k) h₁)`. -/
theorem colon_bm316Chart1_of_le_two (c : ℝ) {k : ℕ} (hk : k ≤ 2) :
    Submodule.colon (Ideal.span {convX ℝ (0 : Fin 2) ^ 2 * bm316Chart1 c})
        (SetLike.coe (Ideal.span {convX ℝ (0 : Fin 2)} ^ k)) =
      Ideal.span {convX ℝ (0 : Fin 2) ^ (2 - k) * bm316Chart1 c} :=
  colon_span_pow_mul_of_le (convX_ne_zero 0) hk

/-- `N = 2` is sharp: the colon by `u` is strictly smaller than the colon by `u²` (`u` is not a
unit and `h₁ ≠ 0`). -/
theorem colon_bm316Chart1_one_lt_two (c : ℝ) :
    Submodule.colon (Ideal.span {convX ℝ (0 : Fin 2) ^ 2 * bm316Chart1 c})
        (SetLike.coe (Ideal.span {convX ℝ (0 : Fin 2)} ^ 1)) <
      Submodule.colon (Ideal.span {convX ℝ (0 : Fin 2) ^ 2 * bm316Chart1 c})
        (SetLike.coe (Ideal.span {convX ℝ (0 : Fin 2)} ^ 2)) := by
  rw [colon_bm316Chart1_of_le_two c (k := 1) one_le_two,
    colon_bm316Chart1_of_two_le c (k := 2) le_rfl, Ideal.span_singleton_lt_span_singleton]
  refine ⟨bm316Chart1_ne_zero c, convX ℝ 0, not_isUnit_convX 0, ?_⟩
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_comm]

/-- [BM97, Example 3.16], chart 2 (`x = u'v'`, `y = v'`; `u' = convX ℝ 0`, `v' = convX ℝ 1`): the
cofactor
`h₂ = u'⁴v'²(u'v'−1)² + 1` of `v'²` in `h ∘ π`. -/
noncomputable def bm316Chart2 : Conv ℝ 2 :=
  convX ℝ 0 ^ 4 * convX ℝ 1 ^ 2 * (convX ℝ 0 * convX ℝ 1 - 1) ^ 2 + 1

/-- `h₂` is a unit of `Conv ℝ 2` — its constant coefficient is `1`. The series is centred at the
origin of chart 2, so this is the statement at that one point of `F`. -/
theorem isUnit_bm316Chart2 : IsUnit bm316Chart2 := by
  refine (isUnit_iff_constantCoeff_ne_zero bm316Chart2.2).mpr ?_
  have hcoe : (bm316Chart2 : MvPowerSeries (Fin 2) ℝ) =
      X 0 ^ 4 * X 1 ^ 2 * (X 0 * X 1 - 1) ^ 2 + 1 := rfl
  rw [hcoe]
  simp

/-- Chart 2 at its origin, `k ≥ 2`: `(v'² h₂ : v'^k)` is the unit ideal — `X'` does not pass
through the origin of this chart. -/
theorem colon_bm316Chart2_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    Submodule.colon (Ideal.span {convX ℝ (1 : Fin 2) ^ 2 * bm316Chart2})
        (SetLike.coe (Ideal.span {convX ℝ (1 : Fin 2)} ^ k)) = ⊤ := by
  have hnd : ¬ convX ℝ (1 : Fin 2) ∣ bm316Chart2 := fun hd =>
    not_isUnit_convX 1 (isUnit_of_dvd_unit hd isUnit_bm316Chart2)
  rw [colon_span_pow_mul_of_prime (R := Conv ℝ 2) (prime_convX 1) hnd hk,
    Ideal.span_singleton_eq_top]
  exact isUnit_bm316Chart2

/-- [BM97, Example 3.16]: the real zero set of `h₁ = u²(u−1)² + v²` is `{(0,0), (1,0)}`. -/
theorem zeroSet_bm316Chart1Fun :
    {p : Fin 2 → ℝ | p 0 ^ 2 * (p 0 - 1) ^ 2 + p 1 ^ 2 = 0} = {![0, 0], ![1, 0]} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).mp h
    have hp1 : p 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h2
    rcases mul_eq_zero.mp h1 with h0 | h0
    · left
      have hp0 : p 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h0
      ext i
      fin_cases i <;> simp [hp0, hp1]
    · right
      have hp0 : p 0 = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
      ext i
      fin_cases i <;> simp [hp0, hp1]
  · rintro (rfl | rfl) <;> simp

/-- `X' ∩ F = {(0,0)}`, the one point of the support of `X'` on the exceptional divisor. -/
theorem zeroSet_bm316Chart1Fun_inter_exceptional :
    {p : Fin 2 → ℝ | p 0 ^ 2 * (p 0 - 1) ^ 2 + p 1 ^ 2 = 0} ∩ {p | p 0 = 0} = {![0, 0]} := by
  rw [zeroSet_bm316Chart1Fun]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · rfl
    · exact absurd h (by simp)
  · rintro rfl
    exact ⟨Or.inl rfl, by simp⟩

/-- The closure of the zero set of `h₁` off `F` is `{(1,0)}`. [BM97, Example 3.16] states that
this is the support of the geometric strict transform `X''`, strictly smaller than the support
`{(0,0), (1,0)}` of `X'`; that identification is the source's statement. -/
theorem closure_zeroSet_bm316Chart1Fun_diff_exceptional :
    closure ({p : Fin 2 → ℝ | p 0 ^ 2 * (p 0 - 1) ^ 2 + p 1 ^ 2 = 0} \ {p | p 0 = 0}) =
      {![1, 0]} := by
  rw [zeroSet_bm316Chart1Fun]
  have : ({![0, 0], ![1, 0]} : Set (Fin 2 → ℝ)) \ {p | p 0 = 0} = {![1, 0]} := by
    ext p
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨rfl | rfl, h⟩
      · exact absurd (by simp) h
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, by simp⟩
  rw [this, closure_singleton]

end Hironaka.Examples
