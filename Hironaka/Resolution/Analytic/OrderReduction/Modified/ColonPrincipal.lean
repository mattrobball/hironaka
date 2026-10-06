/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.Defs
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Dividing an ideal by a principal prime: the order along divisors

The algebra behind the exponents after a step of the monomial phase (the controlled transform
`(M/𝓘(D)) · N` of the remarks after [Wlo09, Theorem 2.0.3]; the cosupport of `N(I)` contains no
`E^i`, [Kol07, Definition–Lemma 110]). In a domain `R`, for an ideal `I ⊆ (g)`:

* `I = g · (I : g)` (`Ideal.span_singleton_mul_colon_of_le`, from `BMO/SplitOrder.lean`);
* along the divisor `(g)` itself the colon drops the order by exactly one:
  `(I : g) ⊆ (g)^p ↔ I ⊆ (g)^{p+1}` (`Ideal.colon_span_singleton_le_pow_iff`, cancelling `g ≠ 0`);
* along another prime divisor `(f)` with `f ∤ g` the colon does not change the order:
  `(I : g) ⊆ (f)^p ↔ I ⊆ (f)^p` (`Ideal.colon_span_singleton_le_pow_iff_of_prime`, from
  `Prime.pow_dvd_of_dvd_mul_left`).

Read on the stalks of ideal sheaves (`ordAlongIdeal`), these give `ord_D (J : D) + 1 = ord_D J` for
the principal centre `D` and `ord_{D'} (J : D) = ord_{D'} J` for a transversal prime divisor `D'`
(`IdealSheaf.ordAlongIdeal_colon_add_one`, `IdealSheaf.ordAlongIdeal_colon_of_prime`). The stalks of
the structure sheaf are domains (`isDomain_stalk`) and the coordinates of a chart with simple normal
crossings are pairwise non-dividing primes (`IsSncChartAt.prime_coord`,
`IsSncChartAt.not_coord_dvd`), which is how `Step2bExponent.lean` applies them.
-/

public section

universe u

section Algebra

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Along the principal divisor `(g)` itself, dividing by `g` drops the order by one:
`(I : g) ⊆ (g)^p ↔ I ⊆ (g)^{p+1}` (for `I ⊆ (g)`, `g ≠ 0`). -/
theorem Ideal.colon_span_singleton_le_pow_iff {I : Ideal R} {g : R} (hg : g ≠ 0)
    (hI : I ≤ Ideal.span {g}) (p : ℕ) :
    I.colon (Ideal.span {g}) ≤ Ideal.span {g} ^ p ↔ I ≤ Ideal.span {g} ^ (p + 1) := by
  constructor
  · intro h
    rw [← Ideal.span_singleton_mul_colon_of_le hI, pow_succ']
    exact Ideal.mul_mono_right h
  · intro h
    rw [← Ideal.span_singleton_mul_colon_of_le hI, pow_succ'] at h
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Ideal.span_singleton_mul_le_span_singleton_mul.mp h z hz
    rwa [mul_left_cancel₀ hg hzw]

/-- Along a prime divisor `(f)` with `f ∤ g`, dividing by `g` does not change the order:
`(I : g) ⊆ (f)^p ↔ I ⊆ (f)^p` (for `I ⊆ (g)`). -/
theorem Ideal.colon_span_singleton_le_pow_iff_of_prime {I : Ideal R} {f g : R} (hf : Prime f)
    (hfg : ¬ f ∣ g) (hI : I ≤ Ideal.span {g}) (p : ℕ) :
    I.colon (Ideal.span {g}) ≤ Ideal.span {f} ^ p ↔ I ≤ Ideal.span {f} ^ p := by
  constructor
  · intro h
    rw [← Ideal.span_singleton_mul_colon_of_le hI]
    exact Ideal.mul_le.mpr fun r _ s hs => (Ideal.span {f} ^ p).mul_mem_left r (h hs)
  · intro h z hz
    have hgz : g * z ∈ I := by
      have := Submodule.mem_colon.mp hz g (Ideal.mem_span_singleton_self g)
      rwa [smul_eq_mul, mul_comm] at this
    have h1 : f ^ p ∣ g * z := by
      have := h hgz
      rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hf.pow_dvd_of_dvd_mul_left p hfg h1

end Algebra

namespace Manifold

open CategoryTheory

variable {X : TopCat} {𝒪 : TopCat.Sheaf CommRingCat X}

/-- `p ≤ a` for every natural `p` with `p ≤ b`, and conversely, gives `a = b` in `ℕ∞`
(`ENat.eq_of_forall_natCast_le_iff`); the shifted form used below. -/
theorem _root_.Hironaka.Manifold.ENat.eq_add_one_of_forall_succ_le_iff {a b : ℕ∞}
    (h : ∀ p : ℕ, (p : ℕ∞) ≤ a ↔ (p : ℕ∞) + 1 ≤ b) : a + 1 = b := by
  refine ENat.eq_of_forall_natCast_le_iff fun q => ?_
  cases q with
  | zero => simp
  | succ p =>
    rw [Nat.cast_succ]
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).trans (h p)

/-- Along the principal centre `D` with stalk `(g)`, the order of the colon `J : D` is one less
than the order of `J` (for `J_a ⊆ (g)`, `g ≠ 0`): `ord_D (J : D) + 1 = ord_D J`. -/
theorem IdealSheaf.ordAlongIdeal_colon_add_one (D J J' : IdealSheaf 𝒪) {a : X}
    {g : 𝒪.presheaf.stalk a} [IsDomain (𝒪.presheaf.stalk a)]
    (hD : D.stalkIdeal a = Ideal.span {g}) (hg : g ≠ 0)
    (hJ : J.stalkIdeal a ≤ Ideal.span {g})
    (hJ' : J'.stalkIdeal a = (J.stalkIdeal a).colon (Ideal.span {g})) :
    IdealSheaf.ordAlongIdeal D J' a + 1 = IdealSheaf.ordAlongIdeal D J a := by
  refine Hironaka.Manifold.ENat.eq_add_one_of_forall_succ_le_iff fun p => ?_
  rw [← Nat.cast_succ, IdealSheaf.le_ordAlongIdeal_iff, IdealSheaf.le_ordAlongIdeal_iff, hD, hJ']
  exact Ideal.colon_span_singleton_le_pow_iff hg hJ p

/-- Along a prime divisor `D'` with stalk `(f)`, `f ∤ g`, the order of the colon `J : (g)` equals
the order of `J` (for `J_a ⊆ (g)`): `ord_{D'} (J : g) = ord_{D'} J`. -/
theorem IdealSheaf.ordAlongIdeal_colon_of_prime (D' J J' : IdealSheaf 𝒪) {a : X}
    {f g : 𝒪.presheaf.stalk a} [IsDomain (𝒪.presheaf.stalk a)]
    (hD' : D'.stalkIdeal a = Ideal.span {f}) (hf : Prime f) (hfg : ¬ f ∣ g)
    (hJ : J.stalkIdeal a ≤ Ideal.span {g})
    (hJ' : J'.stalkIdeal a = (J.stalkIdeal a).colon (Ideal.span {g})) :
    IdealSheaf.ordAlongIdeal D' J' a = IdealSheaf.ordAlongIdeal D' J a := by
  refine ENat.eq_of_forall_natCast_le_iff fun p => ?_
  rw [IdealSheaf.le_ordAlongIdeal_iff, IdealSheaf.le_ordAlongIdeal_iff, hD', hJ']
  exact Ideal.colon_span_singleton_le_pow_iff_of_prime hf hfg hJ p

end Manifold
