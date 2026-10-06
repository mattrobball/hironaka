/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# The kernel of `R[T] → S`, `T ↦ ξ`, for an integrally closed base

Let `R` be an integrally closed domain, `S` a domain and `f : R →+* S` injective. If `ξ ∈ S` is
a root of a monic irreducible `Q ∈ R[T]`, then `Q` is the minimal polynomial of `ξ` over `R` and
every `H ∈ R[T]` with `H(ξ) = 0` is divisible by `Q`: Mathlib's `minpoly.isIntegrallyClosed_dvd`
(the minimal polynomial over an integrally closed domain divides every annihilating polynomial),
a consequence of Gauss's lemma. In the parametrization theorem [Fre17, Ch. I, 8.3] this identifies
the kernel of `𝒪_d[T] → 𝒪_n/P'`, `T ↦ X_{i₀}`, with `(Q)`: the base `𝒪_d` is a unique
factorization domain (`UFD.lean`), hence integrally closed, and `𝒪_n/P'` is a domain into which
`𝒪_d` embeds (the injectivity of the Noether normalization).

Stated with a ring map (`Polynomial.eval₂ f`), for the same reason as in
`PrimitiveRelations.lean`: the `S` it is applied to is a quotient of `𝒪_n`, and the `R`-algebra
structure is introduced only locally, inside the proof.
-/

@[expose] public section

open Polynomial

namespace Analytic

/-- Over an integrally closed domain `R` embedded in a domain `S` by `f`, a monic irreducible
`Q ∈ R[T]` with root `ξ` divides every `H ∈ R[T]` vanishing at `ξ` (Gauss's lemma through
Mathlib's `minpoly.isIntegrallyClosed_dvd`). -/
theorem dvd_of_eval₂_eq_zero_of_monic_irreducible {R S : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] (f : R →+* S) (hinj : Function.Injective f)
    {ξ : S} {Q : R[X]} (hQ : Q.Monic) (hQirr : Irreducible Q) (hQξ : eval₂ f ξ Q = 0) {H : R[X]}
    (hHξ : eval₂ f ξ H = 0) : Q ∣ H := by
  let _ := f.toAlgebra
  have hTF : Module.IsTorsionFree R S := ⟨fun r hr => by
    intro s₁ s₂ h
    have hr0 : algebraMap R S r ≠ 0 := by
      intro h0
      exact (isRegular_iff_ne_zero.mp hr) (hinj (by rw [map_zero]; exact h0))
    have h' : algebraMap R S r * s₁ = algebraMap R S r * s₂ := by
      simpa only [Algebra.smul_def] using h
    exact mul_left_cancel₀ hr0 h'⟩
  have hξ : IsIntegral R ξ := ⟨Q, hQ, hQξ⟩
  -- the minimal polynomial divides `Q`, so equals it (`Q` irreducible, both monic)
  have hmin : minpoly R ξ ∣ Q := minpoly.isIntegrallyClosed_dvd hξ hQξ
  have hassoc : Associated (minpoly R ξ) Q := by
    rcases (hQirr.dvd_iff).mp hmin with hunit | hass
    · exact absurd hunit (minpoly.not_isUnit R ξ)
    · exact hass.symm
  have heq : minpoly R ξ = Q := eq_of_monic_of_associated (minpoly.monic hξ) hQ hassoc
  rw [← heq]
  exact minpoly.isIntegrallyClosed_dvd hξ hHξ

end Analytic
