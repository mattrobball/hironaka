/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Split
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The decomposition `I = M(I) · N(I)` at the stalk

The nonmonomial part `N(I) = I : M(I)` is defined so that `I = M(I) · N(I)`
([Kol07, Definition–Lemma 110]). This file proves that identity at every stalk,
`M(I)_x · N(I)_x = I_x`. It is an instance of the ring-theoretic fact that for an ideal `I ≤ (g)`
one has `(g) · (I : (g)) = I`, applied with `(g) = M(I)_x`, which is principal
(`exists_nonZeroDivisor_stalkIdeal_monomialPart`) and contains `I_x` (`stalkIdeal_le_monomialPart`).
The analytic counterpart of `Hironaka.BMO.monomialPart_mul_nonmonomialPart`.
-/

public section

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

/-- In a commutative ring, if `I ≤ (g)` then `(g) · (I : (g)) = I`. No regularity of `g` is needed:
the invertibility of the monomial part enters the decomposition `I = M(I) · N(I)` only through the
containment `I ≤ M(I)` and the local principal generator. Not in the sources. -/
theorem _root_.Ideal.span_singleton_mul_colon_of_le {R : Type*} [CommRing R] {g : R} {I : Ideal R}
    (hle : I ≤ Ideal.span {g}) :
    Ideal.span {g} * Submodule.colon I (↑(Ideal.span {g}) : Set R) = I := by
  apply le_antisymm
  · rw [Ideal.mul_le]
    intro x hx y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
    have hyg : y * g ∈ I := by
      have := Submodule.mem_colon.mp hy g (Ideal.mem_span_singleton_self g)
      rwa [smul_eq_mul] at this
    have hrw : g * c * y = c * (y * g) := by ring
    rw [hrw]
    exact I.mul_mem_left c hyg
  · intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp (hle ha)
    have hb : b ∈ Submodule.colon I (↑(Ideal.span {g}) : Set R) := by
      rw [Submodule.mem_colon]
      intro s hs
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hs
      rw [smul_eq_mul]
      have hrw : b * (g * d) = g * b * d := by ring
      rw [hrw]
      exact I.mul_mem_right d ha
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hb

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

variable (F : HypersurfaceFamily M)

/-- At every stalk the monomial part times the nonmonomial part is `I`: `M(I)_x · N(I)_x = I_x`
([Kol07, Definition–Lemma 110]). The stalk `M(I)_x` is principal and contains `I_x`, so
`Ideal.span_singleton_mul_colon_of_le` applies to the colon `N(I)_x = I_x : M(I)_x`. -/
theorem stalkIdeal_monomialPart_mul_nonmonomialPart (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) (x : M) :
    (monomialPart F hF I).stalkIdeal x * (nonmonomialPart F hF I).stalkIdeal x =
      I.stalkIdeal x := by
  obtain ⟨g, _hg, hgspan⟩ := exists_nonZeroDivisor_stalkIdeal_monomialPart F hF I x
  rw [stalkIdeal_nonmonomialPart, hgspan]
  exact Ideal.span_singleton_mul_colon_of_le (hgspan ▸ stalkIdeal_le_monomialPart F hF I x)

end Hironaka.Manifold.BMO
