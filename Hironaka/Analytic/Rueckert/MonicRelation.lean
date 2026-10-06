/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Reexpansion
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Positivity.Finset

/-!
# Monic relations of the fibre coordinates as polynomials over the base

Under a finite Noether normalization, every coordinate `X_i` satisfies a monic relation
`X_i^D + ∑_k c_k(x_base) X_i^k ∈ P` in the coordinates of `σ` (`exists_monic_relation_of_finite`
of `Reexpansion.lean`, in its `shapeSeries` form; the finiteness of [Fre17, Ch. I, 7.2] read as
monic relations). The parametrization theorem (`FibreDivision.lean`) uses the relation as a
polynomial `Qf ∈ 𝒪_d[T]` with `Qf(X_i) ∈ comap σ P`; this module performs the translation.
-/

@[expose] public section

open Polynomial

namespace Analytic

variable {n d : ℕ}

/-- The monic polynomial `T^D + ∑_k C (c k) T^k`. -/
noncomputable def monicOfCoeffs {D : ℕ} (c : Fin D → Conv ℂ d) : Polynomial (Conv ℂ d) :=
  X ^ D + ∑ k : Fin D, C (c k) * X ^ (k : ℕ)

theorem monicOfCoeffs_monic {D : ℕ} (c : Fin D → Conv ℂ d) : (monicOfCoeffs c).Monic :=
  (monic_X_pow D).add_of_left (by rw [degree_X_pow]; exact degree_sum_fin_lt _)

/-- `monicOfCoeffs c` evaluated at `X_i` with coefficients embedded along `e` is the `shapeSeries`
of `Reexpansion.lean` with translation `0`. -/
theorem eval_map_monicOfCoeffs (e : Fin d ↪ Fin n) (i : Fin n) {D : ℕ} (c : Fin D → Conv ℂ d) :
    ((monicOfCoeffs c).map (convEmbed ℂ e).toRingHom).eval (convX ℂ i) =
      shapeSeries ℂ i e 0 c := by
  rw [monicOfCoeffs, shapeSeries]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul,
    eval_C, map_zero, add_zero]
  rfl

/-- Under a finite Noether normalization, every coordinate `X_i` satisfies a monic relation
`Qf(X_i) ∈ comap σ P` with `Qf ∈ 𝒪_d[T]` (from `exists_monic_relation_of_finite`). -/
theorem exists_monic_eval_map_mem_comap (P : Ideal (Conv ℂ n)) (e : Fin d ↪ Fin n)
    (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ))
    (hfin : RingHom.Finite (A := Conv ℂ d) (B := Conv ℂ n ⧸ P)
      (normMap ℂ P e L : Conv ℂ d →+* Conv ℂ n ⧸ P)) (i : Fin n) :
    ∃ Qf : Polynomial (Conv ℂ d), Qf.Monic ∧
      (Qf.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i) ∈ Ideal.comap (substEquiv L) P := by
  obtain ⟨D, c, hc⟩ := exists_monic_relation_of_finite P e L hfin i
  refine ⟨monicOfCoeffs c, monicOfCoeffs_monic c, ?_⟩
  rw [eval_map_monicOfCoeffs, Ideal.mem_comap]
  exact hc

end Analytic
