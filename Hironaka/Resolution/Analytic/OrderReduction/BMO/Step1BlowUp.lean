/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Transform.StrictCharts
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Algebra.ColonPow
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.LogDerivTransform
import Hironaka.Manifold.BlowUp.Transform.MarkedAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The total transform as the exceptional power times the marked transform

For a blow-up `π : M' → M` with centre `Y` and exceptional divisor `F`, the marked transform of a
marked ideal `(J, k)` with `k ≤ ord_Y J` is defined by `π_*^{-1}(J, k) := (𝒪(kF) · π^* J, k)`
[Kol07, Definition 60, (60.1)], that is, by dividing the `k`-th power of the ideal of `F` out of the
total transform `π^* J`. This file states the definition as a product: at every point of `M'`,
`π^*(J) = 𝓘_F^k · π_*^{-1}(J, k)` as ideal sheaves
(`totalTransform_eq_exc_pow_mul_birationalTransform`). Over the centre this is the exact division `A
= u^k · (A : u^k)` in the stalk, read in a blow-up chart where the exceptional divisor is a
coordinate hyperplane; off the centre both sides are the pull-back of `J`. As a special case, the
total transform of the ideal sheaf of a smooth hypersurface `D ⊇ Y` is the exceptional ideal times
the ideal of the strict transform of `D`.

Step 1 of the proof of [Kol07, Theorem 107] uses this to compare the marked transform of `(𝓘, m)`
with the transform of the nonmonomial part `N(𝓘)`: the two differ by a power of the exceptional
ideal, which the nonmonomial part ignores (`BMO/Step1PerBlowUp.lean`).
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} (hY : IsClosedSubmanifold ψ Y c)
  (h : IsBlowUp ψ Y c π)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- At a point `p` over the centre in a blow-up chart, the stalk of the total transform `π^* J` is
the `k`-th power of the stalk of the exceptional ideal times the stalk of the marked transform of
`(J, k)`, for `k ≤ ord_Y J`: the exact division `A = u^k · (A : u^k)` of [Kol07, Definition 60,
(60.1)], where `u` is the coordinate of the exceptional divisor in the chart. -/
theorem stalkIdeal_totalTransform_eq_exc_pow_mul_birationalTransform
    {J : IdealSheaf (structureSheaf 𝕜 E M)} {k : ℕ}
    (hk : ∀ x ∈ Y, (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J x)
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {i : Fin c}
    {Φ : OpenPartialHomeomorph M' E} (hφ : IsAdaptedChart ψ Y φ σ) (hΦ : IsBlowUpChart ψ π φ σ i Φ)
    {p : M'} (hp : p ∈ Φ.source) (hpY : π p ∈ Y) :
    (J.pullback π h.contMDiff).stalkIdeal p =
      (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p ^ k *
        (MarkedIdealSheaf.birationalTransform hY h ⟨J, k⟩).I.stalkIdeal p := by
  rw [birationalTransform_stalkIdeal_eq_colon_coord hY h hk hφ hΦ hp,
    stalkIdeal_exceptionalIdealSheaf_eq_span_coord hY h hφ hΦ hp, Ideal.span_singleton_pow]
  exact (Ideal.span_pow_mul_colon_of_le _ _ k
    (totalTransform_stalkIdeal_le_span_coord_pow hY h hk hφ hΦ hp hpY)).symm

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The identity `π^*(J) = 𝓘_F^k · π_*^{-1}(J, k)` as ideal sheaves on the blow-up, for a mark
`k ≤ ord_Y J` [Kol07, Definition 60, (60.1)]: stalkwise, over the centre by the chart computation
`stalkIdeal_totalTransform_eq_exc_pow_mul_birationalTransform`, off the centre because the
exceptional ideal is the unit ideal and the marked transform is the total transform there. -/
theorem totalTransform_eq_exc_pow_mul_birationalTransform
    {J : IdealSheaf (structureSheaf 𝕜 E M)} {k : ℕ}
    (hk : ∀ x ∈ Y, (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J x) :
    J.pullback π h.contMDiff =
      hY.idealSheaf.pullback π h.contMDiff ^ k *
        (MarkedIdealSheaf.birationalTransform hY h ⟨J, k⟩).I := by
  refine IdealSheaf.ext fun p => ?_
  rw [IdealSheaf.stalkIdeal_mul, IdealSheaf.stalkIdeal_pow]
  by_cases hpY : π p ∈ Y
  · obtain ⟨φ, σ, hpφ, hφ⟩ := hY.exists_adaptedChart _ hpY
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hpφ
    exact stalkIdeal_totalTransform_eq_exc_pow_mul_birationalTransform hY h hk hφ hΦ hpΦ hpY
  · rw [stalkIdeal_exceptionalIdealSheaf_of_notMem hY h hpY, Ideal.top_pow, Ideal.top_mul,
      birationalTransform_stalkIdeal_of_notMem hY h hk hpY]

/-- For a smooth hypersurface `D` containing the centre `Y`, the total transform of its ideal sheaf
is the exceptional ideal times the ideal sheaf of the strict transform of `D`:
`π^*(𝓘_D) = 𝓘_F · 𝓘_{D̃}`. The case `k = 1` of `totalTransform_eq_exc_pow_mul_birationalTransform`,
`𝓘_D` having order `≥ 1` along `Y ⊆ D`, together with the identification of the ideal of the strict
transform with the marked transform of `(𝓘_D, 1)`. -/
theorem comap_idealSheaf_eq_exc_mul_strictTransform {D : Set M} (hD : IsClosedSubmanifold ψ D 1)
    (hYD : Y ⊆ D) :
    hD.idealSheaf.pullback π h.contMDiff =
      hY.idealSheaf.pullback π h.contMDiff *
        (isClosedSubmanifold_strictTransform hY h hD hYD).idealSheaf := by
  rw [totalTransform_eq_exc_pow_mul_birationalTransform hY h
      (hY.one_le_ordAlongIdeal_idealSheaf hD hYD), pow_one,
    ← idealSheaf_strictTransform_eq_markedTransform_one hY h hD hYD]

end Hironaka.Manifold.BMO
