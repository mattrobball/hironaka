/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Germ.Coordinate
public import Hironaka.Analytic.Rueckert.Embed
public import Hironaka.Analytic.Rueckert.Subst
public import Hironaka.Analytic.Rueckert.ZeroSet
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.Rueckert.Nullstellensatz
import Hironaka.Analytic.Rueckert.Reexpansion
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Zero-set germs under a linear change, graphs as zero sets, and consequences of the Nullstellensatz

Tools for the density of the simple points of a reduced complex space ([Fre17, Ch. II, 5.13],
through the local parametrization theorem of `ParametrizationGraph.lean`): the zero-set germ of
`σ⁻¹(S)`, `σ = substEquiv L`, is `L (V(S))` (`eventually_mem_zeroSet_image_symm_iff`, with
`span_image_symm : span σ⁻¹(S) = comap σ (span S)`, the generating system of an ideal in the
coordinates of `σ`); the graph of an analytic section `φ` of the base projection through a point
`x` is, near `x`, the common zero set of the series `X_j − T_j(X ∘ e)` over the fibre coordinates,
`T_j` the Taylor series of `u ↦ φ (x ∘ e + u) j − x j` (`exists_conv_eventuallyEq_shift`,
`eventually_graph_eq_zero_iff`); and two consequences of Rückert's Nullstellensatz
(`Nullstellensatz.lean`): radical ideals with the same zero-set germ are equal
(`eq_of_isRadical_of_zeroSet_eventuallyEq`), and a prime's zero set has points arbitrarily near
`0` off any `g ∉ P` (`frequently_mem_zeroSet_and_ne_zero`; the zero set of `g` is thin at `0`,
[Fre17, Ch. I, 9.2–9.3]). The zero sets and vanishing ideals are those of `ZeroSet.lean`, the
substitutions those of `Subst.lean`.
-/

public section

open MvPowerSeries Filter Topology

namespace Analytic

variable {K : Type*} [RCLike K] {n : ℕ}

/-- `σ⁻¹ f` is the substitution of `L⁻¹`. -/
theorem substEquiv_symm_apply (L : (Fin n → K) ≃L[K] (Fin n → K)) (f : Conv K n) :
    (substEquiv L).symm f = substConv (L.symm : (Fin n → K) →L[K] (Fin n → K)) f := rfl

/-- The zero set of `σ⁻¹(S)` near `0` is `L (V(S))`. -/
theorem eventually_mem_zeroSet_image_symm_iff [DecidableEq (Conv K n)]
    (L : (Fin n → K) ≃L[K] (Fin n → K)) (S : Finset (Conv K n)) :
    ∀ᶠ x in 𝓝 (0 : Fin n → K),
      (x ∈ zeroSet (S.image (substEquiv L).symm) ↔ L.symm x ∈ zeroSet S) := by
  have h : ∀ᶠ x in 𝓝 (0 : Fin n → K), ∀ g ∈ S,
      evalSeries (((substEquiv L).symm g : Conv K n) : MvPowerSeries (Fin n) K) x =
        evalSeries (g : MvPowerSeries (Fin n) K) (L.symm x) := by
    rw [eventually_all_finset]
    intro g _
    have := evalSeries_substConv (L.symm : (Fin n → K) →L[K] (Fin n → K)) g
    filter_upwards [this] with x hx
    rw [substEquiv_symm_apply, hx]
    rfl
  filter_upwards [h] with x hx
  simp only [mem_zeroSet_iff, Finset.mem_image]
  constructor
  · intro h' g hg
    rw [← hx g hg]
    exact h' _ ⟨g, hg, rfl⟩
  · rintro h' _ ⟨g, hg, rfl⟩
    rw [hx g hg]
    exact h' g hg

/-- `span σ⁻¹(S) = comap σ (span S)`: a generating system of the ideal in the coordinates of `σ`. -/
theorem span_image_symm (L : (Fin n → K) ≃L[K] (Fin n → K)) (S : Finset (Conv K n))
    [DecidableEq (Conv K n)] :
    Ideal.span ((S.image (substEquiv L).symm : Finset (Conv K n)) : Set (Conv K n)) =
      Ideal.comap (substEquiv L) (Ideal.span (S : Set (Conv K n))) := by
  rw [Finset.coe_image]
  have : (⇑(substEquiv L).symm : Conv K n → Conv K n) = ⇑((substEquiv L).toRingEquiv.symm) := rfl
  rw [this, ← Ideal.map_span, Ideal.map_symm]
  rfl

/-- Rückert's Nullstellensatz for radical ideals with the same zero-set germ: they are equal. -/
theorem eq_of_isRadical_of_zeroSet_eventuallyEq {I₁ I₂ : Ideal (Conv ℂ n)} (h₁ : I₁.IsRadical)
    (h₂ : I₂.IsRadical) {S₁ S₂ : Finset (Conv ℂ n)} (hS₁ : Ideal.span (S₁ : Set (Conv ℂ n)) = I₁)
    (hS₂ : Ideal.span (S₂ : Set (Conv ℂ n)) = I₂)
    (h : ∀ᶠ x in 𝓝 (0 : Fin n → ℂ), (x ∈ zeroSet S₁ ↔ x ∈ zeroSet S₂)) : I₁ = I₂ := by
  have hv : vanishingIdeal I₁ = vanishingIdeal I₂ := by
    ext g
    rw [mem_vanishingIdeal_iff hS₁, mem_vanishingIdeal_iff hS₂]
    constructor
    · intro hg
      filter_upwards [hg, h] with x hx hx'
      exact fun h2 => hx (hx'.mpr h2)
    · intro hg
      filter_upwards [hg, h] with x hx hx'
      exact fun h1 => hx (hx'.mp h1)
  rw [vanishingIdeal_eq_radical, vanishingIdeal_eq_radical, h₁.radical, h₂.radical] at hv
  exact hv

/-- Rückert's contrapositive: off a series `g ∉ P`, the zero set of the prime `P` has points
arbitrarily near `0`. -/
theorem frequently_mem_zeroSet_and_ne_zero {P : Ideal (Conv ℂ n)} [hP : P.IsPrime]
    {S : Finset (Conv ℂ n)} (hS : Ideal.span (S : Set (Conv ℂ n)) = P) {g : Conv ℂ n}
    (hg : g ∉ P) :
    ∃ᶠ x in 𝓝 (0 : Fin n → ℂ), x ∈ zeroSet S ∧ evalSeries (g : MvPowerSeries (Fin n) ℂ) x ≠ 0 := by
  have hnot : g ∉ vanishingIdeal P := by
    rw [vanishingIdeal_eq_radical, hP.radical]
    exact hg
  rw [mem_vanishingIdeal_iff hS] at hnot
  unfold VanishesOn at hnot
  rw [Filter.not_eventually] at hnot
  exact hnot.mono fun x hx => Classical.not_imp.mp hx


variable {d : ℕ}

/-- The Taylor series at `0` of `u ↦ g (u₀ + u)` for `g` analytic at `u₀`. -/
theorem exists_conv_eventuallyEq_shift {g : (Fin d → ℂ) → ℂ} {u₀ : Fin d → ℂ}
    (hg : AnalyticAt ℂ g u₀) :
    ∃ T : Conv ℂ d, ∀ᶠ u in 𝓝 (0 : Fin d → ℂ),
      g (u₀ + u) = evalSeries (T : MvPowerSeries (Fin d) ℂ) u := by
  have h : AnalyticAt ℂ (fun u : Fin d → ℂ => g (u₀ + u)) 0 := by
    have := hg.comp_of_eq (f := fun u : Fin d → ℂ => u₀ + u) (x := 0)
      (analyticAt_const.add analyticAt_id) (by simp)
    exact this
  obtain ⟨ρ, c, hc, h'⟩ := AnalyticAt.exists_eventuallyEq_evalSeries h
  refine ⟨⟨c, ρ, hc⟩, h'.mono fun u hu => ?_⟩
  simpa using hu

/-- `Conv`-level evaluation of a difference near `0`. -/
theorem evalSeries_conv_sub_eventually (f g : Conv ℂ n) :
    evalSeries ((f - g : Conv ℂ n) : MvPowerSeries (Fin n) ℂ) =ᶠ[𝓝 (0 : Fin n → ℂ)] fun x =>
      evalSeries (f : MvPowerSeries (Fin n) ℂ) x - evalSeries (g : MvPowerSeries (Fin n) ℂ) x := by
  have hfg : f - g = f + algebraMap ℂ (Conv ℂ n) (-1) * g := by
    rw [map_neg, map_one]
    ring
  rw [hfg]
  filter_upwards [evalSeries_conv_add_eventually f (algebraMap ℂ (Conv ℂ n) (-1) * g),
    evalSeries_conv_mul_eventually (algebraMap ℂ (Conv ℂ n) (-1)) g] with x h1 h2
  rw [h1, h2, evalSeries_algebraMap_conv, neg_one_mul, sub_eq_add_neg]

/-- The graph of a section `φ` of the base projection through `x`, as the common zero set near `0`
of the series `X_j − T_j(X ∘ e)` over the fibre coordinates, `T_j` the Taylor series of
`u ↦ φ (x ∘ e + u) j − x j`. -/
theorem eventually_graph_eq_zero_iff (e : Fin d ↪ Fin n) (φ : (Fin d → ℂ) → (Fin n → ℂ))
    (x : Fin n → ℂ) (hφe : ∀ u, φ u ∘ e = u) (T : Fin n → Conv ℂ d)
    (hT : ∀ j, j ∉ Set.range e → ∀ᶠ u in 𝓝 (0 : Fin d → ℂ),
      φ (x ∘ e + u) j - x j = evalSeries (T j : MvPowerSeries (Fin d) ℂ) u) :
    ∀ᶠ y' in 𝓝 (0 : Fin n → ℂ),
      ((∀ j, j ∉ Set.range e →
        evalSeries ((convX ℂ j - convEmbed ℂ e (T j) : Conv ℂ n) : MvPowerSeries (Fin n) ℂ) y' = 0)
        ↔ x + y' = φ ((x + y') ∘ e)) := by
  have hT' : ∀ᶠ y' in 𝓝 (0 : Fin n → ℂ), ∀ j, j ∉ Set.range e →
      φ (x ∘ e + y' ∘ e) j - x j = evalSeries (T j : MvPowerSeries (Fin d) ℂ) (y' ∘ e) := by
    rw [eventually_all]
    intro j
    by_cases hj : j ∉ Set.range e
    · filter_upwards [(tendsto_comp_embedding e).eventually (hT j hj)] with y' h _
      exact h
    · exact Eventually.of_forall fun _ h => absurd h hj
  have hsub : ∀ᶠ y' in 𝓝 (0 : Fin n → ℂ), ∀ j,
      evalSeries ((convX ℂ j - convEmbed ℂ e (T j) : Conv ℂ n) : MvPowerSeries (Fin n) ℂ) y' =
        y' j - evalSeries (T j : MvPowerSeries (Fin d) ℂ) (y' ∘ e) := by
    rw [eventually_all]
    intro j
    filter_upwards [evalSeries_conv_sub_eventually (convX ℂ j) (convEmbed ℂ e (T j))] with y' h
    rw [h, evalSeries_convX, evalSeries_convEmbed]
  have hx : ∀ y' : Fin n → ℂ, x ∘ e + y' ∘ e = (x + y') ∘ e := fun y' => by
    funext k
    simp
  filter_upwards [hT', hsub] with y' h1 h2
  constructor
  · intro h
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hj
      have := congrFun (hφe ((x + y') ∘ e)) k
      exact this.symm
    · have h3 := h1 j hj
      rw [hx] at h3
      have h4 := h j hj
      rw [h2 j] at h4
      rw [Pi.add_apply]
      linear_combination h4 - h3
  · intro h j hj
    rw [h2 j]
    have h3 := h1 j hj
    rw [hx, ← h, Pi.add_apply] at h3
    linear_combination h3

end Analytic
