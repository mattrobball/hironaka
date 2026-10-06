/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Blow-up charts of the local model

Let `𝕜` be `ℝ` or `ℂ`. The blowing-up of an open neighbourhood `V` of `0` in `𝕜^m` with centre
`{0}` is covered by the charts `V'_i = {ξ_i ≠ 0}`, `i = 1, …, m`, with coordinates `x_ii = x_i` and
`x_ij = ξ_j / ξ_i` for `j ≠ i` [BM88, Definition 4.1]; `blowUpChartMap σ i` is the chart map `π_i`
in *block form* on `𝕜^n`, the centre being the coordinate subspace `{x_{σ k} = 0}` cut out by an
embedding `σ : Fin c ↪ Fin n` (the block need not consist of consecutive coordinates) and the
coordinates off the block being carried along unchanged. This file adds the rest of the chart
data of the local model and the pointwise unfoldings:

* `blowUpChartMap_apply_scaling`, `blowUpChartMap_apply_ratio`, `blowUpChartMap_apply_off`: slot
  `σ i` is the scaling variable, the block slots `σ k` with `k ≠ i` are multiplied by it, the
  coordinates off the block pass through;
* `blowUpCenter σ` is the centre `{x_{σ k} = 0}`;
* `blowUpTransition σ i k` is the transition map from chart `i` to chart `k`:
  `u'_{σ k} = u_{σ i} u_{σ k}`, `u'_{σ i} = 1 / u_{σ k}`, `u'_{σ j} = u_{σ j} / u_{σ k}` for
  `j ≠ i, k`, the identity off the block (in the coordinates of the source,
  `x_{kj} = ξ_j / ξ_k = x_{ij} / x_{ik}`); its domain `blowUpTransitionDomain σ i k` is
  `{u_{σ k} ≠ 0}`, the whole space when `i = k`;
* `blowUpChartInv σ i` is the inverse of `π_i` off the hyperplane `{x_{σ i} = 0}`.

The identity `π_k ∘ T_ik = π_i`, the inverse and cocycle laws, analyticity and the compactness
estimate are proved in `Hironaka.Manifold.BlowUp.Transition`.
-/

@[expose] public section

open scoped ContDiff

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ}

/-- The centre of the blow-up in block form: the coordinate subspace `{x_{σ k} = 0}`. -/
def blowUpCenter (σ : Fin c ↪ Fin n) : Set (Fin n → 𝕜) := {x | ∀ k, x (σ k) = 0}

/-- The transition map from blow-up chart `i` to blow-up chart `k`, defined where `u_{σ k} ≠ 0`
(and the identity for `i = k`); in the coordinates of [BM88, Definition 4.1] it is
`x_{kj} = ξ_j / ξ_k = x_{ij} / x_{ik}`. -/
noncomputable def blowUpTransition (σ : Fin c ↪ Fin n) (i k : Fin c) :
    (Fin n → 𝕜) → (Fin n → 𝕜) := by
  classical
  exact if i = k then id else fun u j =>
    if j = σ k then u (σ i) * u (σ k)
    else if j = σ i then (u (σ k))⁻¹
    else if ∃ l, σ l = j then u j / u (σ k) else u j

/-- The domain of the transition map from chart `i` to chart `k`: `{u_{σ k} ≠ 0}` (the whole space
for `i = k`). -/
def blowUpTransitionDomain (σ : Fin c ↪ Fin n) (i k : Fin c) : Set (Fin n → 𝕜) :=
  if i = k then Set.univ else {u | u (σ k) ≠ 0}

section Apply

variable (σ : Fin c ↪ Fin n) {i k : Fin c} (u : Fin n → 𝕜)

@[simp]
theorem blowUpChartMap_apply_scaling : blowUpChartMap σ i u (σ i) = u (σ i) := by
  classical
  simp [blowUpChartMap]

theorem blowUpChartMap_apply_ratio (hk : k ≠ i) :
    blowUpChartMap σ i u (σ k) = u (σ i) * u (σ k) := by
  classical
  simp [blowUpChartMap, hk]

theorem blowUpChartMap_apply_off {j : Fin n} (hj : ∀ k, σ k ≠ j) :
    blowUpChartMap σ i u j = u j := by
  classical
  have h : ¬ ∃ k, k ≠ i ∧ σ k = j := fun ⟨k, _, hkj⟩ => hj k hkj
  simp [blowUpChartMap, h]

theorem blowUpTransition_self (i : Fin c) : blowUpTransition (𝕜 := 𝕜) σ i i = id := by
  simp [blowUpTransition]

theorem blowUpTransition_apply_k (hik : i ≠ k) :
    blowUpTransition σ i k u (σ k) = u (σ i) * u (σ k) := by
  classical
  simp [blowUpTransition, hik]

theorem blowUpTransition_apply_i (hik : i ≠ k) : blowUpTransition σ i k u (σ i) = (u (σ k))⁻¹ := by
  classical
  have h : σ i ≠ σ k := fun h => hik (σ.injective h)
  simp [blowUpTransition, hik, h]

theorem blowUpTransition_apply_block (hik : i ≠ k) {l : Fin c} (hli : l ≠ i) (hlk : l ≠ k) :
    blowUpTransition σ i k u (σ l) = u (σ l) / u (σ k) := by
  classical
  have h1 : σ l ≠ σ k := fun h => hlk (σ.injective h)
  have h2 : σ l ≠ σ i := fun h => hli (σ.injective h)
  simp [blowUpTransition, hik, h1, h2]

theorem blowUpTransition_apply_off (hik : i ≠ k) {j : Fin n} (hj : ∀ l, σ l ≠ j) :
    blowUpTransition σ i k u j = u j := by
  classical
  have h1 : j ≠ σ k := fun h => hj k h.symm
  have h2 : j ≠ σ i := fun h => hj i h.symm
  have h3 : ¬ ∃ l, σ l = j := fun ⟨l, hl⟩ => hj l hl
  simp [blowUpTransition, hik, h1, h2, h3]

theorem mem_blowUpTransitionDomain (hik : i ≠ k) :
    u ∈ blowUpTransitionDomain σ i k ↔ u (σ k) ≠ 0 := by
  simp [blowUpTransitionDomain, hik]

theorem blowUpTransitionDomain_self (i : Fin c) :
    blowUpTransitionDomain (𝕜 := 𝕜) σ i i = Set.univ := by
  simp [blowUpTransitionDomain]

end Apply

/-- The inverse of the chart map `π_i` off the hyperplane `{x_{σ i} = 0}`: `u_{σ i} = x_{σ i}`,
`u_{σ k} = x_{σ k} / x_{σ i}` for `k ≠ i`, and the identity off the block (the coordinates
`x_ij = ξ_j / ξ_i` of [BM88, Definition 4.1]). -/
noncomputable def blowUpChartInv (σ : Fin c ↪ Fin n) (i : Fin c) :
    (Fin n → 𝕜) → (Fin n → 𝕜) := by
  classical
  exact fun x j => if ∃ k, k ≠ i ∧ σ k = j then x j / x (σ i) else x j

theorem blowUpChartInv_apply_scaling (σ : Fin c ↪ Fin n) {i : Fin c} (x : Fin n → 𝕜) :
    blowUpChartInv σ i x (σ i) = x (σ i) := by
  classical
  simp [blowUpChartInv]

theorem blowUpChartInv_apply_ratio (σ : Fin c ↪ Fin n) {i k : Fin c} (x : Fin n → 𝕜) (hk : k ≠ i) :
    blowUpChartInv σ i x (σ k) = x (σ k) / x (σ i) := by
  classical
  simp [blowUpChartInv, hk]

theorem blowUpChartInv_apply_off (σ : Fin c ↪ Fin n) {i : Fin c} (x : Fin n → 𝕜) {j : Fin n}
    (hj : ∀ k, σ k ≠ j) : blowUpChartInv σ i x j = x j := by
  classical
  have h : ¬ ∃ k, k ≠ i ∧ σ k = j := fun ⟨k, _, hkj⟩ => hj k hkj
  simp [blowUpChartInv, h]

end Manifold
