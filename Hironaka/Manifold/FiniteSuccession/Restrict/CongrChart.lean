/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A blowing-up does not depend on the linear chart `ψ`

A finite succession carries one chosen linear chart `ψ_i : E ≃ 𝕜^{n_i}` per step
(`FiniteSuccession.chartAt`, extracted from the monoidality witness of the step), while the
restriction of a succession to a closed submanifold `S ⊆ M` [Kol07, Definition 30.2], given for one
chart `ψ`, has to read every step's blowing-up in that chart. As for closed submanifolds
(`IsClosedSubmanifold.congr_chart`), the notion "blowing-up along `Y` of codimension `c`" in the
sense of [BM88, Definition 4.1] (`IsBlowUp`) does not depend on `ψ`: `n = n'` by dimension, and the
linear automorphism `L = ψ'⁻¹ ∘ ψ` of `E` carries the adapted charts and the blow-up charts for `ψ`
to those for `ψ'`, with the same coordinate functions (`IsBlowUp.congr_chart`). Not in the sources;
the proof is a routine transport of charts.
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ} {M' : Type u} [TopologicalSpace M']
  [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']
  {π : M' → M}

/-- Membership in the image of a set under a continuous linear equivalence. -/
theorem mem_image_clm_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E ≃L[𝕜] F)
    (T : Set E) (w : F) : w ∈ e '' T ↔ e.symm w ∈ T := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [e.symm_apply_apply]
  · intro hw
    exact ⟨e.symm w, hw, e.apply_symm_apply w⟩

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The notion "blowing-up along `Y` of codimension `c`" does not depend on the linear chart
`ψ : E ≃ 𝕜ⁿ`: the adapted charts and the blow-up charts for `ψ'` are those for `ψ` composed with
the linear automorphism `ψ'⁻¹ ∘ ψ` of `E`, with the same coordinate functions. -/
theorem IsBlowUp.congr_chart {n' : ℕ} (ψ' : E ≃L[𝕜] (Fin n' → 𝕜)) (h : IsBlowUp ψ Y c π) :
    IsBlowUp ψ' Y c π := by
  have hn : n = n' := by
    have h := (ψ.symm.trans ψ').toLinearEquiv.finrank_eq
    simpa [Module.finrank_fin_fun] using h
  subst hn
  set L : E ≃L[𝕜] E := ψ.trans ψ'.symm with hLdef
  have hL : ∀ v, ψ' (L v) = ψ v := fun v => ψ'.apply_symm_apply (ψ v)
  have hL' : ∀ w, ψ (L.symm w) = ψ' w := fun w => by
    rw [hLdef, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
      ψ.apply_symm_apply]
  have hLg : L.toHomeomorph.toOpenPartialHomeomorph ∈ contDiffGroupoid ω 𝓘(𝕜, E) :=
    mem_contDiffGroupoid_self _ L.contDiff.contDiffOn L.symm.contDiff.contDiffOn
  have hLg' : L.symm.toHomeomorph.toOpenPartialHomeomorph ∈ contDiffGroupoid ω 𝓘(𝕜, E) :=
    mem_contDiffGroupoid_self _ L.symm.contDiff.contDiffOn L.symm.symm.contDiff.contDiffOn
  -- the adapted charts for `ψ'` read through `L⁻¹` are adapted charts for `ψ`
  have hAd : ∀ (φ' : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), IsAdaptedChart ψ' Y φ' σ →
      IsAdaptedChart ψ Y (φ'.trans L.symm.toHomeomorph.toOpenPartialHomeomorph) σ := by
    intro φ' σ hφ'
    refine ⟨trans_mem_maximalAtlas hφ'.1 hLg', fun x hx => ?_⟩
    rw [OpenPartialHomeomorph.trans_source] at hx
    rw [hφ'.2 x hx.1]
    refine forall_congr' fun i => ?_
    change ψ' (φ' x) (σ i) = 0 ↔ ψ (L.symm (φ' x)) (σ i) = 0
    rw [hL']
  -- the images of the targets agree
  have hT : ∀ φ' : OpenPartialHomeomorph M E,
      ψ '' (φ'.trans L.symm.toHomeomorph.toOpenPartialHomeomorph).target = ψ' '' φ'.target := by
    intro φ'
    ext w
    rw [mem_image_clm_iff, mem_image_clm_iff, OpenPartialHomeomorph.trans_target]
    change ψ.symm w ∈ Set.univ ∧ L (ψ.symm w) ∈ φ'.target ↔ ψ'.symm w ∈ φ'.target
    have e2 : L (ψ.symm w) = ψ'.symm w := by
      rw [hLdef, ContinuousLinearEquiv.trans_apply, ψ.apply_symm_apply]
    rw [e2]
    exact ⟨fun h => h.2, fun h => ⟨Set.mem_univ _, h⟩⟩
  -- the blow-up charts for `ψ` composed with `L` are blow-up charts for `ψ'`
  have hBC : ∀ (φ' : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (i : Fin c)
      (Φ : OpenPartialHomeomorph M' E),
      IsBlowUpChart ψ π (φ'.trans L.symm.toHomeomorph.toOpenPartialHomeomorph) σ i Φ →
        IsBlowUpChart ψ' π φ' σ i (Φ.trans L.toHomeomorph.toOpenPartialHomeomorph) := by
    intro φ' σ i Φ hΦ
    refine ⟨trans_mem_maximalAtlas hΦ.mem_maximalAtlas hLg, fun p hp => ?_, fun v => ?_,
      fun p hp => ?_⟩
    · exact (hΦ.source_subset hp.1).1
    · rw [OpenPartialHomeomorph.trans_target]
      change v ∈ Set.univ ∧ L.symm v ∈ Φ.target ↔ _
      rw [hΦ.mem_target_iff, hL', hT]
      exact ⟨fun h => h.2, fun h => ⟨Set.mem_univ _, h⟩⟩
    · change ψ' (φ' (π p)) = blowUpChartMap σ i (ψ' (L (Φ p)))
      rw [hL]
      have h1 := hΦ.comm p hp.1
      change ψ (L.symm (φ' (π p))) = _ at h1
      rw [hL'] at h1
      exact h1
  refine
    { contMDiff := h.contMDiff
      isProperMap := h.isProperMap
      isLocalDiffeomorphOn_compl := h.isLocalDiffeomorphOn_compl
      bijOn_compl := h.bijOn_compl
      exists_chart := fun φ' σ hφ' i => ?_
      cover := fun φ' σ hφ' p hp => ?_ }
  · obtain ⟨Φ, hΦ⟩ := h.exists_chart _ σ (hAd φ' σ hφ') i
    exact ⟨_, hBC φ' σ i Φ hΦ⟩
  · obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover _ σ (hAd φ' σ hφ') p ⟨hp, Set.mem_univ _⟩
    exact ⟨i, _, hBC φ' σ i Φ hΦ, ⟨hpΦ, Set.mem_univ _⟩⟩

end Manifold

end
