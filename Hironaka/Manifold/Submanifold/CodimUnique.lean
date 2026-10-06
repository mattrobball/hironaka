/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The codimension of a nonempty closed submanifold is unique

`IsClosedSubmanifold ψ Y c` carries the codimension `c` as a label; for `Y = ∅` every `c` is
legitimate (`isClosedSubmanifold_empty'`), so the codimension chosen from the monoidality
witnesses of a finite succession (`FiniteSuccession.codim`) is not determined by the centre in
general. For a nonempty `Y` it is: two adapted charts `φ` (for `ψ`, `σ`, codimension `c`) and `φ'`
(for `ψ'`, `σ'`, codimension `c'`) at a point `a ∈ Y` read `Y` as the coordinate subspaces
`{z_σ = 0} ≅ 𝕜^{n-c}` and `{z_{σ'} = 0} ≅ 𝕜^{n'-c'}`; the chart change between the two induced
charts of `Y` (`IsAdaptedChart.chartOn`) is analytic with analytic inverse, so its derivative at
the point is a linear isomorphism `𝕜^{n-c} ≃ 𝕜^{n'-c'}` and `n - c = n' - c'`; with `c ≤ n`,
`c' ≤ n'` and `n = n'` (`E ≃ 𝕜^n ≃ 𝕜^{n'}`) this gives `c = c'`
(`IsClosedSubmanifold.codim_eq_of_nonempty`). The two chart models `ψ`, `ψ'` are allowed to
differ because the chart chosen for a succession need not be the one a list of centres was
written in.

Not in the sources (linear algebra of the chart change). It is used to match the codimensions of
the centres when a blow-up sequence is pushed forward along a closed embedding
([Kol07, 30.3]; the empty-centre proviso is [Kol07, 32]), in
`Hironaka/Manifold/FiniteSuccession/Functor/ToSuccessionPushforward.lean`.
-/

public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Two adapted charts at a common point of `Y`, for the models `ψ : E ≃ 𝕜^n` (codimension `c`)
and `ψ' : E ≃ 𝕜^{n'}` (codimension `c'`), give `n - c = n' - c'`: the chart change between the two
induced charts of `Y` is analytic with analytic inverse, so its derivative at the point is a linear
isomorphism `𝕜^{n-c} ≃ 𝕜^{n'-c'}`. -/
theorem IsAdaptedChart.sub_codim_eq_of_mem {n n' : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
    {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {Y : Set M} {c c' : ℕ} {φ φ' : OpenPartialHomeomorph M E}
    {σ : Fin c ↪ Fin n} {σ' : Fin c' ↪ Fin n'} (h : IsAdaptedChart ψ Y φ σ)
    (h' : IsAdaptedChart ψ' Y φ' σ') {a : M} (ha : a ∈ Y) (haφ : a ∈ φ.source)
    (haφ' : a ∈ φ'.source) : n - c = n' - c' := by
  -- the two chart changes, read on the coordinate subspaces
  set g : (Fin (n - c) → 𝕜) → (Fin (n' - c') → 𝕜) :=
    (projCompl σ' ∘ ψ') ∘ (φ' ∘ φ.symm) ∘ (ψ.symm ∘ embedCompl σ) with hg_def
  set g' : (Fin (n' - c') → 𝕜) → (Fin (n - c) → 𝕜) :=
    (projCompl σ ∘ ψ) ∘ (φ ∘ φ'.symm) ∘ (ψ'.symm ∘ embedCompl σ') with hg'_def
  set U : Set (Fin (n - c) → 𝕜) := (ψ.symm ∘ embedCompl σ) ⁻¹' (φ.target ∩ φ.symm ⁻¹' φ'.source)
    with hU_def
  set U' : Set (Fin (n' - c') → 𝕜) :=
    (ψ'.symm ∘ embedCompl σ') ⁻¹' (φ'.target ∩ φ'.symm ⁻¹' φ.source) with hU'_def
  have hUo : IsOpen U :=
    (φ.isOpen_inter_preimage_symm φ'.open_source).preimage
      (ψ.symm.continuous.comp (contDiff_embedCompl σ).continuous)
  have hU'o : IsOpen U' :=
    (φ'.isOpen_inter_preimage_symm φ.open_source).preimage
      (ψ'.symm.continuous.comp (contDiff_embedCompl σ').continuous)
  -- the base points
  set w₀ : Fin (n - c) → 𝕜 := projCompl σ (ψ (φ a)) with hw₀_def
  set v₀ : Fin (n' - c') → 𝕜 := projCompl σ' (ψ' (φ' a)) with hv₀_def
  have hew₀ : embedCompl σ w₀ = ψ (φ a) := embedCompl_projCompl σ ((h.2 a haφ).mp ha)
  have hev₀ : embedCompl σ' v₀ = ψ' (φ' a) := embedCompl_projCompl σ' ((h'.2 a haφ').mp ha)
  have hw₀U : w₀ ∈ U := by
    change ψ.symm (embedCompl σ w₀) ∈ φ.target ∩ φ.symm ⁻¹' φ'.source
    rw [hew₀, ψ.symm_apply_apply]
    exact ⟨φ.map_source haφ, by rw [Set.mem_preimage, φ.left_inv haφ]; exact haφ'⟩
  have hv₀U' : v₀ ∈ U' := by
    change ψ'.symm (embedCompl σ' v₀) ∈ φ'.target ∩ φ'.symm ⁻¹' φ.source
    rw [hev₀, ψ'.symm_apply_apply]
    exact ⟨φ'.map_source haφ', by rw [Set.mem_preimage, φ'.left_inv haφ']; exact haφ⟩
  have hgw₀ : g w₀ = v₀ := by
    simp only [hg_def, hv₀_def, Function.comp_apply, hew₀, ψ.symm_apply_apply, φ.left_inv haφ]
  have hg'v₀ : g' v₀ = w₀ := by
    simp only [hg'_def, hw₀_def, Function.comp_apply, hev₀, ψ'.symm_apply_apply, φ'.left_inv haφ']
  -- the chart changes are analytic on the open sets
  have hgC : ContDiffOn 𝕜 ω g U :=
    ((contDiff_projCompl σ').comp ψ'.contDiff).comp_contDiffOn
      ((contDiffOn_chartChange h.1 h'.1).comp
        ((ψ.symm.contDiff.comp (contDiff_embedCompl σ)).contDiffOn) fun _ hw => hw)
  have hg'C : ContDiffOn 𝕜 ω g' U' :=
    ((contDiff_projCompl σ).comp ψ.contDiff).comp_contDiffOn
      ((contDiffOn_chartChange h'.1 h.1).comp
        ((ψ'.symm.contDiff.comp (contDiff_embedCompl σ')).contDiffOn) fun _ hv => hv)
  -- they are mutually inverse on the open sets
  have hinv : ∀ w ∈ U, g' (g w) = w := by
    intro w hw
    have hw₁ : ψ.symm (embedCompl σ w) ∈ φ.target := hw.1
    have hw₂ : φ.symm (ψ.symm (embedCompl σ w)) ∈ φ'.source := hw.2
    have hxφ : φ.symm (ψ.symm (embedCompl σ w)) ∈ φ.source := φ.map_target hw₁
    have hxY : φ.symm (ψ.symm (embedCompl σ w)) ∈ Y := by
      refine (h.2 _ hxφ).mpr fun i => ?_
      rw [φ.right_inv hw₁, ψ.apply_symm_apply, embedCompl_apply_range]
    simp only [hg_def, hg'_def, Function.comp_apply]
    rw [embedCompl_projCompl σ' ((h'.2 _ hw₂).mp hxY), ψ'.symm_apply_apply, φ'.left_inv hw₂,
      φ.right_inv hw₁, ψ.apply_symm_apply, projCompl_embedCompl]
  have hinv' : ∀ v ∈ U', g (g' v) = v := by
    intro v hv
    have hv₁ : ψ'.symm (embedCompl σ' v) ∈ φ'.target := hv.1
    have hv₂ : φ'.symm (ψ'.symm (embedCompl σ' v)) ∈ φ.source := hv.2
    have hxφ' : φ'.symm (ψ'.symm (embedCompl σ' v)) ∈ φ'.source := φ'.map_target hv₁
    have hxY : φ'.symm (ψ'.symm (embedCompl σ' v)) ∈ Y := by
      refine (h'.2 _ hxφ').mpr fun i => ?_
      rw [φ'.right_inv hv₁, ψ'.apply_symm_apply, embedCompl_apply_range]
    simp only [hg_def, hg'_def, Function.comp_apply]
    rw [embedCompl_projCompl σ ((h.2 _ hv₂).mp hxY), ψ.symm_apply_apply, φ.left_inv hv₂,
      φ'.right_inv hv₁, ψ'.apply_symm_apply, projCompl_embedCompl]
  -- derivatives at the base points
  have hgD : HasFDerivAt g (fderiv 𝕜 g w₀) w₀ :=
    ((hgC.differentiableOn WithTop.top_ne_zero).differentiableAt (hUo.mem_nhds hw₀U)).hasFDerivAt
  have hg'D : HasFDerivAt g' (fderiv 𝕜 g' v₀) v₀ :=
    ((hg'C.differentiableOn WithTop.top_ne_zero).differentiableAt
      (hU'o.mem_nhds hv₀U')).hasFDerivAt
  have hg'D' : HasFDerivAt g' (fderiv 𝕜 g' v₀) (g w₀) := by rwa [hgw₀]
  have hgD' : HasFDerivAt g (fderiv 𝕜 g w₀) (g' v₀) := by rwa [hg'v₀]
  -- chain rule: the two derivatives are mutually inverse
  have hcomp₁ : (fderiv 𝕜 g' v₀).comp (fderiv 𝕜 g w₀) = ContinuousLinearMap.id 𝕜 _ := by
    have h1 : HasFDerivAt (g' ∘ g) ((fderiv 𝕜 g' v₀).comp (fderiv 𝕜 g w₀)) w₀ := hg'D'.comp w₀ hgD
    have h2 : HasFDerivAt id ((fderiv 𝕜 g' v₀).comp (fderiv 𝕜 g w₀)) w₀ :=
      h1.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hUo.mem_nhds hw₀U)
        fun w hw => (hinv w hw).symm)
    exact h2.unique (hasFDerivAt_id w₀)
  have hcomp₂ : (fderiv 𝕜 g w₀).comp (fderiv 𝕜 g' v₀) = ContinuousLinearMap.id 𝕜 _ := by
    have h1 : HasFDerivAt (g ∘ g') ((fderiv 𝕜 g w₀).comp (fderiv 𝕜 g' v₀)) v₀ := hgD'.comp v₀ hg'D
    have h2 : HasFDerivAt id ((fderiv 𝕜 g w₀).comp (fderiv 𝕜 g' v₀)) v₀ :=
      h1.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hU'o.mem_nhds hv₀U')
        fun v hv => (hinv' v hv).symm)
    exact h2.unique (hasFDerivAt_id v₀)
  -- the linear isomorphism and the dimensions
  let e : (Fin (n - c) → 𝕜) ≃L[𝕜] (Fin (n' - c') → 𝕜) :=
    ContinuousLinearEquiv.equivOfInverse (fderiv 𝕜 g w₀) (fderiv 𝕜 g' v₀)
      (fun w => by
        have := congrArg (fun L : (Fin (n - c) → 𝕜) →L[𝕜] (Fin (n - c) → 𝕜) => L w) hcomp₁
        simpa using this)
      (fun v => by
        have := congrArg (fun L : (Fin (n' - c') → 𝕜) →L[𝕜] (Fin (n' - c') → 𝕜) => L v) hcomp₂
        simpa using this)
  have := e.toLinearEquiv.finrank_eq
  simpa [Module.finrank_fin_fun] using this

/-- **The codimension of a nonempty closed submanifold is unique**, across chart models: if `Y` is
a closed submanifold of codimension `c` for `ψ : E ≃ 𝕜^n` and of codimension `c'` for
`ψ' : E ≃ 𝕜^{n'}`, and `Y ≠ ∅`, then `c = c'` (two adapted charts at a point of `Y`,
`IsAdaptedChart.sub_codim_eq_of_mem`, with `c ≤ n`, `c' ≤ n'` and `n = n'`). For `Y = ∅` the
codimension is free (`isClosedSubmanifold_empty'`), the case Kollár's empty-blow-up convention
[Kol07, 32] sets aside. -/
theorem IsClosedSubmanifold.codim_eq_of_nonempty {n n' : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
    {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)} {Y : Set M} {c c' : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    (hY' : IsClosedSubmanifold ψ' Y c') (hne : Y.Nonempty) : c = c' := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨φ, σ, haφ, h⟩ := hY.exists_adaptedChart a ha
  obtain ⟨φ', σ', haφ', h'⟩ := hY'.exists_adaptedChart a ha
  have hsub : n - c = n' - c' := h.sub_codim_eq_of_mem h' ha haφ haφ'
  have hc : c ≤ n := by simpa using Fintype.card_le_of_embedding σ
  have hc' : c' ≤ n' := by simpa using Fintype.card_le_of_embedding σ'
  have hn : n = n' := by
    have := (ψ.toLinearEquiv.symm.trans ψ'.toLinearEquiv).finrank_eq
    simpa [Module.finrank_fin_fun] using this
  omega

end Manifold

end
