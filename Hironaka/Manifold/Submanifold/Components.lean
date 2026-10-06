/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# Connected components of a closed submanifold

The connected components of a closed submanifold are closed submanifolds of the same codimension,
and the family of components is locally finite. The one geometric input is that an adapted chart
`(φ, σ)` at a point of `Y` gives `Y` connected open neighbourhoods, arbitrarily small: the inverse
image under the induced chart `IsAdaptedChart.chartOn` of a small ball of `𝕜^{n-c}` (a ball is
convex, hence preconnected, and the inverse chart is continuous on it;
`exists_preconnected_mem_nhds`). Hence `Y` is locally connected (`locallyConnectedSpace'`), each
component is open in `Y` — so, shrinking an adapted chart to an open set of `M` meeting `Y` inside
the component, adapted for the component — and closed in `M` (`connectedComponent'`), every point
of `M` has a neighbourhood meeting at most one component (`locallyFinite_connectedComponents'`),
and every point `b ∈ Y` has an adapted chart whose source meets `Y` only inside the component of
`b` (`exists_adaptedChart_source_inter_subset`). Not in the sources; these are the topological
facts behind the treatment of the components of a centre (Hironaka's centres are irreducible; the
algorithm's centres are unions of components, blown up one at a time or together).
-/

public noncomputable section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Y : Set M} {φ : OpenPartialHomeomorph M E} {c : ℕ} {σ : Fin c ↪ Fin n}

/-- Inside any neighbourhood of a point of `Y` lying in the source of an adapted chart there is an
open connected neighbourhood: the inverse image of a small ball under the induced chart. -/
theorem IsAdaptedChart.exists_preconnected_mem_nhds (h : IsAdaptedChart ψ Y φ σ) {a : M}
    (ha : a ∈ Y) (has : a ∈ φ.source) {U : Set Y} (hU : U ∈ 𝓝 (⟨a, ha⟩ : Y)) :
    ∃ V ∈ 𝓝 (⟨a, ha⟩ : Y), IsOpen V ∧ IsPreconnected V ∧ V ⊆ U := by
  set e := h.chartOn ha with he
  have hx : (⟨a, ha⟩ : Y) ∈ e.source := has
  have hU' : U ∈ 𝓝 (e.symm (e ⟨a, ha⟩)) := by rwa [e.left_inv hx]
  have h1 : e.symm ⁻¹' U ∈ 𝓝 (e ⟨a, ha⟩) :=
    (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds hU'
  have h2 : e.target ∈ 𝓝 (e ⟨a, ha⟩) := e.open_target.mem_nhds (e.map_source hx)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem h1 h2)
  have hsub : Metric.ball (e ⟨a, ha⟩) r ⊆ e.target := hball.trans inter_subset_right
  have hopen : IsOpen (e.symm '' Metric.ball (e ⟨a, ha⟩) r) := by
    rw [e.symm_image_eq_source_inter_preimage hsub]
    exact e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨e.symm '' Metric.ball (e ⟨a, ha⟩) r, hopen.mem_nhds ⟨_, Metric.mem_ball_self hr,
    e.left_inv hx⟩, hopen, ?_, ?_⟩
  · exact (convex_ball _ _).isPreconnected.image _ (e.continuousOn_symm.mono hsub)
  · rintro _ ⟨w, hw, rfl⟩
    exact (hball hw).1

/-- A closed submanifold is locally connected. -/
theorem IsClosedSubmanifold.locallyConnectedSpace' (hY : IsClosedSubmanifold ψ Y c) :
    LocallyConnectedSpace Y := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  rintro ⟨a, ha⟩ U hU
  obtain ⟨φ, σ, has, h⟩ := hY.exists_adaptedChart a ha
  obtain ⟨V, hV, -, hVc, hVU⟩ := h.exists_preconnected_mem_nhds ha has hU
  exact ⟨V, hV, hVc, hVU⟩

/-- The connected components of a closed submanifold are closed submanifolds of the same
codimension. -/
theorem IsClosedSubmanifold.connectedComponent' (hY : IsClosedSubmanifold ψ Y c) (a : Y) :
    IsClosedSubmanifold ψ (Subtype.val '' connectedComponent a) c := by
  refine ⟨hY.isClosed.isClosedMap_subtype_val _ isClosed_connectedComponent, fun b hb => ?_⟩
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨φ, σ, hbs, h⟩ := hY.exists_adaptedChart b' b'.2
  obtain ⟨V, hV, hVo, hVc, -⟩ := h.exists_preconnected_mem_nhds b'.2 hbs univ_mem
  have hVsub : V ⊆ connectedComponent a := by
    have h1 : V ⊆ connectedComponent b' := hVc.subset_connectedComponent (mem_of_mem_nhds hV)
    rwa [← connectedComponent_eq hb'] at h1
  obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp hVo
  refine ⟨φ.restrOpen W hWo, σ, ?_, ?_, fun x hx => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨hbs, ?_⟩
    have : b' ∈ V := mem_of_mem_nhds hV
    rw [← hWV] at this
    exact this
  · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ h.1 hWo
  · rw [OpenPartialHomeomorph.restrOpen_source] at hx
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (h.2 _ hx.1).mp y.2
    · intro hz
      have hxY : x ∈ Y := (h.2 x hx.1).mpr hz
      have : (⟨x, hxY⟩ : Y) ∈ V := by
        rw [← hWV]
        exact hx.2
      exact ⟨⟨x, hxY⟩, hVsub this, rfl⟩

/-- The family of connected components of a closed submanifold is locally finite in `M`: a point
of `Y` has a connected neighbourhood in `Y`, a point off `Y` a neighbourhood missing `Y`. -/
theorem IsClosedSubmanifold.locallyFinite_connectedComponents' (hY : IsClosedSubmanifold ψ Y c) :
    LocallyFinite fun C : ConnectedComponents Y =>
      (Subtype.val '' (ConnectedComponents.mk ⁻¹' {C} : Set Y) : Set M) := by
  intro x
  by_cases hx : x ∈ Y
  · obtain ⟨φ, σ, hxs, h⟩ := hY.exists_adaptedChart x hx
    obtain ⟨V, hV, hVo, hVc, -⟩ := h.exists_preconnected_mem_nhds hx hxs univ_mem
    obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp hVo
    have hxW : x ∈ W := by
      have : (⟨x, hx⟩ : Y) ∈ V := mem_of_mem_nhds hV
      rw [← hWV] at this
      exact this
    refine ⟨W, hWo.mem_nhds hxW,
      (Set.finite_singleton (ConnectedComponents.mk (⟨x, hx⟩ : Y))).subset ?_⟩
    rintro C ⟨_, ⟨y, hyC, rfl⟩, hyW⟩
    have hyV : y ∈ V := by
      rw [← hWV]
      exact hyW
    have hy : y ∈ connectedComponent (⟨x, hx⟩ : Y) :=
      hVc.subset_connectedComponent (mem_of_mem_nhds hV) hyV
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hyC
    rw [Set.mem_singleton_iff, ← hyC]
    exact ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hy).symm
  · refine ⟨Yᶜ, hY.isClosed.isOpen_compl.mem_nhds hx, Set.finite_empty.subset ?_⟩
    rintro C ⟨_, ⟨y, -, rfl⟩, hyc⟩
    exact hyc y.2

/-! ### Adapted charts inside a connected component -/

section M20

open Set Topology

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- Every point `b` of a closed submanifold `Y` has an adapted chart of `Y` whose source meets `Y`
only inside the connected component of `b` in `Y`. -/
theorem IsClosedSubmanifold.exists_adaptedChart_source_inter_subset
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) {b : M} (hb : b ∈ Y) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n), b ∈ φ.source ∧
      IsAdaptedChart ψ₀ Y φ σ ∧ φ.source ∩ Y ⊆ connectedComponentIn Y b := by
  obtain ⟨φ, σ, hbs, h⟩ := hY.exists_adaptedChart b hb
  obtain ⟨V, hV, hVo, hVc, -⟩ := h.exists_preconnected_mem_nhds hb hbs Filter.univ_mem
  have hVsub : V ⊆ connectedComponent (⟨b, hb⟩ : Y) :=
    hVc.subset_connectedComponent (mem_of_mem_nhds hV)
  obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp hVo
  refine ⟨φ.restrOpen W hWo, σ, ?_, h.restrOpen' W hWo, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨hbs, ?_⟩
    have : (⟨b, hb⟩ : Y) ∈ V := mem_of_mem_nhds hV
    rw [← hWV] at this
    exact this
  · rintro x ⟨hxs, hxY⟩
    rw [OpenPartialHomeomorph.restrOpen_source] at hxs
    have hxV : (⟨x, hxY⟩ : Y) ∈ V := by
      rw [← hWV]
      exact hxs.2
    rw [connectedComponentIn_eq_image hb]
    exact ⟨⟨x, hxY⟩, hVsub hxV, rfl⟩

end M20

end Manifold
