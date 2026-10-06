/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.Chart.Atlas
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Adapted charts off the centre and their coordinate changes

Two inputs of the gluing of the blowing-up of a manifold along a closed submanifold `Y`
[BM88, Definition 4.1]:

* the maximal atlas is stable under composition with an element of the structure groupoid of the
  model, and an analytic automorphism of `E` (a translation, say) is such an element; hence
  **every point off the centre `Y` has a chart adapted to `Y`** (`IsAdaptedChart`): a chart
  inside `M ∖ Y`, shrunk so that one block coordinate varies by less than `1`, then translated so
  that this coordinate is nonzero, which makes both sides of the adaptedness condition false on
  its source;
* the **coordinate change** between two charts `φ`, `φ'` of the maximal atlas, read in `𝕜ⁿ`
  through `ψ` (`chartChange ψ φ φ' = ψ ∘ φ' ∘ φ⁻¹ ∘ ψ⁻¹` on `chartChangeDom ψ φ φ'`), is an
  analytic bijection between open subsets of `𝕜ⁿ` satisfying the inverse and cocycle laws;
  between two adapted charts it carries the centre `{x_σ = 0}` onto the centre `{x_σ' = 0}`.
  These are the hypotheses of the lifting lemma of `Hironaka.Manifold.BlowUp.Lift`.

The blown-up manifold is glued from the blow-up charts over these adapted charts in
`Hironaka.Manifold.BlowUp.Glue`. None of this is stated in the source; the arguments are
routine.
-/

@[expose] public section

open TopologicalSpace
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-! ### The maximal atlas and the groupoid of the model -/

section Groupoid

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : StructureGroupoid H}

/-- The maximal atlas is stable under composition with an element of the groupoid. -/
theorem mem_maximalAtlas_trans_of_mem_groupoid {e : OpenPartialHomeomorph M H}
    (he : e ∈ G.maximalAtlas M) {f : OpenPartialHomeomorph H H} (hf : f ∈ G) :
    e ≫ₕ f ∈ G.maximalAtlas M := by
  intro e' he'
  obtain ⟨h1, h2⟩ := he e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact G.trans (G.symm hf) h1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact G.trans h2 hf

end Groupoid

section Model

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The translation `x ↦ x + t` of the model is an element of the analytic groupoid. -/
theorem addRight_mem_contDiffGroupoid (t : E) :
    (Homeomorph.addRight t).toOpenPartialHomeomorph ∈ contDiffGroupoid ω 𝓘(𝕜, E) := by
  refine mem_contDiffGroupoid_omega_of_analytic' _ (fun x _ => ?_) (fun x _ => ?_)
  · have h : AnalyticAt 𝕜 (fun y : E => y + t) x := analyticAt_id.add analyticAt_const
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    rw [Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.coe_addRight]
  · have h : AnalyticAt 𝕜 (fun y : E => y + -t) x := analyticAt_id.add analyticAt_const
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    rw [← Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.addRight_symm, Homeomorph.coe_addRight]

end Model

/-! ### Adapted charts at the points off the centre -/

section Adapted

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

/-- Every point off the centre has a chart adapted to `Y` for any block `σ`: a chart inside
`M ∖ Y`, shrunk so that the block coordinate `σ i₀` varies by less than `1`, then translated so
that this coordinate is nonzero, which makes both sides of the adaptedness condition fail on the
source. -/
theorem exists_isAdaptedChart_of_notMem (hY : IsClosedSubmanifold ψ Y c) (σ : Fin c ↪ Fin n)
    (i₀ : Fin c) {a : M} (ha : a ∉ Y) :
    ∃ φ : OpenPartialHomeomorph M E, a ∈ φ.source ∧ IsAdaptedChart ψ Y φ σ := by
  set e := chartAt E a with he
  set x₀ : 𝕜 := ψ (e a) (σ i₀) with hx₀
  set s : Set M := Yᶜ ∩ (e.source ∩ e ⁻¹' (ψ ⁻¹' {x | ‖x (σ i₀) - x₀‖ < 1})) with hs_def
  have hsopen : IsOpen s := by
    refine hY.isClosed.isOpen_compl.inter (e.isOpen_inter_preimage ?_)
    exact (isOpen_lt (by fun_prop) continuous_const).preimage ψ.continuous
  set t : E := ψ.symm (Pi.single (σ i₀) (1 - x₀)) with ht
  refine ⟨(e.restrOpen s hsopen).trans (Homeomorph.addRight t).toOpenPartialHomeomorph, ?_, ?_,
    ?_⟩
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source,
      Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]
    refine ⟨mem_chart_source E a, ha, mem_chart_source E a, ?_⟩
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_ofPred_eq, hx₀, sub_self, norm_zero]
    exact zero_lt_one
  · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact mem_maximalAtlas_trans_of_mem_groupoid
      (restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas a) hsopen)
      (addRight_mem_contDiffGroupoid t)
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.restrOpen_source] at hx
    obtain ⟨⟨-, hxY, -, hxlt⟩, -⟩ := hx
    refine ⟨fun h => absurd h hxY, fun h => ?_⟩
    exfalso
    have h1 := h i₀
    simp only [OpenPartialHomeomorph.trans_apply, Homeomorph.toOpenPartialHomeomorph_apply,
      Homeomorph.coe_addRight, OpenPartialHomeomorph.coe_restrOpen, map_add, Pi.add_apply, ht,
      ContinuousLinearEquiv.apply_symm_apply, Pi.single_eq_same] at h1
    have h2 : ψ (e x) (σ i₀) - x₀ = -1 := by linear_combination h1
    rw [Set.mem_preimage, Set.mem_preimage, Set.mem_ofPred_eq, h2, norm_neg, norm_one] at hxlt
    exact lt_irrefl _ hxlt

end Adapted

/-! ### Coordinate changes read in `Kⁿ` -/

section ChartChange

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M]

/-- The domain in `Kⁿ` of the coordinate change from the chart `φ` to the chart `φ'`:
`ψ(φ(φ.source ∩ φ'.source))`. -/
def chartChangeDom (φ φ' : OpenPartialHomeomorph M E) : Set (Fin n → 𝕜) :=
  ψ '' (φ.target ∩ φ.symm ⁻¹' φ'.source)

/-- The coordinate change `ψ ∘ φ' ∘ φ⁻¹ ∘ ψ⁻¹` from the chart `φ` to the chart `φ'`. -/
def chartChange (φ φ' : OpenPartialHomeomorph M E) (x : Fin n → 𝕜) : Fin n → 𝕜 :=
  ψ (φ' (φ.symm (ψ.symm x)))

variable {φ φ' φ'' : OpenPartialHomeomorph M E}

/-- The chart-change domain is open (the image under `ψ` of an open subset of `φ.target`). -/
theorem isOpen_chartChangeDom : IsOpen (chartChangeDom ψ φ φ') :=
  ψ.toHomeomorph.isOpenMap _ (φ.isOpen_inter_preimage_symm φ'.open_source)

/-- Membership in the chart-change domain, unfolded. -/
theorem mem_chartChangeDom_iff {x : Fin n → 𝕜} :
    x ∈ chartChangeDom ψ φ φ' ↔ ψ.symm x ∈ φ.target ∧ φ.symm (ψ.symm x) ∈ φ'.source := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨ψ.symm x, h, ψ.apply_symm_apply x⟩

/-- A point of both chart sources has its `φ`-coordinates in the chart-change domain. -/
theorem mem_chartChangeDom_of_mem {y : M} (hy : y ∈ φ.source) (hy' : y ∈ φ'.source) :
    ψ (φ y) ∈ chartChangeDom ψ φ φ' :=
  ⟨φ y, ⟨φ.map_source hy, by rw [Set.mem_preimage, φ.left_inv hy]; exact hy'⟩, rfl⟩

/-- The chart-change domain lies in the coordinate image of `φ.target`. -/
theorem chartChangeDom_subset : chartChangeDom ψ φ φ' ⊆ ψ '' φ.target :=
  Set.image_mono Set.inter_subset_left

/-- The chart change maps its domain into the domain of the reverse change. -/
theorem chartChange_mem {x : Fin n → 𝕜} (hx : x ∈ chartChangeDom ψ φ φ') :
    chartChange ψ φ φ' x ∈ chartChangeDom ψ φ' φ := by
  rw [mem_chartChangeDom_iff] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [chartChange, ContinuousLinearEquiv.symm_apply_apply]
    exact φ'.map_source h2
  · simp only [chartChange, ContinuousLinearEquiv.symm_apply_apply, φ'.left_inv h2]
    exact φ.map_target h1

/-- The reverse chart change inverts the chart change on its domain. -/
theorem chartChange_chartChange {x : Fin n → 𝕜} (hx : x ∈ chartChangeDom ψ φ φ') :
    chartChange ψ φ' φ (chartChange ψ φ φ' x) = x := by
  rw [mem_chartChangeDom_iff] at hx
  simp only [chartChange, ContinuousLinearEquiv.symm_apply_apply, φ'.left_inv hx.2,
    φ.right_inv hx.1, ContinuousLinearEquiv.apply_symm_apply]

/-- The chart change is a bijection from its domain onto the domain of the reverse change. -/
theorem bijOn_chartChange :
    Set.BijOn (chartChange ψ φ φ') (chartChangeDom ψ φ φ') (chartChangeDom ψ φ' φ) :=
  Set.InvOn.bijOn
    ⟨fun _ hx => chartChange_chartChange ψ hx, fun _ hx => chartChange_chartChange ψ hx⟩
    (fun _ hx => chartChange_mem ψ hx) (fun _ hx => chartChange_mem ψ hx)

/-- The chart change of a chart with itself is the identity on its domain. -/
theorem chartChange_self {x : Fin n → 𝕜} (hx : x ∈ chartChangeDom ψ φ φ) :
    chartChange ψ φ φ x = x := by
  rw [mem_chartChangeDom_iff] at hx
  simp only [chartChange, φ.right_inv hx.1, ContinuousLinearEquiv.apply_symm_apply]

/-- Composable chart changes: `chartChange φ φ' x` lies in the domain of the change `φ' → φ''` when
`x` lies in the domains of the changes `φ → φ'` and `φ → φ''`. -/
theorem chartChange_mem_of_mem {x : Fin n → 𝕜} (hx : x ∈ chartChangeDom ψ φ φ')
    (hx' : x ∈ chartChangeDom ψ φ φ'') : chartChange ψ φ φ' x ∈ chartChangeDom ψ φ' φ'' := by
  rw [mem_chartChangeDom_iff] at hx hx' ⊢
  refine ⟨?_, ?_⟩
  · simp only [chartChange, ContinuousLinearEquiv.symm_apply_apply]
    exact φ'.map_source hx.2
  · simp only [chartChange, ContinuousLinearEquiv.symm_apply_apply, φ'.left_inv hx.2]
    exact hx'.2

/-- The cocycle law of the coordinate changes. -/
theorem chartChange_comp {x : Fin n → 𝕜} (hx : x ∈ chartChangeDom ψ φ φ') :
    chartChange ψ φ' φ'' (chartChange ψ φ φ' x) = chartChange ψ φ φ'' x := by
  rw [mem_chartChangeDom_iff] at hx
  simp only [chartChange, ContinuousLinearEquiv.symm_apply_apply, φ'.left_inv hx.2]

variable [ChartedSpace E M]

/-- The coordinate change between two charts of the maximal atlas is analytic. -/
theorem analyticOnNhd_chartChange (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (hφ' : φ' ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    AnalyticOnNhd 𝕜 (chartChange ψ φ φ') (chartChangeDom ψ φ φ') := by
  have h1 : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (φ' ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
    (contMDiffOn_of_mem_maximalAtlas hφ').comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono Set.inter_subset_left) fun _ hx => hx.2
  have h2 : ContDiffOn 𝕜 ω (φ' ∘ φ.symm) (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
    contMDiffOn_iff_contDiffOn.mp h1
  have hopen : IsOpen (φ.target ∩ φ.symm ⁻¹' φ'.source) :=
    φ.isOpen_inter_preimage_symm φ'.open_source
  rintro x ⟨y, hy, rfl⟩
  have hy' : AnalyticAt 𝕜 (φ' ∘ φ.symm) y := (h2.contDiffAt (hopen.mem_nhds hy)).analyticAt
  have hψ : AnalyticAt 𝕜 (⇑ψ) (φ' (φ.symm y)) := ψ.toContinuousLinearMap.analyticAt _
  have hψs : AnalyticAt 𝕜 (⇑ψ.symm) (ψ y) := ψ.symm.toContinuousLinearMap.analyticAt _
  have h : AnalyticAt 𝕜 (⇑ψ ∘ (φ' ∘ φ.symm) ∘ ⇑ψ.symm) (ψ y) :=
    hψ.comp_of_eq (hy'.comp_of_eq hψs (ψ.symm_apply_apply y)) (by simp)
  exact h

/-- Between two adapted charts the coordinate change carries the centre `{x_σ = 0}` onto the
centre `{x_σ' = 0}`: both are the coordinate image of `Y`. -/
theorem mem_center_iff_chartChange {Y : Set M} {c : ℕ} {σ σ' : Fin c ↪ Fin n}
    (hφ : IsAdaptedChart ψ Y φ σ) (hφ' : IsAdaptedChart ψ Y φ' σ') {x : Fin n → 𝕜}
    (hx : x ∈ chartChangeDom ψ φ φ') :
    x ∈ blowUpCenter σ ↔ chartChange ψ φ φ' x ∈ blowUpCenter σ' := by
  rw [mem_chartChangeDom_iff] at hx
  have h1 := hφ.2 _ (φ.map_target hx.1)
  have h2 := hφ'.2 _ hx.2
  rw [φ.right_inv hx.1, ψ.apply_symm_apply] at h1
  exact h1.symm.trans h2

end ChartChange

end Manifold
