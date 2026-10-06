/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.AnalyticManifold.Defs
/-!
# The model transport of an analytic manifold

The manifold-level analytic main theorems (at the ends of
`Hironaka/Resolution/Analytic/Wlo09/HironakaAssembly.lean` and
`Hironaka/Resolution/Analytic/BM97/JacobianAssembly.lean`) take a manifold
`M : AnalyticManifold ℝ E` for any finite-dimensional real `E`, while the resolution
(`resolveFam`) is built at the standard model `Fin n → 𝕜` with the chart
isomorphism `ContinuousLinearEquiv.refl`. The proofs therefore carry `M` to the standard model along
a linear isomorphism `ψ : E ≃L[ℝ] (Fin (finrank ℝ E) → ℝ)` (`ContinuousLinearEquiv.ofFinrankEq`),
run the resolution there, and carry the resulting family and its clauses back
(`Hironaka/Resolution/Analytic/ModelTransport/`, of which this module is the first layer: the
manifold itself).

`M.transport ψ` is `M` re-modelled on `E'`: the same carrier and topology (so the same compacts and
opens), the charts composed with `ψ` (`transportChartedSpace`); it is an analytic manifold because
the transition maps of the new atlas are `ψ ∘ τ ∘ ψ⁻¹` for the transitions `τ` of `M`
(`isManifold_transportChartedSpace`, Mathlib's `isManifold_of_contDiffOn` with
`ψ.contDiff.comp_contDiffOn`); Mathlib's own `ModelWithCorners.transContinuousLinearEquiv` changes
the model with corners keeping the charts, whereas `AnalyticManifold 𝕜 E'` has charts into `E'` and
the model `𝓘(𝕜, E')`. The identity `M → M.transport ψ` is an analytic isomorphism across the two
models (`transportDiffeomorph`, a `Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E')`): in the charts it is `ψ`.
Consequences: analyticity into or out of the re-modelled manifold is analyticity of the composite
with the identity (`contMDiff_transport_source_iff`, `contMDiff_transport_target_iff`); the maximal
atlas of the re-modelled manifold is the maximal atlas of `M` composed with `ψ`
(`mem_maximalAtlas_transport_iff`, `exists_trans_of_mem_maximalAtlas_transport`, through the
conjugation of the analytic groupoid `trans_mem_contDiffGroupoid_iff`); the identity of an open
subset `U` is an analytic isomorphism between `M.restrict U` and `(M.transport ψ).restrict U`
(`restrictTransportDiffeomorph`, the stage-`0` identification of the transported successions of
`Hironaka/Resolution/Analytic/ModelTransport/Succession.lean`).

A type ascription `(x : M.transport ψ)` on a point `x : M` is dropped by Lean when the two carriers
are definitionally equal, after which instance search for `ChartedSpace E'` on the carrier of `M`
fails; every statement therefore goes through the identities with their declared types
(`toTransport`, `ofTransport`, `transportOpens`, `restrictToTransport`, `restrictOfTransport`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E E' : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

/-- **The charts of `M` composed with the linear isomorphism `ψ`**: the charted-space structure on
the points of `M` modelled on `E'`, `chartAt x := (chartAt E x) ≫ₕ ψ`. -/
@[instance_reducible]
def _root_.AnalyticManifold.transportChartedSpace
    (M : AnalyticManifold.{u} 𝕜 E)
    (ψ : E ≃L[𝕜] E') : ChartedSpace E' M where
  atlas := (fun e : OpenPartialHomeomorph M E =>
    e.trans ψ.toHomeomorph.toOpenPartialHomeomorph) '' atlas E M
  chartAt x := (chartAt E x).trans ψ.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
    exact ⟨mem_chart_source E x, mem_univ _⟩
  chart_mem_atlas x := ⟨_, chart_mem_atlas E x, rfl⟩

variable (M : AnalyticManifold.{u} 𝕜 E) (ψ : E ≃L[𝕜] E')

/-- The charts composed with `ψ` are analytically compatible: their transition maps are
`ψ ∘ (transition of `M`) ∘ ψ⁻¹` (Mathlib's `isManifold_of_contDiffOn` with
`ψ.contDiff.comp_contDiffOn`). -/
theorem isManifold_transportChartedSpace :
    @IsManifold 𝕜 _ E' _ _ E' _ 𝓘(𝕜, E') ω M _ (M.transportChartedSpace ψ) := by
  refine @isManifold_of_contDiffOn 𝕜 _ E' _ _ E' _ 𝓘(𝕜, E') ω M _ (M.transportChartedSpace ψ)
    fun e₁ e₂ h₁ h₂ => ?_
  obtain ⟨f₁, hf₁, rfl⟩ := h₁
  obtain ⟨f₂, hf₂, rfl⟩ := h₂
  have hc := ((contDiffGroupoid ω 𝓘(𝕜, E)).compatible hf₁ hf₂).1
  have hfun : (𝓘(𝕜, E') ∘ ((f₁.trans ψ.toHomeomorph.toOpenPartialHomeomorph).symm ≫ₕ
        (f₂.trans ψ.toHomeomorph.toOpenPartialHomeomorph)) ∘ 𝓘(𝕜, E').symm) =
      ψ ∘ (𝓘(𝕜, E) ∘ (f₁.symm ≫ₕ f₂) ∘ 𝓘(𝕜, E).symm) ∘ ψ.symm := by
    ext y
    simp [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.coe_trans_symm, Function.comp]
  rw [hfun]
  refine ψ.contDiff.comp_contDiffOn (hc.comp ψ.symm.contDiff.contDiffOn ?_)
  intro y hy
  simp only [mfld_simps, Function.comp] at hy ⊢
  exact hy

/-- **`M` re-modelled on `E'` along `ψ`**: the same points, the same topology (hence the same
compacts and opens), the charts composed with `ψ`. The analytic main theorems carry their
`M : AnalyticManifold ℝ E` to `Fin (finrank ℝ E) → ℝ` along `ContinuousLinearEquiv.ofFinrankEq`,
run the resolution there, and carry the family back
(`Hironaka/Resolution/Analytic/ModelTransport/Family.lean`). -/
def _root_.AnalyticManifold.transport : AnalyticManifold.{u} 𝕜 E' :=
  letI := M.transportChartedSpace ψ
  haveI : IsManifold 𝓘(𝕜, E') ω M := isManifold_transportChartedSpace M ψ
  { carrier := M }

/-- The identity `M → M.transport ψ` with its declared type (a type ascription on `x : M` is
dropped when the two carriers are definitionally equal, and instance search then fails). -/
def _root_.AnalyticManifold.toTransport : M → M.transport ψ := fun x => x

/-- The identity `M.transport ψ → M` with its declared type. -/
def _root_.AnalyticManifold.ofTransport : M.transport ψ → M := fun x => x

/-- The chart of the re-modelled manifold at a point. -/
theorem _root_.AnalyticManifold.chartAt_transport (x : M) :
    chartAt E' (M.toTransport ψ x) = (chartAt E x).trans ψ.toHomeomorph.toOpenPartialHomeomorph :=
  rfl

/-- The identity `M → M.transport ψ` is analytic: in the charts it is `ψ` (`contMDiffWithinAt_iff'`,
the chart representative agrees with `ψ` on the chart's target). -/
theorem _root_.AnalyticManifold.contMDiff_toTransport :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') ω (M.toTransport ψ) := by
  intro x
  refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
  refine ψ.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
  · have h1 : y ∈ (chartAt E x).target := by simpa [extChartAt_target] using hy.1
    change ψ (chartAt E x ((chartAt E x).symm y)) = ψ y
    rw [(chartAt E x).right_inv h1]
  · refine ⟨(extChartAt 𝓘(𝕜, E) x).map_source (mem_extChartAt_source x), trivial, ?_⟩
    change M.toTransport ψ ((extChartAt 𝓘(𝕜, E) x).symm (extChartAt 𝓘(𝕜, E) x x)) ∈
      (extChartAt 𝓘(𝕜, E') (M.toTransport ψ x)).source
    rw [(extChartAt 𝓘(𝕜, E) x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source _

/-- The identity `M.transport ψ → M` is analytic: in the charts it is `ψ⁻¹`. -/
theorem _root_.AnalyticManifold.contMDiff_ofTransport :
    ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω (M.ofTransport ψ) := by
  intro x
  refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
  refine ψ.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
  · have h1 : y ∈ (chartAt E' x).target := by simpa [extChartAt_target] using hy.1
    have h2 : (chartAt E' x).target = ψ.toHomeomorph.toOpenPartialHomeomorph.target ∩
        ψ.toHomeomorph.toOpenPartialHomeomorph.symm ⁻¹' (chartAt E (M.ofTransport ψ x)).target :=
      OpenPartialHomeomorph.trans_target _ _
    rw [h2] at h1
    change chartAt E (M.ofTransport ψ x) ((chartAt E (M.ofTransport ψ x)).symm (ψ.symm y)) =
      ψ.symm y
    exact (chartAt E (M.ofTransport ψ x)).right_inv h1.2
  · refine ⟨(extChartAt 𝓘(𝕜, E') x).map_source (mem_extChartAt_source x), trivial, ?_⟩
    change M.ofTransport ψ ((extChartAt 𝓘(𝕜, E') x).symm (extChartAt 𝓘(𝕜, E') x x)) ∈
      (extChartAt 𝓘(𝕜, E) (M.ofTransport ψ x)).source
    rw [(extChartAt 𝓘(𝕜, E') x).left_inv (mem_extChartAt_source x)]
    exact mem_extChartAt_source _

/-- **The identity `M → M.transport ψ` as an analytic isomorphism across the two models**
(Mathlib's `Diffeomorph` takes two models with corners). Every transport of this directory is a
transport along such an isomorphism. -/
def _root_.AnalyticManifold.transportDiffeomorph :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M (M.transport ψ) ω where
  toFun := M.toTransport ψ
  invFun := M.ofTransport ψ
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := M.contMDiff_toTransport ψ
  contMDiff_invFun := M.contMDiff_ofTransport ψ

/-- The isomorphism is the identity on points. -/
theorem _root_.AnalyticManifold.coe_transportDiffeomorph :
    ⇑(M.transportDiffeomorph ψ) = M.toTransport ψ := rfl

/-- Its inverse is the identity on points. -/
theorem _root_.AnalyticManifold.coe_transportDiffeomorph_symm :
    ⇑(M.transportDiffeomorph ψ).symm = M.ofTransport ψ := rfl

variable {M ψ} {H F : Type*} [TopologicalSpace H] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {I : ModelWithCorners 𝕜 F H} {P : Type*} [TopologicalSpace P] [ChartedSpace H P]

/-- Analyticity out of the re-modelled manifold. -/
theorem contMDiff_transport_source_iff {f : M.transport ψ → P} :
    ContMDiff 𝓘(𝕜, E') I ω f ↔ ContMDiff 𝓘(𝕜, E) I ω (f ∘ ⇑(M.transportDiffeomorph ψ)) :=
  ⟨fun h => h.comp (M.transportDiffeomorph ψ).contMDiff,
    fun h => h.comp (M.transportDiffeomorph ψ).symm.contMDiff⟩

/-- Analyticity into the re-modelled manifold. -/
theorem contMDiff_transport_target_iff {f : P → M} :
    ContMDiff I 𝓘(𝕜, E') ω (⇑(M.transportDiffeomorph ψ) ∘ f) ↔ ContMDiff I 𝓘(𝕜, E) ω f :=
  ⟨fun h => (M.transportDiffeomorph ψ).symm.contMDiff.comp h,
    fun h => (M.transportDiffeomorph ψ).contMDiff.comp h⟩

variable (M ψ)

/-- Conjugating an analytic transition of `E` by `ψ` gives an analytic transition of `E'`:
membership in the analytic groupoid is preserved. -/
theorem trans_mem_contDiffGroupoid_iff (g : OpenPartialHomeomorph E E) :
    ψ.toHomeomorph.toOpenPartialHomeomorph.symm.trans
        (g.trans ψ.toHomeomorph.toOpenPartialHomeomorph) ∈ contDiffGroupoid ω 𝓘(𝕜, E') ↔
      g ∈ contDiffGroupoid ω 𝓘(𝕜, E) := by
  simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simp only [mfld_simps, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, Function.comp_assoc,
    ← ContinuousLinearEquiv.toHomeomorph_symm, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [ψ.comp_contDiffOn_iff, ψ.comp_contDiffOn_iff, ψ.symm.contDiffOn_comp_iff,
    ψ.symm.contDiffOn_comp_iff]

/-- A chart of `M` composed with `ψ` is in the maximal atlas of the re-modelled manifold iff the
chart is in the maximal atlas of `M`. -/
theorem mem_maximalAtlas_transport_iff (φ : OpenPartialHomeomorph M E) :
    φ.trans ψ.toHomeomorph.toOpenPartialHomeomorph ∈
        IsManifold.maximalAtlas 𝓘(𝕜, E') ω (M.transport ψ) ↔
      φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M := by
  simp only [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  change (∀ e' ∈ (fun e : OpenPartialHomeomorph M E =>
    e.trans ψ.toHomeomorph.toOpenPartialHomeomorph) '' atlas E M, _) ↔ _
  rw [Set.forall_mem_image]
  refine forall₂_congr fun e _ => ?_
  change ((φ.trans ψ.toHomeomorph.toOpenPartialHomeomorph).symm ≫ₕ
      (e.trans ψ.toHomeomorph.toOpenPartialHomeomorph) ∈ contDiffGroupoid ω 𝓘(𝕜, E') ∧
    (e.trans ψ.toHomeomorph.toOpenPartialHomeomorph).symm ≫ₕ
      (φ.trans ψ.toHomeomorph.toOpenPartialHomeomorph) ∈ contDiffGroupoid ω 𝓘(𝕜, E')) ↔
    (φ.symm ≫ₕ e ∈ contDiffGroupoid ω 𝓘(𝕜, E) ∧ e.symm ≫ₕ φ ∈ contDiffGroupoid ω 𝓘(𝕜, E))
  have h1 : (φ.trans ψ.toHomeomorph.toOpenPartialHomeomorph).symm ≫ₕ
      (e.trans ψ.toHomeomorph.toOpenPartialHomeomorph) =
      ψ.toHomeomorph.toOpenPartialHomeomorph.symm.trans
        ((φ.symm ≫ₕ e).trans ψ.toHomeomorph.toOpenPartialHomeomorph) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_assoc]
  have h2 : (e.trans ψ.toHomeomorph.toOpenPartialHomeomorph).symm ≫ₕ
      (φ.trans ψ.toHomeomorph.toOpenPartialHomeomorph) =
      ψ.toHomeomorph.toOpenPartialHomeomorph.symm.trans
        ((e.symm ≫ₕ φ).trans ψ.toHomeomorph.toOpenPartialHomeomorph) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_assoc]
  rw [h1, h2, trans_mem_contDiffGroupoid_iff, trans_mem_contDiffGroupoid_iff]

/-- Every chart of the maximal atlas of the re-modelled manifold is a chart of `M` composed with
`ψ`. -/
theorem exists_trans_of_mem_maximalAtlas_transport (φ' : OpenPartialHomeomorph (M.transport ψ) E')
    (h : φ' ∈ IsManifold.maximalAtlas 𝓘(𝕜, E') ω (M.transport ψ)) :
    ∃ φ : OpenPartialHomeomorph M E, φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M ∧
      φ' = φ.trans ψ.toHomeomorph.toOpenPartialHomeomorph := by
  have heq : φ' = (φ'.trans ψ.toHomeomorph.toOpenPartialHomeomorph.symm).trans
      ψ.toHomeomorph.toOpenPartialHomeomorph := by
    refine OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun y => ?_) ?_
    · simp [OpenPartialHomeomorph.trans_apply]
    · simp [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_apply]
    · simp
  refine ⟨φ'.trans ψ.toHomeomorph.toOpenPartialHomeomorph.symm,
    (mem_maximalAtlas_transport_iff M ψ _).mp ?_, heq⟩
  exact heq ▸ h

/-- An open set of `M` as an open set of the re-modelled `M` (the same set, the same topology),
with its declared type, so that the instances of the re-modelled manifold are found. -/
abbrev _root_.AnalyticManifold.transportOpens (U : Opens M) :
    Opens (M.transport ψ) :=
  ⟨(U : Set M), U.isOpen⟩

/-- The identity of `U`, from the restriction of `M` to the restriction of the re-modelled `M`. -/
def _root_.AnalyticManifold.restrictToTransport (U : Opens M) :
    M.restrict U → (M.transport ψ).restrict (M.transportOpens ψ U) :=
  fun q => ⟨M.toTransport ψ q.1, q.2⟩

/-- The identity of `U`, back. -/
def _root_.AnalyticManifold.restrictOfTransport (U : Opens M) :
    (M.transport ψ).restrict (M.transportOpens ψ U) → M.restrict U :=
  fun q => ⟨M.ofTransport ψ q.1, q.2⟩

/-- The identity of `U` is analytic into the re-modelled restriction (Mathlib's
`liftPropWithinAt_subtypeVal_comp_iff`). -/
theorem _root_.AnalyticManifold.contMDiff_restrictToTransport (U : Opens M) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E') ω (M.restrictToTransport ψ U) := fun q =>
  (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := M.transportOpens ψ U)
    (M.restrictToTransport ψ U) Set.univ q).mp
    (((M.contMDiff_toTransport ψ).comp contMDiff_subtype_val) q)

/-- The identity of `U`, back, is analytic. -/
theorem _root_.AnalyticManifold.contMDiff_restrictOfTransport (U : Opens M) :
    ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω (M.restrictOfTransport ψ U) := fun q =>
  (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) (M.restrictOfTransport ψ U)
    Set.univ q).mp
    (((M.contMDiff_ofTransport ψ).comp (contMDiff_subtype_val (U := M.transportOpens ψ U))) q)

/-- **The identity of the open subset `U`, between the restriction of `M` and the restriction of
the re-modelled `M`**, as an analytic isomorphism across the models: the stage-`0` identification
of the transported successions (`Hironaka/Resolution/Analytic/ModelTransport/Succession.lean`). -/
def _root_.AnalyticManifold.restrictTransportDiffeomorph (U : Opens M) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') (M.restrict U) ((M.transport ψ).restrict (M.transportOpens ψ U))
      ω where
  toFun := M.restrictToTransport ψ U
  invFun := M.restrictOfTransport ψ U
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := M.contMDiff_restrictToTransport ψ U
  contMDiff_invFun := M.contMDiff_restrictOfTransport ψ U

/-- The isomorphism is the identity on points. -/
theorem _root_.AnalyticManifold.coe_restrictTransportDiffeomorph
    (U : Opens M) :
    ⇑(M.restrictTransportDiffeomorph ψ U) = M.restrictToTransport ψ U := rfl

/-- The point of `M.transport ψ` under the isomorphism. -/
theorem _root_.AnalyticManifold.restrictTransportDiffeomorph_apply_val
    (U : Opens M)
    (q : M.restrict U) :
    ((M.restrictTransportDiffeomorph ψ U q).1 : M.transport ψ) = M.toTransport ψ q.1 := rfl

end Hironaka.Manifold

end
