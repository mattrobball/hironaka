/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Jacobian.Defs
public import Hironaka.Resolution.Analytic.ModelTransport.IdealSheaf
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Jacobian.Bundled
import Hironaka.Manifold.Jacobian.Units
import Hironaka.Resolution.Analytic.ModelTransport.Square
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The Jacobian ideal and the monoidal transformations along a square across the models

The chart-level notions of the vocabulary — adapted charts and closed submanifolds, the ideal
sheaf of a submanifold, blow-up charts, blowings-up and monoidal transformations
([BM88, Definition 4.1]), the Jacobian ideal ([BM97, Theorem 1.10, the sentence after it]) —
transport along a square `f ∘ g' = g ∘ f'` of
analytic isomorphisms `g : N ≃ M`, `g' : N' ≃ M'` across the models (`IsModelSquare`). The device is
one chart: `chartOfSquare g ψ φ := ψ ∘ φ ∘ g`, a chart of `N` read from a chart `φ` of `M` through
`g` and a linear isomorphism `ψ : E ≃L[𝕜] E'` of the models. It is in the maximal atlas of `N`
(`mem_maximalAtlas_of_contMDiffOn`), its source is `g⁻¹(φ.source)`, and reading a chart of `N`
through `g⁻¹, ψ⁻¹` and back gives the chart (`chartOfSquare_chartOfSquare_symm`).

* The predicates carry a chart isomorphism `ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)`; on `N` it becomes
  `ψ.symm.trans ψ₀`. An adapted chart of `M` reads as an adapted chart of `N` and back
  (`IsAdaptedChart.of_square`, `of_square_symm`), a closed submanifold `Y` pulls back to `g⁻¹(Y)`,
  the ideal sheaf of `Y` pulls back to the ideal sheaf of `g⁻¹(Y)` — the coordinate germs
  correspond under the stalk isomorphism of `g` (`stalkRingEquiv_coord`), whatever the witnesses
  of the two submanifolds (`IsClosedSubmanifold.idealSheaf_pullbackDiffeomorph`) — and a blow-up
  chart of
  `f` over `ψ⁻¹ ∘ φ' ∘ g⁻¹` reads as a blow-up chart of `f'` over `φ'` (`IsBlowUpChart.of_square`),
  so a blowing-up transports (`IsBlowUp.of_square`) and with it a monoidal transformation
  (`AnalyticMap.IsMonoidalTransformation.of_square`).
* The Jacobian: in the charts read from those of `f`, the chart representative of `f'` is the
  conjugate `ψ ∘ (φ ∘ f ∘ φ'⁻¹) ∘ ψ⁻¹` of the representative of `f`, so the Jacobian determinants
  are equal (`LinearMap.det_conj`, `det_clm_conj`) — no unit germs enter — and the Jacobian stalk
  transports along the stalk isomorphism of `g'` (`jacobianStalk_of_square`), whence the Jacobian
  ideal (`AnalyticMap.jacobianIdeal_of_square`). This needs no model isomorphism: at a point `b` of
  `N'` the inverse differential of `g'` (`Diffeomorph.mfderivToContinuousLinearEquiv`) serves as
  `ψ`.
* The monoidal transformation takes the model isomorphism `ψ`: the chart isomorphism of `N` is
  `ψ.symm.trans ψ₀`, and without some `E ≃L[𝕜] E'` the statement fails when `N` and `N'` are empty
  and `E'` is not linearly isomorphic to `Fin n → 𝕜`.

These are the steps by which the successions of the resolution are carried between the models
(`Hironaka/Resolution/Analytic/ModelTransport/Succession.lean`).
-/

@[expose] public section

noncomputable section

open AnalyticManifold TopologicalSpace Set Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N M ω) (ψ : E ≃L[𝕜] E')

/-! ### The chart of `N` read from a chart of `M` -/

/-- The chart of `N` read from a chart `φ` of `M` through the analytic isomorphism `g : N ≃ M` and
the linear isomorphism `ψ` of the models, `ψ ∘ φ ∘ g`. -/
def chartOfSquare (φ : OpenPartialHomeomorph M E) : OpenPartialHomeomorph N E' :=
  (g.toHomeomorph.toOpenPartialHomeomorph.trans φ).trans ψ.toHomeomorph.toOpenPartialHomeomorph

variable (φ : OpenPartialHomeomorph M E)

/-- `chartOfSquare g ψ φ x = ψ (φ (g x))`. -/
theorem chartOfSquare_apply (x : N) : chartOfSquare g ψ φ x = ψ (φ (g x)) := rfl

/-- The inverse of the read chart is `g⁻¹ ∘ φ⁻¹ ∘ ψ⁻¹`. -/
theorem chartOfSquare_symm_apply (v : E') :
    (chartOfSquare g ψ φ).symm v = g.symm (φ.symm (ψ.symm v)) := rfl

/-- The read chart as a function. -/
theorem coe_chartOfSquare : ⇑(chartOfSquare g ψ φ) = fun x => ψ (φ (g x)) := rfl

/-- The inverse of the read chart as a function. -/
theorem coe_chartOfSquare_symm :
    ⇑(chartOfSquare g ψ φ).symm = fun v => g.symm (φ.symm (ψ.symm v)) := rfl

/-- The source of the read chart is `g⁻¹(φ.source)`. -/
theorem chartOfSquare_source : (chartOfSquare g ψ φ).source = ⇑g ⁻¹' φ.source := by
  simp [chartOfSquare]

/-- The target of the read chart is `ψ(φ.target)`, as a preimage under `ψ⁻¹`. -/
theorem chartOfSquare_target : (chartOfSquare g ψ φ).target = ⇑ψ.symm ⁻¹' φ.target := by
  simp [chartOfSquare]

variable {φ}

/-- A chart of the maximal atlas of `M` reads as a chart of the maximal atlas of `N`
(`mem_maximalAtlas_of_contMDiffOn`: `ψ ∘ φ ∘ g` and its inverse are analytic on the source and the
target). -/
theorem chartOfSquare_mem_maximalAtlas (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) :
    chartOfSquare g ψ φ ∈ maximalAtlas 𝓘(𝕜, E') ω N := by
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · rw [chartOfSquare_source, coe_chartOfSquare]
    exact ψ.contDiff.contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas hφ).comp g.contMDiff.contMDiffOn fun _ hx => hx)
  · rw [chartOfSquare_target, coe_chartOfSquare_symm]
    exact g.symm.contMDiff.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).comp ψ.symm.contDiff.contMDiff.contMDiffOn
        fun _ hv => hv)

/-! ### Adapted charts, closed submanifolds, the ideal sheaf of a submanifold -/

variable {n : ℕ}

/-- The adapted-chart predicate depends on the chart isomorphism only pointwise. -/
theorem _root_.Manifold.IsAdaptedChart.congr_cle {ψ₁ ψ₂ : E ≃L[𝕜] (Fin n → 𝕜)} (h : ∀ v,
    ψ₁ v = ψ₂ v)
    {Y : Set M} {c : ℕ} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ₁ Y φ σ) :
    IsAdaptedChart ψ₂ Y φ σ :=
  ⟨hφ.1, fun x hx => by rw [hφ.2 x hx]; simp only [h]⟩

variable (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))

/-- An adapted chart of `M` for `Y` reads as an adapted chart of `N` for `g⁻¹(Y)`, with the chart
isomorphism `ψ.symm.trans ψ₀`. -/
theorem _root_.Manifold.IsAdaptedChart.of_square {Y : Set M} {c : ℕ} {σ : Fin c ↪ Fin n}
    (h : IsAdaptedChart ψ₀ Y φ σ) :
    IsAdaptedChart (ψ.symm.trans ψ₀) (⇑g ⁻¹' Y) (chartOfSquare g ψ φ) σ := by
  refine ⟨chartOfSquare_mem_maximalAtlas g ψ h.1, fun x hx => ?_⟩
  rw [chartOfSquare_source] at hx
  rw [Set.mem_preimage, h.2 (g x) hx]
  simp only [chartOfSquare_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- A closed submanifold of `M` pulls back along `g` to a closed submanifold of `N` of the same
codimension. -/
theorem _root_.Manifold.IsClosedSubmanifold.preimage_of_square {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) :
    IsClosedSubmanifold (ψ.symm.trans ψ₀) (⇑g ⁻¹' Y) c where
  isClosed := hY.isClosed.preimage g.continuous
  exists_adaptedChart a ha := by
    obtain ⟨φ, σ, hφa, hφ⟩ := hY.exists_adaptedChart (g a) ha
    exact ⟨chartOfSquare g ψ φ, σ, by rw [chartOfSquare_source]; exact hφa,
      hφ.of_square g ψ ψ₀⟩

/-- The adapted chart of `M` read from an adapted chart of `N` (the converse direction, through
`g⁻¹` and `ψ⁻¹`). -/
theorem _root_.Manifold.IsAdaptedChart.of_square_symm {Y : Set M} {c : ℕ} {σ : Fin c ↪ Fin n}
    {φ' : OpenPartialHomeomorph N E'} (h : IsAdaptedChart (ψ.symm.trans ψ₀) (⇑g ⁻¹' Y) φ' σ) :
    IsAdaptedChart ψ₀ Y (chartOfSquare g.symm ψ.symm φ') σ := by
  have h1 := h.of_square g.symm ψ.symm (ψ.symm.trans ψ₀)
  have hset : ⇑g.symm ⁻¹' (⇑g ⁻¹' Y) = Y := by ext y; simp [g.apply_symm_apply]
  rw [hset] at h1
  refine h1.congr_cle (ψ₂ := ψ₀) fun v => ?_
  simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The coordinate germs along `g`: the stalk isomorphism of `g` carries the `i`-th coordinate germ
of `φ` to the `i`-th coordinate germ of `ψ ∘ φ ∘ g`. -/
theorem stalkRingEquiv_coord {a : N} (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (ha : g a ∈ φ.source) (i : Fin n) :
    g.stalkRingEquiv a (coord E ψ₀ φ hφ ha i) =
      coord E' (ψ.symm.trans ψ₀) (chartOfSquare g ψ φ) (chartOfSquare_mem_maximalAtlas g ψ hφ)
        (by rw [chartOfSquare_source]; exact ha) i := by
  apply stalkToGerm_injective 𝓘(𝕜, E') ω N a
  rw [Diffeomorph.coe_stalkRingEquiv, stalkToGerm_germMap]
  unfold coord
  rw [stalkToGerm_structureSheaf_germ, stalkToGerm_structureSheaf_germ, Germ.coe_compTendsto]
  refine Germ.coe_eq.mpr ?_
  filter_upwards [(φ.open_source.preimage g.continuous).mem_nhds
    (show a ∈ ⇑g ⁻¹' φ.source from ha)] with x hx
  simp only [Function.comp_apply]
  rw [extendSection_of_mem 𝕜 E _ hx, extendSection_of_mem 𝕜 E' _
    (by change x ∈ (chartOfSquare g ψ φ).source; rw [chartOfSquare_source]; exact hx)]
  simp only [chartSection, chartOfSquare_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The coordinate germs of equal charts agree. -/
theorem coord_congr_chart {φ₁ φ₂ : OpenPartialHomeomorph M E} (h : φ₁ = φ₂)
    (hφ₁ : φ₁ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {a : M} (ha₁ : a ∈ φ₁.source) (i : Fin n) :
    coord E ψ₀ φ₁ hφ₁ ha₁ i = coord E ψ₀ φ₂ (h ▸ hφ₁) (h ▸ ha₁) i := by
  subst h
  rfl

/-- Reading a chart of `N` through `g⁻¹`, `ψ⁻¹` and back through `g`, `ψ` gives the chart. -/
theorem chartOfSquare_chartOfSquare_symm (φ' : OpenPartialHomeomorph N E') :
    chartOfSquare g ψ (chartOfSquare g.symm ψ.symm φ') = φ' := by
  refine OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun v => ?_) ?_
  · change ψ (ψ.symm (φ' (g.symm (g x)))) = φ' x
    rw [ContinuousLinearEquiv.apply_symm_apply, g.symm_apply_apply]
  · change g.symm (g (φ'.symm (ψ (ψ.symm v)))) = φ'.symm v
    rw [ContinuousLinearEquiv.apply_symm_apply, g.symm_apply_apply]
  · rw [chartOfSquare_source, chartOfSquare_source]
    exact Set.ext fun x => by
      change g.symm (g x) ∈ φ'.source ↔ x ∈ φ'.source
      rw [g.symm_apply_apply]

/-- The ideal sheaf of a closed submanifold `Y` pulls back along `g` to the ideal sheaf of
`g⁻¹(Y)`: the cosupport by `cosupport_pullback`, the stalks at the points of `g⁻¹(Y)` because the
coordinate germs of the adapted charts correspond (`stalkRingEquiv_coord`), each adapted chart of
`N` being the reading of an adapted chart of `M`. -/
theorem _root_.Manifold.IsIdealSheafOf.pullbackDiffeomorph {Y : Set M} {c : ℕ}
    {D : AnalyticManifold.IdealSheaf M}
    (hD : IsIdealSheafOf ψ₀ Y c D) :
    IsIdealSheafOf (ψ.symm.trans ψ₀) (⇑g ⁻¹' Y) c (D.pullbackDiffeomorph g) := by
  refine ⟨?_, fun φ' σ hφ' a ha haY => ?_⟩
  · rw [IdealSheaf.support_pullback, hD.1]
  · have hφ := hφ'.of_square_symm g ψ ψ₀
    have hga : g a ∈ (chartOfSquare g.symm ψ.symm φ').source := by
      rw [chartOfSquare_source, Set.mem_preimage, g.symm_apply_apply]; exact ha
    have hgaY : g a ∈ Y := haY
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, hD.2 _ σ hφ (g a) hga hgaY, Ideal.map_span,
      ← Set.range_comp]
    congr 2
    funext i
    rw [Function.comp_apply, stalkRingEquiv_coord g ψ ψ₀ hφ.1 hga (σ i),
      coord_congr_chart (ψ₀ := ψ.symm.trans ψ₀) (chartOfSquare_chartOfSquare_symm g ψ φ')]

include ψ in
/-- The ideal sheaf of a closed submanifold `Y` of `M` pulls back along `g` to the ideal sheaf of
`g⁻¹(Y)`, whatever witnesses of `IsClosedSubmanifold` the two carry: the pull-back is an ideal
sheaf of `g⁻¹(Y)` (`IsIdealSheafOf.pullbackDiffeomorph`), which is unique
(`IsIdealSheafOf.eq_idealSheaf`) and depends only on the set
(`IsClosedSubmanifold.idealSheaf_congr`). -/
theorem _root_.Manifold.IsClosedSubmanifold.idealSheaf_pullbackDiffeomorph {n' c c' : ℕ}
    {ψ₁ : E' ≃L[𝕜] (Fin n' → 𝕜)} {Y : Set M} {Y' : Set N} (hY : IsClosedSubmanifold ψ₀ Y c)
    (hY' : IsClosedSubmanifold ψ₁ Y' c') (e : Y' = ⇑g ⁻¹' Y) :
    IdealSheaf.pullbackDiffeomorph g hY.idealSheaf = hY'.idealSheaf := by
  have hpre := hY.preimage_of_square g ψ
  exact ((hY.isIdealSheafOf_idealSheaf.pullbackDiffeomorph g ψ).eq_idealSheaf hpre).trans
    (IsClosedSubmanifold.idealSheaf_congr hpre hY' e.symm)

/-! ### Blow-up charts, blowings-up, monoidal transformations along a square -/

variable {M' : AnalyticManifold.{u} 𝕜 E} {N' : AnalyticManifold.{u} 𝕜 E'}
  (g' : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N' M' ω) (f : AnalyticMap M' M)
  (f' : AnalyticMap N' N) (hsq : IsModelSquare g g' f f')

include hsq in
/-- A blow-up chart of `f` over the chart of `M` read from `φ'` is, read on `N'` through `g'` and
`ψ`, a blow-up chart of `f'` over `φ'`: the four fields through the square. -/
theorem _root_.Manifold.IsBlowUpChart.of_square {c : ℕ} {σ : Fin c ↪ Fin n} {i : Fin c}
    {φ' : OpenPartialHomeomorph N E'} {Φ : OpenPartialHomeomorph M' E}
    (hΦ : IsBlowUpChart ψ₀ ⇑f (chartOfSquare g.symm ψ.symm φ') σ i Φ) :
    IsBlowUpChart (ψ.symm.trans ψ₀) ⇑f' φ' σ i (chartOfSquare g' ψ Φ) where
  mem_maximalAtlas := chartOfSquare_mem_maximalAtlas g' ψ hΦ.mem_maximalAtlas
  source_subset := fun p hp => by
    rw [chartOfSquare_source] at hp
    have := hΦ.source_subset hp
    rw [Set.mem_preimage, chartOfSquare_source, Set.mem_preimage,
      ← IsModelSquare.apply_eq g g' f f' hsq p] at this
    exact this
  mem_target_iff := fun v => by
    rw [chartOfSquare_target, Set.mem_preimage, hΦ.mem_target_iff, chartOfSquare_target,
      ContinuousLinearEquiv.symm_symm, ← ψ.image_symm_eq_preimage, Set.image_image]
    exact Iff.rfl
  comm := fun p hp => by
    rw [chartOfSquare_source] at hp
    have h1 := hΦ.comm (g' p) hp
    simp only [chartOfSquare_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.symm_apply_apply] at h1 ⊢
    rwa [← IsModelSquare.apply_eq g g' f f' hsq p] at h1

include hsq in
/-- A blowing-up [BM88, Definition 4.1] along a square: analyticity, properness
(`isProperMap_of_square_iff`), the local-isomorphism and bijection clauses off the centre, and the
blow-up charts by `IsBlowUpChart.of_square`, each chart of `N` being the reading of a chart of
`M`. -/
theorem _root_.Manifold.IsBlowUp.of_square {Y : Set M} {c : ℕ} (hB : IsBlowUp ψ₀ Y c ⇑f) :
    IsBlowUp (ψ.symm.trans ψ₀) (⇑g ⁻¹' Y) c ⇑f' where
  contMDiff := f'.contMDiff
  isProperMap := (isProperMap_of_square_iff g g' f f' hsq).mpr hB.isProperMap
  isLocalDiffeomorphOn_compl := by
    have := isLocalDiffeomorphOn_of_square g g' f f' hsq (U := Yᶜ) hB.isLocalDiffeomorphOn_compl
    rwa [Set.preimage_compl] at this
  bijOn_compl := by
    have := bijOn_of_square g g' f f' hsq (U := Yᶜ) hB.bijOn_compl
    rwa [Set.preimage_compl] at this
  exists_chart := fun φ' σ hφ' i => by
    obtain ⟨Φ, hΦ⟩ := hB.exists_chart _ σ (hφ'.of_square_symm g ψ ψ₀) i
    exact ⟨chartOfSquare g' ψ Φ, hΦ.of_square g ψ ψ₀ g' f f' hsq⟩
  cover := fun φ' σ hφ' p hp => by
    have hp' : f (g' p) ∈ (chartOfSquare g.symm ψ.symm φ').source := by
      rw [chartOfSquare_source, Set.mem_preimage, ← IsModelSquare.apply_eq g g' f f' hsq p]
      exact hp
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := hB.cover _ σ (hφ'.of_square_symm g ψ ψ₀) (g' p) hp'
    exact ⟨i, chartOfSquare g' ψ Φ, hΦ.of_square g ψ ψ₀ g' f f' hsq,
      by rw [chartOfSquare_source]; exact hpΦ⟩

include hsq ψ in
/-- **A monoidal transformation along a square of analytic isomorphisms across the models**, with
the model isomorphism `ψ`, which names the chart isomorphism of `N` as `ψ.symm.trans ψ₀` (without
some `E ≃L[𝕜] E'` the statement fails when `N` and `N'` are empty and `E'` is not linearly
isomorphic to `Fin n → 𝕜`). The centre `Y` pulls back to `g⁻¹(Y)`, its ideal sheaf to the pull-back
of the ideal sheaf, the blowing-up transports by `IsBlowUp.of_square`. -/
theorem _root_.AnalyticMap.IsMonoidalTransformation.of_square
    {D : AnalyticManifold.IdealSheaf M} (h : f.IsMonoidalTransformation D) :
    f'.IsMonoidalTransformation (D.pullbackDiffeomorph g) := by
  obtain ⟨n, ψ₀, c, hY, hD, hB⟩ := h
  refine ⟨n, ψ.symm.trans ψ₀, c, ?_, ?_, ?_⟩
  · rw [IdealSheaf.support_pullbackDiffeomorph]
    exact hY.preimage_of_square g ψ ψ₀
  · rw [IdealSheaf.support_pullbackDiffeomorph]
    exact hD.pullbackDiffeomorph g ψ ψ₀
  · rw [IdealSheaf.support_pullbackDiffeomorph]
    exact hB.of_square g ψ ψ₀ g' f f' hsq

/-! ### The Jacobian ideal along a square -/

/-- The determinant of the conjugate `ψ ∘ A ∘ ψ⁻¹` of an endomorphism `A` of `E` by the linear
isomorphism `ψ : E ≃L[𝕜] E'` is the determinant of `A` (Mathlib's `LinearMap.det_conj` through the
coercion to linear maps). -/
theorem det_clm_conj (A : E →L[𝕜] E) :
    ((ψ : E →L[𝕜] E').comp (A.comp (ψ.symm : E' →L[𝕜] E))).det = A.det :=
  LinearMap.det_conj (A : E →ₗ[𝕜] E) ψ.toLinearEquiv

include hsq in
/-- The Jacobian determinant of `f'` in the charts read from those of `f` is the Jacobian
determinant of `f` at the corresponding point: the chart representatives are conjugate by `ψ`
(`det_clm_conj`), so the two are equal — no unit germ enters. -/
theorem jacobianFun_of_square (χ : OpenPartialHomeomorph M E) (φ : OpenPartialHomeomorph M' E)
    (y : N') :
    jacobianFun 𝕜 ⇑f' (chartOfSquare g ψ χ) (chartOfSquare g' ψ φ) y =
      jacobianFun 𝕜 ⇑f χ φ (g' y) := by
  unfold jacobianFun
  have hfun : ⇑(chartOfSquare g ψ χ) ∘ ⇑f' ∘ ⇑(chartOfSquare g' ψ φ).symm =
      ⇑ψ ∘ ((⇑χ ∘ ⇑f ∘ ⇑φ.symm) ∘ ⇑ψ.symm) := by
    funext w
    simp only [Function.comp_apply, coe_chartOfSquare, coe_chartOfSquare_symm]
    rw [← hsq (g'.symm (φ.symm (ψ.symm w))), g'.apply_symm_apply]
  rw [hfun, chartOfSquare_apply, ContinuousLinearEquiv.comp_fderiv,
    ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply, det_clm_conj]

omit ψ in
include hsq in
/-- The Jacobian stalk along a square: the stalk isomorphism of `g'` carries the Jacobian stalk of
`f` at `g' b` to the Jacobian stalk of `f'` at `b`, the generators (the Jacobian determinants in
charts) corresponding by `jacobianFun_of_square` in the charts read through `g`, `g'`. No model
isomorphism is assumed: the inverse differential of `g'` at `b`
(`Diffeomorph.mfderivToContinuousLinearEquiv`) serves as the `ψ` of the read charts. -/
theorem jacobianStalk_of_square (b : N') :
    jacobianStalk (𝕜 := 𝕜) (E := E') ⇑f' b =
      Ideal.map (g'.stalkRingEquiv b) (jacobianStalk (𝕜 := 𝕜) (E := E) ⇑f (g' b)) := by
  let ψ : E ≃L[𝕜] E' :=
    (g'.mfderivToContinuousLinearEquiv (n := ω) (by simp) b).symm
  have hχ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) (f (g' b))
  have hφ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) (g' b)
  have hb : b ∈ (chartOfSquare g' ψ (chartAt E (g' b))).source := by
    rw [chartOfSquare_source]; exact mem_chart_source E (g' b)
  have hfb : f' b ∈ (chartOfSquare g ψ (chartAt E (f (g' b)))).source := by
    rw [chartOfSquare_source, Set.mem_preimage, ← hsq b]; exact mem_chart_source E (f (g' b))
  obtain ⟨s, hs, hspan⟩ := exists_stalk_jacobianStalk_eq_span_of_charts f'.contMDiff
    (chartOfSquare_mem_maximalAtlas g ψ hχ) (chartOfSquare_mem_maximalAtlas g' ψ hφ) hb hfb
  obtain ⟨t, ht, htspan⟩ := exists_stalk_jacobianStalk_eq_span_of_charts f.contMDiff hχ hφ
    (mem_chart_source E (g' b)) (mem_chart_source E (f (g' b)))
  rw [hspan, htspan, Ideal.map_span, Set.image_singleton]
  congr 2
  apply stalkToGerm_injective 𝓘(𝕜, E') ω N' b
  rw [hs, Diffeomorph.coe_stalkRingEquiv, stalkToGerm_germMap, ht, Germ.coe_compTendsto]
  refine Germ.coe_eq.mpr (Filter.Eventually.of_forall fun y => ?_)
  exact jacobianFun_of_square g ψ g' f f' hsq _ _ y

omit ψ in
include hsq in
/-- **The Jacobian ideal [BM97, Theorem 1.10, the sentence after it] along a square of analytic
isomorphisms across the models**: stalk by stalk, `jacobianStalk_of_square`; no model isomorphism
in the statement. -/
theorem _root_.AnalyticMap.jacobianIdeal_of_square :
    AnalyticMap.jacobianIdeal f' =
      (AnalyticMap.jacobianIdeal f).pullbackDiffeomorph g' :=
  IdealSheaf.ext fun b => by
    rw [jacobianIdeal_stalkIdeal, IdealSheaf.stalkIdeal_pullbackDiffeomorph,
      jacobianIdeal_stalkIdeal, jacobianStalk_of_square g g' f f' hsq b]

end Hironaka.Manifold

end
