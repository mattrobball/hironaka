/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Jacobian.Defs
import Hironaka.Analytic.Calculus.Det
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Jacobian determinant of an analytic map in charts is analytic

Bierstone–Milman's Jacobian clause speaks of "the ideal generated (locally, with respect to any
coordinate system) by the Jacobian determinant" of the blow-down [BM97, Theorem 1.10, the sentence
after it]; for the ideal to make sense the Jacobian determinant of an analytic map, read in charts,
must be an analytic function. This module proves it, from three elementary facts.

* **The determinant is analytic on `E →L[𝕜] E`** (`contDiff_det`). When `E` has a finite basis `b`,
  `det L = det (toMatrix b b L)` and the determinant of a matrix is a polynomial in its entries
  (Leibniz's formula `Matrix.det_apply'`, a sum over permutations of signed products), each entry
  `L ↦ b.repr (L (b j)) i` being a continuous linear function of `L`; when `E` has no finite basis
  Mathlib's determinant is the constant `1` (`LinearMap.det_eq_one_of_not_module_finite`).
* **The derivative of a `C^ω` map on an open set is `C^ω`** (Mathlib's `ContDiffOn.fderiv_of_isOpen`
  with `ω + 1 = ω`), so `x ↦ det (DF x)` is `C^ω` on the open set (`contDiffOn_det_fderiv`).
* **The chart representative `χ ∘ f ∘ φ'⁻¹` of an analytic map is `C^ω`** on
  `φ'.target ∩ φ'⁻¹(f⁻¹(χ.source))` (`contDiffOn_chartRep`): the composite of the analytic chart
  inverse, `f` and the analytic chart, read through `contMDiffOn_iff_contDiffOn` on the model space.
  The chart change `χ' ∘ χ⁻¹` between two charts of the maximal atlas is `C^ω` on
  `χ.target ∩ χ⁻¹(χ'.source)` by the same composition (`contDiffOn_chartChange` of
  `Hironaka/Manifold/Submanifold/Manifold.lean`), the input of the chain rule in
  `Hironaka/Manifold/Jacobian/Units.lean`.

Then `jacobianFun 𝕜 f χ φ' = (det ∘ D(χ ∘ f ∘ φ'⁻¹)) ∘ φ'` is `C^ω` on `φ'.source ∩ f⁻¹(χ.source)`
(`contMDiffOn_jacobianFun`). Two small identities on determinants complete the module:
`det (A ∘ B) = det A * det B` for continuous linear maps (`det_clm_comp`, Mathlib's
`LinearMap.det_comp` through the coercion) and the chain rule for a left inverse
`det (Dg'(g x)) * det (Dg x) = 1` (`det_fderiv_mul_det_fderiv_eq_one`).

The three calculus lemmas `det_clm_comp`, `contDiff_det` and `contDiffOn_det_fderiv` are proved in
`Hironaka/Analytic/Calculus/Det.lean` (namespace `Hironaka.Analytic`), where the `Hironaka`
library's `analyticOnNhd_det_fderiv` joins them; the three names below are one-line restatements
kept with their original signatures for the chart lemmas of this directory.
-/

public section

open Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Manifold

universe u

section Det

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The determinant of a composite of continuous linear maps is the product of the determinants
(Mathlib's `LinearMap.det_comp` through the coercion `E →L[𝕜] E → E →ₗ[𝕜] E`). -/
theorem det_clm_comp (A B : E →L[𝕜] E) : (A.comp B).det = A.det * B.det :=
  Analytic.det_clm_comp A B

/-- **The determinant is analytic on `E →L[𝕜] E`**: a restatement of
`Analytic.contDiff_det` (`Hironaka/Analytic/Calculus/Det.lean`) under the name the
chart lemmas use. -/
theorem contDiff_det {n : WithTop ℕ∞} : ContDiff 𝕜 n fun L : E →L[𝕜] E => L.det :=
  Analytic.contDiff_det

/-- **`x ↦ det (DF x)` is `C^ω` on an open set on which `F` is `C^ω`**: a restatement of
`Analytic.contDiffOn_det_fderiv` (`Hironaka/Analytic/Calculus/Det.lean`) under the
name the chart lemmas use. -/
theorem contDiffOn_det_fderiv {F : E → E} {s : Set E} (hF : ContDiffOn 𝕜 ω F s) (hs : IsOpen s) :
    ContDiffOn 𝕜 ω (fun x => (fderiv 𝕜 F x).det) s :=
  Analytic.contDiffOn_det_fderiv hF hs

/-- Chain rule for a left inverse: if `g' ∘ g = id` on an open neighbourhood of `x` then
`det (Dg'(g x)) * det (Dg x) = 1` (the model-space case `Fin n → 𝕜` is `fderiv_comp_fderiv_eq_id`
of `Hironaka/Manifold/BlowUp/Lift.lean`). -/
theorem det_fderiv_mul_det_fderiv_eq_one {g g' : E → E} {V : Set E} (hV : IsOpen V) {x : E}
    (hx : x ∈ V) (hg : DifferentiableAt 𝕜 g x) (hg' : DifferentiableAt 𝕜 g' (g x))
    (hgg' : ∀ y ∈ V, g' (g y) = y) :
    (fderiv 𝕜 g' (g x)).det * (fderiv 𝕜 g x).det = 1 := by
  have h1 : (fderiv 𝕜 g' (g x)).comp (fderiv 𝕜 g x) = ContinuousLinearMap.id 𝕜 E := by
    rw [← fderiv_comp x hg' hg]
    have : (g' ∘ g) =ᶠ[𝓝 x] id := eventuallyEq_of_mem (hV.mem_nhds hx) fun z hz => hgg' z hz
    rw [this.fderiv_eq, fderiv_id]
  have h2 := congrArg ContinuousLinearMap.det h1
  have hid : (ContinuousLinearMap.id 𝕜 E).det = 1 := LinearMap.det_id
  rw [det_clm_comp, hid] at h2
  exact h2

end Det

section Topology

variable {E : Type*} [TopologicalSpace E] {M : Type u} [TopologicalSpace M] {N : Type u}
  [TopologicalSpace N] {f : N → M}

/-- `χ.target ∩ χ⁻¹(s)` is open for `s` open. -/
theorem isOpen_target_inter_preimage_symm (χ : OpenPartialHomeomorph M E) {s : Set M}
    (hs : IsOpen s) : IsOpen (χ.target ∩ χ.symm ⁻¹' s) :=
  χ.symm.isOpen_inter_preimage hs

/-- The chart `φ'` maps `φ'.source ∩ f⁻¹(χ.source)` into `φ'.target ∩ φ'⁻¹(f⁻¹(χ.source))`. -/
theorem mapsTo_chart_target_inter (χ : OpenPartialHomeomorph M E) (φ' : OpenPartialHomeomorph N E) :
    MapsTo φ' (φ'.source ∩ f ⁻¹' χ.source) (φ'.target ∩ φ'.symm ⁻¹' (f ⁻¹' χ.source)) := by
  intro y hy
  refine ⟨φ'.map_source hy.1, ?_⟩
  change f (φ'.symm (φ' y)) ∈ χ.source
  rw [φ'.left_inv hy.1]
  exact hy.2

end Topology

section Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {N : Type u} [TopologicalSpace N]
  [ChartedSpace E N] {f : N → M}

/-- **The chart representative `χ ∘ f ∘ φ'⁻¹` of an analytic map `f` is `C^ω`** on
`φ'.target ∩ φ'⁻¹(f⁻¹(χ.source))`, for charts `χ`, `φ'` of the maximal atlases. -/
theorem contDiffOn_chartRep (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) {χ : OpenPartialHomeomorph M E}
    (hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M) {φ' : OpenPartialHomeomorph N E}
    (hφ' : φ' ∈ maximalAtlas 𝓘(𝕜, E) ω N) :
    ContDiffOn 𝕜 ω (χ ∘ f ∘ φ'.symm) (φ'.target ∩ φ'.symm ⁻¹' (f ⁻¹' χ.source)) :=
  contMDiffOn_iff_contDiffOn.mp <|
    (contMDiffOn_of_mem_maximalAtlas hχ).comp
      (hf.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas hφ').mono inter_subset_left))
      fun _ hv => hv.2

/-- **The Jacobian determinant of an analytic map `f` in charts `χ` of the target and `φ'` of the
source is analytic** on the common domain `φ'.source ∩ f⁻¹(χ.source)`: it is
`(det ∘ D(χ ∘ f ∘ φ'⁻¹)) ∘ φ'`, the composite of the analytic chart with the analytic function
`det ∘ DF` of the analytic chart representative `F` ([BM97, Theorem 1.10, the sentence after it]:
"the ideal generated … by the Jacobian determinant"). -/
theorem contMDiffOn_jacobianFun (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f)
    {χ : OpenPartialHomeomorph M E} (hχ : χ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    {φ' : OpenPartialHomeomorph N E} (hφ' : φ' ∈ maximalAtlas 𝓘(𝕜, E) ω N) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (jacobianFun 𝕜 f χ φ') (φ'.source ∩ f ⁻¹' χ.source) := by
  have hopen : IsOpen (φ'.target ∩ φ'.symm ⁻¹' (f ⁻¹' χ.source)) :=
    isOpen_target_inter_preimage_symm φ' (χ.open_source.preimage hf.continuous)
  have hG : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜) ω (fun x => (fderiv 𝕜 (χ ∘ f ∘ φ'.symm) x).det)
      (φ'.target ∩ φ'.symm ⁻¹' (f ⁻¹' χ.source)) :=
    contMDiffOn_iff_contDiffOn.mpr (contDiffOn_det_fderiv (contDiffOn_chartRep hf hχ hφ') hopen)
  exact hG.comp ((contMDiffOn_of_mem_maximalAtlas hφ').mono inter_subset_left)
    (mapsTo_chart_target_inter χ φ')

end Manifold

end Manifold
