/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Charts
public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transition
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Example: the strict transform of a line under the blow-up of the plane at the origin

The blowing-up of the origin of `𝕜²` in the local model (`blowUpChartMap`, `blowUpCenter` on
`Fin 2 → 𝕜`, indices `0`, `1`) has two charts, `(u, v) ↦ (u, uv)` (index `0`) and
`(s, t) ↦ (st, t)` (index `1`) — the charts `V'_i = {ξ_i ≠ 0}` of Bierstone–Milman's blowing-up
[BM88, Definition 4.1]. The strict transform of the line `E = {z₀ = 0}` is `{u₀ = 0}` in the chart
of index `1` and misses the chart of index `0` (Kollár: "only `r − 1` of these can be written in
the above form", [Kol07, Theorem 88, proof]); the exceptional divisor is `{u_i = 0}` in the chart
of index `i` ([Kol07, Notation 19]: the exceptional divisor of a blow-up is the preimage of the
centre). The identities are instances of the chart-level lemmas on strict transforms
(`strictTransform_inter_source_of_ne`, `strictTransform_inter_source_self`) for the identity chart
of the model, which is a blow-up chart over itself (`isBlowUpChart_model`), and of
`blowUpChartMap_mem_center_iff`.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n c : ℕ} (σ : Fin c ↪ Fin n) (i : Fin c)

/-- The identity chart of the model `Fin n → 𝕜` lies in the maximal analytic atlas. -/
theorem refl_mem_maximalAtlas_model :
    OpenPartialHomeomorph.refl (Fin n → 𝕜) ∈
      maximalAtlas 𝓘(𝕜, Fin n → 𝕜) ω (Fin n → 𝕜) := by
  have := IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, Fin n → 𝕜)) (n := ω) (0 : Fin n → 𝕜)
  rwa [chartAt_self_eq] at this

/-- The identity chart of the model is adapted to the block centre `blowUpCenter σ`. -/
theorem isAdaptedChart_model :
    IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (blowUpCenter σ)
      (OpenPartialHomeomorph.refl (Fin n → 𝕜)) σ :=
  ⟨refl_mem_maximalAtlas_model, fun _ _ => Iff.rfl⟩

/-- The identity chart of the model is a blow-up chart of index `i` over the identity chart, for
the blow-up chart map `π_i` itself. -/
theorem isBlowUpChart_model :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (blowUpChartMap σ i)
      (OpenPartialHomeomorph.refl (Fin n → 𝕜)) σ i (OpenPartialHomeomorph.refl (Fin n → 𝕜)) where
  mem_maximalAtlas := refl_mem_maximalAtlas_model
  source_subset := fun _ _ => trivial
  mem_target_iff := fun v => ⟨fun _ => ⟨blowUpChartMap σ i v, trivial, rfl⟩, fun _ => trivial⟩
  comm := fun _ _ => rfl

/-- In the chart of index `1`, `(s, t) ↦ (st, t)`, the strict transform of the line `E = {z₀ = 0}`
is `{u₀ = 0}`. -/
theorem strictTransformSet_fin_two_one :
    strictTransformSet (blowUpChartMap (𝕜 := 𝕜) (Function.Embedding.refl (Fin 2)) 1)
      (blowUpCenter (𝕜 := 𝕜) (Function.Embedding.refl (Fin 2))) {x : Fin 2 → 𝕜 | x 0 = 0} =
      {u : Fin 2 → 𝕜 | u 0 = 0} := by
  have h := strictTransform_inter_source_of_ne
    (isAdaptedChart_model (Function.Embedding.refl (Fin 2)))
    (isBlowUpChart_model (Function.Embedding.refl (Fin 2)) 1) (k := 0)
    (H := {x : Fin 2 → 𝕜 | x 0 = 0}) (fun _ _ => Iff.rfl) (by decide)
  rw [OpenPartialHomeomorph.refl_source, Set.inter_univ] at h
  rw [h]
  ext u
  exact ⟨fun hu => hu.2, fun hu => ⟨trivial, hu⟩⟩

/-- In the chart of index `0`, `(u, v) ↦ (u, uv)`, the strict transform of the line `E = {z₀ = 0}`
is empty ([Kol07, Theorem 88, proof]). -/
theorem strictTransformSet_fin_two_zero :
    strictTransformSet (blowUpChartMap (𝕜 := 𝕜) (Function.Embedding.refl (Fin 2)) 0)
      (blowUpCenter (𝕜 := 𝕜) (Function.Embedding.refl (Fin 2))) {x : Fin 2 → 𝕜 | x 0 = 0} = ∅ := by
  have h := strictTransform_inter_source_self
    (isAdaptedChart_model (Function.Embedding.refl (Fin 2)))
    (isBlowUpChart_model (Function.Embedding.refl (Fin 2)) 0)
    (H := {x : Fin 2 → 𝕜 | x 0 = 0}) (fun _ _ => Iff.rfl)
  rwa [OpenPartialHomeomorph.refl_source, Set.inter_univ] at h

/-- In the chart of index `i` the exceptional divisor is `{u_i = 0}` [Kol07, Notation 19]. -/
theorem preimage_center_fin_two (i : Fin 2) :
    blowUpChartMap (𝕜 := 𝕜) (Function.Embedding.refl (Fin 2)) i ⁻¹'
      blowUpCenter (𝕜 := 𝕜) (Function.Embedding.refl (Fin 2)) = {u : Fin 2 → 𝕜 | u i = 0} :=
  Set.ext fun u => blowUpChartMap_mem_center_iff (Function.Embedding.refl (Fin 2)) (i := i) u

end Hironaka.Manifold
