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
# Clopen parts of closed submanifolds

A part of a closed submanifold `Y` that is open in `Y` and closed in the ambient manifold — a
clopen part of `Y`, written `Y ∩ O` with `O` open — is a closed submanifold of the same
codimension: its adapted charts are the adapted charts of `Y` restricted to `O`. Not in the
sources; used where a centre is a union of some of the components of an intersection of boundary
hypersurfaces (`Hironaka/Resolution/Analytic/Principalization/SncClopen.lean`).
-/

public section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The restriction of an adapted chart of `Y` to an open set `O` is an adapted chart of the
clopen part `Y ∩ O`. -/
theorem IsAdaptedChart.inter_restrOpen {Y : Set M} {φ : OpenPartialHomeomorph M E} {c : ℕ}
    {σ : Fin c ↪ Fin n} (h : IsAdaptedChart ψ Y φ σ) {O : Set M} (hO : IsOpen O) :
    IsAdaptedChart ψ (Y ∩ O) (φ.restrOpen O hO) σ := by
  refine ⟨(h.restrOpen' O hO).1, fun x hx => ?_⟩
  have hx' := hx
  rw [OpenPartialHomeomorph.restrOpen_source] at hx'
  have hiff := (h.restrOpen' O hO).2 x hx
  constructor
  · intro hxYO
    exact hiff.mp hxYO.1
  · intro hz
    exact ⟨hiff.mpr hz, hx'.2⟩

/-- A closed part of a closed submanifold that is open in it is a closed submanifold of the same
codimension. -/
theorem IsClosedSubmanifold.inter_of_isOpen {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c)
    {O : Set M} (hO : IsOpen O) (hZ : IsClosed (Y ∩ O)) : IsClosedSubmanifold ψ (Y ∩ O) c where
  isClosed := hZ
  exists_adaptedChart := by
    rintro a ⟨haY, haO⟩
    obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a haY
    refine ⟨φ.restrOpen O hO, σ, ?_, hφ.inter_restrOpen hO⟩
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨haφ, haO⟩

end Manifold
