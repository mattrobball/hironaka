/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Model
public import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
public import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.BlowUp.Transform.StrictFlag
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A closed submanifold of a closed submanifold

The push-forward of a blow-up sequence of `S` to the ambient `X` regards the centres
`Z_i^S ⊆ S_i ⊆ X_i` as closed submanifolds of `X_i` [Kol07, Definition 30.3], and conversely the
restriction to `S` [Kol07, Definition 30.2] needs the centre `Y ⊆ S` as a closed submanifold of the
bundled `S`, so that the restricted blow-down can be a blowing-up of `S` along `Y` in the sense
of [BM88, Definition 4.1]. This module proves that a closed submanifold `Y ⊆ S` of `M` of
codimension `c` is a closed submanifold of the bundled `S` (with its induced charts on `𝕜^{n-s}`)
of codimension `c − s` (`IsClosedSubmanifold.preimage_val_of_subset`); that a smooth subspace of
a manifold is locally a coordinate subspace is [BM97, (3.8)(2)]. The adapted charts are the
induced charts of the flag charts (`exists_adaptedChart_flag`, `isAdaptedChart_chartOn_flag`): in
a flag chart `Y = {z_σ = 0}` and `S = {z_{σ (τ j)} = 0}`, so on `S` the remaining centre
coordinates `z_{σ k}`, `k ∉ range τ`, cut out `Y`; read in the complementary coordinates of `S`'s
induced chart they are the coordinates of index `restrictEmb σ τ` (`Model.lean`). Not in the
sources; the proof is a chart computation.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {Y S : Set M} {c s : ℕ}

/-- The induced chart of an adapted chart of `S` (`IsAdaptedChart.chartOn`), typed as a chart of
the bundled `S` (so that statements about it elaborate on the bundled manifold). -/
def IsClosedSubmanifold.inducedChart (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ' : Fin s ↪ Fin n} (hφS : IsAdaptedChart ψ S φ σ') {a : M}
    (ha : a ∈ S) :
    OpenPartialHomeomorph hS.toAnalyticManifold (Fin (n - s) → 𝕜) :=
  hφS.chartOn ha

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.inducedChart_apply (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ' : Fin s ↪ Fin n} (hφS : IsAdaptedChart ψ S φ σ') {a : M}
    (ha : a ∈ S) (x : hS.toAnalyticManifold) :
    hS.inducedChart hφS ha x = projCompl σ' (ψ (φ (x : S).1)) :=
  rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.mem_inducedChart_source (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ' : Fin s ↪ Fin n} (hφS : IsAdaptedChart ψ S φ σ') {a : M}
    (ha : a ∈ S) (x : hS.toAnalyticManifold) :
    x ∈ (hS.inducedChart hφS ha).source ↔ (x : S).1 ∈ φ.source :=
  Iff.rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.mem_inducedChart_target (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ' : Fin s ↪ Fin n} (hφS : IsAdaptedChart ψ S φ σ') {a : M}
    (ha : a ∈ S) (w : Fin (n - s) → 𝕜) :
    w ∈ (hS.inducedChart hφS ha).target ↔ ψ.symm (embedCompl σ' w) ∈ φ.target :=
  Iff.rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.inducedChart_mem_maximalAtlas (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ' : Fin s ↪ Fin n} (hφS : IsAdaptedChart ψ S φ σ') {a : M}
    (ha : a ∈ S) :
    hS.inducedChart hφS ha ∈ maximalAtlas 𝓘(𝕜, Fin (n - s) → 𝕜) ω hS.toAnalyticManifold :=
  hφS.chartOn_mem_maximalAtlas' hS ha

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The induced chart of a flag chart of `Y ⊆ S` is a chart of the bundled `S` adapted to `Y`,
with the block embedding `restrictEmb σ τ`: on `S` the remaining centre coordinates `z_{σ k}`,
`k ∉ range τ`, cut out `Y`. -/
theorem isAdaptedChart_chartOn_flag (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n} {τ : Fin s ↪ Fin c}
    (hφ : IsAdaptedChart ψ Y φ σ) (hSflag : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0)
    {a : M} (ha : a ∈ S) :
    IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (hS.preimageVal Y)
      (hS.inducedChart (hφ.flag hSflag) ha) (restrictEmb σ τ) := by
  have hφS : IsAdaptedChart ψ S φ (τ.trans σ) := hφ.flag hSflag
  refine ⟨hS.inducedChart_mem_maximalAtlas hφS ha, fun x hx => ?_⟩
  have hxφ : (x : S).1 ∈ φ.source := hx
  have hxS : (x : S).1 ∈ S := (x : S).2
  have hτ0 : ∀ j, ψ (φ (x : S).1) (σ (τ j)) = 0 := (hSflag _ hxφ).mp hxS
  have hcoord : ∀ m, (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (hS.inducedChart hφS ha x) (restrictEmb σ τ m) =
        ψ (φ (x : S).1) (σ ((complEquiv τ).symm m).1) := by
    intro m
    change ψ (φ (x : S).1) ((complEquiv (τ.trans σ)).symm (restrictEmb σ τ m)).1 = _
    rw [symm_restrictEmb]
  have hmem : x ∈ hS.preimageVal Y ↔ ∀ i, ψ (φ (x : S).1) (σ i) = 0 :=
    (hS.mem_preimageVal Y x).trans (hφ.2 _ hxφ)
  refine hmem.trans ⟨fun hall m => (hcoord m).trans (hall _), fun hm k => ?_⟩
  by_cases hk : k ∈ Set.range τ
  · obtain ⟨j, rfl⟩ := hk
    exact hτ0 j
  · have h1 := hm (restrictIdx τ hk)
    rw [hcoord, symm_restrictIdx] at h1
    exact h1

/-- A closed submanifold of a closed submanifold is a closed submanifold: a closed submanifold
`Y ⊆ S` of codimension `c` is a closed submanifold of the bundled `S` of codimension `c − s`, in
the induced charts — the adapted charts are the induced charts of the flag charts of `Y ⊆ S`. -/
theorem IsClosedSubmanifold.preimage_val_of_subset (hS : IsClosedSubmanifold ψ S s)
    (hY : IsClosedSubmanifold ψ Y c) (hYS : Y ⊆ S) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) (hS.preimageVal Y)
      (c - s) := by
  refine ⟨hY.isClosed.preimage continuous_subtype_val, fun a' ha' => ?_⟩
  obtain ⟨φ, σ, τ, haφ, hφ, hSflag⟩ := exists_adaptedChart_flag hY hS hYS ha'
  exact ⟨hS.inducedChart (hφ.flag hSflag) (a' : S).2, restrictEmb σ τ, haφ,
    isAdaptedChart_chartOn_flag hS hφ hSflag (a' : S).2⟩

end Manifold

end
