/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Nested
public import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The induced blow-up charts of the strict transform

Of the `r` charts covering the blow-up of a centre of codimension `r`, the `r − 1` whose
distinguished coordinate is not the equation of a hypersurface `S` through the centre completely
cover the strict transform `S_1` [Kol07, Theorem 88, proof]. This module proves the chart
statement for a closed submanifold `S` of arbitrary codimension: over a flag chart `φ` of `Y ⊆ S`
(`Y = {z_σ = 0}`, `S = {z_{σ (τ j)} = 0}`), an ambient blow-up chart `Φ` of index `i ∉ range τ` is
adapted to the strict transform `S'` (`isAdaptedChart_strictTransform_of_not_mem_range`), and its
induced chart on `S'` — the complementary coordinates `projCompl (τ.trans σ) ∘ ψ ∘ Φ` — is a
blow-up chart of the restricted blow-down `π|_{S'} : S' → S` over the induced chart of `φ` on `S`,
of index `restrictIdx τ hi` and block `restrictEmb σ τ` (`isBlowUpChart_chartOn_flag`): the chart
relation is the ambient one read in the complementary coordinates (`projCompl_blowUpChartMap` of
`Model.lean`), and the target is the whole `i`-th piece over the induced chart because the
blow-up chart map preserves the coordinate subspace `{u_{σ (τ j)} = 0}`
(`blowUpChartMap_embedCompl`). The lemma `symm_embedCompl_mem_strictTransform` produces the point
of `S'` over a point of that target. These are the chart clauses of a blowing-up in the sense of
[BM88, Definition 4.1] for the restricted blow-down, in Kollár's identification of the stage
`S_{i+1}` of a restricted blow-up sequence with `Bl_{Z_i ∩ S_i} S_i` [Kol07, Definition 30.2]. Not
in the sources beyond the remark cited; the proof is a chart computation.
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
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {Y S : Set M} {c s : ℕ}
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
  {τ : Fin s ↪ Fin c} {i : Fin c} {Φ : OpenPartialHomeomorph M' E}

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] in
/-- Membership in the image of a set under the identity chart `refl`. -/
theorem mem_image_refl_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : Set F)
    (x : F) : x ∈ (ContinuousLinearEquiv.refl 𝕜 F) '' T ↔ x ∈ T := by
  rw [mem_image_clm_iff]
  exact Iff.rfl

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] in
/-- A point of the `restrictIdx τ hi`-th piece over the induced chart of `S` embeds into the target
of the ambient blow-up chart on the coordinate subspace `{u_{σ (τ j)} = 0}`. -/
theorem symm_embedCompl_mem_target_of_mem (hS : IsClosedSubmanifold ψ S s)
    (hφ : IsAdaptedChart ψ Y φ σ)
    (hSflag : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0) {a : M} (ha : a ∈ S)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hi : i ∉ Set.range τ) {v : Fin (n - s) → 𝕜}
    (hv : blowUpChartMap (restrictEmb σ τ) (restrictIdx τ hi) v ∈
      (hS.inducedChart (hφ.flag hSflag) ha).target) :
    ψ.symm (embedCompl (τ.trans σ) v) ∈ Φ.target := by
  rw [hΦ.mem_target_iff, ψ.apply_symm_apply, blowUpChartMap_embedCompl σ τ hi, mem_image_clm_iff]
  exact hv

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] in
/-- The point of the ambient blow-up chart on the coordinate subspace `{u_{σ (τ j)} = 0}` lies in
the strict transform of `S`. -/
theorem symm_embedCompl_mem_strictTransform (hφ : IsAdaptedChart ψ Y φ σ)
    (hSflag : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hi : i ∉ Set.range τ) {v : Fin (n - s) → 𝕜}
    (hv : ψ.symm (embedCompl (τ.trans σ) v) ∈ Φ.target) :
    Φ.symm (ψ.symm (embedCompl (τ.trans σ) v)) ∈ strictTransformSet π Y S := by
  have hE := strictTransform_inter_source_of_not_mem_range hφ hΦ hSflag hi
  have hs : Φ.symm (ψ.symm (embedCompl (τ.trans σ) v)) ∈ Φ.source := Φ.map_target hv
  have hmem : Φ.symm (ψ.symm (embedCompl (τ.trans σ) v)) ∈
      {p ∈ Φ.source | ∀ j, ψ (Φ p) (σ (τ j)) = 0} := by
    refine ⟨hs, fun j => ?_⟩
    rw [Φ.right_inv hv, ψ.apply_symm_apply]
    exact embedCompl_apply_range (τ.trans σ) v j
  exact ((Set.ext_iff.mp hE _).mpr hmem).1

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Over a flag chart of `Y ⊆ S`, the ambient blow-up chart of an index `i ∉ range τ`, read on
the strict transform `S'` in the complementary coordinates, is a blow-up chart of the restricted
blow-down `π|_{S'} : S' → S` over the induced chart of `S`, of index `restrictIdx τ hi` (the
`r − 1` charts covering `S_1` in [Kol07, Theorem 88, proof]). -/
theorem isBlowUpChart_chartOn_flag (hS : IsClosedSubmanifold ψ S s) (h : IsBlowUp ψ Y c π)
    (hS' : IsClosedSubmanifold ψ (strictTransformSet π Y S) s) (hφ : IsAdaptedChart ψ Y φ σ)
    (hSflag : ∀ x ∈ φ.source, x ∈ S ↔ ∀ j, ψ (φ x) (σ (τ j)) = 0) {a : M} (ha : a ∈ S)
    (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hi : i ∉ Set.range τ) {p₀ : M'}
    (hp₀ : p₀ ∈ strictTransformSet π Y S) :
    IsBlowUpChart (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (hS'.restrictMap hS π h.contMDiff
        (strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed))
      (hS.inducedChart (hφ.flag hSflag) ha) (restrictEmb σ τ) (restrictIdx τ hi)
      (hS'.inducedChart (isAdaptedChart_strictTransform_of_not_mem_range hφ hΦ hSflag hi) hp₀) where
  mem_maximalAtlas :=
    hS'.inducedChart_mem_maximalAtlas
      (isAdaptedChart_strictTransform_of_not_mem_range hφ hΦ hSflag hi) hp₀
  source_subset := fun p hp => hΦ.source_subset hp
  mem_target_iff := fun v => by
    change ψ.symm (embedCompl (τ.trans σ) v) ∈ Φ.target ↔ _
    rw [hΦ.mem_target_iff, ψ.apply_symm_apply, blowUpChartMap_embedCompl σ τ hi,
      mem_image_clm_iff]
    constructor
    · intro hv
      exact ⟨_, hv, rfl⟩
    · rintro ⟨w, hw, hwv⟩
      have e : w = blowUpChartMap (restrictEmb σ τ) (restrictIdx τ hi) v := hwv
      rw [← e]
      exact hw
  comm := fun p hp => by
    change projCompl (τ.trans σ) (ψ (φ (π (p : strictTransformSet π Y S).1))) =
      blowUpChartMap (restrictEmb σ τ) (restrictIdx τ hi)
        (projCompl (τ.trans σ) (ψ (Φ (p : strictTransformSet π Y S).1)))
    rw [hΦ.comm (p : strictTransformSet π Y S).1 hp, projCompl_blowUpChartMap σ τ hi]

end Manifold

end
