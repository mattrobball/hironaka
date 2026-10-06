/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.LocalDiffeomorph
public import Hironaka.Manifold.BlowUp.Defs
public import Hironaka.Manifold.Chart.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Transport of a blowing-up along a diffeomorphism of the source

Kollár identifies the stage `S_{i+1} := Bl_{Z_i ∩ S_i} S_i` of a restricted blow-up sequence with
the birational transform of `S_i` [Kol07, Definition 30.2]. Once the strict transform `S'` of a
closed submanifold `S` under a blowing-up along `Y ⊆ S` is identified with the blowing-up of `S`
along `Y` by a diffeomorphism `g : S' → Bl_Y S` over `S`, the restricted blow-down
`π|_{S'} = blowUpπ ∘ g` is itself a blowing-up in the sense of [BM88, Definition 4.1] (`IsBlowUp`).
This module proves the transport statement used there: the six clauses of `IsBlowUp` transport
along a diffeomorphism of the source, analyticity, properness, the isomorphism off the centre and
the bijection by composition, the blow-up charts by pre-composition with `g` (`transportChart`
along `g⁻¹`, which keeps the target and the chart relations). Nothing here is specific to
submanifolds. Not in the sources; the proof is routine.
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(𝕜, E) ω N] [T2Space N] [SecondCountableTopology N] {π : M' → M}

omit [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M']
  [T2Space N] [SecondCountableTopology N] in
/-- A blow-up chart of `π` pre-composed with a diffeomorphism `g : N → M'` is a blow-up chart of
`π ∘ g` over the same adapted chart, with the same target. -/
theorem IsBlowUpChart.comp_diffeomorph {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
    {i : Fin c} {Φ : OpenPartialHomeomorph M' E} (hΦ : IsBlowUpChart ψ π φ σ i Φ)
    (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M' ω) :
    IsBlowUpChart ψ (π ∘ g) φ σ i (transportChart g.toPartialDiffeomorphUniv.symm Φ) where
  mem_maximalAtlas := transportChart_mem_maximalAtlas _ hΦ.mem_maximalAtlas
  source_subset := fun _ hx => hΦ.source_subset hx.2
  mem_target_iff := fun v => by
    rw [transportChart_target_eq _ fun _ _ => Set.mem_univ _]
    exact hΦ.mem_target_iff v
  comm := fun p hp => hΦ.comm (g p) hp.2

/-- A blowing-up composed with a diffeomorphism of its source is a blowing-up with the same
centre. -/
theorem IsBlowUp.comp_diffeomorph (h : IsBlowUp ψ Y c π) (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M' ω) :
    IsBlowUp ψ Y c (π ∘ g) where
  contMDiff := h.contMDiff.comp g.contMDiff
  isProperMap := h.isProperMap.comp g.toHomeomorph.isProperMap
  isLocalDiffeomorphOn_compl := fun x => by
    obtain ⟨Ψ, hxΨ, hΨ⟩ := (h.isLocalDiffeomorphOn_compl ⟨g x.1, x.2⟩).exists_partialDiffeomorph
    exact IsLocalDiffeomorphAt.of_eqOn (g.toPartialDiffeomorphUniv.trans Ψ) ⟨Set.mem_univ _, hxΨ⟩
      fun y hy => hΨ hy.2
  bijOn_compl := h.bijOn_compl.comp ⟨fun _ hx => hx, g.toEquiv.injective.injOn, fun y hy =>
    ⟨g.symm y, by
      change π (g (g.symm y)) ∈ Yᶜ
      rw [g.apply_symm_apply]; exact hy, g.apply_symm_apply y⟩⟩
  exists_chart := fun φ σ hφ i =>
    let ⟨_, hΦ⟩ := h.exists_chart φ σ hφ i
    ⟨_, hΦ.comp_diffeomorph g⟩
  cover := fun φ σ hφ p hp =>
    let ⟨i, _, hΦ, hpΦ⟩ := h.cover φ σ hφ (g p) hp
    ⟨i, _, hΦ.comp_diffeomorph g, ⟨Set.mem_univ _, hpΦ⟩⟩

end Manifold

end
