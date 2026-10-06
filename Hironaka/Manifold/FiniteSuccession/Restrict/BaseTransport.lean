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
# Transport of a blowing-up along a diffeomorphism of the base

The push-forward `j_* B` of a blow-up sequence `B` of a closed subscheme `S ⊆ X` to `X`
[Kol07, Definition 30.3] identifies the stage `S_i` of the given sequence with the strict
transform inside `X_i` through an isomorphism `e_i : S_i ≃ S_i'`; the next blow-down
`S_{i+1} → S_i`, composed with `e_i`, is then a blowing-up of `S_i'` along `e_i(Z_i)`. This module
proves the manifold statement behind that step: a blowing-up `π : M' → M` along `Y` in the sense
of [BM88, Definition 4.1] (`IsBlowUp`) composed with a diffeomorphism `g : M ≃ N` of the base is a
blowing-up of `N` along `g '' Y` (`IsBlowUp.diffeomorph_comp`). The adapted charts of `g '' Y` pull
back along `g` to adapted charts of `Y` (`transportChart` along `g⁻¹`), a blow-up chart of `π`
over `φ ∘ g` is a blow-up chart of `g ∘ π` over `φ` (`IsBlowUpChart.diffeomorph_comp`), and the
remaining clauses transport by composition. Likewise a closed submanifold is carried to a closed
submanifold by a diffeomorphism (`IsClosedSubmanifold.image_diffeomorph`). Not in the sources; the
proofs are routine.
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
  [IsManifold 𝓘(𝕜, E) ω M] {N : Type u} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(𝕜, E) ω N] {Y : Set M} {c : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω N] in
/-- The image of `Y` under a diffeomorphism, in the form the chart transport `transportChart`
expects. -/
theorem image_inter_source_eq_of_diffeomorph (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) (Y : Set M) :
    g.toPartialDiffeomorphUniv '' (Y ∩ g.toPartialDiffeomorphUniv.source) =
      g '' Y ∩ g.toPartialDiffeomorphUniv.target := by
  change g '' (Y ∩ Set.univ) = g '' Y ∩ Set.univ
  rw [Set.inter_univ, Set.inter_univ]

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω N] in
/-- The preimage of `g '' Y` under a diffeomorphism, in the form the chart transport
`transportChart` expects. -/
theorem symm_image_image_inter_source_eq_of_diffeomorph (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (Y : Set M) :
    g.toPartialDiffeomorphUniv.symm '' (g '' Y ∩ g.toPartialDiffeomorphUniv.symm.source) =
      Y ∩ g.toPartialDiffeomorphUniv.symm.target := by
  change g.symm '' (g '' Y ∩ Set.univ) = Y ∩ Set.univ
  rw [Set.inter_univ, Set.inter_univ]
  exact g.toEquiv.symm_image_image Y

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- A closed submanifold is carried to a closed submanifold by a diffeomorphism: the adapted
charts of `g '' Y` are those of `Y` transported along `g⁻¹`. -/
theorem IsClosedSubmanifold.image_diffeomorph (hY : IsClosedSubmanifold ψ Y c)
    (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) : IsClosedSubmanifold ψ (g '' Y) c := by
  refine ⟨g.toHomeomorph.isClosedMap _ hY.isClosed, fun b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hb
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  refine ⟨transportChart g.toPartialDiffeomorphUniv φ, σ, ⟨Set.mem_univ _, ?_⟩,
    isAdaptedChart_transportChart g.toPartialDiffeomorphUniv
      (image_inter_source_eq_of_diffeomorph g Y) hφ⟩
  change g.symm (g a) ∈ φ.source
  rw [g.symm_apply_apply]
  exact haφ

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω N] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] in
/-- A blow-up chart of `π` over the pull-back `φ ∘ g` of a chart `φ` of `N` is a blow-up chart of
`g ∘ π` over `φ`. -/
theorem IsBlowUpChart.diffeomorph_comp (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    {φ : OpenPartialHomeomorph N E} {σ : Fin c ↪ Fin n} {i : Fin c} {Φ : OpenPartialHomeomorph M' E}
    (hΦ : IsBlowUpChart ψ π (transportChart g.toPartialDiffeomorphUniv.symm φ) σ i Φ) :
    IsBlowUpChart ψ (g ∘ π) φ σ i Φ where
  mem_maximalAtlas := hΦ.mem_maximalAtlas
  source_subset := fun p hp => (hΦ.source_subset hp).2
  mem_target_iff := fun v => by
    rw [hΦ.mem_target_iff, transportChart_target_eq _ fun _ _ => Set.mem_univ _]
  comm := fun p hp => hΦ.comm p hp

omit [IsManifold 𝓘(𝕜, E) ω N] in
/-- A blowing-up of `M` along `Y` composed with a diffeomorphism `g : M ≃ N` of the base is a
blowing-up of `N` along `g '' Y`. -/
theorem IsBlowUp.diffeomorph_comp (h : IsBlowUp ψ Y c π) (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) :
    IsBlowUp ψ (g '' Y) c (g ∘ π) where
  contMDiff := g.contMDiff.comp h.contMDiff
  isProperMap := g.toHomeomorph.isProperMap.comp h.isProperMap
  isLocalDiffeomorphOn_compl := fun x => by
    have hx : π x.1 ∉ Y := fun hY => x.2 ⟨π x.1, hY, rfl⟩
    obtain ⟨Ψ, hxΨ, hΨ⟩ := (h.isLocalDiffeomorphOn_compl ⟨x.1, hx⟩).exists_partialDiffeomorph
    exact IsLocalDiffeomorphAt.of_eqOn (Ψ.trans g.toPartialDiffeomorphUniv) ⟨hxΨ, Set.mem_univ _⟩
      fun y hy => congrArg g (hΨ hy.1)
  bijOn_compl := by
    have hpre : (g ∘ π) ⁻¹' (g '' Y)ᶜ = π ⁻¹' Yᶜ := by
      ext p
      change g (π p) ∉ g '' Y ↔ π p ∉ Y
      exact not_congr ⟨fun ⟨y, hy, e⟩ => g.toEquiv.injective e ▸ hy, fun hp => ⟨π p, hp, rfl⟩⟩
    have himg : g '' Yᶜ = (g '' Y)ᶜ := Set.image_compl_eq g.toEquiv.bijective
    rw [hpre, ← himg]
    exact (g.toEquiv.injective.injOn.bijOn_image).comp h.bijOn_compl
  exists_chart := fun φ σ hφ i => by
    obtain ⟨Φ, hΦ⟩ := h.exists_chart _ σ (isAdaptedChart_transportChart
      g.toPartialDiffeomorphUniv.symm (symm_image_image_inter_source_eq_of_diffeomorph g Y) hφ) i
    exact ⟨Φ, hΦ.diffeomorph_comp g⟩
  cover := fun φ σ hφ p hp => by
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover _ σ (isAdaptedChart_transportChart
      g.toPartialDiffeomorphUniv.symm (symm_image_image_inter_source_eq_of_diffeomorph g Y) hφ) p
      ⟨Set.mem_univ _, hp⟩
    exact ⟨i, Φ, hΦ.diffeomorph_comp g, hpΦ⟩

end Manifold

end
