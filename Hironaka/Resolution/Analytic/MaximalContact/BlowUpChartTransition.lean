/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.BlowUp.Charts
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Manifold.BlowUp.Unique
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transitions between the abstract blow-up charts

The blowing-up `π : M' → M` of a closed submanifold is characterised abstractly (`IsBlowUp`): over
an adapted chart `φ` of the centre, blow-up charts `Φ_i` of every index exist (`exists_chart`) and
cover `π⁻¹(φ.source)` (`cover`), each reading `ψ ∘ φ ∘ π = π_i ∘ ψ ∘ Φ_i` (`comm`) with the model
chart domain as target (`mem_target_iff`). Nothing says directly which points of `M'` lie in which
chart. This module derives the transition rule from the axioms — Kollár's proof of the uniqueness of
blow-up sequences needs the two lifts `f'(q)`, `g'(q)` to be read in one chart of `Bl_Y M`
[Kol07, Theorem 97, proof]:

* `IsBlowUpChart.mem_source_of_mem_transitionDomain`: if `p ∈ Φ_i.source` and the chart
  coordinates `ψ (Φ_i p)` lie in the transition domain `T_ik` (`u_{σ k} ≠ 0`, or `i = k`), then
  `p ∈ Φ_k.source` and `ψ (Φ_k p) = T_ik (ψ (Φ_i p))` — the abstract charts are glued by the
  transition maps of the model blow-up (`blowUpTransition`), the chart changes of
  Bierstone–Milman's description of the blowing-up [BM88, Definition 4.1].

The proof is the uniqueness of lifts (`IsBlowUp.eqOn_of_comp_eq`, from the density of the
complement of the exceptional divisor): the candidate `q ↦ Φ_k⁻¹(ψ⁻¹(T_ik(ψ(Φ_i q))))` is a
continuous map over `π` on the open set of transverse points, so it is the identity there.
-/

public section

open TopologicalSpace Topology Filter
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {Y : Set M} {c : ℕ}
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} {φ : OpenPartialHomeomorph M E} {σ : Fin c ↪ Fin n}
  {i k : Fin c} {Φ₁ Φ₂ : OpenPartialHomeomorph M' E}

/-- A point of the blow-up chart of index `i` whose coordinates lie in the transition domain
`T_ik` (`u_{σ k} ≠ 0`, or `i = k`) lies in the blow-up chart of index `k` over the same adapted
chart, with coordinates `T_ik` of the old ones (the chart changes of the blowing-up,
[BM88, Definition 4.1]). By the uniqueness of lifts (`IsBlowUp.eqOn_of_comp_eq`). -/
theorem IsBlowUpChart.mem_source_of_mem_transitionDomain (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hΦ₁ : IsBlowUpChart ψ π φ σ i Φ₁) (hΦ₂ : IsBlowUpChart ψ π φ σ k Φ₂)
    {p : M'} (hp : p ∈ Φ₁.source) (hpk : ψ (Φ₁ p) ∈ blowUpTransitionDomain σ i k) :
    p ∈ Φ₂.source ∧ ψ (Φ₂ p) = blowUpTransition σ i k (ψ (Φ₁ p)) := by
  -- the open set of transverse points of the chart of index `i`
  have hNopen : IsOpen (Φ₁.source ∩ Φ₁ ⁻¹' (ψ ⁻¹' blowUpTransitionDomain σ i k)) :=
    Φ₁.isOpen_inter_preimage
      ((isOpen_blowUpTransitionDomain (σ := σ) (i := i) (k := k)).preimage ψ.continuous)
  -- the transported coordinates lie in the target of the chart of index `k`
  have hv : ∀ q ∈ Φ₁.source ∩ Φ₁ ⁻¹' (ψ ⁻¹' blowUpTransitionDomain σ i k),
      ψ.symm (blowUpTransition σ i k (ψ (Φ₁ q))) ∈ Φ₂.target := by
    intro q hq
    rw [hΦ₂.mem_target_iff, ψ.apply_symm_apply,
      blowUpChartMap_blowUpTransition σ _ hq.2, ← hΦ₁.comm q hq.1]
    exact ⟨_, φ.map_source (hΦ₁.source_subset hq.1), rfl⟩
  -- the candidate lift lies over `π`
  have hπG' : ∀ q ∈ Φ₁.source ∩ Φ₁ ⁻¹' (ψ ⁻¹' blowUpTransitionDomain σ i k),
      π (Φ₂.symm (ψ.symm (blowUpTransition σ i k (ψ (Φ₁ q))))) = π q := by
    intro q hq
    have hs : Φ₂.symm (ψ.symm (blowUpTransition σ i k (ψ (Φ₁ q)))) ∈ Φ₂.source :=
      Φ₂.map_target (hv q hq)
    have h1 := hΦ₂.comm _ hs
    rw [Φ₂.right_inv (hv q hq), ψ.apply_symm_apply,
      blowUpChartMap_blowUpTransition σ _ hq.2, ← hΦ₁.comm q hq.1] at h1
    exact φ.injOn (hΦ₂.source_subset hs) (hΦ₁.source_subset hq.1) (ψ.injective h1)
  -- and is continuous
  have hcont : ContinuousOn (fun q => Φ₂.symm (ψ.symm (blowUpTransition σ i k (ψ (Φ₁ q)))))
      (Φ₁.source ∩ Φ₁ ⁻¹' (ψ ⁻¹' blowUpTransitionDomain σ i k)) := by
    refine Φ₂.continuousOn_symm.comp ?_ fun q hq => hv q hq
    refine ψ.symm.continuous.comp_continuousOn ?_
    refine (analyticOnNhd_blowUpTransition (σ := σ) (i := i) (k := k)).continuousOn.comp ?_
      fun q hq => hq.2
    exact ψ.continuous.comp_continuousOn (Φ₁.continuousOn.mono Set.inter_subset_left)
  -- uniqueness of lifts: the candidate is the identity
  have heq := IsBlowUp.eqOn_of_comp_eq hY h h hNopen continuousOn_id hcont (fun _ _ => rfl) hπG'
  have hpN : p ∈ Φ₁.source ∩ Φ₁ ⁻¹' (ψ ⁻¹' blowUpTransitionDomain σ i k) := ⟨hp, hpk⟩
  have hpe : p = Φ₂.symm (ψ.symm (blowUpTransition σ i k (ψ (Φ₁ p)))) := heq hpN
  refine ⟨?_, ?_⟩
  · rw [hpe]
    exact Φ₂.map_target (hv p hpN)
  · conv_lhs => rw [hpe]
    rw [Φ₂.right_inv (hv p hpN), ψ.apply_symm_apply]

end Manifold
