/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Transport
public import Hironaka.Manifold.BlowUp.Defs
import Hironaka.Manifold.BlowUp.Quadratic
import Hironaka.Manifold.BlowUp.Transition
import Hironaka.Manifold.BlowUp.Unique
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Coordinate germs under the blow-down and the chart change

Three facts about the blowing-up `π : Bl_Y M → M` and its blow-up charts, used to show that a
morphism into the blowing-up over a given map is determined by its chart coordinates (the
uniqueness half of the universal property of the blowing-up):

* `IsBlowUpChart.germMap_coord_off`: in a blow-up chart of index `i` the pulled-back off-block
  coordinates are the off-block coordinates of the chart, `z_j ∘ π = u_j` (the chart formula of
  [BM88, Definition 4.1] in germ form; `IsBlowUpChart.germMap_coord_self` and
  `IsBlowUpChart.germMap_coord_of_ne` are the block cases `z_{σ i} ∘ π = u_i`,
  `z_{σ k} ∘ π = u_i u_k`).
* `germMap_coord_transportChart`: off the centre, where `π` agrees with a partial diffeomorphism
  `Φ₀`, the pulled-back coordinate germs of a chart `φ` of `M` are the coordinate germs of the
  transported chart `φ ∘ Φ₀ = φ ∘ π` of `Bl_Y M` (`transportChart`).
* `IsBlowUp.mem_source_of_coord_ne_zero`: a point of the blow-up chart `Φₖ` whose `σ i`-th
  coordinate is nonzero lies in the blow-up chart `Φᵢ` over the same adapted chart: the chart
  change `Φᵢ⁻¹ ∘ T_{ki} ∘ Φₖ` through the transition map of the local model is a continuous lift
  of `π` on that region, so it is the identity by the uniqueness of continuous lifts
  (`IsBlowUp.eqOn_of_comp_eq`).

These facts enter the comparison of the blowing-up of a manifold with the monoidal transformation
of an analytic space (`Hironaka.AnalyticSpace.MonoidalUnique`) and the strict transform of smooth
subspaces (`Hironaka.Manifold.BlowUp.Transform.StrictSmooth`).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {M' : Type u}
  [TopologicalSpace M'] [ChartedSpace E M'] {π : M' → M} {φ : OpenPartialHomeomorph M E} {c : ℕ}
  {σ : Fin c ↪ Fin n} {i : Fin c} {Φ : OpenPartialHomeomorph M' E} {p : M'}

/-- `z_j ∘ π = u_j` for `j` off the block: the pullback of an off-centre coordinate of the adapted
chart is the same coordinate of the blow-up chart (the chart formula of [BM88, Definition 4.1] in
germ form). -/
theorem IsBlowUpChart.germMap_coord_off (hπ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hΦ : IsBlowUpChart ψ π φ σ i Φ) (hp : p ∈ Φ.source)
    {j : Fin n} (hj : ∀ k, σ k ≠ j) :
    germMap π hπ p (coord E ψ φ hφ (hΦ.source_subset hp) j) =
      coord E ψ Φ hΦ.mem_maximalAtlas hp j := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M' p
  rw [stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord, Germ.coe_compTendsto,
    Germ.coe_eq]
  filter_upwards [Φ.open_source.mem_nhds hp] with x hx
  rw [Function.comp_apply, extendSection_of_mem 𝕜 E _ (hΦ.source_subset hx),
    extendSection_of_mem 𝕜 E _ hx]
  exact blowUpChart_coord_off hΦ hx hj

/-- The coordinate germs of a chart `φ` of `M` pulled back along a map `π` that agrees with a
partial diffeomorphism `Φ₀ : M' → M` near `p` are the coordinate germs of the transported chart
`φ ∘ Φ₀ = φ ∘ π` of `M'` (`transportChart`). -/
theorem germMap_coord_transportChart [IsManifold 𝓘(𝕜, E) ω M']
    (hπ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (Φ₀ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M' M ω)
    (hΦ₀ : Set.EqOn π Φ₀ Φ₀.source) (hp : p ∈ Φ₀.source) (hπp : π p ∈ φ.source) (j : Fin n) :
    germMap π hπ p (coord E ψ φ hφ hπp j) =
      coord E ψ (transportChart Φ₀.symm φ) (transportChart_mem_maximalAtlas Φ₀.symm hφ)
        (show p ∈ (transportChart Φ₀.symm φ).source from ⟨hp, by
          change Φ₀ p ∈ φ.source; rw [← hΦ₀ hp]; exact hπp⟩) j := by
  apply stalkToGerm_injective 𝓘(𝕜, E) ω M' p
  rw [stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord, Germ.coe_compTendsto,
    Germ.coe_eq]
  have hop : IsOpen (Φ₀.source ∩ π ⁻¹' φ.source) :=
    Φ₀.open_source.inter (φ.open_source.preimage hπ.continuous)
  filter_upwards [hop.mem_nhds ⟨hp, hπp⟩] with x hx
  rw [Function.comp_apply, extendSection_of_mem 𝕜 E _ hx.2,
    extendSection_of_mem 𝕜 E _ (show x ∈ (transportChart Φ₀.symm φ).source from
      ⟨hx.1, by change Φ₀ x ∈ φ.source; rw [← hΦ₀ hx.1]; exact hx.2⟩)]
  change ψ (φ (π x)) j = ψ (φ (Φ₀.symm.invFun x)) j
  rw [hΦ₀ hx.1]
  rfl

section ChartChange

variable [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {Y : Set M}

/-- Two blow-up charts of the same index over the same adapted chart have the same source:
`Φ⁻¹ ∘ Φₖ` is a continuous lift of `π` on `Φₖ.source` (`IsBlowUpChart.blowDown_symm_apply`), so
it is the identity by the uniqueness of lifts (`IsBlowUp.eqOn_of_comp_eq`). -/
theorem IsBlowUp.mem_source_of_same_index (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    {Φk : OpenPartialHomeomorph M' E} (hΦk : IsBlowUpChart ψ π φ σ i Φk)
    (hΦi : IsBlowUpChart ψ π φ σ i Φ) (hp : p ∈ Φk.source) : p ∈ Φ.source := by
  have hw : Φk p ∈ Φ.target := by rw [← hΦk.target_eq hΦi]; exact Φk.map_source hp
  have hN : IsOpen Φk.source := Φk.open_source
  have hG : ContinuousOn (fun q => Φ.symm (Φk q)) Φk.source := by
    refine Φ.continuousOn_symm.comp Φk.continuousOn ?_
    intro q hq
    rw [← hΦk.target_eq hΦi]
    exact Φk.map_source hq
  have key := IsBlowUp.eqOn_of_comp_eq hY h h hN hG continuousOn_id
    (fun q hq => hΦk.blowDown_symm_apply hΦi hq) (fun _ _ => rfl) hp
  change Φ.symm (Φk p) = p at key
  rw [← key]
  exact Φ.map_target hw

/-- A point of the blow-up chart `Φₖ` whose `σ i`-th coordinate is nonzero lies in the blow-up chart
`Φᵢ` over the same adapted chart: the chart change through the transition map `T_{ki}` is a
continuous lift of `π` on that region, hence the identity (`IsBlowUp.eqOn_of_comp_eq`). -/
theorem IsBlowUp.mem_source_of_coord_ne_zero (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    {k : Fin c} {Φk : OpenPartialHomeomorph M' E} (hΦk : IsBlowUpChart ψ π φ σ k Φk)
    (hΦi : IsBlowUpChart ψ π φ σ i Φ) (hp : p ∈ Φk.source) (hne : ψ (Φk p) (σ i) ≠ 0) :
    p ∈ Φ.source := by
  by_cases hik : k = i
  · subst hik
    exact IsBlowUp.mem_source_of_same_index hY h hΦk hΦi hp
  · -- the chart change `Φ⁻¹ ∘ ψ⁻¹ ∘ T_{ki} ∘ ψ ∘ Φk` on `{u_i ≠ 0}` lifts `π`
    have hdom : ∀ q ∈ Φk.source, ψ (Φk q) (σ i) ≠ 0 →
        ψ (Φk q) ∈ blowUpTransitionDomain σ k i :=
      fun q _ hq => (mem_blowUpTransitionDomain σ (ψ (Φk q)) hik).mpr hq
    have hmemT : ∀ q ∈ Φk.source, ψ (Φk q) (σ i) ≠ 0 →
        ψ.symm (blowUpTransition σ k i (ψ (Φk q))) ∈ Φ.target := by
      intro q hq hne'
      rw [hΦi.mem_target_iff, ψ.apply_symm_apply,
        blowUpChartMap_blowUpTransition σ _ (hdom q hq hne'),
        ← hΦk.comm q hq]
      exact ⟨_, φ.map_source (hΦk.source_subset hq), rfl⟩
    set N : Set M' := Φk.source ∩ (fun q => ψ (Φk q) (σ i)) ⁻¹' {t | t ≠ 0} with hNdef
    have hN : IsOpen N := Φk.continuousOn.isOpen_inter_preimage Φk.open_source
      (isOpen_ne.preimage ((continuous_apply _).comp ψ.continuous))
    set G : M' → M' := fun q => Φ.symm (ψ.symm (blowUpTransition σ k i (ψ (Φk q)))) with hGdef
    have hG : ContinuousOn G N := by
      refine Φ.continuousOn_symm.comp ?_ (fun q hq => hmemT q hq.1 hq.2)
      refine ψ.symm.continuous.comp_continuousOn ?_
      refine (analyticOnNhd_blowUpTransition σ (i := k) (k := i)).continuousOn.comp
        (ψ.continuous.comp_continuousOn (Φk.continuousOn.mono Set.inter_subset_left)) ?_
      intro q hq
      exact hdom q hq.1 hq.2
    have hπG : ∀ q ∈ N, π (G q) = π q := by
      intro q hq
      have hGq : G q ∈ Φ.source := Φ.map_target (hmemT q hq.1 hq.2)
      have h1 := hΦi.comm _ hGq
      rw [show Φ (G q) = ψ.symm (blowUpTransition σ k i (ψ (Φk q))) from
        Φ.right_inv (hmemT q hq.1 hq.2), ψ.apply_symm_apply,
        blowUpChartMap_blowUpTransition σ _ (hdom q hq.1 hq.2), ← hΦk.comm q hq.1] at h1
      exact φ.injOn (hΦi.source_subset hGq) (hΦk.source_subset hq.1) (ψ.injective h1)
    have key := IsBlowUp.eqOn_of_comp_eq hY h h hN hG continuousOn_id hπG (fun _ _ => rfl) ⟨hp, hne⟩
    change G p = p at key
    rw [← key]
    exact Φ.map_target (hmemT p hp hne)

end ChartChange

end Manifold
