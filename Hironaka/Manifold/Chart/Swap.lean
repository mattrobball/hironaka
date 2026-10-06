/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Chart.Atlas
public import Hironaka.Manifold.Chart.Basic
public import Hironaka.Manifold.Germ.TaylorHom
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Germ.TaylorCompletion
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The coordinate swap between two charts at a point

For two charts `e, e'` of the maximal atlas centred at `p`, the coordinate swap `φ_p = e'⁻¹ ∘ e`
is the chart change of `Hironaka/Manifold/Chart/Atlas.lean` (`PartialDiffeomorph.chartChange`),
an analytic isomorphism from `U(p) = e.source ∩ e⁻¹(e'.target)` onto
`V(p) = e'.source ∩ e'⁻¹(e.target)` — two neighbourhoods of `p`, in general distinct — with
`e' ∘ φ_p = e` (`IsCoordinateSwap`). It fixes `p`, pulls the coordinate functions of `e'` back to
those of `e` (Kollár's `φ^*(x'_1, x_2, …, x_n) = (x_1, x_2, …, x_n)` [Kol07, 95]), induces the
pullback of germs `φ_p^* : 𝒪_{M,p} →+* 𝒪_{M,p}` — the stalk map `germMapOn` of an analytic map
fixing `p` — and satisfies the Taylor identity `T_e ∘ φ_p^* = T_{e'}`: the `e`-expansion of
`g ∘ φ_p` is the `e'`-expansion of `g`, because `(g ∘ φ_p) ∘ e⁻¹ = g ∘ e'⁻¹` near `0 = e p = e' p`,
so `T_e ∘ φ_p^*` satisfies the specification `IsTaylorHom` of the Taylor homomorphism of the chart
`e'` and equals it by uniqueness (`IsTaylorHom.eq`). Kollár's formal automorphism `φ^*` of
`𝒪̂_{M,p} ≅ 𝕜[[x]]` [Kol07, 95] is `T_{e'} ∘ T_e⁻¹`, the composite of the two completion
isomorphisms `taylorCompletionEquiv`; with the Taylor identity this reads `T_e ∘ φ_p^* = φ^* ∘ T_e`.
Włodarczyk's coordinate change `φ_{uv}` between two tangent directions is the same construction
[Wlo09, Lemma 5.5.3, proof, step (0)]. It is used to compare hypersurfaces of maximal contact
given by different charts (`Hironaka/Resolution/Analytic/MaximalContact/SwapRealizes.lean`).
-/

public section

noncomputable section

open TopologicalSpace Opposite Filter Topology Set IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The chart change of two charts centred at `p` is their coordinate swap in the sense of the
specification `IsCoordinateSwap`. -/
theorem isCoordinateSwap_chartChange {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) {p : M}
    (hp : p ∈ e.source) (hp' : p ∈ e'.source) (h0 : e p = 0) (h0' : e' p = 0) :
    IsCoordinateSwap E M e e' p (PartialDiffeomorph.chartChange he he') := by
  have hsrc : (PartialDiffeomorph.chartChange he he').source = e.source ∩ e ⁻¹' e'.target := by
    change (e.trans e'.symm).source = _
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  have htgt : (PartialDiffeomorph.chartChange he he').target =
      e'.source ∩ e' ⁻¹' e.target := by
    change (e.trans e'.symm).target = _
    rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.symm_symm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    refine ⟨hp, ?_⟩
    change e p ∈ e'.target
    rw [h0, ← h0']
    exact e'.map_source hp'
  · rw [hsrc]
    exact inter_subset_left
  · rw [htgt]
    exact inter_subset_left
  · intro x hx
    rw [hsrc] at hx
    change e' (e'.symm (e x)) = e x
    exact e'.right_inv hx.2

/-- For two charts of the maximal atlas centred at `p`, the coordinate swap `φ_p = e'⁻¹ ∘ e` exists
as an analytic isomorphism between two neighbourhoods of `p`. -/
theorem exists_isCoordinateSwap' {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) {p : M}
    (hp : p ∈ e.source) (hp' : p ∈ e'.source) (h0 : e p = 0) (h0' : e' p = 0) :
    ∃ Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω, IsCoordinateSwap E M e e' p Φ :=
  ⟨_, isCoordinateSwap_chartChange E M he he' hp hp' h0 h0'⟩

variable {E M}
variable {e e' : OpenPartialHomeomorph M E} {p : M} {Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M M ω}

/-- The coordinate swap maps its source into the source of `e'`. -/
theorem IsCoordinateSwap.apply_mem_source (h : IsCoordinateSwap E M e e' p Φ) {x : M}
    (hx : x ∈ Φ.source) : Φ x ∈ e'.source :=
  h.2.2.1 (Φ.toPartialEquiv.map_source hx)

/-- The coordinate swap of two charts centred at `p` fixes `p`. -/
theorem IsCoordinateSwap.apply_self' (h : IsCoordinateSwap E M e e' p Φ) (hp' : p ∈ e'.source)
    (h0 : e p = 0) (h0' : e' p = 0) : Φ p = p :=
  e'.injOn (h.apply_mem_source h.1) hp' (by rw [h.2.2.2 p h.1, h0, h0'])

/-- `V(p) = Φ.target` is a neighbourhood of `p`. -/
theorem IsCoordinateSwap.mem_target' (h : IsCoordinateSwap E M e e' p Φ) (hp' : p ∈ e'.source)
    (h0 : e p = 0) (h0' : e' p = 0) : p ∈ Φ.target := by
  have := Φ.toPartialEquiv.map_source h.1
  rwa [h.apply_self' hp' h0 h0'] at this

/-- The coordinate functions of `e'` pull back along the swap to those of `e` (Kollár's
`φ^*(x'_1, x_2, …, x_n) = (x_1, x_2, …, x_n)`, [Kol07, 95]). -/
theorem IsCoordinateSwap.comp_eq' (h : IsCoordinateSwap E M e e' p Φ) {z z' : Fin n → M → 𝕜}
    (hz : ∀ x ∈ e.source, ∀ j, z j x = ψ (e x) j) (hz' : ∀ x ∈ e'.source, ∀ j, z' j x = ψ (e' x) j)
    {x : M} (hx : x ∈ Φ.source) (j : Fin n) : z' j (Φ x) = z j x := by
  rw [hz' _ (h.apply_mem_source hx), h.2.2.2 x hx, hz x (h.2.1 hx)]

/-- The pullback of germs along the coordinate swap: the stalk map of an analytic map
(`germMapOn`) for `φ_p`, which fixes `p`. -/
theorem IsCoordinateSwap.exists_isPullbackStalk' (h : IsCoordinateSwap E M e e' p Φ)
    (hp' : p ∈ e'.source) (h0 : e p = 0) (h0' : e' p = 0) :
    ∃ r : (structureSheaf 𝕜 E M).presheaf.stalk p →+* (structureSheaf 𝕜 E M).presheaf.stalk p,
      IsPullbackStalk E M (⇑Φ) r := by
  have hc : (⇑Φ) p = p := h.apply_self' hp' h0 h0'
  have hΦ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω (⇑Φ)
      ((⟨Φ.source, Φ.open_source⟩ : Opens M) : Set M) := Φ.contMDiffOn_toFun
  refine ⟨germMapOn (⇑Φ) hΦ h.1 hc, tendsto_of_contMDiffOn_of_eq (⇑Φ) hΦ h.1 hc, fun s => ?_⟩
  rw [stalkToGerm_germMapOn]
  rfl

/-- The pullback of germs is determined by its specification (`stalkToGerm` is injective). -/
theorem IsPullbackStalk.unique' {Φ : M → M}
    {r r' : (structureSheaf 𝕜 E M).presheaf.stalk p →+* (structureSheaf 𝕜 E M).presheaf.stalk p}
    (hr : IsPullbackStalk E M Φ r) (hr' : IsPullbackStalk E M Φ r') : r = r' := by
  obtain ⟨_, hr⟩ := hr
  obtain ⟨_, hr'⟩ := hr'
  refine RingHom.ext fun s => stalkToGerm_injective 𝓘(𝕜, E) ω M p ?_
  rw [hr s, hr' s]

/-- `T_e ∘ φ_p^* = T_{e'}`, the primitive form of Kollár's `T_p ∘ φ_p^* = φ^* ∘ T_p` [Kol07, 95]:
the `e`-expansion of `g ∘ φ_p` is the `e'`-expansion of `g`, both at `0 = e p = e' p`. -/
theorem IsPullbackStalk.taylorHom_eq' (hΦ : IsCoordinateSwap E M e e' p Φ)
    (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M) (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (hp : p ∈ e.source) (hp' : p ∈ e'.source) (h0 : e p = 0) (h0' : e' p = 0)
    {r : (structureSheaf 𝕜 E M).presheaf.stalk p →+* (structureSheaf 𝕜 E M).presheaf.stalk p}
    (hr : IsPullbackStalk E M (⇑Φ) r) (s : (structureSheaf 𝕜 E M).presheaf.stalk p) :
    taylorHom E ψ e hp he (r s) = taylorHom E ψ e' hp' he' s := by
  obtain ⟨_, hr⟩ := hr
  have hpt : ψ (e' p) = ψ (e p) := by rw [h0, h0']
  -- `Φ ∘ e.symm = e'.symm` near `e p`
  have h3 : ∀ᶠ y in 𝓝 (e p), Φ (e.symm y) = e'.symm y := by
    have hev : ∀ᶠ y in 𝓝 (e p), e.symm y ∈ Φ.source := by
      have := (e.continuousAt_symm (e.map_source hp)).tendsto
      rw [e.left_inv hp] at this
      exact this.eventually_mem (Φ.open_source.mem_nhds hΦ.1)
    filter_upwards [hev, e.open_target.mem_nhds (e.map_source hp)] with y hy hyt
    have h1 : e' (Φ (e.symm y)) = y := by rw [hΦ.2.2.2 _ hy, e.right_inv hyt]
    calc Φ (e.symm y) = e'.symm (e' (Φ (e.symm y))) := (e'.left_inv (hΦ.apply_mem_source hy)).symm
      _ = e'.symm y := by rw [h1]
  have hT : Tendsto (fun y => e.symm (ψ.symm y)) (𝓝 (ψ (e p))) (𝓝 p) := by
    have h1' : Tendsto ψ.symm (𝓝 (ψ (e p))) (𝓝 (e p)) := by
      have := ψ.symm.continuous.continuousAt.tendsto (x := ψ (e p))
      rwa [ψ.symm_apply_apply] at this
    have h2' : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
      have := (e.continuousAt_symm (e.map_source hp)).tendsto
      rwa [e.left_inv hp] at this
    exact h2'.comp h1'
  have h1ψ : Tendsto ψ.symm (𝓝 (ψ (e p))) (𝓝 (e p)) := by
    have := ψ.symm.continuous.continuousAt.tendsto (x := ψ (e p))
    rwa [ψ.symm_apply_apply] at this
  -- `T_e ∘ r` satisfies the specification of the Taylor homomorphism of the chart `e'`
  have hT' : IsTaylorHom E ψ e' p ((taylorHom E ψ e hp he).comp r) := by
    refine ⟨fun s => (isTaylorHom_taylorHom E ψ e hp he).1 _, fun U hU f => ?_⟩
    obtain ⟨U', hU', f', hf'⟩ :=
      (structureSheaf 𝕜 E M).presheaf.exists_germ_eq
        (r ((structureSheaf 𝕜 E M).presheaf.germ U p hU f))
    have h1 := (isTaylorHom_taylorHom E ψ e hp he).2 U' hU' f'
    have h2 : extendSection 𝕜 E f' =ᶠ[𝓝 p] extendSection 𝕜 E f ∘ Φ := by
      have := hr ((structureSheaf 𝕜 E M).presheaf.germ U p hU f)
      rw [← hf', stalkToGerm_structureSheaf_germ, stalkToGerm_structureSheaf_germ,
        germCompRingHom_coe] at this
      exact Germ.coe_eq.mp this
    rw [RingHom.comp_apply, ← hf', hpt]
    filter_upwards [h1, hT.eventually h2, h1ψ.eventually h3] with y hy1 hy2 hy3
    simp only [Function.comp] at hy1 hy2 hy3 ⊢
    rw [← hy1, hy2, hy3]
  have := IsTaylorHom.eq E ψ e' hT' (isTaylorHom_taylorHom E ψ e' hp' he')
  exact congrArg (fun T => T s) this

/-- Kollár's formal automorphism `φ` of `𝒪̂_p ≅ 𝕜[[x]]` [Kol07, 95]: the composite `T_{e'} ∘ T_e⁻¹`
of the two completion isomorphisms carries the `e`-expansion of every germ to its
`e'`-expansion. -/
theorem exists_taylor_automorphism' (he : e ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (he' : e' ∈ maximalAtlas 𝓘(𝕜, E) ω M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    ∃ Φ : MvPowerSeries (Fin n) 𝕜 ≃+* MvPowerSeries (Fin n) 𝕜,
      ∀ s : (structureSheaf 𝕜 E M).presheaf.stalk p,
        Φ (taylorHom E ψ e hp he s) = taylorHom E ψ e' hp' he' s := by
  refine ⟨(taylorCompletionEquiv E ψ e hp he).symm.trans (taylorCompletionEquiv E ψ e' hp' he'),
    fun s => ?_⟩
  rw [RingEquiv.trans_apply, ← taylorCompletionEquiv_algebraMap E ψ e hp he s,
    RingEquiv.symm_apply_apply, taylorCompletionEquiv_algebraMap]

end Manifold

end
