/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.AnalyticManifold.Defs
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# A local analytic isomorphism injective on an open set

In the proof of [Kol07, Proposition 37], `X'' := ∐_{i≤j} Uᵢ ∩ Uⱼ` comes with the surjective open
immersions `τ₁, τ₂ : X'' → X'`: the pieces of a coproduct of open embeddings `g : N → M` are the
clopen sets on which `g` is injective, and there `g` is an analytic isomorphism onto its (open)
image, the inverse being, near each point, the inverse of a local inverse of `g`. The analytic
isomorphism `restrictInjOn` (source the open set, target its image) transports charts: a chart of
`M` whose source contains the image gives a chart of `N` with source exactly the open set
(`exists_chart_eq_of_injOn`, through `transportChart`). These are the charts of the fibre product
in the hypothesis `LocalCoversFibreClosed` of the globalization theorem.
-/

@[expose] public section

noncomputable section

open Set Topology Function
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N : AnalyticManifold.{u} 𝕜 E}

section RestrictInj

variable {h : AnalyticMap N M} (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {W : Set N}
  (hW : IsOpen W) (hi : InjOn h W)
include hh hW hi

/-- Near a point of `h '' W`, `Function.invFunOn h W` is the inverse of a local inverse of `h`. -/
theorem _root_.IsLocalDiffeomorph.contMDiffAt_invFunOn [Nonempty N] {y : M} (hy : y ∈ h '' W) :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (invFunOn h W) y := by
  obtain ⟨x, hxW, rfl⟩ := hy
  obtain ⟨Φ, hxΦ, hΦ⟩ := (hh x).exists_partialDiffeomorph
  have hyΦ : h x ∈ Φ.target := by
    rw [hΦ hxΦ]
    exact Φ.map_source hxΦ
  have hO : IsOpen (Φ.target ∩ Φ.symm ⁻¹' W) :=
    Φ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hW
  have hyO : h x ∈ Φ.target ∩ Φ.symm ⁻¹' W := by
    refine ⟨hyΦ, ?_⟩
    change Φ.symm (h x) ∈ W
    rw [hΦ hxΦ]
    change Φ.toPartialEquiv.symm (Φ.toPartialEquiv x) ∈ W
    rw [Φ.toPartialEquiv.left_inv hxΦ]
    exact hxW
  have hsymm : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω Φ.symm (h x) :=
    Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hyΦ)
  refine hsymm.congr_of_eventuallyEq ?_
  filter_upwards [hO.mem_nhds hyO] with y' hy'
  have hmem : Φ.symm y' ∈ Φ.source := Φ.map_target hy'.1
  have hh' : h (Φ.symm y') = y' := by
    rw [hΦ hmem]
    exact Φ.right_inv hy'.1
  have hW' : Φ.symm y' ∈ W := hy'.2
  exact hi (invFunOn_mem ⟨Φ.symm y', hW', hh'⟩) hW'
    ((invFunOn_eq ⟨Φ.symm y', hW', hh'⟩).trans hh'.symm)

/-- A local analytic isomorphism injective on an open set `W` as an analytic isomorphism from `W`
onto its image (the pieces `Uᵢ` of `X' = ∐ Uᵢ → X` in [Kol07, Proposition 37]). -/
def _root_.IsLocalDiffeomorph.restrictInjOn [Nonempty N] :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω where
  toFun := h
  invFun := invFunOn h W
  source := W
  target := h '' W
  map_source' _ hx := mem_image_of_mem h hx
  map_target' _ hy := invFunOn_mem hy
  left_inv' _ hx := hi.leftInvOn_invFunOn hx
  right_inv' _ hy := invFunOn_eq hy
  open_source := hW
  open_target := hh.isOpenMap W hW
  contMDiffOn_toFun := h.contMDiff.contMDiffOn
  contMDiffOn_invFun _ hy := (hh.contMDiffAt_invFunOn hW hi hy).contMDiffWithinAt

theorem _root_.IsLocalDiffeomorph.restrictInjOn_source [Nonempty N] :
    (hh.restrictInjOn hW hi).source = W := rfl

theorem _root_.IsLocalDiffeomorph.restrictInjOn_target [Nonempty N] :
    (hh.restrictInjOn hW hi).target = h '' W := rfl

theorem _root_.IsLocalDiffeomorph.restrictInjOn_apply [Nonempty N] (x : N) :
    hh.restrictInjOn hW hi x = h x := rfl

theorem _root_.IsLocalDiffeomorph.restrictInjOn_symm_apply [Nonempty N] (y : M) :
    (hh.restrictInjOn hW hi).symm y = invFunOn h W y := rfl

/-- A chart of `M` whose source contains `h '' W` transports along the inverse of `h|_W` to a chart
of `N` with source exactly `W` (`transportChart`). -/
theorem _root_.IsLocalDiffeomorph.exists_chart_eq_of_injOn [Nonempty N]
    {φ : OpenPartialHomeomorph M E} (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)
    (hsub : W ⊆ h ⁻¹' φ.source) :
    ∃ χ : OpenPartialHomeomorph N E, χ ∈ maximalAtlas 𝓘(𝕜, E) ω N ∧ χ.source = W := by
  refine ⟨transportChart (hh.restrictInjOn hW hi).symm φ, transportChart_mem_maximalAtlas _ hφ, ?_⟩
  rw [transportChart_source]
  exact inter_eq_left.mpr hsub

end RestrictInj

end Manifold

end
