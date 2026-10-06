/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
import Hironaka.Manifold.Chart.Atlas
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# Charts transported along partial diffeomorphisms

A chart `φ` of the maximal analytic atlas of `M₁`, composed with the inverse of a partial
diffeomorphism `g : M₁ → M₂`, is a chart `transportChart g φ = g⁻¹ ≫ φ` of the maximal atlas of
`M₂` (`transportChart_mem_maximalAtlas`: an open partial homeomorphism of `E` which is `C^ω` in
both directions lies in the analytic groupoid, `mem_contDiffGroupoid_of_contMDiffOn`). When `g`
carries `Y₁ ∩ g.source` onto `Y₂ ∩ g.target` it carries the adapted charts of `Y₁` inside its source
to adapted charts of `Y₂` (`isAdaptedChart_transportChart`); hence the preimage `h⁻¹(Y)` of a
closed submanifold of codimension `c` under a local analytic isomorphism `h : N → M` is a closed
submanifold of codimension `c`, its adapted charts being those of `Y` transported along the local
inverses of `h` (`IsClosedSubmanifold.preimage_of_isLocalDiffeomorph`; the analytic form of the
centres `Z_i ×_X Y` of the pull-back of a blow-up sequence [Kol07, 30.1]).

These are the chart-level ingredients of the functoriality of the blowing-up under local
isomorphisms (`Hironaka.Manifold.BlowUp.Functor`) and of its lift along local analytic
isomorphisms (`Hironaka.Manifold.FiniteSuccession.Lift`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Charts transported along a partial diffeomorphism -/

section Transport

/-- A `C^ω` map between open subsets of `E` is analytic there. -/
theorem analyticOnNhd_of_contMDiffOn {f : E → E} {s : Set E}
    (h : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω f s) (hs : IsOpen s) : AnalyticOnNhd 𝕜 f s := fun _ hx =>
  ((contMDiffOn_iff_contDiffOn.mp h).contDiffAt (hs.mem_nhds hx)).analyticAt

/-- An open partial homeomorphism of `E` which is `C^ω` in both directions lies in the analytic
groupoid. -/
theorem mem_contDiffGroupoid_of_contMDiffOn (f : OpenPartialHomeomorph E E)
    (hf : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω f f.source)
    (hf' : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω f.symm f.target) : f ∈ contDiffGroupoid ω 𝓘(𝕜, E) :=
  mem_contDiffGroupoid_omega_of_analytic' f (analyticOnNhd_of_contMDiffOn hf f.open_source)
    (analyticOnNhd_of_contMDiffOn hf' f.open_target)

variable {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] {M₂ : Type u}
  [TopologicalSpace M₂] [ChartedSpace E M₂] (g : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω)
  {φ : OpenPartialHomeomorph M₁ E}

/-- A chart of `M₁` composed with the inverse of a partial diffeomorphism `g : M₁ → M₂`. -/
noncomputable def transportChart (φ : OpenPartialHomeomorph M₁ E) : OpenPartialHomeomorph M₂ E :=
  g.symm.toOpenPartialHomeomorph ≫ₕ φ

/-- The source of the transported chart: the points of `g.target` whose preimage lies in `φ.source`.
-/
@[simp]
theorem transportChart_source :
    (transportChart g φ).source = g.target ∩ g.invFun ⁻¹' φ.source := rfl

/-- The transported chart reads `φ` after `g⁻¹`. -/
theorem transportChart_apply (x : M₂) : transportChart g φ x = φ (g.invFun x) := rfl

/-- The target of the transported chart. -/
theorem transportChart_target : (transportChart g φ).target = φ.target ∩ φ.symm ⁻¹' g.source :=
  rfl

/-- The inverse of the transported chart is `g ∘ φ⁻¹`. -/
theorem transportChart_symm_apply (v : E) : (transportChart g φ).symm v = g (φ.symm v) := rfl

/-- When `φ.source ⊆ g.source` the transported chart keeps the target of `φ`. -/
theorem transportChart_target_eq (hsub : φ.source ⊆ g.source) :
    (transportChart g φ).target = φ.target := by
  rw [transportChart_target]
  exact Set.inter_eq_left.mpr fun v hv => hsub (φ.map_target hv)

variable [IsManifold 𝓘(𝕜, E) ω M₂]

/-- A chart `χ : M₂ → E` which is `C^ω` with `C^ω` inverse lies in the maximal atlas. -/
theorem mem_maximalAtlas_of_contMDiffOn (χ : OpenPartialHomeomorph M₂ E)
    (hχ : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω χ χ.source)
    (hχ' : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) ω χ.symm χ.target) :
    χ ∈ maximalAtlas 𝓘(𝕜, E) ω M₂ := by
  intro e he
  have he' : e ∈ maximalAtlas 𝓘(𝕜, E) ω M₂ := IsManifold.subset_maximalAtlas he
  refine ⟨mem_contDiffGroupoid_of_contMDiffOn _ ?_ ?_, mem_contDiffGroupoid_of_contMDiffOn _ ?_ ?_⟩
  · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source]
    exact (contMDiffOn_of_mem_maximalAtlas he').comp (hχ'.mono Set.inter_subset_left)
      fun _ hx => hx.2
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.symm_target]
    exact hχ.comp ((contMDiffOn_symm_of_mem_maximalAtlas he').mono Set.inter_subset_left)
      fun _ hx => hx.2
  · rw [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source]
    exact hχ.comp ((contMDiffOn_symm_of_mem_maximalAtlas he').mono Set.inter_subset_left)
      fun _ hx => hx.2
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.symm_target]
    exact (contMDiffOn_of_mem_maximalAtlas he').comp (hχ'.mono Set.inter_subset_left)
      fun _ hx => hx.2

/-- The transported chart lies in the maximal atlas. -/
theorem transportChart_mem_maximalAtlas
    (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M₁) :
    transportChart g φ ∈ maximalAtlas 𝓘(𝕜, E) ω M₂ := by
  refine mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · rw [transportChart_source]
    exact (contMDiffOn_of_mem_maximalAtlas hφ).comp
      (g.contMDiffOn_invFun.mono Set.inter_subset_left) fun _ hx => hx.2
  · rw [transportChart_target]
    exact g.contMDiffOn_toFun.comp
      ((contMDiffOn_symm_of_mem_maximalAtlas hφ).mono Set.inter_subset_left) fun _ hx => hx.2

end Transport

/-! ### Charts carrying one centre to another -/

section Centres

variable {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace E M₁] {M₂ : Type u}
  [TopologicalSpace M₂] [ChartedSpace E M₂] {Y₁ : Set M₁} {Y₂ : Set M₂} {c : ℕ}
  (g : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω) (hg : g '' (Y₁ ∩ g.source) = Y₂ ∩ g.target)

include hg in
/-- `g` carries the centre to the centre, pointwise on its source. -/
theorem mem_iff_apply_mem_of_image_eq {x : M₁} (hx : x ∈ g.source) : x ∈ Y₁ ↔ g x ∈ Y₂ := by
  constructor
  · intro hxY
    have : g x ∈ Y₂ ∩ g.target := hg ▸ ⟨x, ⟨hxY, hx⟩, rfl⟩
    exact this.1
  · intro hgx
    have : g x ∈ g '' (Y₁ ∩ g.source) := hg ▸ ⟨hgx, g.map_source hx⟩
    obtain ⟨y, ⟨hyY, hy⟩, hyx⟩ := this
    rw [← g.injOn hy hx hyx]
    exact hyY

include hg in
/-- The hypothesis on the centres for the inverse partial diffeomorphism. -/
theorem image_symm_eq_of_image_eq : g.symm '' (Y₂ ∩ g.symm.source) = Y₁ ∩ g.symm.target := by
  change g.invFun '' (Y₂ ∩ g.target) = Y₁ ∩ g.source
  ext x
  constructor
  · rintro ⟨y, ⟨hyY, hy⟩, rfl⟩
    have hy' : g.invFun y ∈ g.source := g.map_target hy
    refine ⟨?_, hy'⟩
    rw [mem_iff_apply_mem_of_image_eq g hg hy']
    have e : g (g.invFun y) = y := g.right_inv hy
    rw [e]
    exact hyY
  · rintro ⟨hxY, hx⟩
    refine ⟨g x, ⟨(mem_iff_apply_mem_of_image_eq g hg hx).mp hxY, g.map_source hx⟩, ?_⟩
    exact g.left_inv hx

variable {φ : OpenPartialHomeomorph M₁ E} {σ : Fin c ↪ Fin n}

include hg in
/-- An adapted chart of `Y₁` inside the source of `g` transports to an adapted chart of `Y₂`. -/
theorem isAdaptedChart_transportChart [IsManifold 𝓘(𝕜, E) ω M₂]
    (hφ : IsAdaptedChart ψ Y₁ φ σ) : IsAdaptedChart ψ Y₂ (transportChart g φ) σ := by
  refine ⟨transportChart_mem_maximalAtlas g hφ.1, fun x hx => ?_⟩
  rw [transportChart_source] at hx
  have hx' : g.invFun x ∈ g.source := g.map_target hx.1
  rw [transportChart_apply, ← hφ.2 _ hx.2, mem_iff_apply_mem_of_image_eq g hg hx']
  have e : g (g.invFun x) = x := g.right_inv hx.1
  rw [e]

end Centres

section Preimage

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  {N : Type u} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(𝕜, E) ω N]
  {h : N → M} {Y : Set M} {c : ℕ}

/-! ### The preimage of a closed submanifold under a local analytic isomorphism -/

omit [IsManifold 𝓘(𝕜, E) ω M] [IsManifold 𝓘(𝕜, E) ω N] in
/-- A partial diffeomorphism `Φ : N → M` agreeing with `h` on its source carries `h⁻¹(Y)` to `Y`
(the hypothesis under which a partial diffeomorphism lifts to the blowings-up). -/
theorem image_preimage_eq_of_eqOn (Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω)
    (hΦ : EqOn h Φ Φ.source) : Φ '' (h ⁻¹' Y ∩ Φ.source) = Y ∩ Φ.target := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxY, hxs⟩, rfl⟩
    refine ⟨?_, Φ.map_source hxs⟩
    have hx : h x ∈ Y := hxY
    rwa [hΦ hxs] at hx
  · rintro ⟨hyY, hyt⟩
    refine ⟨Φ.invFun y, ⟨?_, Φ.map_target hyt⟩, Φ.right_inv hyt⟩
    change h (Φ.invFun y) ∈ Y
    have hm : Φ.invFun y ∈ Φ.source := Φ.map_target hyt
    have e : Φ (Φ.invFun y) = y := Φ.right_inv hyt
    rw [hΦ hm, e]
    exact hyY

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- **The preimage of a closed submanifold of codimension `c` under a local analytic isomorphism
is a closed submanifold of codimension `c`**: its adapted charts are the adapted charts of `Y`
transported along the local inverses of `h` (`transportChart`, `isAdaptedChart_transportChart`).
This is the analytic form of the centres `Z_i ×_X Y` of the pull-back
[Kol07, 30.1]. -/
theorem IsClosedSubmanifold.preimage_of_isLocalDiffeomorph (hY : IsClosedSubmanifold ψ Y c)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) : IsClosedSubmanifold ψ (h ⁻¹' Y) c where
  isClosed := hY.isClosed.preimage hh.contMDiff.continuous
  exists_adaptedChart := by
    intro a ha
    obtain ⟨Φ, haΦ, hΦ⟩ := (hh a).exists_partialDiffeomorph
    obtain ⟨φ, σ, hφa, hφ⟩ := hY.exists_adaptedChart (h a) ha
    have hg : Φ.symm '' (Y ∩ Φ.symm.source) = h ⁻¹' Y ∩ Φ.symm.target :=
      image_symm_eq_of_image_eq Φ (image_preimage_eq_of_eqOn Φ hΦ)
    refine ⟨transportChart Φ.symm φ, σ, ?_, isAdaptedChart_transportChart Φ.symm hg hφ⟩
    rw [transportChart_source]
    refine ⟨haΦ, ?_⟩
    change Φ a ∈ φ.source
    rw [← hΦ haΦ]
    exact hφa

end Preimage

end Manifold

end
