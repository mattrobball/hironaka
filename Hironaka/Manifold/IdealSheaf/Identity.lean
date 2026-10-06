/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Defs
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.Germ.ChartTransport
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Ideal sheaves with a zero stalk on a connected manifold

On an analytic manifold, the set of points at which an ideal sheaf `J` has zero stalk is clopen:
open because the local generators vanish near a point with zero stalk
(`isOpen_setOf_stalkIdeal_eq_bot`), closed by the identity theorem applied in a chart ball to a
section with nonzero germ (`isClosed_setOf_stalkIdeal_eq_bot`). So on a connected manifold one
zero stalk forces `J = 0` (`eq_bot_of_isPreconnected`), and "nonzero everywhere" is "nonzero
somewhere" (`isNonzeroEverywhere_iff_exists`): Hironaka's "coherent sheaf of non-zero ideals"
[Hir64, Main Theorem II''(N), p. 158] and Kollár's "ideal sheaf that is nonzero on every
irreducible component" [Kol07, Definition 31] agree on a connected manifold. The clopen
description is used to run the resolution componentwise
(`Hironaka/Resolution/Analytic/OrderReduction/FirstStep.lean`).
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Manifold

namespace IdealSheaf

section General

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  (J : IdealSheaf (structureSheaf 𝕜 E M))

omit J in
/-- A germ of a section vanishes iff the section vanishes near the point. -/
theorem germ_eq_zero_iff {U : Opens M} {a : M} (ha : a ∈ U)
    (f : (structureSheaf 𝕜 E M).presheaf.obj (op U)) :
    (structureSheaf 𝕜 E M).presheaf.germ U a ha f = 0 ↔ extendSection 𝕜 E f =ᶠ[𝓝 a] 0 := by
  rw [← (stalkToGerm_injective 𝓘(𝕜, E) ω M a).eq_iff, map_zero, stalkToGerm_structureSheaf_germ]
  exact Germ.coe_eq

/-- The set of points with zero stalk is open (the generators vanish near a point with zero
stalk). -/
theorem isOpen_setOf_stalkIdeal_eq_bot : IsOpen {a : M | J.stalkIdeal a = ⊥} := by
  rw [isOpen_iff_forall_mem_open]
  intro a ha
  obtain ⟨U, haU, k, f, -, hgen⟩ := J.exists_generators a
  have h0 : ∀ i, extendSection 𝕜 E (f i) =ᶠ[𝓝 a] 0 := fun i =>
    (germ_eq_zero_iff haU (f i)).mp (by
      rw [← Ideal.mem_bot, ← (show J.stalkIdeal a = ⊥ from ha), hgen a haU]
      exact Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨V, hV, hVo, haV⟩ :=
    eventually_nhds_iff.mp ((eventually_all.mpr h0).and (U.2.mem_nhds haU))
  refine ⟨V, fun b hb => ?_, hVo, haV⟩
  have hbU : b ∈ U := (hV b hb).2
  rw [Set.mem_ofPred_eq, hgen b hbU, eq_bot_iff, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_bot, germ_eq_zero_iff hbU]
  filter_upwards [hVo.mem_nhds hb] with x hx
  exact (hV x hx).1 i

end General

section Analytic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  (J : IdealSheaf (structureSheaf 𝕜 E M))

/-- The identity theorem: the set of points with zero stalk is closed — a section with a nonzero
germ at `b` has nonzero germs on a chart ball around `b`. -/
theorem isClosed_setOf_stalkIdeal_eq_bot : IsClosed {a : M | J.stalkIdeal a = ⊥} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro b hb
  obtain ⟨s, hs, hs0⟩ : ∃ s ∈ J.stalkIdeal b, s ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hb (eq_bot_iff.mpr fun s hs => Ideal.mem_bot.mpr (h s hs))
  obtain ⟨V, hbV, g, hg, rfl⟩ := J.mem_stalkIdeal_iff.mp hs
  set φ : OpenPartialHomeomorph M E := chartAt E b with hφdef
  have hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M := IsManifold.chart_mem_maximalAtlas b
  have hbφ : b ∈ φ.source := mem_chart_source E b
  set h : E → 𝕜 := extendSection 𝕜 E g ∘ φ.symm with hhdef
  let W : Opens M := V ⊓ ⟨φ.source, φ.open_source⟩
  have hbW : b ∈ W := Opens.mem_inf.mpr ⟨hbV, hbφ⟩
  have hWφ : (W : Set M) ⊆ φ.source := fun x hx => (Opens.mem_inf.mp hx).2
  have hSo : IsOpen (φ '' W) := (φ.isOpen_image_iff_of_subset_source hWφ).mpr W.2
  -- `h` is analytic on `φ '' W`
  have hSan : AnalyticOnNhd 𝕜 h (φ '' W) := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hcV, hcφ⟩ := Opens.mem_inf.mp hc
    have h1 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω (extendSection 𝕜 E g) c :=
      (contMDiffOn_extendSection g).contMDiffAt (V.2.mem_nhds hcV)
    have h2 : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜) ω h (φ c) :=
      ContMDiffAt.comp_of_eq h1 (contMDiffAt_chart_symm E φ hcφ hφ) (φ.left_inv hcφ)
    exact (contMDiffAt_iff_contDiffAt.mp h2).analyticAt
  -- a preconnected ball around `φ b` inside `φ '' W`
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hSo (φ b) ⟨b, hbW, rfl⟩
  have hpre : IsPreconnected (Metric.ball (φ b) r) := by
    let _i : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    exact Metric.isPreconnected_ball
  refine ⟨(W : Set M) ∩ (φ.source ∩ φ ⁻¹' Metric.ball (φ b) r), fun c hc => ?_,
    W.2.inter (φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball),
    ⟨hbW, hbφ, Metric.mem_ball_self hr⟩⟩
  obtain ⟨hcW, -, hcb⟩ := hc
  obtain ⟨hcV, hcφ⟩ := Opens.mem_inf.mp hcW
  -- if the stalk at `c` were zero, `h` would vanish near `φ c`, hence on the ball, hence near `φ b`
  intro hc0
  apply hs0
  have hgc : (structureSheaf 𝕜 E M).presheaf.germ V c hcV g = 0 := by
    rw [← Ideal.mem_bot, ← hc0]
    exact J.germ_mem_stalkIdeal hcV hg
  have h0c : h =ᶠ[𝓝 (φ c)] 0 := (φ.tendsto_symm hcφ).eventually ((germ_eq_zero_iff hcV g).mp hgc)
  have hzero : Set.EqOn h 0 (Metric.ball (φ b) r) :=
    (hSan.mono hball).eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hcb h0c
  rw [germ_eq_zero_iff hbV g]
  filter_upwards [φ.open_source.mem_nhds hbφ,
    (φ.continuousAt hbφ).preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))]
    with x hxφ hxb
  have : extendSection 𝕜 E g x = h (φ x) := by
    simp only [hhdef, Function.comp_apply, φ.left_inv hxφ]
  rw [this, hzero hxb]
  rfl

/-- The set of points with zero stalk is clopen. -/
theorem isClopen_setOf_stalkIdeal_eq_bot : IsClopen {a : M | J.stalkIdeal a = ⊥} :=
  ⟨J.isClosed_setOf_stalkIdeal_eq_bot, J.isOpen_setOf_stalkIdeal_eq_bot⟩

/-- On a connected manifold, one zero stalk forces `J = 0` ([Hir64, Main Theorem II''(N), p. 158];
[Kol07, Definition 31]). -/
theorem eq_bot_of_isPreconnected [PreconnectedSpace M] {a : M} (h : J.stalkIdeal a = ⊥) :
    J = ⊥ := by
  have huniv : {x : M | J.stalkIdeal x = ⊥} = Set.univ :=
    J.isClopen_setOf_stalkIdeal_eq_bot.eq_univ ⟨a, h⟩
  refine IdealSheaf.ext fun x => ?_
  rw [stalkIdeal_bot]
  exact Set.eq_univ_iff_forall.mp huniv x

/-- On a connected manifold, "nonzero everywhere" is "nonzero somewhere": Hironaka's "sheaf of
non-zero ideals" and Kollár's "nonzero on every irreducible component" agree. -/
theorem isNonzeroEverywhere_iff_exists [ConnectedSpace M] :
    J.IsNonzeroEverywhere ↔ ∃ a, J.stalkIdeal a ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨a⟩ := (inferInstance : Nonempty M)
    exact ⟨a, h a⟩
  · rintro ⟨a, ha⟩ x hx
    exact ha (by rw [J.eq_bot_of_isPreconnected hx, stalkIdeal_bot])

end Analytic

end IdealSheaf

end Manifold
