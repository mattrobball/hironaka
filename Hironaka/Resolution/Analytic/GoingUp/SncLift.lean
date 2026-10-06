/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.ImageVal
public import Hironaka.Manifold.Snc.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Going up: lifting simple normal crossings from a submanifold

The converse of the trace lemma `hasSncWith_traceFamily`, the normal-crossings ingredient of
Kollár's Corollary 85 [Kol07, Corollary 85]: for `S ⊆ M` a closed submanifold and `F` a simple
normal crossing family having simple normal crossings with `S` properly (`E + S` is a simple normal
crossing divisor and no component contains `S`), a closed submanifold `Z' ⊆ S` having simple
normal crossings with the trace `F|_S` in `S` has, read in `M`, simple normal crossings with `F`
in the sense of [Kol07, Definition 24].

At a point `a'` of `Z'`: the proper simple-normal-crossing chart `φ` of `F` adapted to `S` (its
component coordinates off the `S`-block), the chart `χ` of `S` adapted to `Z'`, which is a
simple-normal-crossing chart of the trace, and the extended chart
`φ ≫ₕ extendComplE ψ σ₁ (χ₀⁻¹ ≫ₕ χ)` of `M` (`isAdaptedChart_extendComplE`: the `S`-equations of
`φ`, the `Z'`-coordinates of `χ`). Its component coordinates are the trace's component
coordinates read through `χ`: a component `E_j` of `F` through `a'` is, in `φ`, the hyperplane
`{z_{c_j} = 0}` with `c_j` off the `S`-block, so its equation depends only on the complementary
coordinates and `E_j` is the pull-back of its trace under the projection to `S`, which `χ`
straightens. Not in the sources in this form; the algebraic counterpart is
`hasSncWith_append_of_comap_of_isClosedImmersion`.
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {S : Set M} {s : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Lifting simple normal crossings from a submanifold, the converse of `hasSncWith_traceFamily`
(the normal-crossings step in the proof of [Kol07, Corollary 85]): for `S ⊆ M` a closed submanifold
and `F` a simple normal crossing family having simple normal crossings with `S` properly
(`HasSncWithProper`: `E + S` is a simple normal crossing divisor), a closed submanifold `Z' ⊆ S`
having simple normal crossings with the trace `F|_S` in `S` has, read in `M`, simple normal
crossings with `F` [Kol07, Definition 24]: the adapted coordinates of `Z'` on `S` extended by the
equations of `S`, the component equations kept (the chart extension `extendComplE`). The
hypotheses `_hF` (`F` is a simple normal crossing family) and `_hZ'` (`Z'` is a closed
submanifold) are present because they describe the setting of [Kol07, Corollary 85] in which the
lemma is applied, the boundary being a simple normal crossing divisor and `Z'` a centre; the proof
does not need them, because `hFS` and `hZF` already provide at every point the adapted charts of
`S` and of `Z'` which are simple-normal-crossing charts of `F` and of `F|_S`, and these are all it
extends. -/
theorem hasSncWith_of_hasSncWith_traceFamily (hS : IsClosedSubmanifold ψ S s)
    (F : HypersurfaceFamily M) (_hF : F.IsSnc ψ) (hFS : F.HasSncWithProper ψ S s)
    {Z' : Set hS.toAnalyticManifold} {c' : ℕ}
    (_hZ' : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z' c')
    (hZF : (hS.traceFamily F).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Z' c') :
    F.HasSncWith ψ (hS.imageVal Z') (c' + s) := by
  rintro _ ⟨a', ha', rfl⟩
  -- the proper simple-normal-crossing chart of `F` adapted to `S` at `a'`
  obtain ⟨φ, σ₁, cidx₁, hφ, hc₁, hproper⟩ := hFS (a' : S).1 (a' : S).2
  have haφ : (a' : S).1 ∈ φ.source := hc₁.2.1
  -- the chart of `S` adapted to `Z'`, a simple-normal-crossing chart of the trace at `a'`
  obtain ⟨χ, σ', cidx', hχ, hcχ⟩ := hZF a' ha'
  have ha'χ : a' ∈ χ.source := hcχ.2.1
  -- the extended chart of `M`, adapted to `imageVal Z'`
  obtain ⟨hmem, hadapt⟩ := hS.isAdaptedChart_extendComplE ha'χ hχ haφ hφ
  -- the induced chart of `φ` on `S`, taken opaque
  have hχ₀app : ∀ p : hS.toAnalyticManifold,
      hS.inducedChart hφ (a' : S).2 p = projCompl σ₁ (ψ (φ (p : S).1)) := fun _ => rfl
  have hχ₀src : ∀ p : hS.toAnalyticManifold,
      p ∈ (hS.inducedChart hφ (a' : S).2).source ↔ (p : S).1 ∈ φ.source := fun _ => Iff.rfl
  set χ₀ := hS.inducedChart hφ (a' : S).2 with hχ₀def
  clear_value χ₀
  refine ⟨φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ), imageValEmb σ₁ σ',
    fun j => ((complEquiv σ₁).symm (cidx' ⟨j.1, j.2⟩)).1, hadapt, hadapt.1, hmem, ?_, ?_⟩
  · -- every component through `a'` is the coordinate hyperplane of its trace's coordinate
    intro j x hx
    have hx1 : x ∈ φ.source := hx.1
    have hx2 : projCompl σ₁ (ψ (φ x)) ∈ (χ₀.symm ≫ₕ χ).source :=
      (mem_extendComplE_source ψ σ₁ _).mp hx.2
    set p : hS.toAnalyticManifold := χ₀.symm (projCompl σ₁ (ψ (φ x))) with hpdef
    have hpχ : p ∈ χ.source := hx2.2
    have hp0 : p ∈ χ₀.source := χ₀.symm.map_source hx2.1
    have hpφ : (p : S).1 ∈ φ.source := (hχ₀src p).mp hp0
    -- the coordinate of `x` in the extended chart is the trace coordinate of the point of `S`
    have hw : ψ ((φ ≫ₕ extendComplE ψ σ₁ (χ₀.symm ≫ₕ χ)) x) =
        extendComplFun σ₁ (χ₀.symm ≫ₕ χ) (ψ (φ x)) :=
      ψ.apply_symm_apply _
    rw [hw, extendComplFun_apply_compl]
    change x ∈ F.hyp j.1 ↔ χ p (cidx' ⟨j.1, j.2⟩) = 0
    -- the component equation depends only on the complementary coordinates
    have hcoordp : ψ (φ (p : S).1) (cidx₁ j) = ψ (φ x) (cidx₁ j) := by
      have h1 : χ₀ p = projCompl σ₁ (ψ (φ x)) := χ₀.right_inv hx2.1
      rw [hχ₀app] at h1
      have h2 := congrFun h1 (complEquiv σ₁ ⟨cidx₁ j, hproper j⟩)
      simpa only [projCompl, Equiv.symm_apply_apply] using h2
    rw [hc₁.mem_iff j hx1, ← hcoordp, ← hc₁.mem_iff j hpφ]
    exact hcχ.mem_iff ⟨j.1, j.2⟩ hpχ
  · -- distinct components have distinct coordinates
    intro j j' hjj'
    have h1 := (complEquiv σ₁).symm.injective (Subtype.ext hjj')
    exact Subtype.ext (congrArg Subtype.val (hcχ.injective h1))

end Hironaka.Manifold

end
