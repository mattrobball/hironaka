/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Manifold.Submanifold
import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.Submanifold.Manifold
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The restriction of an snc divisor to a transverse hypersurface

Kollár: "if `E` does not contain `Z`, then `E|_Z` is again a simple normal crossing divisor on `Z`"
[Kol07, Definition 24], here for a smooth hypersurface `H` having simple normal crossings with `F`
and containing no component of `F` near any point (near every point of `H ∩ E^j` there are points
of `H` off `E^j`). At `a ∈ H`, a chart `φ` adapted to `H` (`H = {z_{σ 0} = 0}`) which is an snc
chart of `F` (`E^j = {z_{c j} = 0}`) has `c j ≠ σ 0` for every component through `a` — otherwise
`E^j` would contain `H` on the chart — so the coordinates of the components through `a` are among
the `n − 1` coordinates that the induced chart `φ|_H` of the manifold `H` keeps (`projCompl`):
`E^j ∩ H = {w_{c' j} = 0}` on `φ|_H`, with `c'` injective. The components of `F|_H` are the traces
`E^j ∩ H`, closed hypersurfaces of `H` by the same charts, and the family stays locally finite (the
preimage of a locally finite family under the continuous inclusion). This is the restriction of the
boundary to a hypersurface of maximal contact
(`Hironaka/Resolution/Analytic/OrderReduction/Modified/StopRestrict.lean`).
-/

public section

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {F : HypersurfaceFamily M} {H : Set M}

namespace HypersurfaceFamily

/-- In a chart adapted to `H` which is an snc chart of `F` at `a ∈ H`, a component through `a` near
which `H` is not contained in the component has its coordinate off the block of `H`. -/
theorem IsSncChartAt.notMem_range_of_frequently {φ : OpenPartialHomeomorph M E} {c : ℕ}
    {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ H φ σ) {a : M}
    {cidx : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ a cidx) (j : {j // a ∈ F.hyp j})
    (hne : ∃ᶠ x in 𝓝[H] a, x ∉ F.hyp j.1) : cidx j ∉ Set.range σ := by
  rintro ⟨i, hi⟩
  have hev : ∀ᶠ x in 𝓝[H] a, x ∈ φ.source ∧ x ∈ H :=
    (eventually_nhdsWithin_of_eventually_nhds (φ.open_source.mem_nhds hc.2.1)).and
      self_mem_nhdsWithin
  obtain ⟨x, hxj, hxφ, hxH⟩ := (hne.and_eventually hev).exists
  refine hxj ((hc.mem_iff j hxφ).mpr ?_)
  rw [← hi]
  exact (hφ.2 x hxφ).mp hxH i

variable (hH : IsClosedSubmanifold ψ H 1)

/-- For `a ∈ H`, a chart adapted to `H` which is an snc chart of `F` at `a`, and no component
through `a` containing `H` near `a`, the induced chart of `H` (`IsAdaptedChart.chartOn`) is an snc
chart of the restriction `F|_H` at `a`, with the indices of the components read in the complement
of the block of `H`. -/
theorem IsSncChartAt.restrict_isSncChartAt {φ : OpenPartialHomeomorph M E} {σ : Fin 1 ↪ Fin n}
    (hφ : IsAdaptedChart ψ H φ σ) {a : M} (ha : a ∈ H) {cidx : {j // a ∈ F.hyp j} → Fin n}
    (hc : F.IsSncChartAt ψ φ a cidx) (hne : ∀ j, a ∈ F.hyp j → ∃ᶠ x in 𝓝[H] a, x ∉ F.hyp j) :
    letI := hH.chartedSpace
    (F.restrict H).IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) (hφ.chartOn ha)
      ⟨a, ha⟩ fun j => complEquiv σ
        ⟨cidx ⟨j.1, j.2⟩, hc.notMem_range_of_frequently hφ ⟨j.1, j.2⟩ (hne j.1 j.2)⟩ := by
  let _i := hH.chartedSpace
  refine ⟨hφ.chartOn_mem_maximalAtlas' hH ha, hc.2.1, fun j x hx => ?_, fun i j hij => ?_⟩
  · have hxφ : (x : M) ∈ φ.source := hx
    change (x : M) ∈ F.hyp j.1 ↔ projCompl σ (ψ (φ x)) (complEquiv σ ⟨cidx ⟨j.1, j.2⟩, _⟩) = 0
    rw [hc.mem_iff ⟨j.1, j.2⟩ hxφ]
    simp only [projCompl, Equiv.symm_apply_apply]
  · have h1 : (⟨cidx ⟨i.1, i.2⟩, _⟩ : {k : Fin n // k ∉ Set.range σ}) = ⟨cidx ⟨j.1, j.2⟩, _⟩ :=
      (complEquiv σ).injective hij
    have h2 : (⟨i.1, i.2⟩ : {j // a ∈ F.hyp j}) = ⟨j.1, j.2⟩ :=
      hc.injective (congrArg Subtype.val h1)
    exact Subtype.ext (congrArg Subtype.val h2)

/-- Kollár's "if `E` does not contain `Z`, then `E|_Z` is again a simple normal crossing divisor on
`Z`" [Kol07, Definition 24]: if the snc divisor `F` has simple normal crossings with the smooth
hypersurface `H` and no component of `F` contains `H` near any point, then `F|_H` is a simple
normal crossings divisor on the manifold `H`. -/
theorem isSnc_restrict (hF : F.IsSnc ψ) (hH : IsClosedSubmanifold ψ H 1)
    (hsnc : F.HasSncWith ψ H 1)
    (hne : ∀ a ∈ H, ∀ j, a ∈ F.hyp j → ∃ᶠ x in 𝓝[H] a, x ∉ F.hyp j) :
    letI := hH.chartedSpace
    (F.restrict H).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) := by
  let _i := hH.chartedSpace
  refine ⟨fun j => ⟨(hF.1 j).isClosed.preimage continuous_subtype_val, fun x hx => ?_⟩, ?_, ?_⟩
  · obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc x.1 x.2
    have hsc := hc.restrict_isSncChartAt hH hφ x.2 (hne x.1 x.2)
    refine ⟨hφ.chartOn x.2, singleEmb (complEquiv σ ⟨cidx ⟨j, hx⟩,
      hc.notMem_range_of_frequently hφ ⟨j, hx⟩ (hne x.1 x.2 j hx)⟩), hc.2.1, ?_⟩
    exact isAdaptedChart_singleIdx hsc.1 fun y hy => hsc.mem_iff ⟨j, hx⟩ hy
  · exact hF.2.1.preimage_continuous continuous_subtype_val
  · intro x
    obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc x.1 x.2
    exact ⟨hφ.chartOn x.2, _, hc.restrict_isSncChartAt hH hφ x.2 (hne x.1 x.2)⟩

end HypersurfaceFamily

end Manifold
