/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Proper
public import Hironaka.Manifold.FiniteSuccession.Restrict.Nested
import Hironaka.Manifold.BlowUp.Transform.StrictCharts
import Hironaka.Manifold.Snc.FlagProtected
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The trace of a divisor on a closed submanifold

Kollár's restriction of a blow-up sequence to a closed subvariety `S` [Kol07, 30.2] works on the
strict transforms `S_i` with the traces `E_i ∩ S_i` of the boundaries. This module defines the
**trace** of a family of hypersurfaces `F` on a closed submanifold `S`
(`IsClosedSubmanifold.traceFamily`: the components `F^j ∩ S`, read on the bundled manifold `S`)
and proves that it is a simple normal crossings divisor of `S` when `S` has simple normal
crossings with `F` properly (`isSnc_traceFamily`): in the proper chart at a point of `S` (adapted
to `S`, snc for `F`, component coordinates off the `S`-block) the induced chart of `S`
(`inducedChart`, the complementary coordinates) is an snc chart of the trace with the component
coordinates re-indexed through `complEquiv` (`isSncChartAt_inducedChart`). When moreover `Z ⊆ S`
has simple normal crossings with `F`, `Z` — as the submanifold `Z ∩ S` of `S` — has simple normal
crossings with the trace (`hasSncWith_traceFamily`; Kollár's centres `Z_i ∩ S_i` with simple
normal crossings with `E_i ∩ S_i`): the simultaneous chart of
`Hironaka/Manifold/Snc/FlagProtected.lean` (`exists_isSncChartAt_flag_proper`) induces the
chart of `S` adapted to `Z ∩ S` (`isAdaptedChart_chartOn_flag`) which is an snc chart of the trace.
These are the boundaries of the restricted sequences of the embedded resolution
(`Hironaka/Resolution/Analytic/Restrict/BoundaryTrace.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] {S : Set M} {s : ℕ}

/-- The **trace** of the family `F` on the closed submanifold `S`: the components `F^j ∩ S`, in
the order of `F`, read on the bundled manifold `S` (`toAnalyticManifold`) — Kollár's boundary
`E_i ∩ S_i` of a restricted blow-up sequence [Kol07, 30.2]. -/
def IsClosedSubmanifold.traceFamily (hS : IsClosedSubmanifold ψ S s) (F : HypersurfaceFamily M) :
    HypersurfaceFamily hS.toAnalyticManifold where
  ι := F.ι
  hyp j := hS.preimageVal (F.hyp j)

omit [IsManifold 𝓘(𝕜, E) ω M] in
theorem IsClosedSubmanifold.traceFamily_hyp (hS : IsClosedSubmanifold ψ S s)
    (F : HypersurfaceFamily M) (j : (hS.traceFamily F).ι) :
    (hS.traceFamily F).hyp j = hS.preimageVal (F.hyp j) :=
  rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The support of the trace is the trace of the support. -/
theorem IsClosedSubmanifold.traceFamily_support (hS : IsClosedSubmanifold ψ S s)
    (F : HypersurfaceFamily M) : (hS.traceFamily F).support = hS.preimageVal F.support := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact Set.mem_iUnion.mpr ⟨j, hj⟩

variable {F : HypersurfaceFamily M}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- In a chart adapted to `S` which is an snc chart of `F` at a point of `S` with the component
coordinates off the `S`-block, the induced chart of `S` (the complementary coordinates,
`inducedChart`) is an snc chart of the trace of `F` on `S`, with the component coordinates
re-indexed through `complEquiv`. -/
theorem IsClosedSubmanifold.isSncChartAt_inducedChart (hS : IsClosedSubmanifold ψ S s)
    {φ : OpenPartialHomeomorph M E} {σ' : Fin s ↪ Fin n} (hφS : IsAdaptedChart ψ S φ σ')
    {b : hS.toAnalyticManifold} {cidx : {j // (b : S).1 ∈ F.hyp j} → Fin n}
    (hc : F.IsSncChartAt ψ φ (b : S).1 cidx) (hproper : ∀ j, cidx j ∉ Set.range σ') :
    (hS.traceFamily F).IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (hS.inducedChart hφS (b : S).2) b
      fun j => complEquiv σ' ⟨cidx ⟨j.1, j.2⟩, hproper _⟩ := by
  refine ⟨hS.inducedChart_mem_maximalAtlas hφS _, (hS.mem_inducedChart_source hφS _ b).mpr hc.2.1,
    ?_, ?_⟩
  · rintro ⟨j, hj⟩ x hx
    have hxφ : (x : S).1 ∈ φ.source := (hS.mem_inducedChart_source hφS _ x).mp hx
    change (x : S).1 ∈ F.hyp j ↔ ψ (φ (x : S).1)
      ((complEquiv σ').symm (complEquiv σ' ⟨cidx ⟨j, hj⟩, hproper _⟩)).1 = 0
    rw [Equiv.symm_apply_apply]
    exact hc.mem_iff ⟨j, hj⟩ hxφ
  · intro j j' h
    have h1 := (complEquiv σ').injective h
    have h2 : cidx ⟨j.1, j.2⟩ = cidx ⟨j'.1, j'.2⟩ := congrArg Subtype.val h1
    exact Subtype.ext (congrArg Subtype.val (hc.injective h2))

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- If the closed submanifold `S` has simple normal crossings with the snc divisor `F` properly,
the trace of `F` on `S` is a simple normal crossings divisor of `S` [Kol07, 30.2]: its components
are closed hypersurfaces of `S` (the induced charts of the proper charts), locally finite
(preimages of a locally finite family), with the induced charts as snc charts
(`isSncChartAt_inducedChart`). -/
theorem IsClosedSubmanifold.isSnc_traceFamily (hS : IsClosedSubmanifold ψ S s) (hF : F.IsSnc ψ)
    (hFS : F.HasSncWithProper ψ S s) :
    (hS.traceFamily F).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) := by
  refine ⟨fun j => ⟨?_, fun b hb => ?_⟩, ?_, fun b => ?_⟩
  · exact (hF.1 j).isClosed.preimage continuous_subtype_val
  · obtain ⟨φ, σ', cidx, hφS, hc, hproper⟩ := hFS (b : S).1 (b : S).2
    have hct := hS.isSncChartAt_inducedChart hφS hc hproper
    exact ⟨hS.inducedChart hφS (b : S).2, singleEmb (complEquiv σ' ⟨cidx ⟨j, hb⟩, hproper _⟩),
      hct.2.1, isAdaptedChart_singleIdx hct.1 fun x hx => hct.mem_iff ⟨j, hb⟩ hx⟩
  · exact hF.2.1.preimage_continuous continuous_subtype_val
  · obtain ⟨φ, σ', cidx, hφS, hc, hproper⟩ := hFS (b : S).1 (b : S).2
    exact ⟨_, _, hS.isSncChartAt_inducedChart hφS hc hproper⟩

/-- If `Z ⊆ S` has simple normal crossings with the snc divisor `F` and `S` has simple normal
crossings with `F` properly, then `Z` — the submanifold `Z ∩ S` of `S`, of codimension `c − s` —
has simple normal crossings with the trace of `F` on `S` (Kollár's centres `Z_i ∩ S_i` and
boundaries `E_i ∩ S_i`, [Kol07, 30.2]). At a point of `Z`, the simultaneous chart
(`exists_isSncChartAt_flag_proper`) induces the chart of `S` adapted to `Z ∩ S`
(`isAdaptedChart_chartOn_flag`), which is an snc chart of the trace. -/
theorem IsClosedSubmanifold.hasSncWith_traceFamily (hS : IsClosedSubmanifold ψ S s)
    (hF : F.IsSnc ψ) {Z : Set M} {c : ℕ} (hZ : IsClosedSubmanifold ψ Z c) (hZS : Z ⊆ S)
    (hFZ : F.HasSncWith ψ Z c) (hFS : F.HasSncWithProper ψ S s) :
    (hS.traceFamily F).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
      (hS.preimageVal Z) (c - s) := by
  intro b hb
  have hbZ : (b : S).1 ∈ Z := hb
  obtain ⟨φ₀, σ₀, cidx₀, hφ₀, hc₀⟩ := hFZ _ hbZ
  obtain ⟨φ₁, σ₁, cidx₁, hφ₁, hc₁, hproper⟩ := hFS _ (b : S).2
  obtain ⟨e, σ, τ, cidx, heZ, hflag, hc, hcτ⟩ :=
    HypersurfaceFamily.exists_isSncChartAt_flag_proper hF hZ hZS hφ₀ hbZ hc₀ hφ₁ hc₁ hproper
  exact ⟨hS.inducedChart (heZ.flag hflag) (b : S).2, restrictEmb σ τ, _,
    isAdaptedChart_chartOn_flag hS heZ hflag (b : S).2,
    hS.isSncChartAt_inducedChart (heZ.flag hflag) hc hcτ⟩

end Manifold

end
