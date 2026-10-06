/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.ProperSnc
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.StrictTransformDensity
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# An embedded desingularization has proper simple normal crossings

Clause (3) of `BEDanFamStar.IsEmbeddedDesing` is proper: for an embedded desingularization functor
`bed` with `bed.IsEmbeddedDesing`, the final strict transform `Ỹ` of every value has, at every point
of its cosupport, a chart adapted to `Ỹ` which is a simple-normal-crossing chart of the final
exceptional family `E_r` in which no component's coordinate is one of the coordinates of `Ỹ`
(`BEDanFamStar.IsProperSnc`, `Hironaka/Resolution/Analytic/Wlo09/ProperSnc.lean`; the coordinate
description of [Kol07, Definition 24], with the transversality of the output of the proof of
[Wlo09, Theorem 7.4.1]).

**Proof.** Clause (3) gives the adapted simple-normal-crossing chart `φ` with the coordinates `σ` of
`Ỹ` and the components' coordinates `cidx`. If a component `E^j` through the point had
`cidx j = σ i`, then on `φ.source` every point of `Ỹ` (where `z_{σ i} = 0`) would lie on `E^j`
(where `z_{cidx j} = 0`), so `Ỹ ∩ φ.source ⊆ E_r`, and the point would not be a limit of points of
`Ỹ` off `E_r`. But `Ỹ` is non-singular (the first conjunct of clause (3)), so every point of its
cosupport is a regular point of the closed subspace (`mem_reg_toAnalyticSpace_iff`), and the density
theorem `mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular`
(`Hironaka/Resolution/Analytic/Wlo09/StrictTransformDensity.lean`) makes it such a limit. The
pointwise step is `IsSncChartAt.cidx_notMem_range_of_mem_closure_diff`. Not in the sources in this
form.

The dot-notation name `BEDanFamStar.IsEmbeddedDesing.isProperSnc` is the form in which the
resolution of analytic spaces invokes it (`hbed.isProperSnc`).
-/

public section

open Set Topology TopologicalSpace Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

section Pointwise

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- The pointwise step: a simple-normal-crossing chart of `F` at `a` whose chart is adapted to `Z`
is proper (`cidx j ∉ range σ`) as soon as `a` is a limit of points of `Z` off `F`; a component
through `a` with `cidx j = σ i` would contain `Z ∩ φ.source`. -/
theorem HypersurfaceFamily.IsSncChartAt.cidx_notMem_range_of_mem_closure_diff
    {F : HypersurfaceFamily M} {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ a c)
    {Z : Set M} {s : ℕ} {σ : Fin s ↪ Fin n} (hφ : IsAdaptedChart ψ Z φ σ)
    (ha : a ∈ closure (Z \ F.support)) : ∀ j, c j ∉ Set.range σ := by
  rintro j ⟨i, hi⟩
  obtain ⟨y, hyφ, hyZ, hyF⟩ := mem_closure_iff_nhds.mp ha _ (φ.open_source.mem_nhds hc.2.1)
  refine hyF (Set.mem_iUnion.mpr ⟨j.1, (hc.2.2.1 j y hyφ).mpr ?_⟩)
  rw [← hi]
  exact (hφ.2 y hyφ).mp hyZ i

end Pointwise

section Functor

/-- **An embedded desingularization has proper simple normal crossings**: clause (3) gives the
adapted simple-normal-crossing chart at every point of the final strict transform `Ỹ`; `Ỹ` is
non-singular, so the point is regular and the density theorem
`mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular` makes it a limit of
points of `Ỹ` off `E_r`; `IsSncChartAt.cidx_notMem_range_of_mem_closure_diff` gives the proper
conjunct. -/
theorem _root_.Hironaka.Manifold.BEDanFamStar.IsEmbeddedDesing.isProperSnc {𝕜 : Type} [RCLike 𝕜]
    {bed : BEDanFamStar.{u} 𝕜} (hbed : bed.IsEmbeddedDesing) : bed.IsProperSnc := by
  intro n M T hT U hU
  obtain ⟨-, -, -, hns, hchart, -⟩ := hbed.1 n T hT U hU
  refine ⟨hns, fun x hx => ?_⟩
  obtain ⟨c, φ, σ, cidx, hφ, hsnc⟩ := hchart x hx
  refine ⟨c, φ, σ, cidx, hφ, hsnc, hsnc.cidx_notMem_range_of_mem_closure_diff hφ ?_⟩
  -- every point of the non-singular `Ỹ` is regular; the density theorem at `x`
  have hreg := (mem_reg_toAnalyticSpace_iff _ ⟨x, hx⟩).mp
    (by have h : _ = Set.univ := hns; rw [h]; exact Set.mem_univ _)
  exact mem_closure_cosupport_strictTransformSubspaceSeq_diff_support_of_isRegular _ _ (Fin.last _)
    x hx hreg

end Functor

end Manifold
