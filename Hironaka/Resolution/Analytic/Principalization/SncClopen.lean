/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Defs
import Hironaka.Manifold.Submanifold.Clopen
import Hironaka.Resolution.Analytic.Principalization.MeetLocusChart
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Simple normal crossings with a clopen part of the centre, and the snc dimension bound

Two facts about an snc family `F` [Kol07, Definition 24]: `F` has simple normal crossings with a
clopen part `Y ∩ O` of a set it has simple normal crossings with (the common adapted/snc chart at
a point restricted to `O`), and at most `n` members of `F` pass through a point (the snc chart at
the point injects the members through it into the `n` coordinates, [Kol07, Definition 24 (3)]).
Placed beside the meet-locus charts (`MeetLocusChart.lean`), whose
`IsSncChartAt.restrOpen_of_isOpen` restricts the snc chart. Used where a centre is a union of some
of the components of an intersection of boundary hypersurfaces
(`Hironaka/Resolution/Analytic/OrderReduction/BMO/Step3Monomial/Ideal.lean`).
-/

public section

open TopologicalSpace Filter Topology Set
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

namespace HypersurfaceFamily

variable {F : HypersurfaceFamily M}

/-- Simple normal crossings with a clopen part of the centre. -/
theorem HasSncWith.inter_of_isOpen {Y : Set M} {c : ℕ} (h : F.HasSncWith ψ Y c) {O : Set M}
    (hO : IsOpen O) : F.HasSncWith ψ (Y ∩ O) c := by
  rintro a ⟨haY, haO⟩
  obtain ⟨φ, σ, cidx, hφ, hsnc⟩ := h a haY
  exact ⟨φ.restrOpen O hO, σ, cidx, hφ.inter_restrOpen hO, hsnc.restrOpen_of_isOpen hO haO⟩

/-- At most `n` members of an snc family pass through a point ([Kol07, Definition 24 (3)]): the snc
chart at the point injects them into the coordinates. -/
theorem IsSnc.card_le (hF : F.IsSnc ψ) (x : M) (s : Finset F.ι) (hs : ∀ j ∈ s, x ∈ F.hyp j) :
    s.card ≤ n := by
  obtain ⟨φ, cidx, hφ⟩ := hF.2.2 x
  have hinj : Function.Injective fun j : s => cidx ⟨j.1, hs j.1 j.2⟩ := by
    intro j j' hjj'
    have h2 : (⟨j.1, hs j.1 j.2⟩ : {j // x ∈ F.hyp j}) = ⟨j'.1, hs j'.1 j'.2⟩ := hφ.2.2.2 hjj'
    exact Subtype.ext (congrArg (fun y : {j // x ∈ F.hyp j} => y.1) h2)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_coe, Fintype.card_fin] using this

end HypersurfaceFamily

end Manifold
