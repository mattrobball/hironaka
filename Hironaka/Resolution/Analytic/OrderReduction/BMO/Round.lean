/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nonmonomial part is nonzero and contains the ideal

Step 1 of the proof of [Kol07, Theorem 107] (item 111) reduces the order of the nonmonomial part
`N(𝓘)` by rounds of order reduction, each at the order `d = max-ord N(𝓘)`. Two elementary
consequences of the decomposition `𝓘 = M(𝓘) · N(𝓘)` (`BMO/SplitOrder.lean`) are recorded here:
`N(𝓘)` is nonzero at every point whenever `𝓘` is, since a stalk product `M(𝓘)_x · N(𝓘)_x = 𝓘_x ≠ 0`
has nonzero factors, so that `(M, N(𝓘), E)` is a genuine triple; and `𝓘 ⊆ N(𝓘)`, since
`M(𝓘)_x · N(𝓘)_x ⊆ N(𝓘)_x`. The inclusion is what lets a blow-up sequence of order `≥ d` for `N(𝓘)`
be read as one of order `≥ m` for `(𝓘, m)` when `m ≤ d`.
-/

public section

open Set
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

/-- The nonmonomial part `N(𝓘)` is nonzero at every point when `𝓘` is: from the decomposition
`M(𝓘)_x · N(𝓘)_x = 𝓘_x`, a factor of a nonzero product is nonzero. Hence `N(𝓘)` is the ideal of a
genuine triple (`BMO/NonmonomialTriple.lean`). -/
theorem nonmonomialPart_isNonzeroEverywhere (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) (hI : I.IsNonzeroEverywhere) :
    (nonmonomialPart F hF I).IsNonzeroEverywhere := by
  intro x hN
  exact hI x (by rw [← stalkIdeal_monomialPart_mul_nonmonomialPart F hF I x, hN, Ideal.mul_bot])

/-- At every stalk the ideal `𝓘` is contained in its nonmonomial part `N(𝓘)`: from
`𝓘_x = M(𝓘)_x · N(𝓘)_x` and `M(𝓘)_x · N(𝓘)_x ⊆ N(𝓘)_x`. Consequently a centre along which `N(𝓘)`
has order `≥ d` is one along which `𝓘` has order `≥ d`, which is how Step 1 of the proof of
[Kol07, Theorem 107] reads a blow-up sequence for `N(𝓘)` as one for `(𝓘, m)`. -/
theorem stalkIdeal_le_nonmonomialPart (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) (x : M) :
    I.stalkIdeal x ≤ (nonmonomialPart F hF I).stalkIdeal x := by
  rw [← stalkIdeal_monomialPart_mul_nonmonomialPart F hF I x]
  exact Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs

/-- The inclusion `𝓘 ≤ N(𝓘)` as ideal sheaves, the sheaf-level form of
`stalkIdeal_le_nonmonomialPart`. -/
theorem le_nonmonomialPart (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    I ≤ nonmonomialPart F hF I :=
  IdealSheaf.le_def.mpr (stalkIdeal_le_nonmonomialPart F hF I)

end Hironaka.Manifold.BMO
