/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Monomials up to a unit on a real manifold, from Mathlib's definitions alone

`IsMonomialAt n g p`: near the point `p` of an `n`-dimensional real manifold, in the coordinates of
the chart at `p`, the function `g` is a monomial times an analytic function that does not vanish
at `p`. It is defined from Mathlib's charts (`extChartAt`) and analytic functions on manifolds
(`ContMDiffAt` of order `ω`), in a module that imports Mathlib only. The challenge file
`Challenge/Standard.lean`, which imports Mathlib only, repeats it word for word, so that the local
monomialization of a real-analytic function (`exists_proper_analytic_monomialization`) can be
stated there.
-/

@[expose] public section

open Filter Topology
open scoped Manifold ContDiff

/-- A real function `g` on an `n`-dimensional manifold `M` is *a monomial at `p`, up to a unit*,
if near `p`, in the coordinates `y` of the chart of `M` at `p`, `g = u · y^α` for an exponent
vector `α` and a real-analytic function `u` that does not vanish at `p`. -/
def IsMonomialAt (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (g : M → ℝ) (p : M) : Prop :=
  ∃ (α : Fin n → ℕ) (u : M → ℝ), ContMDiffAt (𝓡 n) 𝓘(ℝ) ω u p ∧ u p ≠ 0 ∧
    ∀ᶠ q in 𝓝 p, g q = u q * ∏ i, extChartAt (𝓡 n) p q i ^ α i
