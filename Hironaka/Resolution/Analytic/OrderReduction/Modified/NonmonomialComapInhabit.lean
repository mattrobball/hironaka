/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepALink
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nonmonomial part commutes with local analytic isomorphisms, on triples

The rounds on the nonmonomial part take as a parameter the predicate `NonmonomialComap ψ₀`
(`StepALink.lean`): the nonmonomial triple of a triple pulled back along a local analytic
isomorphism is the pull-back of the nonmonomial triple. This module proves it at the standard model
`ψ₀ = refl`: the ideal part is `nonmonomialPart_comap` (the correspondence of connected components
of the boundary under the isomorphism, and the colon), the boundary part is
`nonmonomialTriple_pullback_F`; both are moved across the structure by the two projection lemmas
`nonmonomialTriple_I` and `nonmonomialTriple_F` before the terms are compared, so that the
elaborator never has to unfold `nonmonomialTriple X` against `X`.

This is the compatibility of the decomposition `I = M(I) · N(I)` of [Kol07, Definition–Lemma 110]
with the local analytic isomorphisms, the analytic form of the smooth morphisms of [Kol07, 34.1];
the assembly of the theorem uses `nonmonomialComap_inhabitant` for its parameter `hcomp`.
-/

public noncomputable section

open Set Topology TopologicalSpace Hironaka.Manifold.BMO
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- **The nonmonomial part commutes with pull-back along local analytic isomorphisms, on triples**,
at the standard model: the ideal by `nonmonomialPart_comap`, the boundary by
`nonmonomialTriple_pullback_F` ([Kol07, Definition–Lemma 110] with [Kol07, 34.1]). -/
theorem nonmonomialComap_inhabitant :
    NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  intro M N S h hh
  refine Manifold.AnalyticTriple.ext' ?_ ?_
  · rw [nonmonomialTriple_I]
    exact nonmonomialPart_comap h hh S.F S.isSnc S.I
  · rw [nonmonomialTriple_F, nonmonomialTriple_pullback_F]

end Hironaka.Manifold.BMOmod
