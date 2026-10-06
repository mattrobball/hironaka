/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Round
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nonmonomial triple

Step 1 of the proof of [Kol07, Theorem 107] (item 111) applies order reduction to the nonmonomial
part `N(𝓘)` of the ideal of a triple `(M, 𝓘, E)`. This file forms the triple that step runs on: the
**nonmonomial triple** `(M, N(𝓘), E)`, with the same ambient manifold and boundary and the ideal
replaced by its nonmonomial part (`BMO/NonmonomialPart.lean`). It is a genuine analytic triple
because `N(𝓘)` is nonzero at every point whenever `𝓘` is (`nonmonomialPart_isNonzeroEverywhere`,
`BMO/Round.lean`).

The ideal type of a bundled triple, `AnalyticManifold.IdealSheaf M`, is by definition the type
`IdealSheaf (structureSheaf 𝕜 E M)` on which the monomial and nonmonomial parts are defined, and the
manifold structure of `M` supplies the instances those definitions need, so `nonmonomialPart T.F
T.isSnc T.I` is directly an ideal of `T`. The mark `m` of Kollár's marked triple `(X, I, m, E)` is
not a field of an analytic triple; it is a parameter of the class `BMOClass m`. The analytic
counterpart of `Hironaka.BMO.nonmonomialTriple`. -/

@[expose] public section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The **nonmonomial triple** `(M, N(𝓘), E)` of an analytic triple `(M, 𝓘, E)`: the same ambient
manifold and boundary, the ideal replaced by its nonmonomial part `N(𝓘) = 𝓘 : M(𝓘)`, which is
nonzero at every point. This is the triple to which Step 1 of the proof of [Kol07, Theorem 107]
applies the order reduction functor. -/
noncomputable def nonmonomialTriple (T : AnalyticTriple ψ₀ M) : AnalyticTriple ψ₀ M :=
  { T with
    I := nonmonomialPart T.F T.isSnc T.I
    isNonzeroEverywhere :=
      nonmonomialPart_isNonzeroEverywhere T.F T.isSnc T.I T.isNonzeroEverywhere }

/-- The ideal of the nonmonomial triple is the nonmonomial part of the ideal. -/
@[simp] theorem nonmonomialTriple_I (T : AnalyticTriple ψ₀ M) :
    (nonmonomialTriple T).I = nonmonomialPart T.F T.isSnc T.I := rfl

/-- The boundary of the nonmonomial triple is the boundary of the triple. -/
@[simp] theorem nonmonomialTriple_F (T : AnalyticTriple ψ₀ M) :
    (nonmonomialTriple T).F = T.F := rfl

end Hironaka.Manifold.BMO
