/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
public import Hironaka.Manifold.Germ.StalkNoetherian
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Dimension at a point and irreducible components of an analytic space

* `AnalyticSpace.dimAt X x`, the dimension of `X` at `x` — the dimension that Hironaka's Main
  Theorem I'(n) [Hir64, Ch. 0, §7, p. 155] uses for the space `W` without defining it there: the
  Krull dimension of the stalk `𝒪_{X,x}`, as in [Fre17, II 5.2] ("the dimension of `X` at some
  point `a ∈ X` is the Krull dimension of `𝒪_{X,a}`"), an element of `WithBot ℕ∞` (`⊥` only for
  the trivial ring, which no stalk of an
  analytic space is). The dimension `ClosedSubspace.dim W` of a closed subspace
  (`Hironaka/AnalyticSpace/ClosedSubspace.lean`) is the supremum of these over its points.
* `taylorAffine K n q`: the stalk `𝒜_{Kⁿ,q}` read as convergent power series centred at `q`, through
  the Taylor isomorphism in the identity chart of `Kⁿ`; the bridge between statements about
  convergent power series and the stalks of the local models.
* `AnalyticSpace.analyticComponents X`: the closures of the connected components of the simple
  locus `X.regularLocus`, the irreducible components of a reduced complex space in the sense of the
  global decomposition of [GR84, Ch. 9].
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

open AnalyticSpace

variable {K : Type} [RCLike K]

namespace AnalyticSpace

/-- The dimension of `X` at `x` [Hir64, Main Theorem I'(n), p. 155], [Fre17, II 5.2]: the Krull
dimension of the local ring `𝒪_{X,x}`. -/
def dimAt (X : AnalyticSpace.{u} K) (x : X) : WithBot ℕ∞ :=
  ringKrullDim (X.presheaf.stalk x)

/-- The irreducible components of the analytic space `X` in the analytic sense [GR84, Ch. 9]: the
closures of the connected components of the simple locus `X.regularLocus`. This is NOT Mathlib's
topological `irreducibleComponents X` (the maximal irreducible closed subsets, which in the
Hausdorff topology of an analytic space are the singletons), hence the name. -/
def analyticComponents (X : AnalyticSpace.{u} K) : Set (Set X) :=
  {C | ∃ x ∈ regularLocus X, C = closure (connectedComponentIn (regularLocus X) x)}

end AnalyticSpace

variable (K) (n : ℕ)

/-- The Taylor isomorphism `𝒜_{Kⁿ,q} ≃+* K{x}` in the identity chart of `Kⁿ` (`taylorEquivConv`):
the stalk as convergent power series centred at `q`. -/
def AnalyticSpace.taylorAffine (q : Kn.{u} K n) :
    (affine K n).toLocallyRingedSpace.presheaf.stalk q ≃+* Analytic.Conv K n :=
  taylorEquivConv (Kn.{u} K n) ContinuousLinearEquiv.ulift (chartAt (Kn.{u} K n) q)
    (mem_chart_source _ q) (IsManifold.chart_mem_maximalAtlas q)


end
