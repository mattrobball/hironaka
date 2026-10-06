/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.ClosedSubspace.Defs
import Hironaka.AnalyticSpace.Manifold.Chart
public import Hironaka.Manifold.Exhaustion
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
/-!
# The analytic space of an analytic manifold

An analytic manifold `M` over `K = ℝ` or `ℂ`, modelled on a finite-dimensional normed space `E` with
coordinates `ψ : E ≃L[K] Kⁿ`, is an analytic `K`-space in the sense of Hironaka [Hir64, Ch. 0, §1,
pp. 119–120]: its structure sheaf is the sheaf of analytic functions, with the constants as
`K`-structure, and (i) every point has a chart domain `U` on which `Sp(M) | U` is `K`-isomorphic to
a local analytic `K`-space, namely the open `G = ψ(φ.target) ⊆ Kⁿ` with no equations
(`chartLocalModelIso`); (ii) `M` is countable at infinity, being second countable and locally
compact (the model space is finite-dimensional, hence proper, which is where the coordinates `ψ`
enter); (iii) `M` is Hausdorff. This module defines

* `toSpace ψ M : AnalyticSpace K`, the analytic space `Sp(M)` of a bundled manifold
  `M : AnalyticManifold K E`; its underlying `K`-local-ringed space is `ofManifold K E M` whatever
  the coordinates `ψ`, which enter only the proofs of clauses (i) and (ii);
* `toSpaceHom ψ f : Sp(M) ⟶ Sp(N)`, the morphism of analytic spaces of an analytic map `f : M → N`
  (`ofManifoldHom`);
* `J.toAnalyticSpace`, the closed analytic subspace `Sp(A)/J` of the space of an analytic manifold
  `A` modelled on `Kⁿ`, cut out by an ideal sheaf `J` (`closedSubspace` on `Sp(A)`, the coordinates
  on `Kⁿ` the identity), with its canonical morphism `J.toAnalyticSpaceι : Sp(A)/J ⟶ Sp(A)`.

`Sp` is a functor from analytic manifolds to analytic `K`-spaces. It is fully faithful
(`toSpace_fullyFaithful`); its behaviour on open submanifolds, closed
submanifolds, disjoint unions and the dimension strata of a non-singular space is proved in the
neighbouring modules. Through `Sp` the manifold-level results of the analytic strand (blow-ups of
manifolds, ideal sheaves on manifolds, their strict transforms) are read as statements about
analytic spaces; in particular the ambient blow-up factorization of the resolution theorem for
analytic spaces (`Hom.AmbientBlowUpFactorization`) writes the closed subspaces of a manifold
through `toSpace`, and so do the charts of a simple normal crossings divisor set
(`IsSncDivisorSet`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff

universe u

noncomputable section

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ}
  (ψ : E ≃L[K] (Fin n → K))

/-- Hironaka's clause (i) for the space of a manifold [Hir64, Ch. 0, §1, p. 120]: every point has a
chart domain `U` such that `Sp(M) | U` is `K`-isomorphic to a local analytic `K`-space, namely the
open `ψ(φ.target)` of `Kⁿ` with no equations, restricted to its open subspace `⊤`. -/
theorem exists_localModel_ofManifold (ψ : E ≃L[K] (Fin n → K)) (M : Type u) [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(K, E) ω M] (x : M) :
    ∃ (U : Opens M) (_ : x ∈ U) (n' k : ℕ) (G : Opens (Kn.{u} K n'))
      (f : Fin k → AnalyticFun K n' G) (W : Opens (localModel K n' G f)),
      Nonempty (KIso ((ofManifold K E M).restrictOpen U) ((localModel K n' G f).restrictOpen W)) :=
  have hφ := IsManifold.chart_mem_maximalAtlas (I := 𝓘(K, E)) (n := ω) x
  ⟨chartSourceOpens (chartAt E x), mem_chart_source E x, n, 0, chartOpens ψ (chartAt E x),
    noEquations K n _, ⊤, ⟨chartLocalModelIso ψ hφ⟩⟩

/-- **The analytic `K`-space `Sp(M)` of an analytic manifold** `M` [Hir64, Ch. 0, §1, pp. 119–120]:
the `K`-local-ringed space `(M, 𝒪_M)` of analytic functions with Hironaka's clauses (i)–(iii) (see
the module docstring). The coordinates `ψ` enter only the proofs of clauses (i) and (ii). -/
def toSpace (M : AnalyticManifold.{u} K E) : AnalyticSpace.{u} K where
  toKLocallyRingedSpace := ofManifold K E M
  locallyModel := fun x => exists_localModel_ofManifold ψ (M : Type u) x
  t2 := M.t2
  sigmaCompact :=
    have : FiniteDimensional K E := ψ.symm.toLinearEquiv.finiteDimensional
    have : ProperSpace E := FiniteDimensional.proper_rclike K E
    sigmaCompactSpace_of_chartedSpace E (M : Type u)

/-- **The morphism `Sp(f) : Sp(M) ⟶ Sp(N)` of an analytic map** `f : M → N` between analytic
manifolds: precomposition with `f` on sections (`ofManifoldHom`). -/
def toSpaceHom {M N : AnalyticManifold.{u} K E}
    (f : AnalyticMap M N) :
    toSpace ψ M ⟶ toSpace ψ N :=
  ofManifoldHom (M := M) (N := N) f f.contMDiff

end AnalyticSpace

/-! ### Closed subspaces of manifolds as analytic spaces -/

namespace AnalyticManifold.IdealSheaf

variable {K : Type} [RCLike K] {n : ℕ}

/-- The closed analytic subspace `Sp(A)/J` of the space `Sp(A)` of an analytic manifold `A`
modelled on `Kⁿ`, cut out by the ideal sheaf `J`, as an analytic `K`-space: `closedSubspace` on
`Sp(A)` (the coordinates on `Kⁿ` the identity, as in `IsSncDivisorSet`). -/
noncomputable def toAnalyticSpace {A : AnalyticManifold.{u} K (Fin n → K)}
    (J : IdealSheaf A) : AnalyticSpace.{u} K :=
  AnalyticSpace.closedSubspace
    (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K)) A) J

/-- The canonical morphism `Sp(A)/J ⟶ Sp(A)` of the closed subspace. -/
noncomputable def toAnalyticSpaceι {A : AnalyticManifold.{u} K (Fin n → K)}
    (J : IdealSheaf A) :
    J.toAnalyticSpace ⟶ AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K)) A :=
  AnalyticSpace.closedSubspaceι
    (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin n → K)) A) J

end AnalyticManifold.IdealSheaf
