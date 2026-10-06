/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Sigma
public import Hironaka.Manifold.SigmaManifold
public import Hironaka.AnalyticSpace.Manifold.Defs
import Hironaka.AnalyticSpace.Manifold.Sigma
import Hironaka.AnalyticSpace.Manifold.SigmaStratum
import Hironaka.AnalyticSpace.SigmaLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Disjoint unions of manifolds as coproducts of analytic spaces

Consequences of the coproduct construction of `Hironaka/AnalyticSpace/Sigma.lean` and
`Hironaka/AnalyticSpace/SigmaLemmas.lean`, and of the disjoint union of analytic manifolds
(`sigmaManifold`, `sigmaMk` of `Hironaka/Manifold/SigmaManifold.lean`), restated here for
reference; nothing but the root aggregator imports this module.

* The coproduct `sigma X` in `An/K`: its underlying `K`-local-ringed space and locally ringed
  space are the coproducts of the summands', it is Hausdorff and σ-compact, and the cofan
  `(sigma X, sigmaι X)` is a colimit cocone (`nonempty_isColimit_sigmaCofan`). Once
  `hasCoproduct` is known, Mathlib's `∐ X` exists in `An/K` and `sigma X ≅ ∐ X` canonically
  (`IsColimit.coconePointUniqueUpToIso`), but not by `rfl`: `∐ X` is a `Classical.choice`,
  `sigma X` the explicit construction.
* The space of a disjoint union of manifolds is the coproduct of the spaces of the summands
  (`toSpace_sigma`, `toSpace_sigma_hom`): in the charts of `Σ i, M i` (the charts of the `M i`
  lifted along the open embeddings `Sigma.mk i`) the inclusion of a summand reads as the
  identity, so `Sp(Sigma.mk i)` is an open immersion, and the descent
  `∐ Sp(M i) ⟶ Sp(Σ i, M i)` of these open immersions with disjoint images covering the union is
  an isomorphism by `isIso_sigmaDesc_of_isOpenImmersion` (`toSpaceSigmaIso`, in
  `Hironaka/AnalyticSpace/Manifold/`).
* A non-singular analytic `K`-space is the countable disjoint union of pure-dimensional manifolds
  (`nonsingular_eq_sigma_dim`): the strata `X_d = {x | dim 𝒪_{X,x} = d}` are open, pairwise
  disjoint, cover `X`, and each is `K`-isomorphic to the space of a manifold modelled on `K^d`
  (`stratumManifold`, `stratumSigmaIso`, in `Hironaka/AnalyticSpace/Manifold/`), so the same
  criterion gives `X ≅ ∐ d, Sp(X_d)` with the points of local dimension `d` the points of the
  `d`-th summand. This exhibits Hironaka's non-singular analytic `K`-spaces
  [Hir64, Ch. 0, §1, p. 121] as disjoint unions of manifolds of the several dimensions (the
  decomposition itself is `stratumSigmaIso`).
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AnalyticSpace Manifold
open scoped Manifold ContDiff

universe u v

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-! ### The coproduct in `An/K` -/

section

variable {ι : Type v} [Countable ι] (X : ι → AnalyticSpace.{u} K)

theorem sigma_toLocallyRingedSpace :
    (sigma X).toLocallyRingedSpace = LocallyRingedSpace.coproduct
      (KLocallyRingedSpace.coprodDiagram fun i => (X i).toKLocallyRingedSpace) :=
  rfl

theorem sigma_t2Space : T2Space (sigma X) :=
  (sigma X).t2

theorem sigma_sigmaCompactSpace : SigmaCompactSpace (sigma X) :=
  (sigma X).sigmaCompact

theorem nonempty_isColimit_sigmaCofan : Nonempty (IsColimit (Cofan.mk (sigma X) (sigmaι X))) :=
  ⟨isColimitSigmaCofan X⟩

end

/-! ### Disjoint unions of manifolds and the strata of a non-singular space -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ} (ψ : E ≃L[K] (Fin n → K))
  {ι : Type u} [Countable ι] (M : ι → AnalyticManifold.{u} K E)

theorem toSpace_sigma :
    ∃ e : toSpace ψ (sigmaManifold M) ≅ sigma (fun i => toSpace ψ (M i)),
      ∀ (i : ι) (x : M i),
        Hom.toFun e.hom (Sigma.mk i x) = Hom.toFun (sigmaι (fun i => toSpace ψ (M i)) i) x :=
  ⟨toSpaceSigmaIso ψ M, fun i x => toFun_toSpaceSigmaIso_hom_mk ψ M i x⟩

theorem toSpace_sigma_hom :
    ∃ e : toSpace ψ (sigmaManifold M) ≅ sigma (fun i => toSpace ψ (M i)),
      ∀ i : ι, toSpaceHom ψ (Manifold.sigmaMk M i) ≫ e.hom = sigmaι (fun i => toSpace ψ (M i)) i :=
  ⟨toSpaceSigmaIso ψ M, fun i => toSpaceHom_sigmaMk_comp_toSpaceSigmaIso_hom ψ M i⟩

theorem nonsingular_eq_sigma_dim (X : AnalyticSpace.{u} K) (hX : X.IsNonsingular) :
    ∃ (M : ∀ d : ℕ, AnalyticManifold.{u} K (Fin d → K))
      (e : X ≅ sigma fun d => toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) (M d)),
      ∀ (d : ℕ) (x : X),
        ringKrullDim (X.toLocallyRingedSpace.presheaf.stalk x) = ((d : ℕ) : WithBot ℕ∞) ↔
          ∃ m : M d, Hom.toFun e.hom x =
            Hom.toFun (sigmaι (fun d => toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) (M d)) d)
              m :=
  ⟨fun d => stratumManifold X hX d, stratumSigmaIso X hX,
    fun d x => ringKrullDim_eq_iff_exists X hX d x⟩

end

end AnalyticSpace

