/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.SigmaTripleData
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The summand inclusions of the pieces' closed subspaces

In the library's form of Kollár's local model (the disjoint union of an affine cover,
[Kol07, Proposition 37, proof]), the closed subspace `Y₀ = ⊔ᵢ X|Uᵢ` of the disjoint union `⊔ᵢ Gᵢ`
is the disjoint union of the pieces' closed subspaces `Sp(Gᵢ)/𝓘ᵢ`. Here:
the summand inclusion `Sp(Gᵢ)/𝓘ᵢ → Sp(⊔ⱼ Gⱼ)/𝓘_Σ` — `homOfPullbackEq` along `sigmaMk i`, from
`isPullbackOf_ambientTriple_sigmaTriple` (`SigmaTripleData.lean`) — is an open immersion onto the
part of `Sp(⊔)/𝓘_Σ` over the summand, lying over `Sp(sigmaMk i)`.

Not in the sources; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U)

/-- **The summand inclusion of the closed subspaces** `Sp(Gᵢ)/𝓘ᵢ → Sp(⊔ⱼ Gⱼ)/𝓘_Σ`:
`homOfPullbackEq` along `sigmaMk i` ([Kol07, Proposition 37, proof]). -/
def sigmaSummandHom (i : D.ι) :
    (D.embedding i).ideal.toAnalyticSpace ⟶ D.sigmaTriple.I.toAnalyticSpace :=
  IdealSheaf.homOfPullbackEq (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).contMDiff
    (D.isPullbackOf_ambientTriple_sigmaTriple i).1

/-- It is an open immersion (`isOpenImmersion_homOfPullbackEq_of_injective` at the analytic open
embedding `sigmaMk i`). -/
theorem isOpenImmersion_sigmaSummandHom (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.sigmaSummandHom i).1 :=
  isOpenImmersion_homOfPullbackEq_of_injective _ (isLocalDiffeomorph_sigmaMk _ i)
    (isAnalyticOpenEmbedding_sigmaMk _ i).2 _

/-- Its range: the points of `Sp(⊔)/𝓘_Σ` over the summand. -/
theorem range_toFun_sigmaSummandHom (i : D.ι) :
    Set.range ⇑(D.sigmaSummandHom i) =
      {z : D.sigmaTriple.I.toAnalyticSpace |
        D.sigmaTriple.I.toAnalyticSpaceι z ∈
          Set.range (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)} :=
  range_toFun_homOfPullbackEq _ (isLocalDiffeomorph_sigmaMk _ i) _

/-- It lies over `Sp(sigmaMk i)` (`homOfPullbackEq_comp_toAnalyticSpaceι`). -/
theorem sigmaSummandHom_comp_toAnalyticSpaceι (i : D.ι) :
    D.sigmaSummandHom i ≫ D.sigmaTriple.I.toAnalyticSpaceι =
      (D.embedding i).ideal.toAnalyticSpaceι ≫ AnalyticSpace.toSpaceHom (ContinuousLinearEquiv.refl
          𝕜 (Fin D.n → 𝕜)) (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) :=
  homOfPullbackEq_comp_toAnalyticSpaceι _ _ _

end Hironaka.Manifold.LocalEmbeddingData

end
