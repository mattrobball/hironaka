/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientEmb
public import Hironaka.AnalyticSpace.ClosedSubspace
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The exceptional family of a local embedding datum's COPRODUCT run

Kollár runs the functor once on the disjoint union of an affine cover [Kol07, Proposition 37,
proof]: over a local embedding datum `D` the functor is run ONCE on the coproduct triple
`D.sigmaTriple` (`SigmaTripleData.lean`), the ADMISSIBLE input `⊔ᵢ (Gᵢ, 𝓘_{Yᵢ}, ∅)` over the
relatively compact open `D.ambImage W = ⊔ᵢ Wᵢ` — the run
`bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W) _` behind the ambient blow-up
factorization of the resolution (`D.glueSeq` of `AmbientEmb.lean` is its transport along
`ambTheta`). Its last-stage boundary family — the total transforms of the exceptional divisors
from the EMPTY boundary [Kol07, Definition 25] (`totalTransformSeq_zero`) — is read member by
member as closed subspaces of the coproduct's local resolution
`Sp(Y_r) = bed.localResolutionOn D.sigmaTriple _ (D.ambImage W) _`
(`HypersurfaceFamily.toClosedSubspaces`, the inverse image `comap` along `toAnalyticSpaceι`).
The members are indexed by THE STAGE SET of the single run (one member per blow-up, empty members
allowed): this index set is the LABEL set of the gluing of the exceptional families — within one
datum the pieces already share it, and along the open immersion `resIn i` of each piece's local
resolution (`AmbientLift.lean`) the piece's exceptional members are the coproduct members of the
labels in the range of `eraseEmptyIdx`, the others restricting to the unit ideal (the general
identity of `RunFamilyRestrict.lean` at the summand inclusion `sigmaMk i`).

The members' closedness is clause (1) of `hbed : bed.IsEmbeddedDesing` at the last stage of the
coproduct run — `hbed` is the only hypothesis. The facts about this family — simple normal
crossings (`ClosedSubspace.IsSncFamily`) and support `Π_Σ⁻¹(Y_Σ.singularLocus)` — are in
`CoproductExceptionalSnc.lean`. Not in the sources beyond Kollár's model; bookkeeping.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BEDanFamStar

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M))) (hbed : bed.IsEmbeddedDesing)

/-- **The last-stage boundary family of the functor's run on `T` over `W`** (the empty start) —
the total transforms of the exceptional divisors ([Kol07, Definition 25]); its index type is the
run's stage set. -/
abbrev runFamily :
    HypersurfaceFamily ((bed.seqOn T hT W hW).toSuccession.stage (Fin.last _)) :=
  (bed.seqOn T hT W hW).toSuccession.totalTransformSeq (Fin.last _)

include hbed in
/-- Every member of the run's last-stage boundary family is a closed codimension-one submanifold
(clause (1) of `hbed` at the last stage). -/
theorem isClosedSubmanifold_runFamily (j : (bed.runFamily T hT W hW).ι) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((bed.runFamily T hT W hW).hyp j) 1 :=
  ((hbed.1 n T hT W hW).1 (Fin.last _)).1 j

/-- **The run's exceptional members as closed subspaces of its local resolution**
([Kol07, Definition 25]; [Wlo09, Theorem 2.0.2(1), (3)]) — the last-stage boundary member `j` read
as the closed subspace of the last stage cut out by its ideal sheaf
(`HypersurfaceFamily.toClosedSubspaces`, closedness from `hbed`'s clause (1)) and traced on
`localResolutionOn` along the inclusion `toAnalyticSpaceι` (the inverse image `comap`).
`sigmaMembers` below (a coproduct) is its instance; `hbed` is its only hypothesis. -/
def runMembers :
    (bed.runFamily T hT W hW).ι →
        AnalyticSpace.ClosedSubspace (bed.localResolutionOn T hT W hW) :=
  fun j =>
    AnalyticSpace.ClosedSubspace.comap
      (HypersurfaceFamily.toClosedSubspaces (bed.runFamily T hT W hW)
        (bed.isClosedSubmanifold_runFamily T hT W hW hbed) j)
      (IdealSheaf.toAnalyticSpaceι (bed.lastIdealOn T hT W hW))

end Hironaka.Manifold.BEDanFamStar

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
  (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
  (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))

/-- **The single run of the datum** ([Kol07, Proposition 37, proof]) — the functor's value on the
coproduct triple `D.sigmaTriple` over `D.ambImage W` (`glueSeq` is its transport along
`ambTheta`). -/
abbrev sigmaRun :
    BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
      (D.sigmaAmbient.restrict (D.ambImage W)) :=
  bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W) (D.isCompact_closure_ambImage W hW)

/-- **The last-stage boundary family of the single run** ([Kol07, Definition 25]) — the total
transforms of the exceptional divisors from the empty boundary. -/
abbrev sigmaFamily :
    HypersurfaceFamily ((D.sigmaRun bed W hW).toSuccession.stage (Fin.last _)) :=
  (D.sigmaRun bed W hW).toSuccession.totalTransformSeq (Fin.last _)

/-- **The label set of the datum** — the stage set of the single run (one index per blow-up of the
run). -/
abbrev sigmaIndex : Type u := (D.sigmaFamily bed W hW).ι

/-- Every member of the last-stage boundary family of the single run is a closed codimension-one
submanifold (clause (1) of `hbed` at the last stage). -/
theorem isClosedSubmanifold_sigmaFamily (hbed : bed.IsEmbeddedDesing) (j : D.sigmaIndex bed W hW) :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
      ((D.sigmaFamily bed W hW).hyp j) 1 :=
  bed.isClosedSubmanifold_runFamily _ _ _ _ hbed j

/-- **The exceptional members of the datum's single run, as closed subspaces of the coproduct's
local resolution `Sp(Y_r)`** ([Kol07, Definition 25]; [Wlo09, Theorem 2.0.2(1), (3)]) — the
last-stage boundary member `j` read as the closed subspace of `Sp(P_r)` cut out by its ideal sheaf
(`HypersurfaceFamily.toClosedSubspaces`, closedness from `hbed`'s clause (1)) and traced on
`localResolutionOn` along the inclusion `toAnalyticSpaceι` (the inverse image `comap`): `runMembers`
at the coproduct triple; `hbed` is its only hypothesis. -/
def sigmaMembers (hbed : bed.IsEmbeddedDesing) :
    D.sigmaIndex bed W hW → AnalyticSpace.ClosedSubspace (bed.localResolutionOn D.sigmaTriple
      D.domBEDan_sigmaTriple (D.ambImage W) (D.isCompact_closure_ambImage W hW)) :=
  bed.runMembers D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) hbed

end Hironaka.Manifold.LocalEmbeddingData

end
