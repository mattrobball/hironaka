/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.SigmaIdealSheaf
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceEmbedding
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceResolution
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The disjoint union of the pieces' ambient triples

Kollár's local model is the disjoint union `X' = ⊔ Uᵢ` of an affine cover [Kol07, Proposition 37,
proof]; in the library's form, with the pieces embedded in ambients: for a local embedding datum `D`
over `U ⊆ X`, the disjoint union `⊔ᵢ Gᵢ` of the pieces' ambients (`sigmaAmbient`) carries the
disjoint union of their triples `(Gᵢ, 𝓘ᵢ, ∅)` (`sigmaTriple`, the `ambientTriple` of each piece
summand by summand), a triple of the class of `bed` (`domBEDan_sigmaTriple`), each piece's triple
the pull-back along its summand's inclusion (`isPullbackOf_ambientTriple_sigmaTriple`) — the input
of the functor for the ambient blow-up factorization of the resolution (`AmbientLift.lean`).

Not in the sources; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U)

/-- **The disjoint union of the pieces' ambients** ([Kol07, Proposition 37, proof]). -/
abbrev sigmaAmbient : AnalyticManifold.{u} 𝕜 (Fin D.n → 𝕜) :=
  sigmaManifold fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G

/-- **The disjoint union of the pieces' ambient triples** (`sigmaOfEmpty`). -/
def sigmaTriple : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜)) D.sigmaAmbient :=
  AnalyticTriple.sigmaOfEmpty _ _ (fun i => (D.embedding i).ambientTriple) fun _ => rfl

/-- Each piece's triple is the pull-back of the disjoint union along its summand. -/
theorem isPullbackOf_ambientTriple_sigmaTriple (i : D.ι) :
    (D.embedding i).ambientTriple.IsPullbackOf D.sigmaTriple
      (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) :=
  AnalyticTriple.isPullbackOf_sigmaOfEmpty (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G)
    (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜)) (fun i => (D.embedding i).ambientTriple)
    (fun _ => rfl) i

/-- The disjoint union is a triple of the class of `bed`. -/
theorem domBEDan_sigmaTriple : DomBEDan 𝕜 D.sigmaTriple :=
  domBEDan_sigmaOfEmpty (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G)
    (fun i => (D.embedding i).ambientTriple) (fun _ => rfl) fun i =>
      (D.embedding i).domBEDan_ambientTriple

end Hironaka.Manifold.LocalEmbeddingData

end
