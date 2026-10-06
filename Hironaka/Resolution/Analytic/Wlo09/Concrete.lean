/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/

module

public import Hironaka.Resolution.Analytic.Wlo09.Functoriality
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseModFunctor
public import Hironaka.Resolution.Analytic.OrderReduction.Stage.Concrete
import Hironaka.Resolution.Analytic.Functor.ChainClosedEmbeddingZero
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseClosedEmbedding
import Hironaka.Resolution.Analytic.Wlo09.Assembly
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The concrete embedded desingularization functor

The embedded desingularization functor of this library, assembled from concrete inputs. The modified
marked resolution `concreteBMOmodFam` in every dimension is built by the construction
`BMOmodFamOfInput_of_hid` of Włodarczyk's modified algorithm (the proof of [Wlo09, Theorem 7.4.1])
from the concrete order-reduction families `concreteBOanFam` and `concreteBMOanFam` of the standard
tower (`OrderReduction/Stage/Concrete.lean`) and the transform identity
`nonmonomialTransformIdentity_refl`; it commutes with closed embeddings of empty divisor at every
codimension (`concreteBMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam`: the codimension-one
case of [Wlo09, §7.1], chained along a flag of hypersurfaces as in [Kol07, 108]); and the
all-dimensions embedded desingularization functor `concreteBEDanFamStar` is `BEDanFamStarOfInput` at
these data (`Hironaka/Resolution/Analytic/Wlo09/Functoriality.lean`), with the clauses of
[Wlo09, Theorem 2.0.2] (`concreteBEDanFamStar_isEmbeddedDesing`, the assembly of
`Hironaka/Resolution/Analytic/Wlo09/Assembly.lean`).

This is the functor from which the resolution of analytic spaces `exists_functorial_resolution` is
assembled (`Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionAssembly.lean`).
-/

@[expose] public section

universe u

open scoped Manifold ContDiff
open TopologicalSpace Hironaka.Manifold

namespace Hironaka

variable (K : Type) [RCLike K]


/-- The modified marked resolution in every dimension (the construction `BMOmodFamOfInput_of_hid`
of the proof of [Wlo09, Theorem 7.4.1]) at the concrete order-reduction families `concreteBOanFam`
and `concreteBMOanFam` of the standard tower and the transform identity
`nonmonomialTransformIdentity_refl`. -/
noncomputable def concreteBMOmodFam : ∀ n : ℕ, BMOmodFam.{u} K n :=
  BMOmod.BMOmodFamOfInput_of_hid K (concreteBOanFam K) (concreteBMOanFam K)
      (nonmonomialTransformIdentity_refl K)

/-- `concreteBMOmodFam` commutes with closed embeddings of empty divisor at every codimension `s`:
the codimension-one commutation of `BMOmodFamOfInput_of_hid` (resolving `(M, I, ∅, 1)` commutes
with embeddings of the ambient manifold, [Wlo09, §7.1]) chained along a flag of hypersurfaces
(`BMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all` of
`Functor/ChainClosedEmbeddingZero.lean`, the reduction to the hypersurface case as in
[Kol07, 108]). -/
theorem concreteBMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam (n s : ℕ) :
    (concreteBMOmodFam K n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
      (concreteBMOmodFam K (n - s)).functor :=
  Hironaka.Manifold.BMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all
      (concreteBMOmodFam K)
    (fun m _ =>
        BMOmod.BMOmodFamOfInput_of_hid_commutesWithClosedEmbeddings_one K (concreteBOanFam K)
            (concreteBMOanFam K)
      (nonmonomialTransformIdentity_refl K) m)
    n s

/-- The concrete embedded desingularization functor in all dimensions: `BEDanFamStarOfInput` at
`concreteBMOmodFam`. -/
noncomputable def concreteBEDanFamStar : BEDanFamStar.{u} K :=
  BEDanFamStarOfInput K (concreteBMOmodFam K)
      (concreteBMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam K)

/-- `concreteBEDanFamStar` is an embedded desingularization: the clauses of
[Wlo09, Theorem 2.0.2], by the assembly `BEDanFamStarOfInput_isEmbeddedDesing`. -/
theorem concreteBEDanFamStar_isEmbeddedDesing : (concreteBEDanFamStar K).IsEmbeddedDesing :=
  Hironaka.Manifold.BEDanFamStarOfInput_isEmbeddedDesing K (concreteBMOmodFam K)
      (concreteBMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam K)

end Hironaka
