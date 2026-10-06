/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EmbeddedDesingFam
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Proper simple normal crossings of the final strict transform

The proper form of clause (3) of [Wlo09, Theorem 2.0.2] for an embedded desingularization functor
`bed : BEDanFamStar 𝕜`: for every dimension `n`, every triple of the class `DomBEDan` and every
relatively compact open `U`, the final strict transform `Ỹ` of the value on `U` is non-singular and,
at every point of its cosupport, has a chart adapted to `Ỹ` which is a simple-normal-crossing chart
of the final exceptional family `E_r` in which no component's coordinate is one of the coordinates
of `Ỹ` (`HasSncWithProper` at the point's codimension). Kollár's simple normal crossings of a
subvariety with a divisor allows components of the divisor to contain the subvariety
[Kol07, Definition 24]; the output of Włodarczyk's modified algorithm is a smooth submanifold whose
coordinates are "transversal to exceptional divisors" (the proof of [Wlo09, Theorem 7.4.1]), which
is the proper form. Clause (3) of `BEDanFamStar.IsEmbeddedDesing` is this text without the last
conjunct; the proper form follows from it (`IsEmbeddedDesing.isProperSnc` in
`Hironaka/Resolution/Analytic/Wlo09/ProperSncOfEmbeddedDesing.lean`).

The predicate is a named `Prop` so that the theorems about the resolution of analytic spaces can
bind `hbed : bed.IsEmbeddedDesing` alone and write `hbed.isProperSnc`.
-/

@[expose] public noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable (𝕜 : Type) [RCLike 𝕜]

/-- **`bed` has proper simple normal crossings**: for every `n`, every triple `T` of the class
`DomBEDan` on a manifold `M` modelled on `𝕜ⁿ` and every relatively compact open `U`, with `L` the
value `((bed.fam n).fam T hT).seqOn U hU` and
`Ỹ := L.strictTransformSubspaceSeq (T|U).I (Fin.last _)`, `E_r := L.totalTransformSeq (Fin.last _)`:
`Ỹ` is non-singular, and at every point of its cosupport
there are a codimension `c`, a chart `φ` adapted to `Ỹ.cosupport` with index embedding `σ`, and
component indices `cidx` making `φ` a simple-normal-crossing chart of `E_r` there, with
`cidx j ∉ Set.range σ` for every component `j` through the point (the proper conjunct;
`HasSncWithProper`, `Snc/Proper.lean`). Clause (3) of `IsEmbeddedDesing` is this text without the
last conjunct. -/
def BEDanFamStar.IsProperSnc (bed : BEDanFamStar.{u} 𝕜) : Prop :=
  ∀ (n : ℕ) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))),
    AnalyticSpace.IsNonsingular
      (IdealSheaf.toAnalyticSpace
        ((((bed.fam n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I (Fin.last _))) ∧
    (∀ x ∈ ((((bed.fam n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
        (Fin.last _)).support,
      ∃ (c : ℕ)
        (φ : OpenPartialHomeomorph
          ((((bed.fam n).fam T hT).seqOn U hU).toSuccession.stage (Fin.last _)) (Fin n → 𝕜))
        (σ : Fin c ↪ Fin n)
        (cidx : {j // x ∈ ((((bed.fam n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).hyp j} → Fin n),
        IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          ((((bed.fam n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
            (Fin.last _)).support φ σ ∧
        ((((bed.fam n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ x cidx ∧
        ∀ j, cidx j ∉ Set.range σ)

end Hironaka.Manifold
