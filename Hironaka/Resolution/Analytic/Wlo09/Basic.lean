/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EmbeddedDesingFam
public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The analytic embedded desingularization as the modified marked resolution on reduced subspaces

Włodarczyk's embedded desingularization of a closed analytic subspace `Y ⊆ M`
[Wlo09, Theorem 2.0.2] is obtained by running the resolution algorithm for the marked ideal
`(M, 𝓘_Y, ∅, 1)` in a modified form (the proof of [Wlo09, Theorem 7.4.1]): the algorithm is stopped
as soon as the controlled transform is the ideal of a smooth hypersurface of maximal contact, and
it ends with the ideal of a smooth submanifold transversal to the exceptional divisors. The
structure `BMOmodFam 𝕜 n` packages such a modified marked resolution in dimension `n` on the class
of marked triples of mark `1`: its `functor` is a compatible family of blow-up sequences per
relatively compact open, and its fields record the order clause (`isOfOrderGe`), the containment
of the centres in the support (`center_mem_support`), the shape of the final controlled transform
(`output_isSmoothSubmanifoldIdeal`) and the stop rule (`stopped_never_blownUp`).

This module defines the embedded desingularization functor in dimension `n` as that resolution
restricted to the class `DomBEDan` of triples with empty boundary and reduced ideal: `Y` is
recovered from `𝓘_Y`, and on this class the modified marked resolution is Włodarczyk's embedded
desingularization itself. Włodarczyk's algebraic version [Wlo05, Theorem 4.7.1] has in addition
an outer loop that isolates the components of the strict transform one codimension at a time;
that loop serves the algebraic ordering of the algorithm and is not part of the analytic
construction, so it is not transcribed. The compatible-family data (`seqOn U hU`,
`noEmptyCenters`, `compat`) are inherited from the modified marked resolution; the final step of
Włodarczyk's proof, blowing up the components of the final support that are not strict
transforms of components of `Y`, is void for reduced `Y`.

* `DomBEDan.bmoClass_one`: a triple of the class is a marked triple of mark `1` (`BMOClass 1`:
  `1 ≤ 1`, and finitely many nonempty boundary members, there being none).
* `bedanFamOfInput bmod n`: the embedded desingularization functor.
* `bedanFamOfInput_fam`: its value unfolded (`rfl`).

The clauses of [Wlo09, Theorem 2.0.2] for this functor are proved in the other modules of
`Hironaka/Resolution/Analytic/Wlo09/` from the fields of `BMOmodFam`, per relatively
compact open, and assembled in `Hironaka/Resolution/Analytic/Wlo09/Assembly.lean`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable (𝕜 : Type) [RCLike 𝕜]

/-- A triple of the class `DomBEDan` is a marked triple of mark `1` (`BMOClass 1` of
`OrderReduction/MarkedData.lean`): `1 ≤ 1`, and the boundary has no members at all
(`IsEmpty T.F.ι`), so finitely many nonempty ones. -/
theorem DomBEDan.bmoClass_one {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} (hT : DomBEDan 𝕜 T) :
    AnalyticTriple.BMOClass 1 T := by
  refine ⟨le_rfl, ?_⟩
  have : IsEmpty T.F.ι := hT.1
  infer_instance

/-- **The embedded desingularization functor in dimension `n`** ([Wlo09, Theorem 2.0.2],
constructed as in the proof of [Wlo09, Theorem 7.4.1]): the modified marked resolution `bmod n`
restricted to the class `DomBEDan` of triples with empty boundary and reduced ideal. -/
def bedanFamOfInput (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ) : BEDanFam.{u} 𝕜 n where
  fam T hT := (bmod n).functor.fam T (DomBEDan.bmoClass_one 𝕜 hT)

/-- The value of the embedded desingularization functor, unfolded (`rfl`). -/
theorem bedanFamOfInput_fam (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T) :
    (bedanFamOfInput 𝕜 bmod n).fam T hT = (bmod n).functor.fam T (DomBEDan.bmoClass_one 𝕜 hT) :=
  rfl

end Hironaka.Manifold

end
