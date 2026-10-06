/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
public import Hironaka.Scheme.BlowUpSequence.Restrict
import Mathlib.Data.Nat.Choose.Multinomial
import HironakaExamples.Sequence.CuspModel
import Hironaka.Scheme.BlowUpSequence.Defs
import Mathlib.AlgebraicGeometry.Scheme
public import HironakaExamples.Sequence.CuspWitness
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
/-!
# Restriction to a closed subscheme: the stage embeddings and Kollár's warning

The restriction `j^* B = B|_S` of a blow-up sequence to a closed subscheme `S = V(J)`
[Kol07, 30.2] is the pullback along `J.subschemeι`; its stage lifts `S_i → X_i` are closed
immersions onto the strict transforms of `S` (`Hironaka/Scheme/BlowUpSequence/Restrict.lean`). This
module restates that fact for the closed immersion `J.subschemeι`
(`isClosedImmersion_pullbackStageHom_subschemeι`) and records, as an `example`, the precise sense
in which "the restriction of a smooth blow-up sequence need not be a smooth blow-up sequence"
[Kol07, 30.2]. On the model of `HironakaExamples/Sequence/CuspModel.lean` (`X = 𝔸²_k`, the center
`V(x, y)`, the cuspidal cubic `S = V(y² − x³)`), blowing up the origin is a smooth blow-up sequence
whose restriction to the cusp starts at a scheme that is not smooth over `k`
(`HironakaExamples/Sequence/CuspWitness.lean`). The predicate `IsSmooth` of this library asks only
that the centers be smooth, and the restricted sequence does satisfy it: its one center
`V(x, y) ∩ V(y² − x³) = Spec k` is smooth. What fails is the ambient clause of [Kol07, Notation 19],
the smoothness of the stages themselves.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Hironaka.Sequence.Cusp

namespace Hironaka.Sequence

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Embedding

variable (J D : X.IdealSheafData)

end Embedding

section Witness

variable (k)

end Witness

section Smooth

variable (S : BlowUpSequence X) (J : X.IdealSheafData) (f : X ⟶ Spec (.of k))

end Smooth

section Stagewise

variable (S : BlowUpSequence X) (J : X.IdealSheafData)

/-- The natural embeddings `S_i ↪ X_i` of the restriction to `V(J)` are closed immersions
[Kol07, 30.2]; the case of `J.subschemeι` of `isClosedImmersion_pullbackStageHom`. -/
theorem isClosedImmersion_pullbackStageHom_subschemeι (i : Fin (S.length + 1)) :
    IsClosedImmersion (S.pullbackStageHom J.subschemeι i) :=
  isClosedImmersion_pullbackStageHom S J.subschemeι i

end Stagewise

/-- With the centers-only predicate `IsSmooth`, the restriction of the blow-up of the origin to
the cusp is a smooth blow-up sequence: its one center `V(x, y) ∩ V(y² − x³) = Spec k` is smooth.
So Kollár's "need not be a smooth blow-up sequence" [Kol07, 30.2] is the failure of the ambient
clause of [Kol07, Notation 19] (`not_smooth_cusp`), not of the condition on the centers. It follows
from `isSmooth_pullback_of_strictTransformSeq_le` at the one stage `i = 0`, where the hypothesis
`Z_0 ⊆ S_0` is `cusp ≤ originCenter`, i.e. `y² − x³ ∈ (x, y)`: the origin lies on the cusp. -/
example (k : Type u) [Field k] :
    ((seqOrigin k).pullback (cusp k).subschemeι).IsSmooth
      ((cusp k).subschemeι ≫ affineSpaceToSpec k 2) := by
  refine isSmooth_pullback_of_strictTransformSeq_le (seqOrigin k) (cusp k)
    (affineSpaceToSpec k 2) (fun i => ?_) (Hironaka.Sequence.Cusp.isSmooth_seqOrigin k)
  obtain ⟨n, hn⟩ := i
  have h0 : n = 0 := by
    have := hn; rw [length_seqOrigin] at this; omega
  subst h0
  change cusp k ≤ originCenter k
  rw [cusp, originCenter, specIdealSheaf_le_iff, cuspIdeal, originCenterIdeal,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ Ideal.span (Set.range MvPolynomial.X) :=
    Ideal.subset_span (Set.mem_range_self 1)
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈ Ideal.span (Set.range MvPolynomial.X) :=
    Ideal.subset_span (Set.mem_range_self 0)
  exact Ideal.sub_mem _ (Ideal.pow_mem_of_mem _ h1 2 two_pos)
    (Ideal.pow_mem_of_mem _ h0 3 three_pos)

end Hironaka.Sequence

