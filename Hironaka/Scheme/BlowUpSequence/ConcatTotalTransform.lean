/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Total transforms, marked transforms and pull-backs of ideals along a concatenation

`concat` glues a blow-up sequence `S` on `X` to a sequence `T` on its end result;
`Hironaka/Scheme/BlowUpSequence/ConcatApi.lean` transports the composite, the weak transforms and
the boundaries along it, and `Hironaka/Scheme/BlowUpSequence/ConcatTransforms.lean` the strict
transforms. The embedded desingularization sequence of [Wlo05, Theorem 1.0.2] is a concatenation of
truncated runs of the marked order reduction functor, one per round, and its clauses (c) and (e)
read the final total transform of the boundary and the pull-back of the ideal of the subvariety to
the end result, so three more transports are needed:

* `totalTransformSeq_concat_last`: the total transform of a divisor family along `S.concat T` is
  the total transform along `T` of the total transform along `S` ([Kol07, Definition 25],
  iterated), read at `T.last` through the cast `eqToHom (last_concat S T)`, by the structural
  induction of `weakTransformSeq_concat_last`;
* `markedTransformSeq_concat_last`: likewise for the marked transform of [Kol07, Definition 66];
* `comap_composite_concat`: the pull-back of an ideal sheaf along the composite of `S.concat T`
  is the pull-back along `T` of the pull-back along `S` (`composite_concat` and the functoriality
  of `comap`).

Nothing here goes beyond the recursive definitions; the composition of the passes of the
resolution algorithm is in [Wlo05, Theorem 4.7.1].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open IdealSheafData

variable {X : Scheme.{u}}

/-- The total transform of a divisor family along a concatenation is the iterated total transform
[Kol07, Definition 25], read at the end result of the second sequence through the cast
`eqToHom (last_concat S T)`. -/
theorem totalTransformSeq_concat_last (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (E : DivisorFamily X) :
    (S.concat T).totalTransformSeq E (Fin.last _) =
      (T.totalTransformSeq (S.totalTransformSeq E (Fin.last _)) (Fin.last _)).comap
        (eqToHom (last_concat S T)) := by
  induction S with
  | nil X =>
    have h0 : eqToHom (last_concat (nil X) T) = 𝟙 T.last := eqToHom_refl _ _
    change T.totalTransformSeq (E : DivisorFamily (nil X).last) (Fin.last _) =
      (T.totalTransformSeq (E : DivisorFamily (nil X).last) (Fin.last _)).comap
        (eqToHom (last_concat (nil X) T))
    erw [h0, DivisorFamily.comap_id]
  | cons X D rest ih =>
    change (rest.concat T).totalTransformSeq (E.totalTransform D) (Fin.last _) =
      (T.totalTransformSeq (rest.totalTransformSeq (E.totalTransform D) (Fin.last _))
        (Fin.last _)).comap (eqToHom _)
    exact ih T (E.totalTransform D)

/-- The marked transform along a concatenation is the iterated marked transform
[Kol07, Definition 66, condition (1′)], read at the end result of the second sequence through the
cast `eqToHom (last_concat S T)`; the analogue of `strictTransformSeq_concat_last` for marked
transforms. -/
theorem markedTransformSeq_concat_last (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (I : X.IdealSheafData) (m : ℕ) :
    (S.concat T).markedTransformSeq I m (Fin.last _) =
      (T.markedTransformSeq (S.markedTransformSeq I m (Fin.last _)) m (Fin.last _)).comap
        (eqToHom (last_concat S T)) := by
  induction S with
  | nil X =>
    have h0 : eqToHom (last_concat (nil X) T) = 𝟙 T.last := eqToHom_refl _ _
    change T.markedTransformSeq (I : (nil X).last.IdealSheafData) m (Fin.last _) =
      (T.markedTransformSeq (I : (nil X).last.IdealSheafData) m (Fin.last _)).comap
        (eqToHom (last_concat (nil X) T))
    erw [h0, Scheme.IdealSheafData.comap_id]
  | cons X D rest ih =>
    change (rest.concat T).markedTransformSeq (I.markedTransform D m) m (Fin.last _) =
      (T.markedTransformSeq (rest.markedTransformSeq (I.markedTransform D m) m (Fin.last _)) m
        (Fin.last _)).comap (eqToHom _)
    exact ih T (I.markedTransform D m)

/-- The pull-back of an ideal sheaf along the composite of a concatenation is the pull-back along
the second sequence of the pull-back along the first, read at `T.last` through the cast
`eqToHom (last_concat S T)`. -/
theorem comap_composite_concat (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (I : X.IdealSheafData) :
    I.comap (S.concat T).composite =
      ((I.comap S.composite).comap T.composite).comap (eqToHom (last_concat S T)) := by
  rw [composite_concat, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]

end AlgebraicGeometry.Scheme.BlowUpSequence
