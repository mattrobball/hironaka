/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Per-stage clauses along a concatenation

`BlowUpSequence.concat` performs the blow-ups of `S` and then those of `T : BlowUpSequence S.last`.
Hironaka's Main Theorem II(N) [Hir64, Main Theorem II(N)] is proved by concatenating rounds of
order reduction, and its clauses (1)–(3) are statements about every stage `i`: the center `B_i`,
the weak transform `J_i` and the boundary `E_i`. This module transports a per-stage predicate
`P (B_i, J_i, E_i)` along `cons` and `concat`, the per-stage form of `forall_center_concat` and
`isOrderSeq_concat` of `Hironaka/Scheme/BlowUpSequence/ConcatApi.lean`, by induction on the first
sequence, and the last-stage clauses (4) of Main Theorem II(N) along `weakTransformSeq_concat_last`
and `boundarySeq_concat_last` (the identification `eqToHom (last_concat S T)` of the end results
changes nothing).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open IdealSheafData

variable {X : Scheme.{u}}

/-- A per-stage predicate `P (D_i, J_i, E_i)` along a `cons`: at stage `0` the data `(D, J, E)` of
the first blow-up, at the later stages the tail's data started at the transforms
`(weakTransform D J, reducedTransform D E)`. -/
theorem forall_stage_cons_iff
    (P : ∀ {Y : Scheme.{u}},
      Y.IdealSheafData → Y.IdealSheafData → Y.IdealSheafData → Prop)
    (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
        (J E : X.IdealSheafData) :
    (∀ i : Fin (cons X D rest).length, P ((cons X D rest).center i)
        ((cons X D rest).weakTransformSeq J i.castSucc)
        ((cons X D rest).boundarySeq E i.castSucc)) ↔
      P D J E ∧ ∀ j : Fin rest.length, P (rest.center j)
        (rest.weakTransformSeq (J.weakTransform D) j.castSucc)
        (rest.boundarySeq (E.reducedTransform D) j.castSucc) := by
  constructor
  · intro h
    exact ⟨h ⟨0, Nat.succ_pos _⟩, fun j => h ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩⟩
  · rintro ⟨h0, ht⟩ ⟨_ | j, hj⟩
    · exact h0
    · exact ht ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- A per-stage predicate holding at every stage of `S` (data started at `(J, E)`) and at every
stage of `T` (data started at the last transforms of `S`) holds at every stage of `S.concat T`;
the per-stage form of `forall_center_concat`. -/
theorem forall_stage_concat
    (P : ∀ {Y : Scheme.{u}},
      Y.IdealSheafData → Y.IdealSheafData → Y.IdealSheafData → Prop)
    (S : BlowUpSequence X) (T : BlowUpSequence S.last) (J E : X.IdealSheafData)
    (hS : ∀ i : Fin S.length,
      P (S.center i) (S.weakTransformSeq J i.castSucc) (S.boundarySeq E i.castSucc))
    (hT : ∀ j : Fin T.length, P (T.center j)
      (T.weakTransformSeq (S.weakTransformSeq J (Fin.last _)) j.castSucc)
      (T.boundarySeq (S.boundarySeq E (Fin.last _)) j.castSucc)) :
    ∀ i : Fin (S.concat T).length, P ((S.concat T).center i)
      ((S.concat T).weakTransformSeq J i.castSucc) ((S.concat T).boundarySeq E i.castSucc) := by
  induction S with
  | nil X => exact hT
  | cons X D rest ih =>
    have hS' := (forall_stage_cons_iff P D rest J E).1 hS
    exact (forall_stage_cons_iff P D (rest.concat T) J E).2
      ⟨hS'.1, ih T (J.weakTransform D) (E.reducedTransform D) hS'.2 hT⟩

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- Having only normal crossings [Hir64, Definition 2] is unchanged by the inverse image along the
identification of two equal schemes. -/
theorem IsSncBoundary.comap_eqToHom {Y Z : Scheme.{u}} (h : Y = Z)
    {I : Z.IdealSheafData} (hI : IsSncBoundary I) :
    IsSncBoundary (I.comap (eqToHom h)) := by
  subst h
  rwa [eqToHom_refl, Scheme.IdealSheafData.comap_id]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open IdealSheafData

variable {X : Scheme.{u}}

/-- The first part of clause (4) of [Hir64, Main Theorem II(N)] along a concatenation: the last
boundary of `S.concat T` has only normal crossings if the last boundary of `T`, started at the
last boundary of `S`, has. -/
theorem isSncBoundary_boundarySeq_concat_last (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (E₀ : X.IdealSheafData)
    (h : IsSncBoundary (T.boundarySeq (S.boundarySeq E₀ (Fin.last _)) (Fin.last _))) :
    IsSncBoundary ((S.concat T).boundarySeq E₀ (Fin.last _)) := by
  rw [boundarySeq_concat_last]
  exact h.comap_eqToHom (last_concat S T)

/-- The second part of clause (4) of [Hir64, Main Theorem II(N)] along a concatenation: the last
weak transform of `S.concat T` is the unit ideal if that of `T`, started at the last weak
transform of `S`, is. -/
theorem weakTransformSeq_concat_last_eq_top (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (J : X.IdealSheafData)
    (h : T.weakTransformSeq (S.weakTransformSeq J (Fin.last _)) (Fin.last _) = ⊤) :
    (S.concat T).weakTransformSeq J (Fin.last _) = ⊤ := by
  rw [weakTransformSeq_concat_last, h, Scheme.IdealSheafData.comap_top]
  rfl

end AlgebraicGeometry.Scheme.BlowUpSequence
