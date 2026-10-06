/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The loci of Hironaka's Corollary 1 and the descent of the order to the base

The proof of [Hir64, Corollary 1 to Main Theorem II] (the simultaneous reduction of a finite
system of ideal sheaves `J_1, …, J_e`) works on the open subscheme `X ∖ S` of the points where no
`J_j` is trivial or `ν(∏ J_j) < d`, and reads off clause (ii) of Main Theorem II that the centers
of the resulting sequence "are mapped into the closed subset `T − S`" of `X`.

* `trivializationLoci_closed`: `T − S = {x : ν((∏ J_j)_x) ≥ d ∧ ∀ j, x ∈ supp J_j}` is closed, as
  the intersection of `{ord ≥ d}`, closed by the upper semicontinuity of the order
  (`isClosed_setOf_le_ord`, characteristic zero), with the closed supports. Hironaka asserts `T`,
  `S` and `T − S` closed without proof ("we can prove"); `T − S` is proved closed here and `S` in
  `Hironaka/Resolution/Algebraic/Hir64/Corollary1.lean` (`isClosed_trivialLocus`); both are used.
* `le_ord_stageMap_of_le_ord_weakTransformSeq` (and its general form without the setting of the
  Corollary): along a sequence whose centers carry weak-transform order `≥ d` (clause (ii) of Main
  Theorem II), a point of a stage at which the weak transform has order `≥ d` lies over a point of
  `X` at which `J` has order `≥ d`. By induction on the sequence: over a point off the center the
  blow-up is a local isomorphism and the weak transform has the order of `J` there
  (`ord_weakTransform_of_notMem`); over a point of the center, (ii) gives `ν(J_i) ≥ d` at that
  point. Applied to the centers themselves it is Hironaka's "all the `D(i)` are mapped into
  `T − S`".
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence
  TopologicalSpace

namespace Hironaka.Sequence

variable {k : Type u} [Field k]

/-! ### The locus `T − S` is closed -/

/-- **`T − S` is closed** (asserted without proof in the proof of [Hir64, Corollary 1 to Main
Theorem II]): `{ord (∏ J_j) ≥ d}` is closed by the upper semicontinuity of the order
(`isClosed_setOf_le_ord`) and the supports are closed. -/
theorem trivializationLoci_closed [CharZero k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    {e : ℕ} (J : Fin e → X.IdealSheafData) (d : ℕ) :
    IsClosed {x : X | (d : ℕ∞) ≤ (∏ j, J j).ord x ∧ ∀ j, x ∈ (J j).support} := by
  obtain ⟨N, hN⟩ := hN
  have h1 : IsClosed {x : X | (d : ℕ∞) ≤ Scheme.IdealSheafData.ord (∏ j, J j) x} :=
    Scheme.IdealSheafData.isClosed_setOf_le_ord (X ↘ Spec (CommRingCat.of k)) N (∏ j, J j) d
  have h2 : IsClosed {x : X | ∀ j, x ∈ (J j).support} := by
    have : {x : X | ∀ j, x ∈ (J j).support} = ⋂ j, ((J j).support : Set X) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, SetLike.mem_coe]
    rw [this]
    exact isClosed_iInter fun j => (J j).support.isClosed
  exact h1.inter h2

/-! ### Points of order `≥ d` lie over points of order `≥ d` -/

/-- The general form, on any scheme: along a sequence whose centers have weak-transform order
`≥ d`, a point of order `≥ d` of a weak transform lies over a point of order `≥ d` of `J`.
Induction on the sequence, off the center by `ord_weakTransform_of_notMem`, on the center by the
hypothesis on the centers. -/
theorem le_ord_stageMap_of_le_ord_weakTransformSeq_gen :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (J : X.IdealSheafData) (d : ℕ),
    (∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
      (d : ℕ∞) ≤ (S.weakTransformSeq J i.castSucc).ord x) →
    ∀ (i : Fin (S.length + 1)) (z : S.stage i), (d : ℕ∞) ≤ (S.weakTransformSeq J i).ord z →
      (d : ℕ∞) ≤ J.ord (S.stageMap i z)
  | _, nil _, _, _, _, ⟨0, _⟩, _, hz => hz
  | _, nil _, _, _, _, ⟨_ + 1, hj⟩, _, _ =>
    (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)).elim
  | _, cons _ _ _, _, _, _, ⟨0, _⟩, _, hz => hz
  | _, cons X D rest, J, d, hii, ⟨j + 1, hj⟩, z, hz => by
    have ih := le_ord_stageMap_of_le_ord_weakTransformSeq_gen rest (J.weakTransform D) d
      (fun i x hx => hii ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ x hx) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z hz
    change (d : ℕ∞) ≤ J.ord (D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z))
    by_cases hz' : rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z ∈
        D.exceptionalDivisor.support
    · have hmem : D.blowUpπ (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z) ∈ D.support
        := by
        change _ ∈ (D.comap D.blowUpπ).support at hz'
        rw [Scheme.IdealSheafData.support_comap] at hz'
        exact hz'
      exact hii ⟨0, Nat.succ_pos _⟩ _ hmem
    · have h := ord_weakTransform_of_notMem D J hz'
      change (d : ℕ∞) ≤ (J.weakTransform D).ord (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ z)
        at ih
      rw [h] at ih
      exact ih

/-- **A point of order `≥ d` of a weak transform lies over a point of order `≥ d` of `J`**, in the
setting of [Hir64, Corollary 1 to Main Theorem II] (by clause (ii) of Main Theorem II, all the
centers `D(i)` "are mapped into the closed subset `T − S`"); the general form is
`le_ord_stageMap_of_le_ord_weakTransformSeq_gen`. -/
theorem le_ord_stageMap_of_le_ord_weakTransformSeq (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (_hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    (S : BlowUpSequence X) (J : X.IdealSheafData) (d : ℕ)
    (hii : ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
      (d : ℕ∞) ≤ (S.weakTransformSeq J i.castSucc).ord x)
    (i : Fin (S.length + 1)) (z : S.stage i) (hz : (d : ℕ∞) ≤ (S.weakTransformSeq J i).ord z) :
    (d : ℕ∞) ≤ J.ord (S.stageMap i z) :=
  le_ord_stageMap_of_le_ord_weakTransformSeq_gen S J d hii i z hz

end Hironaka.Sequence
