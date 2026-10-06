/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalMonomial
import Hironaka.Resolution.Algebraic.Kol07.MarkedProduct
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The marked transform of a product

The marked transform `(π_j)_*^{-1}(J, m)` divides `F^m` out of the total transform `π_j^* J`
[Kol07, Definition 60]. When the sequence has order `≥ m` for `(J, m)`, so that `F_j^m` divides
the pull-back of the marked transform at every step, the marked transform of a product `J · K` is
the marked transform of `J` times the plain pull-back of `K`: the one exceptional factor `F^m` is
taken from the pull-back of `J`, and the colon by the invertible `F^m` cancels it exactly
(`colon_pow_eq_of_mul_eq`). The proof of [Wlo05, Theorem 4.7.1] uses this when the strict
transforms of some components of the subvariety are isolated and ignored by the rest of the
resolution: the marked ideal `I' · I_Γ` transforms as the marked transform of `I'` times the
pull-back of the ideal of the isolated components.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The marked transform of [Kol07, Definition 60] for a product: along a sequence whose every
step has `F_j^m ∣ π_j^*(J_j)`, the marked transform of `J · K` at stage `j` is the marked transform
of `J` times the pull-back of `K` to stage `j`, in the `⟨j, h⟩` form of the indices. -/
theorem markedTransformSeq_mul_comap_mk (S : BlowUpSequence X) (J K : X.IdealSheafData) (m : ℕ)
    (h : ∀ i : Fin S.length,
      S.exceptionalAt i ^ m ∣ (S.markedTransformSeq J m i.castSucc).comap (S.step i)) :
    ∀ (j : ℕ) (hj : j < S.length + 1),
      S.markedTransformSeq (J * K) m ⟨j, hj⟩ =
        S.markedTransformSeq J m ⟨j, hj⟩ * K.comap (S.stageMap ⟨j, hj⟩)
  | 0, hj => by
    cases S with
    | nil _ =>
      change J * K = J * K.comap (𝟙 _)
      rw [IdealSheafData.comap_id]
    | cons _ _ _ =>
      change J * K = J * K.comap (𝟙 _)
      rw [IdealSheafData.comap_id]
  | j + 1, hj => by
    have hj' : j < S.length := Nat.lt_of_succ_lt_succ hj
    have ih := markedTransformSeq_mul_comap_mk S J K m h j (Nat.lt_succ_of_lt hj')
    have hmul : S.exceptionalAt ⟨j, hj'⟩ ^ m *
        S.markedTransformSeq J m (Fin.succ (⟨j, hj'⟩ : Fin S.length)) =
        (S.markedTransformSeq J m ⟨j, Nat.lt_succ_of_lt hj'⟩).comap (S.step ⟨j, hj'⟩) :=
      exceptionalAt_pow_mul_markedTransformSeq_succ S J m ⟨j, hj'⟩ (h ⟨j, hj'⟩)
    rw [markedTransformSeq_mk_succ (I := J * K), ih, stageMap_mk_succ S j hj']
    change ((S.markedTransformSeq J m ⟨j, _⟩ * K.comap (S.stageMap ⟨j, _⟩)).comap
        (S.step ⟨j, hj'⟩)).colon (S.exceptionalAt ⟨j, hj'⟩ ^ m) = _
    rw [IdealSheafData.comap_mul, ← IdealSheafData.comap_comp, ← hmul, mul_assoc]
    exact IdealSheafData.colon_pow_eq_of_mul_eq _ (isInvertible_exceptionalAt S ⟨j, hj'⟩) m _ rfl

/-- `markedTransformSeq_mul_comap_mk` at an arbitrary stage index. -/
theorem markedTransformSeq_mul_comap (S : BlowUpSequence X) (J K : X.IdealSheafData) (m : ℕ)
    (h : ∀ i : Fin S.length,
      S.exceptionalAt i ^ m ∣ (S.markedTransformSeq J m i.castSucc).comap (S.step i))
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq (J * K) m i =
      S.markedTransformSeq J m i * K.comap (S.stageMap i) := by
  obtain ⟨j, hj⟩ := i
  exact markedTransformSeq_mul_comap_mk S J K m h j hj

/-- The divisibility hypothesis of `markedTransformSeq_mul_comap` holds along a smooth blow-up
sequence of order `≥ m` for `(J, m)` [Kol07, Definition 66]
(`exceptionalAt_pow_dvd_comap_step_of_leOrdAlong`). -/
theorem exceptionalAt_pow_dvd_comap_step_of_isOrderGeSeq {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (S : BlowUpSequence X) (J : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (hS : S.IsOrderGeSeq f J m E) (i : Fin S.length) :
    S.exceptionalAt i ^ m ∣ (S.markedTransformSeq J m i.castSucc).comap (S.step i) :=
  exceptionalAt_pow_dvd_comap_step_of_leOrdAlong f n S hS.1 i _ (hS.2 i).2

/-- Along a smooth blow-up sequence of order `≥ m` for `(J, m)`, the marked transform of `J · K`
at the end is the marked transform of `J` times the pull-back of `K` along the composite
[Kol07, Definition 60]. -/
theorem markedTransformSeq_mul_comap_last_of_isOrderGeSeq {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (S : BlowUpSequence X) (J K : X.IdealSheafData) (m : ℕ)
    (E : DivisorFamily X) (hS : S.IsOrderGeSeq f J m E) :
    S.markedTransformSeq (J * K) m (Fin.last _) =
      S.markedTransformSeq J m (Fin.last _) * K.comap (S.stageMap (Fin.last _)) :=
  markedTransformSeq_mul_comap S J K m
    (exceptionalAt_pow_dvd_comap_step_of_isOrderGeSeq f n S J m E hS) (Fin.last _)

end Hironaka.Sequence
