/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.FiniteSuccession.Cons
import Hironaka.Manifold.BlowUp.Transform.Bundled
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Sequences of order `m` and of order `≥ m`: constructor lemmas and the two recursions

A smooth blow-up sequence of order `m` is defined by the recursion (1) `I_{i+1} := (π_i)^{-1}_* I_i`
(the birational transform [Kol07, Definition 48]) with the clauses (3) `Z_i` has normal crossings
with `E_i` and (4) `ord_{Z_i} I_i = m`, and a sequence of order `≥ m` by the marked recursion (1′)
`(I_{i+1}, m) := (π_i)^{-1}_*(I_i, m)` [Kol07, Definition 60] with (4′) `ord_{Z_i} I_i ≥ m`
[Kol07, Definition 66]. This module proves, for `IsOfOrder` and `IsOfOrderGe`:

* **The empty sequence** satisfies both notions vacuously (`isOfOrder_nil`, `isOfOrderGe_nil`).
* **The constructor form** `cons ψ hY rest`: the clauses at the first step are the clauses of
  the head (the centre `Y = cosupp I_Y`, the boundary `E_0 = E₀` and the ideal `I_0 = I`,
  definitionally), and the clauses at the later steps are those of `rest` for the induced data.
  The induced boundary `E_1 = (π_0)^{-1}_{tot} E₀` is the reduced transform `reducedTransform` by
  the first blow-down (`cons_boundarySeq_succ`), the induced ideal `I_1 = (π_0)^{-1}_* I` is the
  weak transform `weakTransform` (`cons_weakTransformSeq_succ`), and the induced marked ideal
  `(I_1, m)` is the sequence's own first marked transform (`cons_markedTransformSeqAux_succ`;
  `birationalTransform` runs at the witnesses chosen from `isMonoidal`, so the constructor form
  names it through the recursion itself). Each recursion lemma is an induction on the stage,
  `rfl` at every step because `cons` puts the head before the fields of `rest` by `Fin.cases`
  over `finStages`.
* **The projections** of the two clauses (`hasOnlyNormalCrossingsWith`, `ordAlong_eq`,
  `le_ordAlong`).
* **The comparison of the recursions** (Kollár's "we pretend that `ord_Z I = m`" of
  [Kol07, Definition 60]): along a sequence of order `m`, the marked transforms `(I_i, m)` are the
  birational transforms `I_i` (`markedTransformSeq_eq_weakTransformSeq`). At each step both are
  characterized by their colon stalks `(π^*I_i)_{a'} : I_{F,a'}^{e(a')}` (`IsDivExceptional`):
  the marked transform divides by `I_F^m` everywhere, the weak transform by `I_F^{ν}` with `ν` the
  generic order of `I_i` along the component of `Z_i` under the point. Clause (4) makes `ν = m`
  over the centre; off the exceptional divisor `I_F` is the unit ideal and any exponent gives the
  same colon. The two ideal sheaves therefore satisfy the same stalkwise characterization and
  coincide (`IsDivExceptional.unique`); this one-blowing-up comparison is
  `birationalTransform_eq_weakTransformOf_of_ordAlong_eq` of `BlowUp/Transform/MarkedWeak.lean`,
  while `IsDivExceptional.congr_exponent` below records the exponent observation on its own and is
  not used. Hence a sequence of order
  `m` is a sequence of order `≥ m` (`IsOfOrder.isOfOrderGe`), the reading Kollár uses in the proof
  of [Kol07, Theorem 80]; the algebraic counterpart is `IsOrderSeq.isOrderGeSeq`.
-/

public section

noncomputable section

open TopologicalSpace Opposite Manifold Topology
open scoped Manifold ContDiff

universe u

namespace Manifold.IdealSheaf

variable {X : TopCat} {𝒪 : TopCat.Sheaf CommRingCat X}

/-- The exponent of `IsDivExceptional` matters only on the cosupport of `I_F`: off it the stalk of
`I_F` is the unit ideal, whose powers are all the unit ideal, so every exponent gives the same
colon stalk. Not in the sources. It records the observation behind the comparison of the two
recursions, which the proof below obtains from
`birationalTransform_eq_weakTransformOf_of_ordAlong_eq` of `BlowUp/Transform/MarkedWeak.lean`;
this lemma itself is not used. -/
theorem IsDivExceptional.congr_exponent {Itot IF J' : IdealSheaf 𝒪} {e₁ e₂ : X → ℕ}
    (he : ∀ a ∈ IF.support, e₁ a = e₂ a) (h : IdealSheaf.IsDivExceptional Itot IF e₁ J') :
    IdealSheaf.IsDivExceptional Itot IF e₂ J' := by
  intro a
  rw [h a]
  by_cases ha : a ∈ IF.support
  · rw [he a ha]
  · have htop : IF.stalkIdeal a = ⊤ := not_not.mp ha
    rw [htop, Ideal.top_pow, Ideal.top_pow]

end Manifold.IdealSheaf

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}

/-! ### The recursions of the boundary and of the marked transforms on `cons` -/

/-- The boundary recursion `E_{i+1} = (π_i)^{-1}_{tot} E_i` [Kol07, Definition 66 (1)] on the
constructor form: the boundaries of `cons ψ hY rest` after the first step are those of `rest`
starting from the reduced transform of `E₀` by the blow-down with centre `I_Y`. -/
theorem cons_boundarySeqAux_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (E₀ : IdealSheaf M) :
    ∀ (k : ℕ) (h : k + 1 < (cons ψ hY rest).length + 1),
      (cons ψ hY rest).boundarySeqAux E₀ (k + 1) h =
        rest.boundarySeqAux (IdealSheaf.reducedTransform (blowUpπ ψ hY) E₀ hY.idealSheaf) k
          (Nat.lt_of_succ_lt_succ h)
  | 0, _ => rfl
  | k + 1, h => by
    change IdealSheaf.reducedTransform ((cons ψ hY rest).map ⟨k + 1,
        _⟩) ((cons ψ hY rest).boundarySeqAux E₀ (k + 1)
        (Nat.lt_of_succ_lt h)) ((cons ψ hY rest).center ⟨k + 1, _⟩) = _
    rw [cons_boundarySeqAux_succ hY rest E₀ k (Nat.lt_of_succ_lt h)]
    rfl

/-- The boundary recursion on `cons`, indexed by `Fin`. -/
theorem cons_boundarySeq_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (E₀ : IdealSheaf M) (j : Fin (rest.length + 1)) :
    (cons ψ hY rest).boundarySeq E₀ j.succ =
      rest.boundarySeq (IdealSheaf.reducedTransform (blowUpπ ψ hY) E₀ hY.idealSheaf) j :=
  cons_boundarySeqAux_succ hY rest E₀ j.1 j.succ.2

/-- The marked recursion [Kol07, Definition 66 (1′)] on the constructor form: the marked transforms
of `cons ψ hY rest` after the first step are those of `rest` starting from the first marked
transform of the whole sequence (`birationalTransform` at the witnesses chosen from
`isMonoidal`). -/
theorem cons_markedTransformSeqAux_succ (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) (m : ℕ) :
    ∀ (k : ℕ) (h : k + 1 < (cons ψ hY rest).length + 1),
      (cons ψ hY rest).markedTransformSeqAux J m (k + 1) h =
        rest.markedTransformSeqAux
          ((cons ψ hY rest).markedTransformSeqAux J m 1 (Nat.succ_lt_succ (Nat.succ_pos _))) m k
          (Nat.lt_of_succ_lt_succ h)
  | 0, _ => rfl
  | k + 1, h => by
    change (MarkedIdealSheaf.birationalTransform
      ((cons ψ hY rest).isClosedSubmanifold_center ⟨k + 1, _⟩)
      ((cons ψ hY rest).isBlowUp_map ⟨k + 1, _⟩)
      ⟨(cons ψ hY rest).markedTransformSeqAux J m (k + 1) (Nat.lt_of_succ_lt h), m⟩).I = _
    rw [cons_markedTransformSeqAux_succ hY rest J m k (Nat.lt_of_succ_lt h)]
    rfl

/-- The boundary at the stage `i + 1` of `cons ψ hY rest`, indexed as the clause of `IsOfOrder`
indexes it. -/
theorem cons_boundarySeq_succ_castSucc (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (E₀ : IdealSheaf M) (i : Fin rest.length) :
    (cons ψ hY rest).boundarySeq E₀ i.succ.castSucc =
      rest.boundarySeq (IdealSheaf.reducedTransform (blowUpπ ψ hY) E₀ hY.idealSheaf) i.castSucc :=
  cons_boundarySeqAux_succ hY rest E₀ i.1 i.succ.castSucc.2

/-- The weak transform at the stage `i + 1` of `cons ψ hY rest` (`cons_weakTransformSeq_succ`),
indexed as the clause of `IsOfOrder` indexes it. -/
theorem cons_weakTransformSeq_succ_castSucc (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (I : IdealSheaf M) (i : Fin rest.length) :
    (cons ψ hY rest).weakTransformSeq I i.succ.castSucc =
      rest.weakTransformSeq (IdealSheaf.weakTransform (blowUpπ ψ hY) I hY.idealSheaf) i.castSucc :=
  cons_weakTransformSeqAux_succ hY rest I i.1 i.succ.castSucc.2

/-- The marked transform at the stage `i + 1` of `cons ψ hY rest`, indexed as the clause of
`IsOfOrderGe` indexes it. -/
theorem cons_markedTransformSeq_succ_castSucc (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (I : IdealSheaf M) (m : ℕ) (i : Fin rest.length) :
    (cons ψ hY rest).markedTransformSeq I m i.succ.castSucc =
      rest.markedTransformSeq
        ((cons ψ hY rest).markedTransformSeq I m (Fin.succ (0 : Fin (rest.length + 1)))) m
        i.castSucc :=
  cons_markedTransformSeqAux_succ hY rest I m i.1 i.succ.castSucc.2

/-! ### The empty sequence, the constructor form, the projections -/

variable (S : FiniteSuccession M) (I E₀ : IdealSheaf M) (m : ℕ)

/-- The empty sequence is of order `m` for every `(M, I, E₀)`: there is no step to check
[Kol07, Definition 66]. -/
theorem isOfOrder_nil : (nil M).IsOfOrder I E₀ m := fun i => i.elim0

/-- The empty sequence is of order `≥ m` for every `(M, I, m, E₀)` [Kol07, Definition 66]. -/
theorem isOfOrderGe_nil : (nil M).IsOfOrderGe I m E₀ := fun i => i.elim0

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M} {I E₀ : IdealSheaf M} {m : ℕ}

/-- The normal-crossings clause [Kol07, Definition 66 (3)]. -/
theorem IsOfOrder.hasOnlyNormalCrossingsWith (h : S.IsOfOrder I E₀ m) (i : Fin S.length) :
    (S.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith (S.center i) := (h i).1

/-- The order clause [Kol07, Definition 66 (4)]. -/
theorem IsOfOrder.ordAlong_eq (h : S.IsOfOrder I E₀ m) (i : Fin S.length)
    {a : S.stage i.castSucc} (ha : a ∈ (S.center i).support) :
    IdealSheaf.ordAlongIdeal (S.center i) (S.weakTransformSeq I i.castSucc) a = (m : ℕ∞) :=
  (h i).2 a ha

/-- The normal-crossings clause [Kol07, Definition 66 (3′)]. -/
theorem IsOfOrderGe.hasOnlyNormalCrossingsWith (h : S.IsOfOrderGe I m E₀) (i : Fin S.length) :
    (S.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith (S.center i) := (h i).1

/-- The order clause [Kol07, Definition 66 (4′)]. -/
theorem IsOfOrderGe.le_ordAlong (h : S.IsOfOrderGe I m E₀) (i : Fin S.length)
    {a : S.stage i.castSucc} (ha : a ∈ (S.center i).support) :
    (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i) (S.markedTransformSeq I m i.castSucc) a :=
  (h i).2 a ha

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
  (I E₀ : IdealSheaf M) (m : ℕ)

/-- [Kol07, Definition 66 (1)–(4)] on the constructor form: `cons ψ hY rest` is of order `m` for
`(M, I, E₀)` iff the head clauses hold at the first centre `Y` and `rest` is of order `m` for the
induced data `((π_0)^{-1}_* I, (π_0)^{-1}_{tot} E₀)`. The first step's clauses are those at index
`0` (definitional, with `cosupp I_Y = Y`); the later steps' clauses are transported by the three
recursion lemmas above. -/
theorem isOfOrder_cons_iff (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) :
    (cons ψ hY rest).IsOfOrder I E₀ m ↔
      (E₀.HasOnlyNormalCrossingsWith hY.idealSheaf ∧
          ∀ a ∈ Y, IdealSheaf.ordAlongIdeal hY.idealSheaf I a = (m : ℕ∞)) ∧
        rest.IsOfOrder
            (IdealSheaf.weakTransform (blowUpπ ψ hY) I hY.idealSheaf)
          (IdealSheaf.reducedTransform (blowUpπ ψ hY) E₀ hY.idealSheaf) m := by
  refine Iff.trans (Fin.forall_fin_succ (P := fun i : Fin (rest.length + 1) =>
      ((cons ψ hY rest).boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith
        ((cons ψ hY rest).center i) ∧
      ∀ a ∈ ((cons ψ hY rest).center i).support,
        IdealSheaf.ordAlongIdeal ((cons ψ hY rest).center i)
          ((cons ψ hY rest).weakTransformSeq I i.castSucc) a = (m : ℕ∞)))
    (and_congr ?_ (forall_congr' fun i => ?_))
  · change (E₀.HasOnlyNormalCrossingsWith hY.idealSheaf ∧
      ∀ a ∈ hY.idealSheaf.support, IdealSheaf.ordAlongIdeal hY.idealSheaf I a = (m : ℕ∞)) ↔ _
    rw [hY.cosupport_idealSheaf]
  · simp only [cons_center_succ, cons_boundarySeq_succ_castSucc,
      cons_weakTransformSeq_succ_castSucc]
    exact Iff.rfl

/-- [Kol07, Definition 66 (1′)–(4′)] on the constructor form: `cons ψ hY rest` is of order `≥ m`
for `(M, I, m, E₀)` iff the head clauses hold at `Y` and `rest` is of order `≥ m` for the induced
marked data, the marked transform of the head being written through the sequence's own recursion
(since `birationalTransform` runs at the witnesses chosen from `isMonoidal`). -/
theorem isOfOrderGe_cons_iff (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) :
    (cons ψ hY rest).IsOfOrderGe I m E₀ ↔
      (E₀.HasOnlyNormalCrossingsWith hY.idealSheaf ∧
          ∀ a ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) ∧
        rest.IsOfOrderGe
          ((cons ψ hY rest).markedTransformSeq I m (Fin.succ (0 : Fin (rest.length + 1)))) m
          (IdealSheaf.reducedTransform (blowUpπ ψ hY) E₀ hY.idealSheaf) := by
  refine Iff.trans (Fin.forall_fin_succ (P := fun i : Fin (rest.length + 1) =>
      ((cons ψ hY rest).boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith
        ((cons ψ hY rest).center i) ∧
      ∀ a ∈ ((cons ψ hY rest).center i).support,
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal ((cons ψ hY rest).center i)
          ((cons ψ hY rest).markedTransformSeq I m i.castSucc) a))
    (and_congr ?_ (forall_congr' fun i => ?_))
  · change (E₀.HasOnlyNormalCrossingsWith hY.idealSheaf ∧
      ∀ a ∈ hY.idealSheaf.support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf I a) ↔ _
    rw [hY.cosupport_idealSheaf]
  · simp only [cons_center_succ, cons_boundarySeq_succ_castSucc,
      cons_markedTransformSeq_succ_castSucc]
    exact Iff.rfl

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M} {I E₀ : IdealSheaf M} {m : ℕ}

/-! ### The two recursions agree along a sequence of order `m` -/

/-- Along a sequence of order `m` the marked transforms `(I_i, m)` are the birational transforms
`I_i` (Kollár's "we pretend that `ord_Z I = m`" [Kol07, Definition 60], with the birational
transform of [Kol07, Definition 48] along the two recursions of [Kol07, Definition 66]). Induction
on the stage: at a step both transforms are the ideal sheaf with colon stalks `(π^*I_i : I_F^{e})`,
with the constant exponent `m` for the marked transform (which needs `m ≤ ord_{Z_i} I_i`, clause
(4)) and the generic order along the centre for the weak transform, which is `m` over the centre
by clause (4) and irrelevant off the exceptional divisor; the colon characterization determines
the ideal sheaf. -/
theorem IsOfOrder.markedTransformSeq_eq_weakTransformSeq (h : S.IsOfOrder I E₀ m)
    (i : Fin (S.length + 1)) : S.markedTransformSeq I m i = S.weakTransformSeq I i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [markedTransformSeq_succ, weakTransformSeq_succ, ih,
      weakTransform_eq (S.map i) (S.isClosedSubmanifold_center i) (S.isIdealSheafOf_center i)
        (S.isBlowUp_map i)]
    exact birationalTransform_eq_weakTransformOf_of_ordAlong_eq (S.isClosedSubmanifold_center i)
      (S.isBlowUp_map i) _ fun a ha => by
        rw [S.idealSheaf_center i]
        exact (h i).2 a ha

/-- A sequence of order `m` is a sequence of order `≥ m`: the marked transforms are the birational
transforms, whose order along the centres is `m`. This is the reading of "a smooth blow-up
sequence of order `m` starting with `(X, I)`" as a sequence of order `≥ m` starting with
`(X, I, m)` used in the proof of [Kol07, Theorem 80]; the algebraic counterpart is
`IsOrderSeq.isOrderGeSeq`. -/
theorem IsOfOrder.isOfOrderGe (h : S.IsOfOrder I E₀ m) : S.IsOfOrderGe I m E₀ := fun i =>
  ⟨(h i).1, fun a ha => by
    rw [h.markedTransformSeq_eq_weakTransformSeq]
    exact ((h i).2 a ha).ge⟩

end AnalyticManifold.FiniteSuccession

end
