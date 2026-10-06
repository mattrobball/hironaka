/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.Resolution.Analytic.Principalization.Assembly
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Bundled
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFunctor
import Hironaka.Resolution.Analytic.Wlo09.EmptyRound
import Hironaka.Resolution.Analytic.Wlo09.Monomial
import Hironaka.Resolution.Analytic.Wlo09.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Hironaka's clauses (i)–(iv) on the resolution family

The dictionary between Kollár's smooth blow-up sequence of order `≥ m` for a marked ideal ([Kol07,
Definition 66]; the field `isOfOrderGe` of `BOanFam`, on the marked transforms) and the clauses
(i)–(iv) of Hironaka's Main Theorem II′(N) [Hir64, p. 156] on the value `resolveSeqOn bo T U hU` of
the resolution family (`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`): the rounds
`BO_{n,d}, …, BO_{n,1}` of [Hir64, Main Theorem II(N), p. 176] with the empty blow-ups erased.

## The dictionary on one round

* `BOanFam.isOfOrder_seqOn`: the value of `B : BOanFam 𝕜 n m` on a triple of its class over a
  relatively compact open is a sequence of order exactly `m` on the weak transforms
  (`isOfOrder_of_isOfOrderGe_of_ord_le`; [Kol07, Remark 67]: along a sequence of order `≥ m`
  starting with `max-ord I = m`, every blow-up has order exactly `m`);
  `BOanFam.markedTransformSeq_seqOn_eq_weakTransformSeq`: along the round the marked transform is
  the weak transform (Kollár's birational transform of `(I, m)` when `ord_Z I = m`,
  [Kol07, Definition 48]; Hironaka's weak transform, [Hir64, p. 142]);
  `BOanFam.ord_weakTransformSeq_seqOn_eq_of_mem_center`: the order of the weak transform is `m`
  at every point of every centre (clause (2) of [Hir64, Main Theorem II(N), p. 176]).
* `FiniteSuccession.IsOfOrder.ord_weakTransformSeq_eq_of_mem_center` (the pointwise form on any
  succession: `≥` from the order along the centre, `≤` from [Kol07, Lemma 61] iterated) and
  `FiniteSuccession.center_isNonsingular` (clause (i): every centre is the ideal sheaf of a closed
  submanifold, hence non-singular).

## Clause (ii) in Hironaka's weak spelling

* `FiniteSuccession.HasConstantPositiveOrderAlongCenters S J`
  (`Hironaka/Manifold/Resolution/Defs.lean`): at every stage the order of the weak transform of `J`
  is a positive constant on the centre, clause (ii) as a predicate;
  `hasConstantPositiveOrderAlongCenters_nil`, `hasConstantPositiveOrderAlongCenters_cons_iff`,
  `IsOfOrder.hasConstantPositiveOrderAlongCenters` (a round satisfies it with the constant `m`),
  and the transports along a concatenation, a pull-back along any local analytic isomorphism (the
  weak transform's exponent is the generic order along the component through the point, which a
  local isomorphism preserves; no surjectivity is needed), a diffeomorphism and the deletion of the
  empty blow-ups (`hasConstantPositiveOrderAlongCenters_{concat,pullback,map,eraseEmpty}`).
* `hasConstantPositiveOrderAlongCenters_resolveFrom`, the invariant of the recursion `resolveFrom`
  (on the pattern of `centersOver_resolveFrom`,
  `Hironaka/Resolution/Analytic/Wlo09/CentersOver.lean`): the round pulled back along the
  corestriction of `ι`, the junction identity (the head's last weak transform of `ι^* 𝓘` is the
  pull-back along `pullbackLiftLast` of the derived ideal, the weak transform being the marked
  transform at the round's mark) and the induction hypothesis on the derived triple;
  `hasConstantPositiveOrderAlongCenters_resolveSeqOn` at the canonical chain, through the
  erasure.

## Clauses (iii) and (iv)

* Clause (iii) is the first conjunct of `isOfOrderGe_zero_resolveSeqOn`
  (`Hironaka/Resolution/Analytic/Wlo09/Monomial.lean`, clause (3′) of [Kol07, Definition 66] for the
  erased value) read through the identification `restrictTriple_F_idealSheaf` of the restricted
  triple's boundary ideal sheaf (`idealSheaf_comap_of_isSnc` at the inclusion);
  `center_resolveSeqOn_hasSncWith` is its family form, a corollary through
  `hasSncWith_totalTransformSeqFrom_center_of_forall_lt`.
* The first half of clause (iv):
  `FiniteSuccession.hasOnlyNormalCrossings_boundarySeq_last_of_isOfOrderGe_zero` (along a
  sequence of order `≥ 0` for `(I, 0, red F)` with `F` a simple normal crossing family, the last
  boundary has only normal crossings: `isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt`
  then `hasOnlyNormalCrossings_idealSheaf`), at `isOfOrderGe_zero_resolveSeqOn`. Hironaka remarks
  that this half follows from (iii) (the remark after [Hir64, Main Theorem II, p. 143]).
* The second half of clause (iv): `weakTransformSeq_last_eq_top_{concat,pullback,eraseEmpty}`
  (the transports of the statement that the last weak transform is the unit ideal),
  `weakTransformSeq_last_resolveFrom_eq_top` (the exit of the recursion in the weak spelling: at
  `d = 0` the list is empty and `cur.I = ⊤` from `ord ≤ 0`; clause (1) of [Kol07, Theorem 68] at
  the last round's mark `1`) and `weakTransformSeq_last_resolveSeqOn_eq_top`.

## Restatements

The last section restates the clauses under the names `resolveSeqOn_clause_ii`,
`resolveSeqOn_clause_iii` and `resolveSeqOn_boundarySeq_last_hasOnlyNormalCrossings`. Each docstring
says which theorem it restates and how the predicate is unfolded;
`Hironaka/Resolution/Analytic/Wlo09/HironakaAssembly.lean` uses `resolveSeqOn_clause_ii`, and the
other two are not used elsewhere.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E}

/-- The empty succession satisfies clause (ii). -/
theorem hasConstantPositiveOrderAlongCenters_nil (J : IdealSheaf M) :
    (nil M).HasConstantPositiveOrderAlongCenters J := fun i => i.elim0

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {Y : Set M} {c : ℕ}

/-- The constructor form (the analogue of `isOfOrderGe_cons_iff`): the head clause on `Y` for `J`
and the tail for the weak transform of `J` along the head. -/
theorem hasConstantPositiveOrderAlongCenters_cons_iff (hY : IsClosedSubmanifold ψ Y c)
    (rest : FiniteSuccession (blowUp ψ hY)) (J : IdealSheaf M) :
    (cons ψ hY rest).HasConstantPositiveOrderAlongCenters J ↔
      (∃ c' : ℕ, 0 < c' ∧ ∀ y ∈ Y, J.ord y = c') ∧
        rest.HasConstantPositiveOrderAlongCenters
          (IdealSheaf.weakTransform (blowUpπ ψ hY) J hY.idealSheaf) := by
  refine Iff.trans (Fin.forall_fin_succ (P := fun i : Fin (rest.length + 1) =>
      ∃ c' : ℕ, 0 < c' ∧ ∀ y ∈ ((cons ψ hY rest).center i).support,
        ((cons ψ hY rest).weakTransformSeq J i.castSucc).ord y = c'))
    (and_congr ?_ (forall_congr' fun i => ?_))
  · change (∃ c' : ℕ, 0 < c' ∧ ∀ y ∈ hY.idealSheaf.support, J.ord y = c') ↔ _
    rw [hY.cosupport_idealSheaf]
  · simp only [cons_center_succ, cons_weakTransformSeq_succ_castSucc]
    exact Iff.rfl

/-- The pointwise form of the round dictionary: along a sequence of order exactly `m` with `ord I ≤
m` everywhere, the weak transform has order `m` at every point of every centre (`≥` from the order
along the centre, `≤` from [Kol07, Lemma 61] iterated). -/
theorem IsOfOrder.ord_weakTransformSeq_eq_of_mem_center {S : FiniteSuccession M}
    {I E₀ : IdealSheaf M} {m : ℕ} (h : S.IsOfOrder I E₀ m) (hI : ∀ y, I.ord y ≤ m)
    (i : Fin S.length) {y : S.stage i.castSucc}
    (hy : y ∈ (S.center i).support) : (S.weakTransformSeq I i.castSucc).ord y = m := by
  refine le_antisymm ?_ ?_
  · have h1 := ord_markedTransformSeq_le (B := S) h.isOfOrderGe hI i.castSucc y
    rwa [h.markedTransformSeq_eq_weakTransformSeq] at h1
  · rw [← h.ordAlong_eq i hy]
    exact Hironaka.Manifold.BMOmod.ordAlongIdeal_le_ord_of_mem_support _ _ hy

/-- The round dictionary on any succession: Hironaka's sequence of order exactly `m ≥ 1` with
`ord I ≤ m` everywhere satisfies clause (ii) with the constant `m` (`IsOfOrder.ordAlong_eq`,
`ordAlongIdeal_le_ord_of_mem_support`, `ord_markedTransformSeq_le` through
`IsOfOrder.markedTransformSeq_eq_weakTransformSeq`). -/
theorem IsOfOrder.hasConstantPositiveOrderAlongCenters
    {S : FiniteSuccession M} {I E₀ : IdealSheaf M} {m : ℕ} (h : S.IsOfOrder I E₀ m) (hm : 1 ≤ m)
    (hI : ∀ y, I.ord y ≤ m) : S.HasConstantPositiveOrderAlongCenters I := by
  exact fun i => ⟨m, hm, fun y hy => h.ord_weakTransformSeq_eq_of_mem_center hI i hy⟩

/-- Clause (i) of [Hir64, Main Theorem II′(N), p. 156]: every centre of a finite succession is
non-singular (`idealSheaf_center` and `isNonsingular_idealSheaf`). -/
theorem center_isNonsingular (S : FiniteSuccession M) (i : Fin S.length) :
    (S.center i).IsNonsingular := by
  rw [← S.idealSheaf_center i]
  exact isNonsingular_idealSheaf (S.chartAt i) (S.isClosedSubmanifold_center i)

/-- The first half of clause (iv) of [Hir64, Main Theorem II′(N), p. 156], in general form (Hironaka
remarks after Main Theorem II, p. 143, that it follows from (iii)): along a succession of order
`≥ 0` for `(I, 0, red F)` with `F` a simple normal crossing family, that is, under clause (3′) of
[Kol07, Definition 66] alone, the last boundary has only normal crossings
(`isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt` and
`hasOnlyNormalCrossings_idealSheaf`). -/
theorem hasOnlyNormalCrossings_boundarySeq_last_of_isOfOrderGe_zero (S : FiniteSuccession M)
    {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) {I : IdealSheaf M}
    (h : S.IsOfOrderGe I 0 F.idealSheaf) :
    (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) (Fin.last _)).HasOnlyNormalCrossings := by
  obtain ⟨hsnc, heq⟩ := isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt (S := S)
    (hF := hF) (i := Fin.last _) (h3 := fun i' _ => (h i').1)
  rw [heq]
  exact hasOnlyNormalCrossings_idealSheaf hsnc

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Clause (ii) along a concatenation (the analogue of `isOfOrderGe_concat`): the tail starts at the
head's last weak transform. -/
theorem hasConstantPositiveOrderAlongCenters_concat :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (J : IdealSheaf M),
    L.toSuccession.HasConstantPositiveOrderAlongCenters J →
    L'.toSuccession.HasConstantPositiveOrderAlongCenters
      (L.toSuccession.weakTransformSeq J (Fin.last _)) →
    (L.concat L').toSuccession.HasConstantPositiveOrderAlongCenters J := by
  intro M L L' J h h'
  induction L with
  | nil M => exact h'
  | cons hY rest ih =>
    rw [concat_cons, toSuccession_cons,
      FiniteSuccession.hasConstantPositiveOrderAlongCenters_cons_iff]
    rw [toSuccession_cons, FiniteSuccession.hasConstantPositiveOrderAlongCenters_cons_iff] at h
    refine ⟨h.1, ih L' _ h.2 ?_⟩
    have e1 : (cons hY rest).toSuccession.weakTransformSeq J (Fin.last _) =
        rest.toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) J hY.idealSheaf)
              (Fin.last _) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY rest.toSuccession J _ (Fin.last _).2
    rw [e1] at h'
    exact h'

/-- Clause (ii) pulls back along any local analytic isomorphism, surjective or not
(`center_pullback`, `weakTransformSeq_pullback`, `ord_comap_of_isLocalDiffeomorphAt` at the lifts).
-/
theorem hasConstantPositiveOrderAlongCenters_pullback
    {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (J : IdealSheaf M) (hL : L.toSuccession.HasConstantPositiveOrderAlongCenters J) :
    (L.pullback h hh).toSuccession.HasConstantPositiveOrderAlongCenters
        (J.pullback h h.contMDiff) := by
  have := finiteDimensional_of_chartIso ψ₀
  intro i
  have hi : i.1 < L.length := Nat.lt_of_lt_of_eq i.2 (length_pullback L h hh)
  obtain ⟨c, hc, hall⟩ := hL ⟨i.1, hi⟩
  refine ⟨c, hc, fun y hy => ?_⟩
  have hc' : (L.pullback h hh).toSuccession.center i =
      Manifold.IdealSheaf.pullback _ (L.pullbackLift h hh (⟨i.1, hi⟩ : Fin
          L.length).castSucc).contMDiff
        (L.toSuccession.center ⟨i.1, hi⟩) :=
    center_pullback L h hh ⟨i.1, hi⟩
  have hy' : L.pullbackLift h hh (⟨i.1, hi⟩ : Fin L.length).castSucc y ∈
      (L.toSuccession.center ⟨i.1, hi⟩).support := by
    rw [hc', IdealSheaf.support_pullback] at hy
    exact hy
  have hw :
      (L.pullback h hh).toSuccession.weakTransformSeq (J.pullback h h.contMDiff)
        i.castSucc =
      Manifold.IdealSheaf.pullback _ (L.pullbackLift h hh (⟨i.1, hi⟩ : Fin
          L.length).castSucc).contMDiff
        (L.toSuccession.weakTransformSeq J (⟨i.1, hi⟩ : Fin L.length).castSucc) :=
    weakTransformSeq_pullback L h hh J (⟨i.1, hi⟩ : Fin L.length).castSucc
  rw [hw, IdealSheaf.ord_comap_of_isLocalDiffeomorphAt
    (L.toSuccession.weakTransformSeq J (⟨i.1, hi⟩ : Fin L.length).castSucc)
    (L.pullbackLift h hh (⟨i.1, hi⟩ : Fin L.length).castSucc)
    (isLocalDiffeomorph_pullbackLift L h hh (⟨i.1, hi⟩ : Fin L.length).castSucc y)]
  exact hall _ hy'

/-- Clause (ii) transports along a diffeomorphism (`map_eq_pullback_symm`,
`hasConstantPositiveOrderAlongCenters_pullback`, `comap_comap_symm`). -/
theorem hasConstantPositiveOrderAlongCenters_map
    {M N : AnalyticManifold.{u} 𝕜 E} (φ : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    (Z : BlowUpSequence ψ₀ M) (J : IdealSheaf N)
    (h : Z.toSuccession.HasConstantPositiveOrderAlongCenters
      (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff)) :
    (Z.map φ).toSuccession.HasConstantPositiveOrderAlongCenters J := by
  have e : (J.pullback _ (Diffeomorph.toAnalyticMap φ).contMDiff).pullback _
      (Diffeomorph.toAnalyticMap φ.symm).contMDiff = J :=
    comap_comap_symm φ.symm J
  rw [map_eq_pullback_symm, ← e]
  exact hasConstantPositiveOrderAlongCenters_pullback Z _ _ _ h

/-- Clause (ii) survives the deletion of the empty blow-ups ([Kol07, 34.1]; the pattern of
`isOfOrderGe_eraseEmpty`: a kept step by `hasConstantPositiveOrderAlongCenters_cons_iff`, a
deleted step by `hasConstantPositiveOrderAlongCenters_map` along `emptyBlowUpDiffeomorph` with
`weakTransform_blowUpπ_of_eq_empty`).
No boundary is involved, so no simple-normal-crossings hypothesis. -/
theorem hasConstantPositiveOrderAlongCenters_eraseEmpty :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (J : IdealSheaf M),
    L.toSuccession.HasConstantPositiveOrderAlongCenters J →
      L.eraseEmpty.toSuccession.HasConstantPositiveOrderAlongCenters J := by
  intro M L J hL
  induction L with
  | nil M => exact FiniteSuccession.hasConstantPositiveOrderAlongCenters_nil J
  | @cons M Y c hY rest ih =>
    rw [toSuccession_cons, FiniteSuccession.hasConstantPositiveOrderAlongCenters_cons_iff] at hL
    obtain ⟨hhead, hrest⟩ := hL
    by_cases hY₀ : Y = ∅
    · rw [eraseEmpty_cons_of_eq_empty hY rest hY₀]
      refine hasConstantPositiveOrderAlongCenters_map (emptyBlowUpDiffeomorph hY hY₀)
        rest.eraseEmpty J ?_
      rw [toAnalyticMap_emptyBlowUpDiffeomorph hY hY₀, ← weakTransform_blowUpπ_of_eq_empty hY hY₀ J]
      exact ih _ hrest
    · rw [eraseEmpty_cons_of_ne_empty hY rest hY₀, toSuccession_cons,
        FiniteSuccession.hasConstantPositiveOrderAlongCenters_cons_iff]
      exact ⟨hhead, ih _ hrest⟩

/-- The last weak transform is the unit ideal along a concatenation, from the tail started at the
head's last weak transform (stated as a transport of the proposition, so no cast across
`stage_last_concat`). -/
theorem weakTransformSeq_last_eq_top_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _)))
        (J : IdealSheaf M),
    L'.toSuccession.weakTransformSeq (L.toSuccession.weakTransformSeq J (Fin.last _))
      (Fin.last _) = ⊤ →
    (L.concat L').toSuccession.weakTransformSeq J (Fin.last _) = ⊤ := by
  intro M L L' J h'
  induction L with
  | nil M => exact h'
  | cons hY rest ih =>
    rw [concat_cons]
    have e0 : (cons hY (rest.concat L')).toSuccession.weakTransformSeq J (Fin.last _) =
        (rest.concat L').toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) J hY.idealSheaf)
              (Fin.last _) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY (rest.concat L').toSuccession J _
        (Fin.last _).2
    rw [e0]
    refine ih L' _ ?_
    have e1 : (cons hY rest).toSuccession.weakTransformSeq J (Fin.last _) =
        rest.toSuccession.weakTransformSeq
          (IdealSheaf.weakTransform (blowUpπ ψ₀ hY) J hY.idealSheaf)
              (Fin.last _) :=
      FiniteSuccession.cons_weakTransformSeqAux_succ hY rest.toSuccession J _ (Fin.last _).2
    rw [e1] at h'
    exact h'

/-- The same along a pull-back (`weakTransformSeq_pullback` at the last stage, `comap ⊤ = ⊤`). -/
theorem weakTransformSeq_last_eq_top_pullback {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (J : IdealSheaf M)
    (hL : L.toSuccession.weakTransformSeq J (Fin.last _) = ⊤) :
    (L.pullback h hh).toSuccession.weakTransformSeq (J.pullback h h.contMDiff)
      (Fin.last _) = ⊤ := by
  have hi : (L.pullback h hh).length < L.length + 1 := by
    rw [length_pullback]; exact Nat.lt_succ_self _
  have h2 : L.toSuccession.weakTransformSeq J ⟨(L.pullback h hh).length, hi⟩ = ⊤ := by
    rw [show (⟨(L.pullback h hh).length, hi⟩ : Fin (L.length + 1)) = Fin.last _ from
      Fin.ext (length_pullback L h hh)]
    exact hL
  change (L.pullback h hh).toSuccession.weakTransformSeqAux
      (J.pullback h h.contMDiff)
    (L.pullback h hh).length (Nat.lt_succ_self _) = ⊤
  rw [weakTransformSeqAux_pullback L h hh J _ hi _]
  change (L.toSuccession.weakTransformSeq J ⟨_, hi⟩).pullback _ _ = ⊤
  rw [h2]
  exact IdealSheaf.pullback_top _ _

/-- The same after the deletion of the empty blow-ups (`weakTransformSeq_last_eraseEmpty`). -/
theorem weakTransformSeq_last_eq_top_eraseEmpty {M : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (J : IdealSheaf M)
    (hL : L.toSuccession.weakTransformSeq J (Fin.last _) = ⊤) :
    L.eraseEmpty.toSuccession.weakTransformSeq J (Fin.last _) = ⊤ := by
  rw [weakTransformSeq_last_eraseEmpty L J, hL]
  exact IdealSheaf.pullback_top _ _

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

section Round

variable {m : ℕ} (B : BOanFam.{u} 𝕜 n m) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
  (hT : AnalyticTriple.BOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The value of `B` on a triple of its class over a relatively compact open is a sequence of order
exactly `m` ([Kol07, Remark 67]): `isOfOrder_of_isOfOrderGe_of_ord_le` on the field `B.isOfOrderGe`
with the class bound restricted to `U` (`ord_comap_of_isLocalDiffeomorphAt`). -/
theorem BOanFam.isOfOrder_seqOn :
    ((B.functor.fam T hT).seqOn U hU).toSuccession.IsOfOrder
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf m := by
  refine FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ (B.isOfOrderGe T hT U hU) fun y => ?_
  change (T.I.pullback _ (M.inclusion U).contMDiff).ord y ≤ (m : ℕ∞)
  rw [IdealSheaf.ord_comap_of_isLocalDiffeomorphAt T.I (M.inclusion U)
    (isLocalDiffeomorph_inclusion M U y)]
  exact hT.2.1 _

/-- Along the value of `B` the marked transform at mark `m` is the weak transform: Kollár's
birational transform of `(I, m)` coincides with the unmarked one when `ord_Z I = m` ([Kol07,
Definition 48]), and that is Hironaka's weak transform ([Hir64, p. 142]). -/
theorem BOanFam.markedTransformSeq_seqOn_eq_weakTransformSeq
    (i : Fin (((B.functor.fam T hT).seqOn U hU).toSuccession.length + 1)) :
    ((B.functor.fam T hT).seqOn U hU).toSuccession.markedTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I m i =
      ((B.functor.fam T hT).seqOn U hU).toSuccession.weakTransformSeq
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i := by
  exact (BOanFam.isOfOrder_seqOn B T hT U hU).markedTransformSeq_eq_weakTransformSeq i

/-- Along the value of `B` the weak transform has order `m` at every point of every centre (clause
(2) of [Hir64, Main Theorem II(N), p. 176]). -/
theorem BOanFam.ord_weakTransformSeq_seqOn_eq_of_mem_center
    (i : Fin ((B.functor.fam T hT).seqOn U hU).toSuccession.length)
    {y : ((B.functor.fam T hT).seqOn U hU).toSuccession.stage i.castSucc}
    (hy : y ∈ (((B.functor.fam T hT).seqOn U hU).toSuccession.center i).support) :
    (((B.functor.fam T hT).seqOn U hU).toSuccession.weakTransformSeq
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i.castSucc).ord y = m := by
  refine (BOanFam.isOfOrder_seqOn B T hT U hU).ord_weakTransformSeq_eq_of_mem_center
    (fun z => ?_) i hy
  change (T.I.pullback _ (M.inclusion U).contMDiff).ord z ≤ (m : ℕ∞)
  rw [IdealSheaf.ord_comap_of_isLocalDiffeomorphAt T.I (M.inclusion U)
    (isLocalDiffeomorph_inclusion M U z)]
  exact hT.2.1 _

/-- The restricted triple's boundary ideal sheaf is the restriction of the boundary ideal sheaf
(`HypersurfaceFamily.idealSheaf_comap_of_isSnc` at the inclusion). -/
theorem restrictTriple_F_idealSheaf :
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf =
      IdealSheaf.restrict T.F.idealSheaf U := by
  exact HypersurfaceFamily.idealSheaf_comap_of_isSnc (M.inclusion U)
    (isLocalDiffeomorph_inclusion M U) T.isSnc

end Round

section Value

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- The invariant of the recursion `resolveFrom` for clause (ii) ([Hir64, Main Theorem II′(N),
p. 156, (ii)] round by round, on the pattern of `centersOver_resolveFrom`): the round pulled back
along the corestriction of `ι` by `hasConstantPositiveOrderAlongCenters_pullback` and
`IsOfOrder.hasConstantPositiveOrderAlongCenters` (`AnalyticTriple.isOfOrderGe_pullback`,
`isOfOrder_of_isOfOrderGe_of_ord_le` with the class bound transported), the tail by the induction
hypothesis on the derived triple with the junction identity (the head's last weak transform of
`ι^* cur.I` is the pull-back along `pullbackLiftLast` of the derived ideal:
`markedTransformSeq_seqOn_eq_weakTransformSeq` at the round,
`markedTransformSeq_last_pullbackLiftLast`), glued by
`hasConstantPositiveOrderAlongCenters_concat`. -/
theorem hasConstantPositiveOrderAlongCenters_resolveFrom :
    ∀ (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
      (hrange : Set.range ι ⊆ Ω 0),
      FiniteSuccession.HasConstantPositiveOrderAlongCenters
        (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).toSuccession
        (cur.I.pullback ι ι.contMDiff) := by
  intro d
  induction d with
  | zero => intro X cur hord hfin Ω hΩ hΩsub N ι hι hrange i; exact i.elim0
  | succ d ih =>
    intro X cur hord hfin Ω hΩ hΩsub N ι hι hrange
    have hgeA := AnalyticTriple.isOfOrderGe_pullback _ (d + 1)
      (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
      ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
      (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
      (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
    have hI :
        Manifold.IdealSheaf.pullback _ (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub
        hrange)).contMDiff
        (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).I =
            cur.I.pullback ι ι.contMDiff := by
      change (cur.I.pullback _ (X.inclusion (Ω d)).contMDiff).pullback _ (AnalyticMap.corestrict ι
          (Ω d) (range_subset_chain hΩsub hrange)).contMDiff = cur.I.pullback ι
            ι.contMDiff
      rw [IdealSheaf.pullback_comp]
      exact congrArg (fun f : AnalyticMap _ _ => cur.I.pullback f f.contMDiff)
          (ContMDiffMap.ext fun _ => rfl)
    have hgeA' : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
        (Nat.lt_succ_self d))).pullback (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub
        hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub
            hrange))).toSuccession.IsOfOrderGe (cur.I.pullback ι ι.contMDiff)
                (d + 1)
        ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub
              hrange))).F.idealSheaf := by
      rw [← hI]
      exact hgeA
    have hbound : ∀ y, (cur.I.pullback ι ι.contMDiff).ord y ≤
        ((d + 1 : ℕ) : ℕ∞) := fun y =>
        by
      rw [IdealSheaf.ord_comap_of_isLocalDiffeomorphAt cur.I ι (hι y)]
      exact hord _
    have hordA := FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ hgeA' hbound
    have hhead := hordA.hasConstantPositiveOrderAlongCenters (Nat.succ_pos d) hbound
    have eM := BlowUpSequence.markedTransformSeq_last_pullbackLiftLast
      (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
          (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
      (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).I (cur.pullback
          (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).F.idealSheaf (d + 1)
      ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
    rw [hI] at eM
    have hj : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
        (Nat.lt_succ_self d))).pullback (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub
        hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub
            hrange))).toSuccession.weakTransformSeq (cur.I.pullback ι ι.contMDiff)
                (Fin.last
            _) =
        (derivedTriple bo cur (boClass_succ_of_ord_le cur
            hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d))).I.pullback _ ((roundList bo cur
                (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast (AnalyticMap.corestrict ι (Ω d)
            (range_subset_chain hΩsub hrange)) (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).contMDiff := by
      rw [← hordA.markedTransformSeq_eq_weakTransformSeq (Fin.last _)]
      exact eM
    have hrest := ih (derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
        (Nat.lt_succ_self d)))
      (derivedTriple_ord_le bo cur _ (Ω d) _) (derivedTriple_finite bo cur _ (Ω d) _)
      (liftChain (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
          (Nat.lt_succ_self d))) Ω)
      (liftChain_isCompact _ hΩ hΩsub rfl) (liftChain_closure_subset _ hΩsub)
      ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self
          d))).pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (range_pullbackLiftLast_subset_liftOpens _ ι hι (Ω 0) hrange
        (range_subset_chain hΩsub hrange))
    rw [← hj] at hrest
    exact BlowUpSequence.hasConstantPositiveOrderAlongCenters_concat _ _ _ hhead hrest

/-- The invariant of the recursion `resolveFrom` for the second half of clause (iv), in the weak
spelling ([Hir64, Main Theorem II′(N), p. 156, (iv)]; clause (1) of [Kol07, Theorem 68] at the
last round's mark `1`): the last weak transform of `ι^* cur.I` along the rounds from `d` is the
unit ideal. The recursion of `hasConstantPositiveOrderAlongCenters_resolveFrom` with
`weakTransformSeq_last_eq_top_concat` and `weakTransformSeq_last_eq_top_pullback` at the junction;
at `d = 0` the list is empty and `cur.I = ⊤` from `∀ x, ord x ≤ 0`, the same exit as inside
`pullbackIsMonomialAtLast_resolveFrom`. -/
theorem weakTransformSeq_last_resolveFrom_eq_top :
    ∀ (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
      (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
      (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
      (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
      (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
      {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
      (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι)
      (hrange : Set.range ι ⊆ Ω 0),
      (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).toSuccession.weakTransformSeq
        (cur.I.pullback ι ι.contMDiff) (Fin.last _) = ⊤ := by
  intro d
  induction d with
  | zero =>
    intro X cur hord hfin Ω hΩ hΩsub N ι hι hrange
    -- the list is empty: the last weak transform is `ι^* cur.I`, and `cur.I = ⊤` from `ord ≤ 0`
    have htop : cur.I = ⊤ := by
      refine IdealSheaf.eq_top_of_support_eq_empty (Set.eq_empty_iff_forall_notMem.mpr fun x hx
          => ?_)
      have h := hord x
      rw [Nat.cast_zero, nonpos_iff_eq_zero, IdealSheaf.ord_eq_zero_iff] at h
      exact h hx
    change cur.I.pullback ι ι.contMDiff = ⊤
    rw [htop]
    exact IdealSheaf.pullback_top _ _
  | succ d ih =>
    intro X cur hord hfin Ω hΩ hΩsub N ι hι hrange
    have hgeA := AnalyticTriple.isOfOrderGe_pullback _ (d + 1) (roundList bo cur
        (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
      ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
      (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
    have hI :
        (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).I.pullback _
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub
        hrange)).contMDiff =
        cur.I.pullback ι ι.contMDiff := by
      change (cur.I.pullback _ (X.inclusion (Ω d)).contMDiff).pullback _ (AnalyticMap.corestrict ι
          (Ω d)
          (range_subset_chain hΩsub hrange)).contMDiff = cur.I.pullback ι ι.contMDiff
      rw [IdealSheaf.pullback_comp]
      exact congrArg (fun f : AnalyticMap _ _ => cur.I.pullback f f.contMDiff)
          (ContMDiffMap.ext fun _ => rfl)
    have hgeA' : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
        (Nat.lt_succ_self d))).pullback (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub
        hrange)) (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub
        hrange))).toSuccession.IsOfOrderGe
        (cur.I.pullback ι ι.contMDiff) (d + 1)
        ((cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).pullback
            (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
            (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub
            hrange))).F.idealSheaf := by
      rw [← hI]
      exact hgeA
    have hbound : ∀ y, (cur.I.pullback ι ι.contMDiff).ord y ≤
        ((d + 1 : ℕ) : ℕ∞) := fun y =>
        by
      rw [IdealSheaf.ord_comap_of_isLocalDiffeomorphAt cur.I ι (hι y)]
      exact hord _
    have hordA := FiniteSuccession.isOfOrder_of_isOfOrderGe_of_ord_le _ hgeA' hbound
    have eM := BlowUpSequence.markedTransformSeq_last_pullbackLiftLast (roundList bo cur
        (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
        (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
        (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange))
      (cur.pullback (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).I (cur.pullback
          (X.inclusion (Ω d)) (isLocalDiffeomorph_inclusion X (Ω d))).F.idealSheaf (d + 1)
      ((bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
    rw [hI] at eM
    have hj : ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
        (Nat.lt_succ_self d))).pullback (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub
        hrange)) (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub
        hrange))).toSuccession.weakTransformSeq
        (cur.I.pullback ι ι.contMDiff) (Fin.last _) =
        (derivedTriple bo cur (boClass_succ_of_ord_le cur
            hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d))).I.pullback _ ((roundList bo cur
                (boClass_succ_of_ord_le cur hord hfin) (Ω d)
            (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast (AnalyticMap.corestrict ι (Ω d)
            (range_subset_chain hΩsub hrange)) (isLocalDiffeomorph_corestrict ι (Ω d) hι
            (range_subset_chain hΩsub hrange))).contMDiff := by
      rw [← hordA.markedTransformSeq_eq_weakTransformSeq (Fin.last _)]
      exact eM
    have hrest := ih (derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
        (Nat.lt_succ_self d))) (derivedTriple_ord_le bo cur _ (Ω d) _) (derivedTriple_finite bo cur
        _ (Ω d) _)
      (liftChain (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d
          (Nat.lt_succ_self d))) Ω) (liftChain_isCompact _ hΩ hΩsub rfl) (liftChain_closure_subset
          _ hΩsub)
      ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self
          d))).pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) (range_subset_chain hΩsub hrange))
          (isLocalDiffeomorph_corestrict ι (Ω d) hι (range_subset_chain hΩsub hrange)))
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (range_pullbackLiftLast_subset_liftOpens _ ι hι (Ω 0) hrange (range_subset_chain hΩsub
          hrange))
    rw [← hj] at hrest
    exact BlowUpSequence.weakTransformSeq_last_eq_top_concat _ _ _ hrest

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- Clause (ii) for the value `resolveSeqOn bo T U hU`:
`hasConstantPositiveOrderAlongCenters_resolveFrom` at the canonical chain
(`resolveSeqOn = (resolveFrom …).eraseEmpty` by `rfl`),
`hasConstantPositiveOrderAlongCenters_eraseEmpty`, and the reading map's identity
`comap (restrictLE _) (outerTriple).I = T.I.restrictOpens U` (`IdealSheaf.pullback_comp`). -/
theorem hasConstantPositiveOrderAlongCenters_resolveSeqOn :
    (resolveSeqOn bo T U hU).toSuccession.HasConstantPositiveOrderAlongCenters
      (T.I.restrict U) := by
  unfold resolveSeqOn resolveSeqOnAlong
  refine BlowUpSequence.hasConstantPositiveOrderAlongCenters_eraseEmpty _ _ ?_
  have h := hasConstantPositiveOrderAlongCenters_resolveFrom bo (canonicalResolveChain T U hU).D
      (canonicalResolveChain T U hU).outerTriple (canonicalResolveChain T U hU).outerTriple_ord_le
    (canonicalResolveChain T U hU).outerTriple_finite (canonicalResolveChain T U hU).trace
        (canonicalResolveChain T U hU).isCompact_closure_trace (canonicalResolveChain T U
        hU).closure_trace_subset
    (M.restrictLE (canonicalResolveChain T U hU).le_outerOpen) (isLocalDiffeomorph_restrictLE _)
    (canonicalResolveChain T U hU).range_restrictLE_subset_trace
  have e :
      Manifold.IdealSheaf.pullback _ (M.restrictLE (canonicalResolveChain T U
          hU).le_outerOpen).contMDiff
      (canonicalResolveChain T U hU).outerTriple.I =
      T.I.restrict U := by
    change (T.I.pullback _ (M.inclusion _).contMDiff).pullback _ (M.restrictLE _).contMDiff =
        T.I.pullback _
        (M.inclusion U).contMDiff
    rw [IdealSheaf.pullback_comp]
    exact congrArg (fun f : AnalyticMap _ _ => T.I.pullback f f.contMDiff)
        (ContMDiffMap.ext fun _ => rfl)
  rw [e] at h
  exact h

/-- The second half of clause (iv) for the value `resolveSeqOn bo T U hU`: the last weak transform
of `𝓘|_U` is the unit ideal (`weakTransformSeq_last_resolveFrom_eq_top` at the canonical chain,
through the erasure `weakTransformSeq_last_eq_top_eraseEmpty` and the reading map's identity). -/
theorem weakTransformSeq_last_resolveSeqOn_eq_top :
    (resolveSeqOn bo T U hU).toSuccession.weakTransformSeq (T.I.restrict U) (Fin.last _) =
      (⊤ : (resolveSeqOn bo T U hU).toSuccession.last.IdealSheaf) := by
  unfold resolveSeqOn resolveSeqOnAlong
  refine BlowUpSequence.weakTransformSeq_last_eq_top_eraseEmpty _ _ ?_
  have h := weakTransformSeq_last_resolveFrom_eq_top bo (canonicalResolveChain T U hU).D
      (canonicalResolveChain T U hU).outerTriple (canonicalResolveChain T U hU).outerTriple_ord_le
    (canonicalResolveChain T U hU).outerTriple_finite (canonicalResolveChain T U hU).trace
        (canonicalResolveChain T U hU).isCompact_closure_trace (canonicalResolveChain T U
        hU).closure_trace_subset
    (M.restrictLE (canonicalResolveChain T U hU).le_outerOpen) (isLocalDiffeomorph_restrictLE _)
        (canonicalResolveChain T U hU).range_restrictLE_subset_trace
  have e :
      Manifold.IdealSheaf.pullback _ (M.restrictLE (canonicalResolveChain T U
          hU).le_outerOpen).contMDiff
      (canonicalResolveChain T U hU).outerTriple.I =
      T.I.restrict U := by
    change (T.I.pullback _ (M.inclusion _).contMDiff).pullback _ (M.restrictLE _).contMDiff =
        T.I.pullback _
        (M.inclusion U).contMDiff
    rw [IdealSheaf.pullback_comp]
    exact congrArg (fun f : AnalyticMap _ _ => T.I.pullback f f.contMDiff)
        (ContMDiffMap.ext fun _ => rfl)
  rw [e] at h
  exact h

/-- The centres of `resolveSeqOn bo T U hU` have simple normal crossings with the accumulated family
`totalTransformSeqFrom (restrictTriple T U).F` at their stage: clause (3′) of [Kol07, Definition 66]
in the family form, from its ideal-sheaf form `isOfOrderGe_zero_resolveSeqOn`
(`Hironaka/Resolution/Analytic/Wlo09/Monomial.lean`) through
`hasSncWith_totalTransformSeqFrom_center_of_forall_lt`. -/
theorem center_resolveSeqOn_hasSncWith (i : Fin (resolveSeqOn bo T U hU).toSuccession.length) :
    ((resolveSeqOn bo T U hU).toSuccession.totalTransformSeqFrom (restrictTriple T U).F
      i.castSucc).HasSncWith (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (((resolveSeqOn bo T U hU).toSuccession.center i).support)
      ((resolveSeqOn bo T U hU).toSuccession.codim i) := by
  exact FiniteSuccession.hasSncWith_totalTransformSeqFrom_center_of_forall_lt
    (restrictTriple T U).isSnc i
    (fun i' _ => (isOfOrderGe_zero_resolveSeqOn bo T U hU i').1)

end Value


/-! ### Restatements under the names of the clauses -/

section

variable (𝕜)

section

variable {m : ℕ} (B : BOanFam.{u} 𝕜 n m) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
  (hT : AnalyticTriple.BOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

end

section

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
  (hU : IsCompact (closure (U : Set M)))

/-- Clause (ii) of [Hir64, Main Theorem II′(N), p. 156] for the value `resolveSeqOn bo T U hU`, with
the predicate `HasConstantPositiveOrderAlongCenters` of
`hasConstantPositiveOrderAlongCenters_resolveSeqOn` unfolded: at every stage there is a positive
constant equal to the order of the weak transform of `𝓘|_U` at every point of the centre. Used by
`resolveFamExt_mainTheoremIIpp`. -/
theorem resolveSeqOn_clause_ii :
    ∀ i : Fin (resolveSeqOn bo T U hU).toSuccession.length, ∃ c : ℕ, 0 < c ∧
      ∀ y ∈ ((resolveSeqOn bo T U hU).toSuccession.center i).support,
        ((resolveSeqOn bo T U hU).toSuccession.weakTransformSeq (T.I.restrict U)
          i.castSucc).ord y = c :=
  hasConstantPositiveOrderAlongCenters_resolveSeqOn bo T U hU

/-- Clause (iii) of [Hir64, Main Theorem II′(N), p. 156] for the value `resolveSeqOn bo T U hU`: at
every stage the boundary sequence of the restricted boundary ideal sheaf has only normal crossings
with the centre; clause (3′) `isOfOrderGe_zero_resolveSeqOn` read through
`restrictTriple_F_idealSheaf`. -/
theorem resolveSeqOn_clause_iii :
    ∀ i : Fin (resolveSeqOn bo T U hU).toSuccession.length,
      ((resolveSeqOn bo T U hU).toSuccession.boundarySeq
        (IdealSheaf.restrict T.F.idealSheaf U)
        i.castSucc).HasOnlyNormalCrossingsWith
        ((resolveSeqOn bo T U hU).toSuccession.center i) := by
  intro i
  rw [← restrictTriple_F_idealSheaf T U]
  exact (isOfOrderGe_zero_resolveSeqOn bo T U hU i).1

/-- The first half of clause (iv) for the value: the last boundary has only normal crossings
(`hasOnlyNormalCrossings_boundarySeq_last_of_isOfOrderGe_zero` at `isOfOrderGe_zero_resolveSeqOn`,
through `restrictTriple_F_idealSheaf`). -/
theorem resolveSeqOn_boundarySeq_last_hasOnlyNormalCrossings :
    ((resolveSeqOn bo T U hU).toSuccession.boundarySeq
      (IdealSheaf.restrict T.F.idealSheaf U)
      (Fin.last _)).HasOnlyNormalCrossings := by
  rw [← restrictTriple_F_idealSheaf T U]
  exact FiniteSuccession.hasOnlyNormalCrossings_boundarySeq_last_of_isOfOrderGe_zero _ _
    (restrictTriple T U).isSnc (isOfOrderGe_zero_resolveSeqOn bo T U hU)

end

end

end Hironaka.Manifold

end
