/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedConcat
public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
public import Hironaka.Resolution.Analytic.OrderReduction.BD
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.Functor.PullbackLiftStages
import Hironaka.Resolution.Analytic.Functor.PullbackSequence
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.MaximalContact.CommonCharts
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Hironaka.Resolution.Analytic.OrderReduction.GlobalizeFamClauses
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopPersistence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial


/-!
# The two stop clauses as predicates on a succession, and their transports

The structure `BMOmodFam` (`Functor/ModifiedMarkedFam.lean`) has two fields about the stop predicate
`IsSmoothTransversalIdealAt`: `output_isSmoothSubmanifoldIdeal`, at every point of the support of
the last marked transform of `(𝓘, 1)` that transform is the ideal of a smooth submanifold
transversal to the total boundary, and `stopped_never_blownUp`, a point of a stage on no member of
the boundary at which the predicate holds is never blown up later. They are the two properties of
the modified algorithm of [Wlo09, Theorem 7.4.1]: the form of its output (coordinates transversal
to the exceptional divisors) and the stop rule of its modified first step. The value of the
modified functor on an open `U` is built from local runs by pull-back along local analytic
isomorphisms, deletion of the empty blow-ups, concatenation along the induced triple and descent
along the maximal-contact cover (`ComposeInduced.lean`, `StepBGlobal.lean`, `GlobalizeFam.lean`),
so the two properties have to be carried across each of these operations. This module isolates
them as predicates on a finite succession from a pair `(𝓘, F)` (`OutputClause`, `StoppedClause`:
the two fields word for word, with `S := L.toSuccession` and `(𝓘, F)` the restricted triple's) and
on a family functor per open (`OutputClauseFam`, `StoppedClauseFam`), and proves the transports
used by the modules `Clause*.lean` that follow. Throughout, "the output clause" is `OutputClause`
and "the stopped clause" is `StoppedClause`.

* Pull-back along a local analytic isomorphism `h` ([Kol07, Definition 30, 30.1]).
  `BlowUpSequence.totalTransformSeqFrom_pullback` (the boundary at every stage of `h^* L` is the
  pull-back along the lift `h_i`; `totalTransform_comap_liftStep` at each step) and
  `BlowUpSequence.stageMapAdd_pullbackLift` (the composite blow-downs intertwine with the lifts);
  both clauses pull back (`outputClause_pullback`, `stoppedClause_pullback`, by
  `IsSmoothTransversalIdealAt.comap`) and descend along a surjective `h`
  (`outputClause_of_pullback_of_surjective`, `stoppedClause_of_pullback_of_surjective`): a point
  lifts along the surjective lift and the predicate comes back along a local inverse
  (`IsSmoothTransversalIdealAt.of_comap`, the converse of `comap`: the chart with simple normal
  crossings is transported by `transportChart`, the stalk read through the bijective germ map).
* Deletion of the empty blow-ups ([Kol07, 32]; the second condition of [Kol07, 34.1]). The output
  clause by the last-stage identifications `markedTransformSeq_last_eraseEmpty` and
  `boundaryCorr_eraseEmpty` (`outputClause_eraseEmpty`); the stopped clause by induction on the
  list (`stoppedClause_eraseEmpty`), a `cons` being read as the clause at stage `0` together with
  the tail's clause from the head triple (`stoppedClause_cons_iff`,
  `stoppedClause_cons_of_forall_notMem`); an empty first step is deleted and the rest carried along
  the diffeomorphism of the empty blow-up (`map_eq_pullback_symm`), the boundary reached being
  `T.F` with one empty member (`StoppedClause.of_isEmptyExtension`).
* Concatenation along the induced triple (`Induced.lean`): `outputClause_cons_iff`,
  `outputClause_concat`, `stoppedClause_concat`, by induction on the first list with `induced_cons`
  and `induced_nil`; a centre of the second list over a predicate point off the boundary lies over
  a predicate point of the join off the boundary
  (`IsSmoothTransversalIdealAt.stageMapAdd_of_forall_notMem_center`: the predicate persists along
  a fibre no centre meets, the analogue for the predicate of
  `notMem_totalTransformSeqFrom_of_forall_notMem_center`), which is excluded at stage `0`
  (`StoppedClause.notMem_center_of_stageMap_eq`, `stageMapAdd_zero_left`).
* Descent along the maximal-contact cover ([Kol07, Theorem 103, Step 3]):
  `outputClauseFam_of_agreeFam`, `stoppedClauseFam_of_agreeFam`, the analogues of
  `isOfOrderGe_of_agreeFam`.
* Two lemmas on the predicate and the members of the boundary,
  `IsSmoothTransversalIdealAt.emptyMember` and
  `IsSmoothTransversalIdealAt.of_emptyMember_of_notMem`: a chart with simple normal crossings at a
  point constrains only the members through the point, so the predicate ignores a member not through
  it; they let the descent and lift of `StopRestrict.lean` be applied with the boundary minus the
  maximal-contact member.

The mathematics is [Kol07, Definition 30, 30.1], [Kol07, 32], [Kol07, 34.1], the descent of
[Kol07, Theorem 103, Step 3] and the persistence lemmas of `StopPersistence.lean`; the statements
themselves are not in the sources.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- **The output clause** for a succession `S` from the pair `(𝓘, F)` (the field
`output_isSmoothSubmanifoldIdeal` of `BMOmodFam`, read on `L.toSuccession` from the restricted
triple): at every point of the support `{ord ≥ 1}` of the marked transform of `(𝓘, 1)` at the last
stage, that transform is locally the ideal of a smooth submanifold with coordinates transversal to
the total boundary. -/
def OutputClause (S : FiniteSuccession M) (I : IdealSheaf M) (F : HypersurfaceFamily M) : Prop :=
  ∀ x : S.stage (Fin.last _),
    (1 : ℕ∞) ≤ (S.markedTransformSeq I 1 (Fin.last _)).ord x →
    HypersurfaceFamily.IsSmoothTransversalIdealAt ψ₀ (S.totalTransformSeqFrom F (Fin.last _))
      (S.markedTransformSeq I 1 (Fin.last _)) x

/-- **The stopped clause** for a succession `S` from `(𝓘, F)` (the field `stopped_never_blownUp` of
`BMOmodFam`): a point `x` of a stage `i` on no member of the boundary at which the marked transform
is a smooth submanifold ideal transversal to the boundary is never blown up: no later centre
contains a point over `x`. -/
def StoppedClause (S : FiniteSuccession M) (I : IdealSheaf M) (F : HypersurfaceFamily M) : Prop :=
  ∀ (i k : ℕ) (h : i + k < S.length)
    (x : S.stage ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩),
    HypersurfaceFamily.IsSmoothTransversalIdealAt ψ₀
      (S.totalTransformSeqFrom F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩)
      (S.markedTransformSeq I 1
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩) x →
    (∀ j, x ∉ (S.totalTransformSeqFrom F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) h)⟩).hyp j) →
    ∀ y : S.stage ⟨i + k, Nat.lt_succ_of_lt h⟩,
      S.stageMapAdd i k (Nat.lt_succ_of_lt h) y = x → y ∉ (S.center ⟨i + k, h⟩).support

/-- The composite blow-down from stage `0` over `k` steps is the succession's `stageMap` at stage
`0 + k` (the bridge between `stageMapAdd` and `stageMapAux`, two recursions peeling the last
blow-up). -/
theorem stageMapAdd_zero_left (S : FiniteSuccession M) (k : ℕ) (hk : 0 + k < S.length + 1)
    (y : S.stage ⟨0 + k, hk⟩) : S.stageMapAdd 0 k hk y = S.stageMap ⟨0 + k, hk⟩ y := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (Nat.lt_of_succ_lt hk) (S.map ⟨0 + k, Nat.lt_of_succ_lt_succ hk⟩ y)

/-- The stopped clause read at stage `0` with `stageMap`: no centre of the succession lies over a
predicate point of the start off the boundary (the stage number generalised to `0 + k`,
`stageMapAdd_zero_left`). -/
theorem StoppedClause.notMem_center_of_stageMap_eq {S : FiniteSuccession M} {I : IdealSheaf M}
    {F : HypersurfaceFamily M} (hS : S.StoppedClause ψ₀ I F) (m : ℕ) (hm : m < S.length)
    {x : S.stage ⟨0, Nat.zero_lt_succ _⟩} (hP : F.IsSmoothTransversalIdealAt ψ₀ I x)
    (hx : ∀ j, x ∉ F.hyp j) (y : S.stage ⟨m, Nat.lt_succ_of_lt hm⟩)
    (hy : S.stageMap ⟨m, Nat.lt_succ_of_lt hm⟩ y = x) : y ∉ (S.center ⟨m, hm⟩).support := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 0 + k := ⟨m, (Nat.zero_add m).symm⟩
  exact hS 0 k hm x hP hx y ((S.stageMapAdd_zero_left k _ y).trans hy)

/-- The stopped clause descends along an empty extension `G ↪ G'` of the boundary family
(`IsEmptyExtension`: the members of `G` are members of `G'` and the other members of `G'` are
empty): stage by stage the boundaries stay in empty extension (`isEmptyExtension_totalTransform`),
and the predicate and "on no member" transport along one, since an empty member is through no
point (`IsSmoothTransversalIdealAt.congr_nhds`). -/
theorem StoppedClause.of_isEmptyExtension {S : FiniteSuccession M} {I : IdealSheaf M}
    {G G' : HypersurfaceFamily M} {e₀ : G.ι ↪o G'.ι} (he : HypersurfaceFamily.IsEmptyExtension e₀)
    (h : S.StoppedClause ψ₀ I G') : S.StoppedClause ψ₀ I G := by
  have hPt : ∀ {X : AnalyticManifold.{u} 𝕜 E} {G₁ G₂ : HypersurfaceFamily X} {e : G₁.ι ↪o G₂.ι},
      HypersurfaceFamily.IsEmptyExtension e → ∀ {J : IdealSheaf X} {x : X},
      G₁.IsSmoothTransversalIdealAt ψ₀ J x → G₂.IsSmoothTransversalIdealAt ψ₀ J x := by
    intro X G₁ G₂ e he J x h
    let f : {j // x ∈ G₁.hyp j} → {j // x ∈ G₂.hyp j} := fun j => ⟨e j.1, by rw [he.1]; exact j.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro j j' hjj'
        exact Subtype.ext (e.injective (congrArg Subtype.val hjj'))
      · rintro ⟨j, hj⟩
        by_cases hr : j ∈ Set.range e
        · obtain ⟨j₀, rfl⟩ := hr
          exact ⟨⟨j₀, by rw [← he.1 j₀]; exact hj⟩, rfl⟩
        · rw [he.2 j hr] at hj
          exact (Set.notMem_empty _ hj).elim
    refine HypersurfaceFamily.IsSmoothTransversalIdealAt.congr_nhds ψ₀ isOpen_univ (Set.mem_univ x)
      (Equiv.ofBijective f hf) (fun j => ?_) (fun a _ => rfl) h
    exact congrArg (· ∩ Set.univ) (he.1 j.1)
  have hOff : ∀ {X : AnalyticManifold.{u} 𝕜 E} {G₁ G₂ : HypersurfaceFamily X} {e : G₁.ι ↪o G₂.ι},
      HypersurfaceFamily.IsEmptyExtension e → ∀ {x : X}, (∀ j, x ∉ G₁.hyp j) →
      ∀ j, x ∉ G₂.hyp j := by
    intro X G₁ G₂ e he x hx j hj
    by_cases hr : j ∈ Set.range e
    · obtain ⟨j₀, rfl⟩ := hr
      rw [he.1 j₀] at hj
      exact hx j₀ hj
    · rw [he.2 j hr] at hj
      exact Set.notMem_empty _ hj
  have hstage : ∀ (i : ℕ) (hi : i < S.length + 1),
      ∃ e : (S.totalTransformSeqFromAux G i hi).ι ↪o (S.totalTransformSeqFromAux G' i hi).ι,
        HypersurfaceFamily.IsEmptyExtension e := by
    intro i
    induction i with
    | zero => intro hi; exact ⟨e₀, he⟩
    | succ i ih =>
      intro hi
      obtain ⟨e, he'⟩ := ih (Nat.lt_of_succ_lt hi)
      exact ⟨_, HypersurfaceFamily.isEmptyExtension_totalTransform
        (S.map ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
        (S.center ⟨i, Nat.lt_of_succ_lt_succ hi⟩).support he'⟩
  intro i k hik x hP hx y hy
  obtain ⟨e, he'⟩ := hstage i (Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik))
  exact h i k hik x (hPt he' hP) (hOff he' hx) y hy

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜))

/-- The output clause of a family functor on its class, per open: the value on `U` from the
restricted triple satisfies `OutputClause`. For `Dom := BMOClass 1` at the model
`refl 𝕜 (Fin n → 𝕜)` this is the field `output_isSmoothSubmanifoldIdeal` of `BMOmodFam` with
`functor := B`, definitionally. -/
def AnalyticFamilyFunctor.OutputClauseFam {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E},
    AnalyticTriple ψ₀ M → Prop} (B : AnalyticFamilyFunctor ψ₀ Dom) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((B.fam T hT).seqOn U hU).toSuccession.OutputClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F

/-- The stopped clause of a family functor on its class, per open (the field
`stopped_never_blownUp` of `BMOmodFam` with `functor := B`, definitionally). -/
def AnalyticFamilyFunctor.StoppedClauseFam {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E},
    AnalyticTriple ψ₀ M → Prop} (B : AnalyticFamilyFunctor ψ₀ Dom) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((B.fam T hT).seqOn U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-! ### Pull-back along a local analytic isomorphism -/

/-- The boundary families along `h^* L` at every stage (the all-stage form of
`totalTransformSeqFrom_last_pullbackLiftLast`): the boundary from `F.comap h` at stage `i` of
`h^* L` is the boundary from `F` at stage `i` of `L` pulled back along the lift `h_i`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.totalTransformSeqFrom_pullback
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (F : HypersurfaceFamily M)
    (i : Fin (L.length + 1)) :
    (L.pullback h hh).toSuccession.totalTransformSeqFrom (F.comap ⇑h)
        ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg (· + 1) (BlowUpSequence.length_pullback L h
            hh).symm)⟩ =
      (L.toSuccession.totalTransformSeqFrom F i).comap ⇑(L.pullbackLift h hh i) := by
  suffices H : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
      {N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
      (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (F : HypersurfaceFamily M) (i : ℕ)
      (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1),
      (L.pullback h hh).toSuccession.totalTransformSeqFromAux (F.comap ⇑h) i hi' =
        (L.toSuccession.totalTransformSeqFromAux F i hi).comap ⇑(L.pullbackLiftAux h hh i hi hi') by
    exact H L h hh F i.1 i.2 _
  intro M L
  induction L with
  | nil M =>
    intro N h hh F i hi hi'
    rcases i with _ | i
    · rfl
    · exact absurd hi (by change ¬ i + 1 < 0 + 1; omega)
  | cons hY rest ih =>
    intro N h hh F i hi hi'
    rcases i with _ | i
    · rfl
    · have e1 : ((BlowUpSequence.cons hY rest).pullback h hh).toSuccession.totalTransformSeqFromAux
        (F.comap ⇑h)
            (i + 1) hi' =
          (rest.pullback (BlowUpSequence.liftStep h hh hY)
            (BlowUpSequence.isLocalDiffeomorph_liftStep h hh
                hY)).toSuccession.totalTransformSeqFromAux
            ((F.comap ⇑h).totalTransform (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
              (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf.support) i
            (Nat.lt_of_succ_lt_succ hi') :=
        FiniteSuccession.cons_totalTransformSeqFromAux_succ (hY.preimage_of_isLocalDiffeomorph hh)
          (rest.pullback (BlowUpSequence.liftStep h hh hY)
              (BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY)).toSuccession
          (F.comap ⇑h) i hi'
      have e2 : (BlowUpSequence.cons hY rest).toSuccession.totalTransformSeqFromAux F (i + 1) hi =
          rest.toSuccession.totalTransformSeqFromAux
            (F.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support) i
            (Nat.lt_of_succ_lt_succ hi) :=
        FiniteSuccession.cons_totalTransformSeqFromAux_succ hY rest.toSuccession F i hi
      rw [e1, e2, hY.cosupport_idealSheaf,
        (hY.preimage_of_isLocalDiffeomorph hh).cosupport_idealSheaf,
        HypersurfaceFamily.totalTransform_comap_liftStep h hh hY F]
      exact ih (BlowUpSequence.liftStep h hh hY) (BlowUpSequence.isLocalDiffeomorph_liftStep h hh
          hY) _ i
        (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')

/-- The composite blow-downs of `h^* L` between two stages are intertwined with those of `L` by the
lifts (`stageMapAdd` along `pullbackLift`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.stageMapAdd_pullbackLift (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (i k : ℕ) (hik : i + k < L.length + 1)
    (hik' : i + k < (L.pullback h hh).length + 1)
    (y : (L.pullback h hh).toSuccession.stage ⟨i + k, hik'⟩) :
    L.pullbackLift h hh ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik⟩
        ((L.pullback h hh).toSuccession.stageMapAdd i k hik' y) =
      L.toSuccession.stageMapAdd i k hik (L.pullbackLift h hh ⟨i + k, hik⟩ y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : i + k < L.length + 1 := Nat.lt_of_succ_lt hik
    have hk' : i + k < (L.pullback h hh).length + 1 := Nat.lt_of_succ_lt hik'
    have hkL : i + k < L.length := Nat.lt_of_succ_lt_succ hik
    change L.pullbackLift h hh ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i (k + 1)) hik⟩
        ((L.pullback h hh).toSuccession.stageMapAdd i k hk'
          ((L.pullback h hh).toSuccession.map ⟨i + k, Nat.lt_of_succ_lt_succ hik'⟩ y)) =
      L.toSuccession.stageMapAdd i k hk
        (L.toSuccession.map ⟨i + k, hkL⟩ (L.pullbackLift h hh ⟨i + (k + 1), hik⟩ y))
    refine (ih hk hk' _).trans ?_
    exact congrArg (L.toSuccession.stageMapAdd i k hk) (L.map_pullbackLift h hh ⟨i + k, hkL⟩ y)

/-- **The predicate descends along a local analytic isomorphism** (the converse of
`IsSmoothTransversalIdealAt.comap`): the predicate for the pulled-back family and ideal at `y` gives
the predicate for `F` and `J` at `g y`. The chart with simple normal crossings at `y` is transported
along a local inverse `Φ⁻¹` of `g` (`transportChart`, the mirror of the proof of `comap`;
`stalkIdeal_comap_eq_map_germMap`, `germMap_coord_eq_coord_transportChart`). Used at the lifted
point in `outputClause_of_pullback_of_surjective` and `stoppedClause_of_pullback_of_surjective`. -/
theorem _root_.Manifold.HypersurfaceFamily.IsSmoothTransversalIdealAt.of_comap
    (F : HypersurfaceFamily M)
    (J : AnalyticManifold.IdealSheaf M) (g : AnalyticMap N M) {y : N}
    (hg : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω g y)
    (h : (F.comap ⇑g).IsSmoothTransversalIdealAt ψ₀ (J.pullback g g.contMDiff) y) :
    F.IsSmoothTransversalIdealAt ψ₀ J (g y) := by
  obtain ⟨Φ, hyΦ, hΦ⟩ := hg.exists_partialDiffeomorph
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  have hφ' : transportChart Φ φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M :=
    transportChart_mem_maximalAtlas Φ hφ.1
  have hgy : g y ∈ Φ.target := hΦ hyΦ ▸ Φ.map_source hyΦ
  have hinv : Φ.invFun (g y) = y := by rw [hΦ hyΦ]; exact Φ.left_inv hyΦ
  have hsrc : ∀ b, b ∈ (transportChart Φ φ).source ↔ b ∈ Φ.target ∧ Φ.invFun b ∈ φ.source :=
    fun b => by rw [transportChart_source]; exact Iff.rfl
  have hy' : g y ∈ (transportChart Φ φ).source := (hsrc _).mpr ⟨hgy, by rw [hinv]; exact hφ.2.1⟩
  have hpt : ∀ b ∈ (transportChart Φ φ).source, ∃ a ∈ Φ.source, g a = b := fun b hb => by
    have hbΦ : b ∈ Φ.target := ((hsrc b).mp hb).1
    have hmem : Φ.invFun b ∈ Φ.source := Φ.map_target hbΦ
    refine ⟨Φ.invFun b, hmem, ?_⟩
    rw [hΦ hmem]
    exact Φ.right_inv hbΦ
  have hinv' : ∀ a ∈ Φ.source, Φ.invFun (g a) = a := fun a ha => by
    rw [hΦ ha]; exact Φ.left_inv ha
  have hsrc' : ∀ a ∈ Φ.source, g a ∈ (transportChart Φ φ).source → a ∈ φ.source := by
    intro a ha hb
    have := ((hsrc _).mp hb).2
    rwa [hinv' a ha] at this
  refine ⟨c, transportChart Φ φ, σ, fun j => cidx ⟨j.1, j.2⟩, ⟨hφ', hy', fun j b hb => ?_,
    fun j j' hjj' => Subtype.ext
      (congrArg (Subtype.val (p := fun j => y ∈ (F.comap ⇑g).hyp j)) (hφ.2.2.2 hjj'))⟩,
    fun b hb => ?_, hne⟩
  · obtain ⟨a, haΦ, rfl⟩ := hpt b hb
    rw [transportChart_apply, hinv' a haΦ]
    exact hφ.2.2.1 ⟨j.1, j.2⟩ a (hsrc' a haΦ hb)
  · obtain ⟨a, haΦ, rfl⟩ := hpt b hb
    have haφ : a ∈ φ.source := hsrc' a haΦ hb
    have hφ'' : transportChart Φ.symm (transportChart Φ φ) ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω N :=
      transportChart_mem_maximalAtlas Φ.symm hφ'
    have ha'' : a ∈ (transportChart Φ.symm (transportChart Φ φ)).source := by
      rw [transportChart_source]
      refine ⟨haΦ, ?_⟩
      change Φ a ∈ (transportChart Φ φ).source
      rw [← hΦ haΦ]
      exact hb
    have hbij : Function.Bijective (germMap (⇑g) g.contMDiff a) :=
      germMap_bijective_of_isLocalDiffeomorphAt (φ := ⇑g) (hφ := g.contMDiff)
        (IsLocalDiffeomorphAt.of_eqOn Φ haΦ hΦ)
    have hmap : Ideal.map (germMap (⇑g) g.contMDiff a) (J.stalkIdeal (g a)) =
        Ideal.map (germMap (⇑g) g.contMDiff a)
          (Ideal.span (Set.range fun i => coord E ψ₀ (transportChart Φ φ) hφ' hb (σ i))) := by
      rw [← stalkIdeal_comap_eq_map_germMap, hJ a haφ, Ideal.map_span, ← Set.range_comp]
      refine congrArg Ideal.span (congrArg Set.range (funext fun i => ?_))
      change coord E ψ₀ φ hφ.1 haφ (σ i) =
        germMap (⇑g) g.contMDiff a (coord E ψ₀ (transportChart Φ φ) hφ' hb (σ i))
      rw [germMap_coord_eq_coord_transportChart ψ₀ g Φ hΦ haΦ (transportChart Φ φ) hφ' hb hφ'' ha'']
      refine coord_eq_coord_of_eventuallyEq E hφ.1 haφ hφ'' ha'' ?_
      filter_upwards [Φ.open_source.mem_nhds haΦ] with x hx
      have hlx : Φ.invFun (Φ x) = x := Φ.left_inv hx
      change ψ₀ (φ x) (σ i) = ψ₀ (φ (Φ.invFun (Φ x))) (σ i)
      rw [hlx]
    calc J.stalkIdeal (g a)
        = (Ideal.map (germMap (⇑g) g.contMDiff a) (J.stalkIdeal (g a))).comap
            (germMap (⇑g) g.contMDiff a) := (Ideal.comap_map_of_bijective _ hbij).symm
      _ = _ := by rw [hmap, Ideal.comap_map_of_bijective _ hbij]

/-- The output clause descends along a surjective local analytic isomorphism: if `h^* L` from the
pulled-back triple satisfies the clause, so does `L` from `T`. A point of the last stage of `L`
lifts along the surjective last lift (`markedTransformSeq_pullback`,
`totalTransformSeqFrom_pullback`), and the predicate comes back along the local isomorphism
(`IsSmoothTransversalIdealAt.of_comap`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.outputClause_of_pullback_of_surjective
    (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (T : AnalyticTriple ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : (L.pullback h hh).toSuccession.OutputClause ψ₀ (T.pullback h hh).I (T.pullback h hh).F) :
    L.toSuccession.OutputClause ψ₀ T.I T.F := by
  have := finiteDimensional_of_chartIso ψ₀
  intro x hx
  obtain ⟨x', rfl⟩ := L.surjective_pullbackLiftLast h hh hs x
  have e1 := L.totalTransformSeqFrom_last_pullbackLiftLast h hh T.F
  have e2 := L.markedTransformSeq_last_pullbackLiftLast h hh T.I T.F.idealSheaf 1 hge
  have hloc := L.isLocalDiffeomorph_pullbackLiftLast h hh x'
  have hord : ((L.toSuccession.markedTransformSeq T.I 1 (Fin.last _)).pullback _
      (L.pullbackLiftLast h hh).contMDiff).ord x' =
      (L.toSuccession.markedTransformSeq T.I 1 (Fin.last _)).ord (L.pullbackLiftLast h hh x') :=
    IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ hloc
  have hx' : (1 : ℕ∞) ≤ ((L.pullback h hh).toSuccession.markedTransformSeq (T.pullback h hh).I 1
      (Fin.last _)).ord x' := by
    rw [(T.isPullbackOf_pullback h hh).1, e2, hord]
    exact hx
  have hP' := hP x' hx'
  rw [(T.isPullbackOf_pullback h hh).1, (T.isPullbackOf_pullback h hh).2, e1, e2] at hP'
  exact HypersurfaceFamily.IsSmoothTransversalIdealAt.of_comap ψ₀ _ _ _ hloc hP'

/-- The output clause pulls back along a local analytic isomorphism
(`IsSmoothTransversalIdealAt.comap`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.outputClause_pullback (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (T : AnalyticTriple ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : L.toSuccession.OutputClause ψ₀ T.I T.F) :
    (L.pullback h hh).toSuccession.OutputClause ψ₀ (T.pullback h hh).I (T.pullback h hh).F := by
  have := finiteDimensional_of_chartIso ψ₀
  intro x' hx'
  have e1 := L.totalTransformSeqFrom_last_pullbackLiftLast h hh T.F
  have e2 := L.markedTransformSeq_last_pullbackLiftLast h hh T.I T.F.idealSheaf 1 hge
  have hloc := L.isLocalDiffeomorph_pullbackLiftLast h hh x'
  have hord : ((L.toSuccession.markedTransformSeq T.I 1 (Fin.last _)).pullback _
      (L.pullbackLiftLast h hh).contMDiff).ord x' =
      (L.toSuccession.markedTransformSeq T.I 1 (Fin.last _)).ord (L.pullbackLiftLast h hh x') :=
    IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ hloc
  rw [(T.isPullbackOf_pullback h hh).1, e2, hord] at hx'
  rw [(T.isPullbackOf_pullback h hh).1, (T.isPullbackOf_pullback h hh).2, e1, e2]
  exact HypersurfaceFamily.IsSmoothTransversalIdealAt.comap ψ₀ _ _ _ hloc (hP _ hx')

/-- The stopped clause descends along a surjective local analytic isomorphism (`center_pullback`,
`totalTransformSeqFrom_pullback`, `stageMapAdd_pullbackLift`, and the predicate brought back by
`IsSmoothTransversalIdealAt.of_comap`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.stoppedClause_of_pullback_of_surjective
    (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (T : AnalyticTriple ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : (L.pullback h hh).toSuccession.StoppedClause ψ₀ (T.pullback h hh).I
      (T.pullback h hh).F) :
    L.toSuccession.StoppedClause ψ₀ T.I T.F := by
  have := finiteDimensional_of_chartIso ψ₀
  intro i k hik x hP₀ hx y hy
  have hik' : i + k < (L.pullback h hh).length := by rw [L.length_pullback h hh]; exact hik
  obtain ⟨y', rfl⟩ := L.surjective_pullbackLift h hh hs ⟨i + k, Nat.lt_succ_of_lt hik⟩ y
  set x' := (L.pullback h hh).toSuccession.stageMapAdd i k (Nat.lt_succ_of_lt hik') y'
  have hlift := BlowUpSequence.stageMapAdd_pullbackLift ψ₀ L h hh i k (Nat.lt_succ_of_lt hik)
    (Nat.lt_succ_of_lt hik') y'
  rw [hy] at hlift
  have hloc := L.isLocalDiffeomorph_pullbackLift h hh
    ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩ x'
  have e1 := BlowUpSequence.totalTransformSeqFrom_pullback ψ₀ L h hh T.F
    ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩
  have e2 := L.markedTransformSeq_pullback h hh T.I T.F.idealSheaf 1 hge
    ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩
  have hPl : HypersurfaceFamily.IsSmoothTransversalIdealAt ψ₀ (L.toSuccession.totalTransformSeqFrom
      T.F ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩)
      (L.toSuccession.markedTransformSeq T.I 1
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩)
      (L.pullbackLift h hh ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩
        x') := by
    rw [hlift]; exact hP₀
  have hP' : HypersurfaceFamily.IsSmoothTransversalIdealAt ψ₀
      ((L.pullback h hh).toSuccession.totalTransformSeqFrom (T.pullback h hh).F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik')⟩)
      ((L.pullback h hh).toSuccession.markedTransformSeq (T.pullback h hh).I 1
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik')⟩) x' := by
    rw [(T.isPullbackOf_pullback h hh).1, (T.isPullbackOf_pullback h hh).2, e1, e2]
    exact HypersurfaceFamily.IsSmoothTransversalIdealAt.comap ψ₀ _ _ _ hloc hPl
  have hx' : ∀ j, x' ∉ ((L.pullback h hh).toSuccession.totalTransformSeqFrom (T.pullback h hh).F
      ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik')⟩).hyp j := by
    rw [(T.isPullbackOf_pullback h hh).2, e1]
    intro j hj
    apply hx j
    rw [← hlift]
    exact hj
  have hnot := hP i k hik' x' hP' hx' y' rfl
  intro hmem
  apply hnot
  rw [L.center_pullback h hh ⟨i + k, hik⟩]
  exact (Set.ext_iff.mp (IdealSheaf.support_pullback _ _ _) y').mpr hmem

/-- The stopped clause pulls back along a local analytic isomorphism. -/
theorem _root_.AnalyticManifold.BlowUpSequence.stoppedClause_pullback (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (T : AnalyticTriple ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : L.toSuccession.StoppedClause ψ₀ T.I T.F) :
    (L.pullback h hh).toSuccession.StoppedClause ψ₀ (T.pullback h hh).I (T.pullback h hh).F := by
  have := finiteDimensional_of_chartIso ψ₀
  intro i k hik' x' hP' hx' y' hy'
  have hik : i + k < L.length := by rw [← L.length_pullback h hh]; exact hik'
  have hlift := BlowUpSequence.stageMapAdd_pullbackLift ψ₀ L h hh i k (Nat.lt_succ_of_lt hik)
    (Nat.lt_succ_of_lt hik') y'
  rw [hy'] at hlift
  have hloc := L.isLocalDiffeomorph_pullbackLift h hh
    ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩ x'
  have e1 := BlowUpSequence.totalTransformSeqFrom_pullback ψ₀ L h hh T.F
    ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩
  have e2 := L.markedTransformSeq_pullback h hh T.I T.F.idealSheaf 1 hge
    ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hik)⟩
  rw [(T.isPullbackOf_pullback h hh).1, (T.isPullbackOf_pullback h hh).2, e1, e2] at hP'
  rw [(T.isPullbackOf_pullback h hh).2, e1] at hx'
  have hPx := HypersurfaceFamily.IsSmoothTransversalIdealAt.of_comap ψ₀ _ _ _ hloc hP'
  have hnot := hP i k hik _ hPx (fun j hj => hx' j hj)
    (L.pullbackLift h hh ⟨i + k, Nat.lt_succ_of_lt hik⟩ y') hlift.symm
  intro hmem
  apply hnot
  rw [L.center_pullback h hh ⟨i + k, hik⟩] at hmem
  exact (Set.ext_iff.mp (IdealSheaf.support_pullback _ _ _) y').mp hmem

/-! ### Deletion of the empty blow-ups ([Kol07, 32], [Kol07, 34.1]) -/

/-- The output clause survives the deletion of the empty blow-ups
(`markedTransformSeq_last_eraseEmpty` and `boundaryCorr_eraseEmpty` at the last stage, the predicate
transported along `eraseEmptyLast`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.outputClause_eraseEmpty (L : BlowUpSequence ψ₀ M)
    (T : AnalyticTriple ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : L.toSuccession.OutputClause ψ₀ T.I T.F) :
    L.eraseEmpty.toSuccession.OutputClause ψ₀ T.I T.F := by
  have := finiteDimensional_of_chartIso ψ₀
  intro x' hx'
  have hJ := L.markedTransformSeq_last_eraseEmpty T.I T.F.idealSheaf 1 hge
  rw [hJ] at hx' ⊢
  set g : AnalyticMap (L.eraseEmpty.stage (Fin.last _)) (L.stage (Fin.last _)) :=
    Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm
  set GA := L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)
  set GB := L.eraseEmpty.toSuccession.totalTransformSeqFrom T.F (Fin.last _)
  set JA := L.toSuccession.markedTransformSeq T.I 1 (Fin.last _)
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω g x' :=
    L.eraseEmptyLast.symm.isLocalDiffeomorph x'
  have hord : (JA.pullback g g.contMDiff).ord x' = JA.ord (g x') :=
    IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _ hloc
  rw [hord] at hx'
  have hP' := HypersurfaceFamily.IsSmoothTransversalIdealAt.comap ψ₀ GA JA g hloc (hP _ hx')
  obtain ⟨e', he1, he2, -⟩ := L.boundaryCorr_eraseEmpty_self T.F fun j => (T.isSnc.1 j).isClosed
  have hmem : ∀ i, x' ∈ (GA.comap ⇑g).hyp (e' i) ↔ x' ∈ GB.hyp i := fun i => by
    rw [← he1 i]
    exact Iff.rfl
  let f : {i // x' ∈ GB.hyp i} → {j // x' ∈ (GA.comap ⇑g).hyp j} :=
    fun i => ⟨e' i.1, (hmem i.1).mpr i.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i i' hii'
      exact Subtype.ext (e'.injective (congrArg Subtype.val hii'))
    · rintro ⟨j, hj⟩
      by_cases hr : j ∈ Set.range e'
      · obtain ⟨i, rfl⟩ := hr
        exact ⟨⟨i, (hmem i).mp hj⟩, rfl⟩
      · have hj' : x' ∈ ⇑g ⁻¹' GA.hyp j := hj
        rw [he2 j hr] at hj'
        exact (Set.notMem_empty _ hj').elim
  refine HypersurfaceFamily.IsSmoothTransversalIdealAt.congr_nhds ψ₀ isOpen_univ (Set.mem_univ x')
    (Equiv.ofBijective f hf).symm (fun j => ?_) (fun a _ => rfl) hP'
  have hfe : e' ((Equiv.ofBijective f hf).symm j).1 = j.1 :=
    congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply j)
  rw [← he1, hfe]
  rfl

/-- The stopped clause for `cons hY L'` from the stopped clause of `L'` for the head triple and the
stage-`0` content (a predicate point off the boundary is not in `Y`): a centre of `L'` over such a
point lies over a predicate point of the head stage off its boundary (the predicate and the absence
from the boundary persist under one blow-up off the centre, the marking legitimate by the head's
order clause), which is excluded at stage `0` by `StoppedClause.notMem_center_of_stageMap_eq`; the
later stages are `L'`'s, one stage in. -/
theorem _root_.AnalyticManifold.BlowUpSequence.stoppedClause_cons_of_forall_notMem {Y : Set M}
    {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (L' : BlowUpSequence ψ₀ (blowUp ψ₀ hY))
        (T : AnalyticTriple ψ₀ M)
    (hh : (BlowUpSequence.cons hY (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I 1
        T.F.idealSheaf)
    (hR : L'.toSuccession.StoppedClause ψ₀ (T.headTriple 1 hY hh).I (T.headTriple 1 hY hh).F)
    (hxY : ∀ x : M, T.F.IsSmoothTransversalIdealAt ψ₀ T.I x → (∀ j, x ∉ T.F.hyp j) → x ∉ Y) :
    (BlowUpSequence.cons hY L').toSuccession.StoppedClause ψ₀ T.I T.F := by
  set S := (BlowUpSequence.cons hY L').toSuccession
  set R := L'.toSuccession
  have hlen : S.length = R.length + 1 := rfl
  have hJ : ∀ a ∈ Y, (1 : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf T.I a := by
    intro a ha
    have := ((FiniteSuccession.isOfOrderGe_cons_iff (I := T.I) (m := 1) (E₀ := T.F.idealSheaf) hY
      (BlowUpSequence.nil _).toSuccession).mp hh).1.2 a ha
    rwa [Nat.cast_one] at this
  have hI1 : ∀ (i : ℕ) (hi : i + 1 < S.length + 1), S.markedTransformSeq T.I 1 ⟨i + 1, hi⟩ =
      R.markedTransformSeq (T.headTriple 1 hY hh).I 1 ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := by
    intro i hi
    rw [AnalyticTriple.headTriple_I, ← FiniteSuccession.cons_markedTransformSeq_one hY R T.I 1]
    exact FiniteSuccession.cons_markedTransformSeqAux_succ hY R T.I 1 i hi
  have hF1 : ∀ (i : ℕ) (hi : i + 1 < S.length + 1), S.totalTransformSeqFrom T.F ⟨i + 1, hi⟩ =
      R.totalTransformSeqFrom (T.headTriple 1 hY hh).F ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := by
    intro i hi
    rw [AnalyticTriple.headTriple_F]
    exact FiniteSuccession.cons_totalTransformSeqFromAux_succ hY R T.F i hi
  have hT : ∀ (i k m : ℕ) (hm : m = i + k + 1) (hmS : m < S.length)
      (y : S.stage ⟨m, Nat.lt_succ_of_lt hmS⟩),
      ∃ y' : R.stage ⟨i + k, Nat.lt_succ_of_lt (by omega)⟩, HEq y y' ∧
        (y ∈ (S.center ⟨m, hmS⟩).support ↔ y' ∈ (R.center ⟨i + k, by omega⟩).support) := by
    intro i k m hm hmS y
    subst hm
    exact ⟨y, HEq.rfl, Iff.rfl⟩
  have hmapAdd : ∀ (i k : ℕ) (hk : i + 1 + k < S.length + 1) (hk' : i + k < R.length + 1)
      (y : S.stage ⟨i + 1 + k, hk⟩) (y' : R.stage ⟨i + k, hk'⟩), HEq y y' →
      S.stageMapAdd (i + 1) k hk y = R.stageMapAdd i k hk' y' := by
    intro i k
    induction k with
    | zero =>
      intro hk hk' y y' hyy'
      exact eq_of_heq hyy'
    | succ k ih =>
      intro hk hk' y y' hyy'
      have hstep : ∀ (m : ℕ) (hm : m = i + k + 1) (p : m < S.length)
          (z : S.stage ⟨m + 1, Nat.succ_lt_succ p⟩)
          (z' : R.stage ⟨i + k + 1, Nat.succ_lt_succ (by omega)⟩), HEq z z' →
          HEq (S.map ⟨m, p⟩ z) (R.map ⟨i + k, by omega⟩ z') := by
        intro m hm p z z' hzz'
        subst hm
        have hz := eq_of_heq hzz'
        subst hz
        exact HEq.rfl
      exact ih (Nat.lt_of_succ_lt hk) (Nat.lt_of_succ_lt hk') _ _
        (hstep (i + 1 + k) (Nat.add_right_comm i 1 k) (Nat.lt_of_succ_lt_succ hk) y y' hyy')
  have hA : ∀ (m : ℕ) (hm : m < S.length) (x : M), T.F.IsSmoothTransversalIdealAt ψ₀ T.I x →
      (∀ j, x ∉ T.F.hyp j) → ∀ y : S.stage ⟨m, Nat.lt_succ_of_lt hm⟩,
      S.stageMap ⟨m, Nat.lt_succ_of_lt hm⟩ y = x → y ∉ (S.center ⟨m, hm⟩).support := by
    intro m
    rcases m with _ | m
    · intro hm x hPx hx y hy
      have hyx : y = x := hy
      subst hyx
      change y ∉ hY.idealSheaf.support
      rw [hY.cosupport_idealSheaf]
      exact hxY y hPx hx
    · intro hm x hPx hx y hy
      have hmR : m < R.length := Nat.lt_of_succ_lt_succ hm
      have hπ : blowUpπ ψ₀ hY (R.stageMap ⟨m, Nat.lt_succ_of_lt hmR⟩ y) = x := by
        rw [← hy]
        exact (BlowUpSequence.stageMapAux_cons_succ hY L' m (Nat.lt_succ_of_lt hm) y).symm
      have hxY' : blowUpπ ψ₀ hY (R.stageMap ⟨m, Nat.lt_succ_of_lt hmR⟩ y) ∉ Y := by
        rw [hπ]
        exact hxY x hPx hx
      have hP₁ := HypersurfaceFamily.IsSmoothTransversalIdealAt.totalTransform_of_notMem ψ₀ hY
        (isBlowUp_blowUpπ ψ₀ hY) T.isSnc hJ hxY' (by rw [hπ]; exact hPx)
      have hx₁ := HypersurfaceFamily.notMem_totalTransform_of_notMem ψ₀ (isBlowUp_blowUpπ ψ₀ hY)
        T.isSnc hxY' (by rw [hπ]; exact hx)
      have hP₁' : (T.headTriple 1 hY hh).F.IsSmoothTransversalIdealAt ψ₀ (T.headTriple 1 hY hh).I
          (R.stageMap ⟨m, Nat.lt_succ_of_lt hmR⟩ y) := by
        rw [AnalyticTriple.headTriple_F, AnalyticTriple.headTriple_I, hY.cosupport_idealSheaf]
        exact hP₁
      have hx₁' : ∀ j, R.stageMap ⟨m, Nat.lt_succ_of_lt hmR⟩ y ∉
          (T.headTriple 1 hY hh).F.hyp j := by
        rw [AnalyticTriple.headTriple_F, hY.cosupport_idealSheaf]
        exact hx₁
      exact FiniteSuccession.StoppedClause.notMem_center_of_stageMap_eq ψ₀ hR m hmR hP₁' hx₁' y rfl
  intro i k h x hP hx y hy
  rcases i with _ | i
  · exact hA (0 + k) h x hP hx y ((S.stageMapAdd_zero_left k _ y).symm.trans hy)
  · have hkR : i + k < R.length := by omega
    obtain ⟨y', hyy, hmem⟩ := hT i k (i + 1 + k) (Nat.add_right_comm i 1 k) h y
    have hPR : HypersurfaceFamily.IsSmoothTransversalIdealAt ψ₀ (R.totalTransformSeqFrom
        (T.headTriple 1 hY hh).F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hkR)⟩)
        (R.markedTransformSeq (T.headTriple 1 hY hh).I 1
          ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hkR)⟩) x := by
      rw [← hI1 i, ← hF1 i]
      exact hP
    have hxR : ∀ j, x ∉ (R.totalTransformSeqFrom (T.headTriple 1 hY hh).F
        ⟨i, Nat.lt_succ_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right i k) hkR)⟩).hyp j := by
      rw [← hF1 i]
      exact hx
    have hnot := hR i k hkR x hPR hxR y' ((hmapAdd i k _ _ y y' hyy).symm.trans hy)
    exact fun hm => hnot (hmem.mp hm)

/-- The stopped clause is read one stage in: for `cons hY rest` it is the clause at stage `0` (no
later centre over a predicate point of `M` off the boundary) together with the clause of `rest`
from the head triple (the marked transform of `(𝓘, 1)` and the total transform of `F` under the
first blow-up, `AnalyticTriple.headTriple`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.stoppedClause_cons_iff {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (T : AnalyticTriple ψ₀ M)
    (hge : (BlowUpSequence.cons hY rest).toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf) :
    (BlowUpSequence.cons hY rest).toSuccession.StoppedClause ψ₀ T.I T.F ↔
      ((∀ (k : ℕ) (h : k < rest.length + 1) (x : M),
        T.F.IsSmoothTransversalIdealAt ψ₀ T.I x → (∀ j, x ∉ T.F.hyp j) →
        ∀ y : (BlowUpSequence.cons hY rest).toSuccession.stage ⟨k, Nat.lt_succ_of_lt h⟩,
          (BlowUpSequence.cons hY rest).toSuccession.stageMap ⟨k, Nat.lt_succ_of_lt h⟩ y = x →
          y ∉ ((BlowUpSequence.cons hY rest).toSuccession.center ⟨k, h⟩).support) ∧
      rest.toSuccession.StoppedClause ψ₀
        (T.headTriple 1 hY (T.isOfOrderGe_head_of_cons 1 hY hge)).I
        (T.headTriple 1 hY (T.isOfOrderGe_head_of_cons 1 hY hge)).F) := by
  set S := (BlowUpSequence.cons hY rest).toSuccession
  set R := rest.toSuccession
  have hlen : S.length = R.length + 1 := rfl
  have hh := T.isOfOrderGe_head_of_cons 1 hY hge
  constructor
  · intro hS
    refine ⟨fun k h x hP hx y hy =>
      FiniteSuccession.StoppedClause.notMem_center_of_stageMap_eq ψ₀ hS k h hP hx y hy, ?_⟩
    have hI1 : ∀ (i : ℕ) (hi : i + 1 < S.length + 1), S.markedTransformSeq T.I 1 ⟨i + 1, hi⟩ =
        R.markedTransformSeq (T.headTriple 1 hY hh).I 1 ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := by
      intro i hi
      rw [AnalyticTriple.headTriple_I, ← FiniteSuccession.cons_markedTransformSeq_one hY R T.I 1]
      exact FiniteSuccession.cons_markedTransformSeqAux_succ hY R T.I 1 i hi
    have hF1 : ∀ (i : ℕ) (hi : i + 1 < S.length + 1), S.totalTransformSeqFrom T.F ⟨i + 1, hi⟩ =
        R.totalTransformSeqFrom (T.headTriple 1 hY hh).F ⟨i, Nat.lt_of_succ_lt_succ hi⟩ := by
      intro i hi
      rw [AnalyticTriple.headTriple_F]
      exact FiniteSuccession.cons_totalTransformSeqFromAux_succ hY R T.F i hi
    have hT' : ∀ (i k m : ℕ) (hm : m = i + k + 1) (hmS : m < S.length)
        (y' : R.stage ⟨i + k, Nat.lt_succ_of_lt (by omega)⟩),
        ∃ y : S.stage ⟨m, Nat.lt_succ_of_lt hmS⟩, HEq y y' ∧
          (y ∈ (S.center ⟨m, hmS⟩).support ↔ y' ∈ (R.center ⟨i + k, by omega⟩).support) := by
      intro i k m hm hmS y'
      subst hm
      exact ⟨y', HEq.rfl, Iff.rfl⟩
    have hmapAdd : ∀ (i k : ℕ) (hk : i + 1 + k < S.length + 1) (hk' : i + k < R.length + 1)
        (y : S.stage ⟨i + 1 + k, hk⟩) (y' : R.stage ⟨i + k, hk'⟩), HEq y y' →
        S.stageMapAdd (i + 1) k hk y = R.stageMapAdd i k hk' y' := by
      intro i k
      induction k with
      | zero =>
        intro hk hk' y y' hyy'
        exact eq_of_heq hyy'
      | succ k ih =>
        intro hk hk' y y' hyy'
        have hstep : ∀ (m : ℕ) (hm : m = i + k + 1) (p : m < S.length)
            (z : S.stage ⟨m + 1, Nat.succ_lt_succ p⟩)
            (z' : R.stage ⟨i + k + 1, Nat.succ_lt_succ (by omega)⟩), HEq z z' →
            HEq (S.map ⟨m, p⟩ z) (R.map ⟨i + k, by omega⟩ z') := by
          intro m hm p z z' hzz'
          subst hm
          have hz := eq_of_heq hzz'
          subst hz
          exact HEq.rfl
        exact ih (Nat.lt_of_succ_lt hk) (Nat.lt_of_succ_lt hk') _ _
          (hstep (i + 1 + k) (Nat.add_right_comm i 1 k) (Nat.lt_of_succ_lt_succ hk) y y' hyy')
    intro i k h x hP hx y' hy'
    have hkS : i + 1 + k < S.length := by omega
    obtain ⟨y, hyy, hmem⟩ := hT' i k (i + 1 + k) (Nat.add_right_comm i 1 k) hkS y'
    have hxS : (S.totalTransformSeqFrom T.F ⟨i + 1, Nat.lt_succ_of_lt
        (Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) k) hkS)⟩).IsSmoothTransversalIdealAt ψ₀
        (S.markedTransformSeq T.I 1 ⟨i + 1, Nat.lt_succ_of_lt
          (Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) k) hkS)⟩) x := by
      rw [hI1, hF1]
      exact hP
    have hxS' : ∀ j, x ∉ (S.totalTransformSeqFrom T.F ⟨i + 1, Nat.lt_succ_of_lt
        (Nat.lt_of_le_of_lt (Nat.le_add_right (i + 1) k) hkS)⟩).hyp j := by
      rw [hF1]
      exact hx
    have hnot := hS (i + 1) k hkS x hxS hxS' y ((hmapAdd i k _ _ y y' hyy).trans hy')
    exact fun hm => hnot (hmem.mpr hm)
  · rintro ⟨hA, hR⟩
    refine BlowUpSequence.stoppedClause_cons_of_forall_notMem ψ₀ hY rest T hh hR fun x hPx hx hxY
        => ?_
    refine hA 0 (Nat.zero_lt_succ _) x hPx hx x rfl ?_
    change x ∈ hY.idealSheaf.support
    rw [hY.cosupport_idealSheaf]
    exact hxY

/-- The stopped clause survives the deletion of the empty blow-ups, by induction on the list with
`stoppedClause_cons_iff`: a nonempty first centre stays (`eraseEmpty_cons_of_ne_empty`) and
`stoppedClause_cons_of_forall_notMem` rebuilds the clause from the tail's; an empty one is deleted
and the rest carried along the diffeomorphism of the empty blow-up (`eraseEmpty_cons_of_eq_empty`
with `map_eq_pullback_symm` and `stoppedClause_pullback`), the head triple's data being `T.I`
pulled back twice and `T.F` with one empty member, so that the clause comes back along
`StoppedClause.of_isEmptyExtension`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.stoppedClause_eraseEmpty (L : BlowUpSequence ψ₀ M)
    (T : AnalyticTriple ψ₀ M)
    (hge : L.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP : L.toSuccession.StoppedClause ψ₀ T.I T.F) :
    L.eraseEmpty.toSuccession.StoppedClause ψ₀ T.I T.F := by
  have := finiteDimensional_of_chartIso ψ₀
  induction L with
  | nil M => exact hP
  | @cons M' Y c hY rest ih =>
    have hh := T.isOfOrderGe_head_of_cons 1 hY hge
    obtain ⟨hA, hR⟩ := (BlowUpSequence.stoppedClause_cons_iff ψ₀ hY rest T hge).mp hP
    have hIH := ih (T.headTriple 1 hY hh) (T.isOfOrderGe_tail_of_cons 1 hY hge) hR
    have hxY : ∀ x : M', T.F.IsSmoothTransversalIdealAt ψ₀ T.I x → (∀ j, x ∉ T.F.hyp j) →
        x ∉ Y := by
      intro x hPx hx hxY
      refine hA 0 (Nat.zero_lt_succ _) x hPx hx x rfl ?_
      change x ∈ hY.idealSheaf.support
      rw [hY.cosupport_idealSheaf]
      exact hxY
    by_cases hY₀ : Y = ∅
    · -- the empty first step is deleted; the rest is carried along the empty blowing-up
      subst hY₀
      rw [BlowUpSequence.eraseEmpty_cons_of_eq_empty hY rest rfl,
          BlowUpSequence.map_eq_pullback_symm]
      set φ := BlowUpSequence.emptyBlowUpDiffeomorph hY rfl
      set g : AnalyticMap M' (blowUp ψ₀ hY) := Diffeomorph.toAnalyticMap φ.symm
      have hge' : rest.eraseEmpty.toSuccession.IsOfOrderGe (T.headTriple 1 hY hh).I 1
          (T.headTriple 1 hY hh).F.idealSheaf :=
        BlowUpSequence.isOfOrderGe_eraseEmpty rest _ 1 (T.headTriple 1 hY hh).isSnc
          (T.isOfOrderGe_tail_of_cons 1 hY hge)
      have hpb := BlowUpSequence.stoppedClause_pullback ψ₀ rest.eraseEmpty g
          φ.symm.isLocalDiffeomorph
        (T.headTriple 1 hY hh) hge' hIH
      rw [((T.headTriple 1 hY hh).isPullbackOf_pullback g φ.symm.isLocalDiffeomorph).1,
        ((T.headTriple 1 hY hh).isPullbackOf_pullback g φ.symm.isLocalDiffeomorph).2,
        AnalyticTriple.headTriple_I, AnalyticTriple.headTriple_F,
        MarkedIdealSheaf.birationalTransform_I_of_eq_empty hY rfl _ ⟨T.I, 1⟩,
        hY.cosupport_idealSheaf] at hpb
      have hπg : ∀ x, blowUpπ ψ₀ hY (g x) = x := fun x => by
        rw [← BlowUpSequence.emptyBlowUpDiffeomorph_apply hY rfl]
        exact φ.apply_symm_apply x
      have hcomp : ⇑(blowUpπ ψ₀ hY) ∘ ⇑g = id := funext hπg
      have hI :
          (T.I.pullback _ (blowUpπ ψ₀ hY).contMDiff).pullback g g.contMDiff =
          T.I := by
        change IdealSheaf.pullback ⇑g _ (IdealSheaf.pullback ⇑(blowUpπ ψ₀ hY) _ T.I) = T.I
        rw [IdealSheaf.pullback_pullback T.I ⇑(blowUpπ ψ₀ hY) (blowUpπ ψ₀ hY).contMDiff ⇑g
          g.contMDiff, IdealSheaf.pullback_congr T.I _ contMDiff_id hcomp]
        exact IdealSheaf.pullback_id_eq_self T.I
      rw [hI] at hpb
      refine FiniteSuccession.StoppedClause.of_isEmptyExtension ψ₀
        (e₀ := (OrderIso.refl T.F.ι).toOrderEmbedding.trans (HypersurfaceFamily.inlLexEmb T.F.ι))
        ⟨fun j => ?_, fun b hb => ?_⟩ hpb
      · change ⇑g ⁻¹' strictTransformSet ⇑(blowUpπ ψ₀ hY) ∅ (T.F.hyp j) = T.F.hyp j
        rw [strictTransformSet_empty_of_isClosed (blowUpπ ψ₀ hY).contMDiff.continuous
          (T.isSnc.1 j).isClosed, ← Set.preimage_comp, hcomp, Set.preimage_id]
      · obtain ⟨b', rfl⟩ : ∃ b', toLex b' = b := ⟨ofLex b, rfl⟩
        rcases b' with j | u
        · exact absurd ⟨j, rfl⟩ hb
        · change ⇑g ⁻¹' (⇑(blowUpπ ψ₀ hY) ⁻¹' ∅) = ∅
          rw [Set.preimage_empty, Set.preimage_empty]
    · rw [BlowUpSequence.eraseEmpty_cons_of_ne_empty hY rest hY₀]
      exact BlowUpSequence.stoppedClause_cons_of_forall_notMem ψ₀ hY rest.eraseEmpty T hh hIH hxY

/-! ### Concatenation along the induced triple -/

/-- The output clause is read one stage in: for `cons hY rest` it is the clause of `rest` from the
head triple (the last stage and its transforms are `rest`'s from the head triple,
`cons_markedTransformSeq_last`, `cons_totalTransformSeqFrom_last`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.outputClause_cons_iff {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (T : AnalyticTriple ψ₀ M)
    (hge : (BlowUpSequence.cons hY rest).toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf) :
    (BlowUpSequence.cons hY rest).toSuccession.OutputClause ψ₀ T.I T.F ↔
      rest.toSuccession.OutputClause ψ₀
        (T.headTriple 1 hY (T.isOfOrderGe_head_of_cons 1 hY hge)).I
        (T.headTriple 1 hY (T.isOfOrderGe_head_of_cons 1 hY hge)).F := by
  unfold FiniteSuccession.OutputClause
  rw [AnalyticTriple.headTriple_I, AnalyticTriple.headTriple_F, hY.cosupport_idealSheaf]
  erw [FiniteSuccession.cons_markedTransformSeq_last hY rest.toSuccession T.I 1,
    FiniteSuccession.cons_totalTransformSeqFrom_last hY rest.toSuccession T.F]
  exact Iff.rfl

/-- The output clause of a concatenation is the output clause of the appended list from the induced
triple, by induction on the first list with `induced_cons` and `induced_nil` (the recursion of
`boClass_induced_concat_aux`); at a `cons` the two rewrites of `outputClause_cons_iff`,
`cons_markedTransformSeq_last` and `cons_totalTransformSeqFrom_last`, with the head clause of
`hge₁`. `outputClause_cons_iff` itself asks for the order clause of the whole `cons` list, which a
concatenation does not carry, so it is not applied directly. -/
theorem _root_.AnalyticManifold.BlowUpSequence.outputClause_concat (L₁ : BlowUpSequence ψ₀ M)
    (L₂ : BlowUpSequence ψ₀ (L₁.stage (Fin.last _))) (T : AnalyticTriple ψ₀ M)
    (hge₁ : L₁.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP₂ : L₂.toSuccession.OutputClause ψ₀ (T.induced 1 L₁ hge₁).I (T.induced 1 L₁ hge₁).F) :
    (L₁.concat L₂).toSuccession.OutputClause ψ₀ T.I T.F := by
  induction L₁ with
  | nil M =>
    rw [AnalyticTriple.induced_nil] at hP₂
    exact hP₂
  | cons hY rest ih =>
    rw [AnalyticTriple.induced_cons] at hP₂
    have h' := ih L₂ _ (T.isOfOrderGe_tail_of_cons 1 hY hge₁) hP₂
    rw [AnalyticTriple.headTriple_I, AnalyticTriple.headTriple_F, hY.cosupport_idealSheaf] at h'
    unfold FiniteSuccession.OutputClause at h' ⊢
    intro x hx
    erw [FiniteSuccession.cons_markedTransformSeq_last hY (rest.concat L₂).toSuccession T.I 1] at hx
    erw [FiniteSuccession.cons_markedTransformSeq_last hY (rest.concat L₂).toSuccession T.I 1,
      FiniteSuccession.cons_totalTransformSeqFrom_last hY (rest.concat L₂).toSuccession T.F]
    exact h' x hx

end Hironaka.Manifold

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- **The predicate persists along a fibre no centre meets** (the analogue for the predicate of
`notMem_totalTransformSeqFrom_of_forall_notMem_center`): a point `x` of stage `i` off the boundary
at which the marked transform is a smooth submanifold ideal transversal to the boundary, none of
whose images at the stages `i, …, i + k − 1` lies in the centre blown up there, keeps the predicate
at every point `y` over it at stage `i + k`. At each step the blow-up is a local isomorphism off the
centre and the marking is legitimate by the order clause
(`IsSmoothTransversalIdealAt.totalTransform_of_notMem`). -/
theorem HypersurfaceFamily.IsSmoothTransversalIdealAt.stageMapAdd_of_forall_notMem_center
    (S : FiniteSuccession M) {I : AnalyticManifold.IdealSheaf M} {F : HypersurfaceFamily M}
    (hge : S.IsOfOrderGe I 1 F.idealSheaf) (hF : F.IsSnc ψ₀) (i k : ℕ) (h : i + k < S.length + 1)
    {x : S.stage ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩}
    (hx : ∀ j,
      x ∉ (S.totalTransformSeqFrom F ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩).hyp j)
    (hP : (S.totalTransformSeqFrom F
        ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩).IsSmoothTransversalIdealAt ψ₀
      (S.markedTransformSeq I 1 ⟨i, Nat.lt_of_le_of_lt (Nat.le_add_right i k) h⟩) x)
    (hcen : ∀ (l : ℕ) (hl : l < k)
      (z : S.stage ⟨i + l, Nat.lt_of_le_of_lt (Nat.add_le_add_left hl.le i) h⟩),
      S.stageMapAdd i l (Nat.lt_of_le_of_lt (Nat.add_le_add_left hl.le i) h) z = x →
      z ∉ (S.center ⟨i + l, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl i)
        (Nat.lt_succ_iff.mp h)⟩).support)
    (y : S.stage ⟨i + k, h⟩) (hy : S.stageMapAdd i k h y = x) :
    (S.totalTransformSeqFrom F ⟨i + k, h⟩).IsSmoothTransversalIdealAt ψ₀
      (S.markedTransformSeq I 1 ⟨i + k, h⟩) y := by
  induction k with
  | zero =>
    have hyx : y = x := hy
    subst hyx
    exact hP
  | succ k ih =>
    have hk : i + k < S.length + 1 := Nat.lt_of_succ_lt h
    have hk' : i + k < S.length := Nat.lt_of_succ_lt_succ h
    have hzx : S.stageMapAdd i k hk (S.map ⟨i + k, hk'⟩ y) = x := hy
    have hz := ih hk hx hP (fun l hl z hz => hcen l (Nat.lt_succ_of_lt hl) z hz) _ hzx
    have hzc : S.map ⟨i + k, hk'⟩ y ∉ (S.center ⟨i + k, hk'⟩).support :=
      hcen k (Nat.lt_succ_self k) _ hzx
    have hFk : (S.totalTransformSeqFrom F ⟨i + k, hk⟩).IsSnc ψ₀ :=
      (S.isSnc_totalTransformSeqFrom_and_boundarySeq_eq (ψ := ψ₀) hF
        (fun j => hge.hasOnlyNormalCrossingsWith j) ⟨i + k, hk⟩).1
    have hJ : ∀ a ∈ (S.center ⟨i + k, hk'⟩).support,
        (1 : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.isClosedSubmanifold_center ⟨i + k, hk'⟩).idealSheaf
          (S.markedTransformSeq I 1 ⟨i + k, hk⟩) a := by
      intro a ha
      rw [S.idealSheaf_center]
      have := hge.le_ordAlong ⟨i + k, hk'⟩ ha
      rwa [Nat.cast_one] at this
    exact HypersurfaceFamily.IsSmoothTransversalIdealAt.totalTransform_of_notMem ψ₀
      (S.isClosedSubmanifold_center ⟨i + k, hk'⟩) (S.isBlowUp_map ⟨i + k, hk'⟩) hFk hJ hzc hz

end Manifold

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) {M N : AnalyticManifold.{u} 𝕜 E}

/-- The stopped clause of a concatenation from the stopped clauses of the two lists, by induction on
the first list with `induced_cons` and `induced_nil`: at a `cons`, `stoppedClause_cons_iff` reads
the first list's clause as its stage-`0` content plus the tail's clause for the head triple, the
induction gives the tail's concatenation, and `stoppedClause_cons_of_forall_notMem` rebuilds the
clause of the `cons`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.stoppedClause_concat (L₁ : BlowUpSequence ψ₀ M)
    (L₂ : BlowUpSequence ψ₀ (L₁.stage (Fin.last _))) (T : AnalyticTriple ψ₀ M)
    (hge₁ : L₁.toSuccession.IsOfOrderGe T.I 1 T.F.idealSheaf)
    (hP₁ : L₁.toSuccession.StoppedClause ψ₀ T.I T.F)
    (hP₂ : L₂.toSuccession.StoppedClause ψ₀ (T.induced 1 L₁ hge₁).I (T.induced 1 L₁ hge₁).F) :
    (L₁.concat L₂).toSuccession.StoppedClause ψ₀ T.I T.F := by
  induction L₁ with
  | nil M =>
    rw [AnalyticTriple.induced_nil] at hP₂
    exact hP₂
  | @cons M' Y c hY rest ih =>
    rw [AnalyticTriple.induced_cons] at hP₂
    have hh := T.isOfOrderGe_head_of_cons 1 hY hge₁
    obtain ⟨hA, hR⟩ := (BlowUpSequence.stoppedClause_cons_iff ψ₀ hY rest T hge₁).mp hP₁
    have hRC := ih L₂ (T.headTriple 1 hY hh) (T.isOfOrderGe_tail_of_cons 1 hY hge₁) hR hP₂
    refine BlowUpSequence.stoppedClause_cons_of_forall_notMem ψ₀ hY (rest.concat L₂) T hh hRC
      fun x hPx hx hxY => ?_
    refine hA 0 (Nat.zero_lt_succ _) x hPx hx x rfl ?_
    change x ∈ hY.idealSheaf.support
    rw [hY.cosupport_idealSheaf]
    exact hxY

/-! ### Descent along the maximal-contact cover ([Kol07, Theorem 103, Step 3]) -/

/-- **The output clause descends per open** (the analogue of `isOfOrderGe_of_agreeFam`): a functor
`B'` on `BOClass 1` agreeing with `B` on the local maximal-contact class and commuting with local
isomorphisms inherits the output clause of `B`. On the finite shrunk maximal-contact cover `k` of
`closure U`, the pull-back `k^*(B'(T)|_U)` is `B` at the pulled-back triple and satisfies the
clause, which descends along the surjective `k` (`outputClause_of_pullback_of_surjective`). -/
theorem AnalyticFamilyFunctor.outputClauseFam_of_agreeFam
    (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass 1))
    (B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass 1))
    (hagree : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass 1 T), B'.fam T hL.1 = B.fam T hL)
    (hB' : B'.CommutesWithLocalIsos)
    (hord : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass 1 T) (U : Opens N) (hU : IsCompact (closure (U : Set N))),
      ((B.fam T hL).seqOn U hU).toSuccession.IsOfOrderGe
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I 1
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf)
    (hB : B.OutputClauseFam ψ₀) : B'.OutputClauseFam ψ₀ := by
  unfold AnalyticFamilyFunctor.OutputClauseFam
  intro N T hG U hU
  obtain ⟨C⟩ := AnalyticTriple.exists_shrunkMCCover hG hU
  have h := hB C.triple (C.localMCClass_triple hG) C.opens C.isCompact_closure_opens
  rw [C.seqOn_coverList_eq B B' hagree hB' hG hU, C.triple_pullback_inclusion_eq] at h
  exact BlowUpSequence.outputClause_of_pullback_of_surjective ψ₀ _ C.coverMap
    C.isLocalDiffeomorph_coverMap C.surjective_coverMap _
    (AnalyticFamilyFunctor.isOfOrderGe_of_agreeFam B B' hagree hB' hord T hG U hU) h

/-- **The stopped clause descends per open** (the same descent with
`stoppedClause_of_pullback_of_surjective`). -/
theorem AnalyticFamilyFunctor.stoppedClauseFam_of_agreeFam
    (B : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.LocalMCClass 1))
    (B' : AnalyticFamilyFunctor ψ₀ (AnalyticTriple.BOClass 1))
    (hagree : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass 1 T), B'.fam T hL.1 = B.fam T hL)
    (hB' : B'.CommutesWithLocalIsos)
    (hord : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N)
      (hL : AnalyticTriple.LocalMCClass 1 T) (U : Opens N) (hU : IsCompact (closure (U : Set N))),
      ((B.fam T hL).seqOn U hU).toSuccession.IsOfOrderGe
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I 1
        (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F.idealSheaf)
    (hB : B.StoppedClauseFam ψ₀) : B'.StoppedClauseFam ψ₀ := by
  unfold AnalyticFamilyFunctor.StoppedClauseFam
  intro N T hG U hU
  obtain ⟨C⟩ := AnalyticTriple.exists_shrunkMCCover hG hU
  have h := hB C.triple (C.localMCClass_triple hG) C.opens C.isCompact_closure_opens
  rw [C.seqOn_coverList_eq B B' hagree hB' hG hU, C.triple_pullback_inclusion_eq] at h
  exact BlowUpSequence.stoppedClause_of_pullback_of_surjective ψ₀ _ C.coverMap
    C.isLocalDiffeomorph_coverMap C.surjective_coverMap _
    (AnalyticFamilyFunctor.isOfOrderGe_of_agreeFam B B' hagree hB' hord T hG U hU) h

/-! ### Two member lemmas on the predicate -/

/-- Emptying a member keeps the predicate (the chart with simple normal crossings, the member's
coordinate forgotten; `HypersurfaceFamily.emptyMember`). -/
theorem _root_.Manifold.HypersurfaceFamily.IsSmoothTransversalIdealAt.emptyMember
    {F : HypersurfaceFamily M}
    {J : AnalyticManifold.IdealSheaf M} {x : M} (h : F.IsSmoothTransversalIdealAt ψ₀ J x)
        (j : F.ι) :
    (F.emptyMember j).IsSmoothTransversalIdealAt ψ₀ J x := by
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  refine ⟨c, φ, σ, fun k => cidx ⟨k.1, F.emptyMember_hyp_subset j k.1 k.2⟩,
    ⟨hφ.1, hφ.2.1, fun k y hy => ?_, fun k k' hkk' => ?_⟩, hJ, fun k i => hne _ i⟩
  · have hkj : k.1 ≠ j := fun hk => by
      have := k.2
      rw [hk, F.emptyMember_hyp_self] at this
      exact this
    rw [F.emptyMember_hyp_of_ne hkj]
    exact hφ.2.2.1 ⟨k.1, F.emptyMember_hyp_subset j k.1 k.2⟩ y hy
  · exact Subtype.ext (congrArg (Subtype.val (p := fun j => x ∈ F.hyp j)) (hφ.2.2.2 hkk'))

/-- A member not through `x` may be restored: the predicate for `F.emptyMember j` at a point
`x ∉ F.hyp j` gives the predicate for `F`. A chart with simple normal crossings at `x` constrains
only the members through `x`, and at `x ∉ F.hyp j` the two index subtypes
`{k // x ∈ (F.emptyMember j).hyp k}` and `{k // x ∈ F.hyp k}` have the same predicate
(the members of `F.emptyMember j` are `if k = j then ∅ else F.hyp k`, `emptyMember_hyp_of_ne`,
`emptyMember_hyp_self`), so the same chart with `cidx` transported is
such a chart for `F` at `x`. No closedness and no shrinking of the chart is needed. -/
theorem _root_.Manifold.HypersurfaceFamily.IsSmoothTransversalIdealAt.of_emptyMember_of_notMem
    {F : HypersurfaceFamily M} {J : AnalyticManifold.IdealSheaf M} {x : M} (j : F.ι)
        (hx : x ∉ F.hyp j)
    (h : (F.emptyMember j).IsSmoothTransversalIdealAt ψ₀ J x) :
    F.IsSmoothTransversalIdealAt ψ₀ J x := by
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  have hmem : ∀ k : {k // x ∈ F.hyp k}, x ∈ (F.emptyMember j).hyp k.1 := fun k => by
    have hkj : k.1 ≠ j := fun hk => hx (hk ▸ k.2)
    rw [F.emptyMember_hyp_of_ne hkj]
    exact k.2
  refine ⟨c, φ, σ, fun k => cidx ⟨k.1, hmem k⟩,
    ⟨hφ.1, hφ.2.1, fun k y hy => ?_, fun k k' hkk' => ?_⟩, hJ, fun k i => hne _ i⟩
  · have hkj : k.1 ≠ j := fun hk => hx (hk ▸ k.2)
    have := hφ.2.2.1 ⟨k.1, hmem k⟩ y hy
    rwa [F.emptyMember_hyp_of_ne hkj] at this
  · exact Subtype.ext
      (congrArg (Subtype.val (p := fun k => x ∈ (F.emptyMember j).hyp k)) (hφ.2.2.2 hkk'))

end Hironaka.Manifold

end
