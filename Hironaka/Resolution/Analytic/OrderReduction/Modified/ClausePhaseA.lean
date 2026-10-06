/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepCExit
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseCompose
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePhaseC
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopPersistence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial


/-!
# The stopped clause of the rounds on the nonmonomial part

The modified second step of [Wlo09, Theorem 7.4.1] at `m = 1` runs, along a shrinking chain of
opens, rounds of order reduction on the nonmonomial part `N(𝓘)` at the bound `d`, `d` descending
from `max ord N(𝓘)` to `2` (`stepAChainState`), then the monomial phase. The stopped clause of
`ClauseTools.lean` (the field `stopped_never_blownUp` of `BMOmodFam`) asks that a point at which
the stop predicate holds and which lies on no member of the boundary is never blown up later. The
centres of the rounds are of order `≥ d ≥ 2` for the transforms of `(N(𝓘), d)`
(`roundValue_isOfOrderGe_nonmonomial`); at a predicate point off the boundary the marked transform
of `(𝓘, 1)` has order `≤ 1` (`ord_le_one_of_isSmoothTransversalIdealAt`) and equals its own
nonmonomial part (the stalk of the monomial part is the unit ideal off the boundary), which the
transform identity `hid` ([Kol07, 111, Step 1]) makes the transform of `(N(𝓘), d)`; so the centre
misses the point. Stage by stage the points over such a point keep the predicate
(`IsSmoothTransversalIdealAt.stageMapAdd_of_forall_notMem_center`) and stay off the boundary
(`notMem_totalTransformSeqFrom_of_forall_notMem_center`), hence miss every centre.

* `FiniteSuccession.StoppedClause.of_forall_notMem_center_of_isSmoothTransversalIdealAt`: the
  generic shape: if no centre contains a predicate point off the boundary of its stage, the stopped
  clause holds, by a strong induction on the number of steps.
* `notMem_center_of_isSmoothTransversalIdealAt_of_nonmonomial`: the fact about one round: a list of
  order `≥ d ≥ 2` for `(N(𝓘), d)`, `d` bounding `ord N(𝓘)`, has no centre through a predicate point
  off the boundary (`ord_le_one_of_isSmoothTransversalIdealAt`, `stalkIdeal_nonmonomialPart`,
  `componentFactor_stalkIdeal_top_of_notMem`, `hid`, `ordAlongIdeal_le_ord_of_mem_support`).
* `BState.roundValue_stoppedClause`, `descentStateAux_stoppedClause`, `stepAFamOn_stoppedClause`,
  `stepAFunctor_stoppedClauseFam`: one round, the descent (`stoppedClause_shrinkAppend`), the value
  on an open (`stoppedClause_pullback`, `stoppedClause_eraseEmpty`), the functor
  (`stepAFunctor_fam_seqOn`).
* `stepACFunctor_stoppedClauseFam`: the stopped clause of the composite of the rounds and the
  monomial phase (`composeInduced_stoppedClauseFam` with `step2bFunctor_stoppedClauseFam`).

Sources: the modified second step of [Wlo09, Theorem 7.4.1]; [Kol07, Definition 66 (4′)] for the
order of a centre and the transform identity of [Kol07, 111, Step 1]; the persistence lemmas of
`StopPersistence.lean`. The statements themselves are not in the sources.
-/

public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **Centres missing every predicate point off the boundary give the stopped clause**: if no centre
of `S` contains a point of its stage at which the stop predicate holds and which lies on no member
of the boundary there, the clause holds. The points over such a point keep the predicate
(`IsSmoothTransversalIdealAt.stageMapAdd_of_forall_notMem_center`) and stay off the boundary
(`notMem_totalTransformSeqFrom_of_forall_notMem_center`), stage by stage (a strong induction on the
number of steps), hence miss the centres. -/
theorem StoppedClause.of_forall_notMem_center_of_isSmoothTransversalIdealAt (S : FiniteSuccession M)
    {I : IdealSheaf M} {F : HypersurfaceFamily M}
    (hge : S.IsOfOrderGe I 1 (F.idealSheaf (𝕜 := 𝕜) (E := E))) (hF : F.IsSnc ψ₀)
    (hc : ∀ (i : Fin S.length) (z : S.stage i.castSucc),
      (S.totalTransformSeqFrom F i.castSucc).IsSmoothTransversalIdealAt ψ₀
        (S.markedTransformSeq I 1 i.castSucc) z →
      (∀ j, z ∉ (S.totalTransformSeqFrom F i.castSucc).hyp j) → z ∉ (S.center i).support) :
    S.StoppedClause ψ₀ I F := by
  intro i k h x hP hx y hy
  have hQ : ∀ (l : ℕ) (hl : i + l < S.length + 1) (z : S.stage ⟨i + l, hl⟩),
      S.stageMapAdd i l hl z = x →
      (S.totalTransformSeqFrom F ⟨i + l, hl⟩).IsSmoothTransversalIdealAt ψ₀
        (S.markedTransformSeq I 1 ⟨i + l, hl⟩) z ∧
        ∀ j, z ∉ (S.totalTransformSeqFrom F ⟨i + l, hl⟩).hyp j := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro hl z hz
      refine ⟨HypersurfaceFamily.IsSmoothTransversalIdealAt.stageMapAdd_of_forall_notMem_center ψ₀ S
          hge hF i l hl hx hP (fun l' hl' z' hz' => ?_) z hz,
        FiniteSuccession.notMem_totalTransformSeqFrom_of_forall_notMem_center ψ₀ S hF
          (fun j => hge.hasOnlyNormalCrossingsWith j) i l hl hx (fun l' hl' z' hz' => ?_) z hz⟩
      · exact hc ⟨i + l', Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl' i) (Nat.lt_succ_iff.mp hl)⟩ z'
          (ih l' hl' _ z' hz').1 (ih l' hl' _ z' hz').2
      · exact hc ⟨i + l', Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl' i) (Nat.lt_succ_iff.mp hl)⟩ z'
          (ih l' hl' _ z' hz').1 (ih l' hl' _ z' hz').2
  exact hc ⟨i + k, h⟩ y (hQ k (Nat.lt_succ_of_lt h) y hy).1 (hQ k (Nat.lt_succ_of_lt h) y hy).2

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

section Round

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **The fact about one round** ([Kol07, Definition 66 (4′)] at `d ≥ 2` against the order bound
`ord_le_one_of_isSmoothTransversalIdealAt`): along a list of order `≥ d` for `(N(𝓘), d)` with `d`
bounding `ord N(𝓘)` and the transform identity `hid`, a point of a stage at which the stop predicate
holds for the marked transform of `(𝓘, 1)` and which lies on no member of the boundary is in no
centre. The centre carries `ord_C N_i ≥ d ≥ 2`; the nonmonomial part equals the ideal off the
boundary (the stalk of the monomial part is the unit ideal there); and the order of the mark-`1`
transform at a predicate point is at most `1`. -/
theorem notMem_center_of_isSmoothTransversalIdealAt_of_nonmonomial
    (hid : NonmonomialTransformIdentity.{u} ψ₀) (S : AnalyticTriple ψ₀ M) (R : BlowUpSequence ψ₀ M)
    {d : ℕ} (hd : 2 ≤ d) (hmax : ∀ x, ((nonmonomialTriple S).I).ord x ≤ (d : ℕ∞))
    (hR : R.toSuccession.IsOfOrderGe (nonmonomialTriple S).I d
      (S.F.idealSheaf (𝕜 := 𝕜) (E := E)))
    (i : Fin R.toSuccession.length) {z : R.toSuccession.stage i.castSucc}
    (hP : (R.toSuccession.totalTransformSeqFrom S.F i.castSucc).IsSmoothTransversalIdealAt ψ₀
      (R.toSuccession.markedTransformSeq S.I 1 i.castSucc) z)
    (hz : ∀ j, z ∉ (R.toSuccession.totalTransformSeqFrom S.F i.castSucc).hyp j) :
    z ∉ (R.toSuccession.center i).support := by
  intro hmem
  have h1d : 1 ≤ d := le_trans one_le_two hd
  have hge1 : R.toSuccession.IsOfOrderGe S.I 1 (S.F.idealSheaf (𝕜 := 𝕜) (E := E)) :=
    isOfOrderGe_of_nonmonomial hid S R le_rfl h1d hmax hR
  have hnz : (R.toSuccession.markedTransformSeq S.I 1 i.castSucc).stalkIdeal z ≠ ⊥ :=
    isNonzeroEverywhere_markedTransformSeq S.isNonzeroEverywhere hge1 i.castSucc z
  have hord1 : (R.toSuccession.markedTransformSeq S.I 1 i.castSucc).ord z ≤ 1 :=
    ord_le_one_of_isSmoothTransversalIdealAt ψ₀ hnz hP
  have hid' := hid S R 1 d le_rfl h1d hmax hR i.castSucc
  set G := R.toSuccession.totalTransformSeqFrom S.F i.castSucc with hGdef
  set J := R.toSuccession.markedTransformSeq S.I 1 i.castSucc with hJdef
  have hG' : G.IsSnc ψ₀ := (R.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq (ψ := ψ₀)
    S.isSnc (fun j => hR.hasOnlyNormalCrossingsWith j) i.castSucc).1
  have hM : (monomialPart G hG' J).stalkIdeal z = ⊤ := by
    rw [stalkIdeal_monomialPart, ← Ideal.one_eq_top]
    refine Finset.prod_eq_one fun c _ => ?_
    rw [componentFactor_stalkIdeal_top_of_notMem G hG' J c z ?_, Ideal.one_eq_top]
    rintro ⟨y, _, rfl⟩
    exact hz c.1 y.2
  have hstalk : (nonmonomialPart G hG' J).stalkIdeal z = J.stalkIdeal z := by
    rw [stalkIdeal_nonmonomialPart, hM, Submodule.top_coe, Submodule.colon_univ]
  have hle := ((hR i).2 z hmem).trans (ordAlongIdeal_le_ord_of_mem_support _ _ hmem)
  have heq : (R.toSuccession.markedTransformSeq (nonmonomialTriple S).I d i.castSucc).ord z =
      J.ord z := by
    rw [← hid']
    exact ord_congr_stalk hstalk
  rw [heq] at hle
  have hd1 : (d : ℕ∞) ≤ 1 := hle.trans hord1
  have : d ≤ 1 := by exact_mod_cast hd1
  omega

end Round

section Descent

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M}
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

include hcomp hid

/-- **The stopped clause of one round** at the bound `d ≥ 2` (mark `1`), for the restricted induced
triple: `StoppedClause.of_forall_notMem_center_of_isSmoothTransversalIdealAt` with the order clause
`roundValue_isOfOrderGe` and `notMem_center_of_isSmoothTransversalIdealAt_of_nonmonomial` at
`roundValue_isOfOrderGe_nonmonomial` and `nonmonomialOrdLe_restrict`. -/
theorem BState.roundValue_stoppedClause {W : Opens M} {d : ℕ} (st : BState T 1 W d) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    (hT : AnalyticTriple.BMOClass 1 T) (hd : 2 ≤ d) :
    (st.roundValue bo hV hVW hT (le_trans one_le_two hd)).toSuccession.StoppedClause
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      ((ChainState.inducedTriple T 1 st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).I
      ((ChainState.inducedTriple T 1 st.toChainState).pullback
        ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
        (isLocalDiffeomorph_inclusion _ _)).F := by
  have h1d : 1 ≤ d := le_trans one_le_two hd
  refine FiniteSuccession.StoppedClause.of_forall_notMem_center_of_isSmoothTransversalIdealAt _
    (st.roundValue_isOfOrderGe hcomp bo hid hV hVW hT le_rfl h1d)
    ((ChainState.inducedTriple T 1 st.toChainState).pullback
      ((st.L.stage (Fin.last _)).inclusion (st.liftOpen hVW))
      (isLocalDiffeomorph_inclusion _ _)).isSnc
    fun i z hP hz => ?_
  exact notMem_center_of_isSmoothTransversalIdealAt_of_nonmonomial hid _ _ hd
    (st.nonmonomialOrdLe_restrict hcomp hVW)
    (st.roundValue_isOfOrderGe_nonmonomial hcomp bo hV hVW hT h1d) i hP hz

variable (T) (hT : AnalyticTriple.BMOClass 1 T) (t : ℕ) (ht : 2 ≤ t)
  (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))

/-- **The stopped clause along the descent** (threshold `t ≥ 2`): the initial state is the empty
list, and each link appends a round at a bound `d ≥ t ≥ 2` (`stoppedClause_shrinkAppend` with
`BState.roundValue_stoppedClause`). -/
theorem descentStateAux_stoppedClause :
    ∀ (j : ℕ) (hj : j ≤ r) (hjt : j ≤ D + 1 - t),
      (descentStateAux T 1 hT bo hcomp hid t le_rfl (by omega) W hW r hWsub D hD j hj
        hjt).L.toSuccession.StoppedClause (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (T.pullback (M.inclusion (W j)) (isLocalDiffeomorph_inclusion M (W j))).I
        (T.pullback (M.inclusion (W j)) (isLocalDiffeomorph_inclusion M (W j))).F := by
  intro j
  induction j with
  | zero =>
    intro hj hjt i k h
    exact absurd h (Nat.not_lt_zero _)
  | succ j ih =>
    intro hj hjt
    have hjt' : j ≤ D + 1 - t := Nat.le_of_succ_le hjt
    have hj' : j ≤ r := Nat.le_of_succ_le hj
    have hd : 2 ≤ D - j := by omega
    set st := descentStateAux T 1 hT bo hcomp hid t le_rfl (by omega) W hW r hWsub D hD j hj' hjt'
    have h := st.L.stoppedClause_shrinkAppend
      (M.restrictLE (ChainState.le_of_closure_subset (hWsub j hj)))
      (isLocalDiffeomorph_restrictLE _)
      (T.pullback (M.inclusion (W j)) (isLocalDiffeomorph_inclusion M (W j))) st.hge (ih hj' hjt')
      (st.roundValue bo (hW (j + 1)) (hWsub j hj) hT (le_trans one_le_two hd))
      (st.roundValue_isOfOrderGe hcomp bo hid (hW (j + 1)) (hWsub j hj) hT le_rfl
        (le_trans one_le_two hd))
      (st.roundValue_stoppedClause hcomp bo hid (hW (j + 1)) (hWsub j hj) hT hd)
    rw [AnalyticTriple.pullback_inclusion_restrictLE T
      (ChainState.le_of_closure_subset (hWsub j hj))] at h
    exact h

end Descent

section Value

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
  (hT : AnalyticTriple.BMOClass 1 T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-- **The stopped clause of the value of the rounds on `U`** (the modified second step of
[Wlo09, Theorem 7.4.1], `t = 2`): the final state of the descent (`descentStateAux_stoppedClause`
at the canonical chain), restricted to `U` (`stoppedClause_pullback`) and cleaned of its empty
blow-ups (`stoppedClause_eraseEmpty`). -/
theorem stepAFamOn_stoppedClause (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (stepAFamOn T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).toSuccession.StoppedClause
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  have hP :
      (stepAChainState T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).L.toSuccession.StoppedClause
        (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (T.pullback (M.inclusion (stepAChainOpens U hU (stepALinks T 2 U hU)))
          (isLocalDiffeomorph_inclusion _ _)).I
        (T.pullback (M.inclusion (stepAChainOpens U hU (stepALinks T 2 U hU)))
          (isLocalDiffeomorph_inclusion _ _)).F :=
    descentStateAux_stoppedClause T hcomp bo hid hT 2 le_rfl (stepAChainOpens U hU)
      (fun k => isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) k)
      (stepALinks T 2 U hU)
      (fun k _ => closure_shrinkChain_succ_subset hU (closure_subset_stepAOuter U hU) k)
      (stepABound T U hU) (stepABound_bound T U hU)
      (descentLength 2 (stepABound T U hU)) le_rfl le_rfl
  have hge := (stepAChainState T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).hge
  have h := BlowUpSequence.stoppedClause_pullback (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (stepAChainState T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU).L
    (M.restrictLE (le_stepAChainOpens U hU _)) (isLocalDiffeomorph_restrictLE _) _ hge hP
  have hge' := AnalyticTriple.isOfOrderGe_pullback _ 1 _ hge
    (M.restrictLE (le_stepAChainOpens U hU _)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE] at h hge'
  exact BlowUpSequence.stoppedClause_eraseEmpty _ _ _ hge' h

variable {T hT}

/-- **The stopped clause of the functor of the rounds** (`stepAFunctor` at `m = 1`, `t = 2`;
`stepAFunctor_fam_seqOn`). -/
theorem stepAFunctor_stoppedClauseFam :
    (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two).StoppedClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  unfold AnalyticFamilyFunctor.StoppedClauseFam
  intro M T hT U hU
  rw [stepAFunctor_fam_seqOn]
  exact stepAFamOn_stoppedClause T hT bo hcomp hid U hU

/-- **The stopped clause of the composite of the rounds and the monomial phase** (`stepACFunctor`):
`composeInduced_stoppedClauseFam` from `stepAFunctor_stoppedClauseFam` and
`step2bFunctor_stoppedClauseFam`, with `step2bFam_isOfOrderGe`. -/
theorem stepACFunctor_stoppedClauseFam :
    (stepACFunctor bo hcomp hid).StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  exact AnalyticFamilyFunctor.composeInduced_stoppedClauseFam
    (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU))
    (stepAFunctor_commutesWithLocalIsos 1 bo hcomp hid 2 le_rfl one_le_two)
    step2bFunctor_commutesWithLocalIsos step2bFunctor_indifferentToEmptyMembers
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (AnalyticFamilyFunctor.bmoClass_classInducedEraseEmptyClosed 1 1)
    (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    (fun T' hT' U' hU' => step2bFam_isOfOrderGe T' hT' U' hU')
    (stepAFunctor_stoppedClauseFam bo hcomp hid) step2bFunctor_stoppedClauseFam

end Value

end Hironaka.Manifold.BMOmod

end
