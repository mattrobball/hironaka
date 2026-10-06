/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bFunctor
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StopPersistence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial


/-!
# The stopped clause of the monomial phase

The monomial phase of the modified second step of [Wlo09, Theorem 7.4.1] blows up, while a boundary
member is active, the positive locus of the greatest active member: a centre inside the boundary
(`step2bCenter_subset_support`). The stopped clause of `ClauseTools.lean` (the field
`stopped_never_blownUp` of `BMOmodFam`) asks that a point at which the stop predicate holds and
which lies on no member of the boundary is never blown up later; for a phase whose centres lie in
the boundary this follows from the persistence of "off the boundary" alone
(`notMem_totalTransformSeqFrom_of_forall_notMem_center`, `StopPersistence.lean`): the points over
such a point stay off the boundary stage by stage, hence outside every centre.

* `FiniteSuccession.StoppedClause.of_forall_center_subset_support`: the generic shape: centres in
  the support of the current boundary family give the stopped clause, by a strong induction on the
  number of steps. The predicate is part of the clause because the stop rule of
  [Wlo09, Theorem 7.4.1] speaks of the points where the algorithm stopped (the field
  `stopped_never_blownUp`); this proof does not need it, since with the centres inside the boundary
  every point off the boundary, stopped or not, is never blown up.
* `center_support_subset_step2bPhase`: the centres of the monomial phase lie in the boundary at
  every stage, along the recursion of `step2bPhase` (`step2bPhase_succ_of_nonempty`): the head
  centre in `T.F.support`, the tail's centres in the boundary from the triple after the step, whose
  family is the total transform (`stepTriple_F`, `cons_totalTransformSeqFromAux_succ`).
* `step2bFunctor_stoppedClauseFam`: the stopped clause of the functor `step2bFunctor`: the value on
  an open is the complete phase of the restricted triple (`step2bFam_seqOn`); the normal-crossings
  clause from `isOfOrderGe_step2bPhase`.

Sources: the monomial phase of [Wlo09, Theorem 7.4.1]; [Kol07, Definition 66]; the persistence
lemmas of `StopPersistence.lean`. The statements themselves are not in the sources.
-/

public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **Centres inside the boundary give the stopped clause**: if every centre of `S` lies in the
support of the current boundary family, no point over a point off the boundary is ever blown up.
By `notMem_totalTransformSeqFrom_of_forall_notMem_center` the points over `x` stay off the boundary,
stage by stage (a strong induction on the number of steps), hence outside the centres. The
predicate is part of the clause because the stop rule of [Wlo09, Theorem 7.4.1] speaks of the
points where the algorithm stopped (the field `stopped_never_blownUp` of `BMOmodFam`); this proof
does not need it, since with the centres inside the boundary every point off the boundary, stopped
or not, is never blown up. -/
theorem StoppedClause.of_forall_center_subset_support (S : FiniteSuccession M)
    {I : IdealSheaf M} {F : HypersurfaceFamily M} (hF : F.IsSnc ψ₀)
    (h3 : ∀ i : Fin S.length, (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
      i.castSucc).HasOnlyNormalCrossingsWith (S.center i))
    (hc : ∀ i : Fin S.length,
      (S.center i).support ⊆ (S.totalTransformSeqFrom F i.castSucc).support) :
    S.StoppedClause ψ₀ I F := by
  intro i k h x _ hx y hy
  have hQ : ∀ (l : ℕ) (hl : i + l < S.length + 1) (z : S.stage ⟨i + l, hl⟩),
      S.stageMapAdd i l hl z = x → ∀ j, z ∉ (S.totalTransformSeqFrom F ⟨i + l, hl⟩).hyp j := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro hl z hz
      refine FiniteSuccession.notMem_totalTransformSeqFrom_of_forall_notMem_center ψ₀ S hF h3 i l hl
        hx (fun l' hl' z' hz' hmem => ?_) z hz
      have hsup := hc ⟨i + l', Nat.lt_of_lt_of_le (Nat.add_lt_add_left hl' i)
        (Nat.lt_succ_iff.mp hl)⟩ hmem
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hsup
      exact ih l' hl' _ z' hz' j hj
  intro hmem
  have hsup := hc ⟨i + k, h⟩ hmem
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hsup
  exact hQ k (Nat.lt_succ_of_lt h) y hy j hj

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **The centres of the monomial phase lie in the boundary** (the centres are the positive loci of
active members, `step2bCenter_subset_support`), at every stage of the phase, along the recursion of
`step2bPhase`: the head centre in `T.F.support`, the tail's centres in the boundary from the triple
after the step, whose family is the total transform (`stepTriple_F`,
`cons_totalTransformSeqFromAux_succ`). -/
theorem center_support_subset_step2bPhase :
    ∀ (k : ℕ) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
      (hT : AnalyticTriple.BMOClass 1 T) (i : Fin (step2bPhase k T hT).toSuccession.length),
      ((step2bPhase k T hT).toSuccession.center i).support ⊆
        ((step2bPhase k T hT).toSuccession.totalTransformSeqFrom T.F i.castSucc).support := by
  intro k
  induction k with
  | zero => intro M T hT i; exact i.elim0
  | succ k ih =>
    intro M T hT i
    by_cases hne : (activeMembers T).Nonempty
    · revert i
      rw [step2bPhase_succ_of_nonempty T hT k hne]
      intro i
      obtain ⟨i, hi⟩ := i
      set hfin := activeMembers_finite T hT
      set hY := stepCenter T hfin hne
      set L' := step2bPhase k (stepTriple T hfin hne) (bmoClass_stepTriple T hfin hne hT)
      rcases i with _ | j
      · change hY.idealSheaf.support ⊆ T.F.support
        rw [hY.cosupport_idealSheaf]
        exact step2bCenter_subset_support T hfin hne
      · have h := ih (stepTriple T hfin hne) (bmoClass_stepTriple T hfin hne hT)
          ⟨j, Nat.lt_of_succ_lt_succ hi⟩
        have e : (BlowUpSequence.cons hY L').toSuccession.totalTransformSeqFromAux T.F (j + 1)
              (Nat.lt_succ_of_lt hi) =
            L'.toSuccession.totalTransformSeqFromAux
              (T.F.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support) j
              (Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ hi)) :=
          FiniteSuccession.cons_totalTransformSeqFromAux_succ hY L'.toSuccession T.F j
            (Nat.lt_succ_of_lt hi)
        change _ ⊆ ((BlowUpSequence.cons hY L').toSuccession.totalTransformSeqFromAux T.F (j + 1)
          (Nat.lt_succ_of_lt hi)).support
        rw [e, hY.cosupport_idealSheaf]
        exact h
    · revert i
      rw [step2bPhase_succ_of_not_nonempty T hT k hne]
      intro i
      exact i.elim0

/-- **The stopped clause of the monomial phase** (the field `stopped_never_blownUp` of `BMOmodFam`
for `step2bFunctor`): the value on every open is the complete phase of the restricted triple
(`step2bFam_seqOn`), its centres lie in the boundary (`center_support_subset_step2bPhase`), so
`StoppedClause.of_forall_center_subset_support` applies with the normal-crossings clause of
`isOfOrderGe_step2bPhase`. -/
theorem step2bFunctor_stoppedClauseFam : (step2bFunctor ψ₀).StoppedClauseFam ψ₀ := by
  unfold AnalyticFamilyFunctor.StoppedClauseFam
  intro M T hT U hU
  rw [step2bFunctor_fam, step2bFam_seqOn]
  exact FiniteSuccession.StoppedClause.of_forall_center_subset_support _
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
    (fun i => (isOfOrderGe_step2bPhase _ _ _).hasOnlyNormalCrossingsWith i)
    (center_support_subset_step2bPhase _ _ _)

end Hironaka.Manifold.BMOmod

end
