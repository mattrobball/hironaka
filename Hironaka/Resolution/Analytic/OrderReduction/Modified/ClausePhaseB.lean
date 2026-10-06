/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePhaseBCore
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBGlobal
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseStep21
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseBridge
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.BoundaryEnlarge
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingPrep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseCompose
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePushforward
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Hironaka.Resolution.Analytic.OrderReduction.Step21FamCosupp
import Hironaka.Resolution.Analytic.OrderReduction.Step22FamFull
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# The two stop clauses of the modified first step, assembled

The modified first step of [Wlo09, Theorem 7.4.1] is the assembly of Kollár's Step 2 at the datum
`stepBData`: the chain of Step 2.1 from the unmodified marked order reduction one dimension down
(`hfStep2FamChain`), the link of Step 2.2 at the greatest member `H_r` with the modified core
(`hfStep22FamOn`), appended, restricted and cleaned of empty blow-ups (`hfStep2SeqFamOn`); the local
functor `hfLocalFunctorFam 1` on the local maximal-contact class; the descent `stepBFunctor` to the
class of `BO_{n,1}`. This module proves the stopped clause and the output clause of
`ClauseTools.lean` along that assembly from three pieces: the chain's stopped clause
(`ClauseStep21.lean`), the clauses of the data of the step with respect to the boundary without the
member (`ClausePhaseBCore.lean`), and the bridges and composition lemmas (`ClauseBridge.lean`,
`ClauseCompose.lean`, `ClauseTools.lean`).

* `membersSubset_emptyMember_idxHOf_induced`: the boundary `E^{exc} + H_r` of the triple of
  [Kol07, Theorem 103, Step 2.2] without `H_r` is a sub-family of the full transformed boundary
  (its members are the exceptional divisors, at the indices `exceptionalEmb`): the hypothesis of
  `StoppedClause.of_membersSubset` for the link.
* `exists_hyp_emptyMember_eq_of_le_ord`, `exists_hyp_emptyMember_eq_of_le_ord'`: a member of the
  full boundary through a point of order `≥ 1` at the end of the link is a member of the boundary
  of Step 2.2 without `H_r`. The transforms of the original members are excluded by the chain's
  cosupport clause: the point lies over a point of order `≥ 1` on such a transform
  (`ord_markedTransformSeq_stageMapAdd_eq_zero`, `notMem_strictTransformSeq_of_stageMapAdd`). This
  is the hypothesis of `OutputClause.of_forall_mem`.
* `hfStep22FamOn_stoppedClause_induced`, `hfStep22FamOn_outputClause_induced`: the link's two
  clauses for the restricted induced triple: the clauses of the data of the step at the re-tuned
  triple of Step 2.2 and its greatest member (`greatestIdx_eq`; the maximal contact of `H_r` by
  `maximalContact_persistsFam_tuned`; the tuning is the identity at the mark `1`, `tuned_one`), the
  boundary changed by `StoppedClause.of_membersSubset` and `OutputClause.of_forall_mem` with the
  order clause at `E − H_r` (`HFamData.IsOfOrderGeEmptyMemberFam`) and at the full boundary
  (`hfStep22FamOn_isOfOrderGe_full`).
* `hfStep2SeqFamOn_stoppedClause`, `hfStep2SeqFamOn_outputClause`: the value of Step 2 on the open:
  the chain's stopped clause and the link's clauses composed at the last link
  (`stoppedClause_shrinkAppend`, `outputClause_shrinkAppend`), restricted (`stoppedClause_pullback`,
  `outputClause_pullback`) and cleaned (`stoppedClause_eraseEmpty`, `outputClause_eraseEmpty`), as
  in `hfStep2SeqFamOn_isOfOrderGe`.
* `hfStep2FamOn_stoppedClause`, `hfStep2FamOn_outputClause`, `hfLocalFunctorFamOn_stoppedClause`,
  `hfLocalFunctorFamOn_outputClause`: with the class's hypersurface of maximal contact, and at the
  mark `1` on the tuned triple (`tuned_pullback`, `tuned_one` at the restricted triple).
* `stepBLocalFunctorFam_stoppedClauseFam`, `stepBLocalFunctorFam_outputClauseFam`,
  `stepBFunctor_stoppedClauseFam`, `stepBFunctor_outputClauseFam`: the local functor of the
  modified first step and its descent along the maximal-contact cover
  (`stoppedClauseFam_of_agreeFam`, `outputClauseFam_of_agreeFam`), from the clauses `hR8` and
  `hR1` of the functor one dimension down.

Sources: the modified first step of [Wlo09, Theorem 7.4.1]; [Kol07, Theorem 103, Steps 2–3] and
[Kol07, 104, Step 2.1] (the full boundary from the boundary of Step 2.2); [Kol07, Corollary 85].
The statements themselves are not in the sources.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {s : ℕ}

namespace BO

open _root_.Manifold

section Bridges

variable {X : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ X) (L : BlowUpSequence ψ₀ X)
  (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) {H : Set X}
  (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)
  (O : Opens (L.stage (Fin.last _)))

omit [FiniteDimensional 𝕜 E] in
/-- **The boundary of Step 2.2 without `H_r` is a sub-family of the full transformed boundary**
(restricted to an open): its members are the exceptional divisors `E^{exc}_k`, members of the full
boundary at the indices `exceptionalEmb k` (`hyp_exceptionalEmb`), and the emptied slot of `H_r`.
The hypothesis of `StoppedClause.of_membersSubset` for the link of Step 2.2. -/
theorem membersSubset_emptyMember_idxHOf_induced :
    (((step22TripleOf T L hL hsnc).pullback ((L.stage (Fin.last _)).inclusion O)
      (isLocalDiffeomorph_inclusion _ _)).F.emptyMember (idxHOf T s L hL hsnc)).MembersSubset
      ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F := by
  intro a
  obtain ⟨a', rfl⟩ : ∃ a', toLex a' = a := ⟨ofLex a, rfl⟩
  rcases a' with e | ⟨⟩
  · -- an exceptional divisor of the chain: a member of the full boundary at `exceptionalEmb`
    right
    refine ⟨L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 e, ?_⟩
    have hne : (toLex (Sum.inl e) : (((step22TripleOf T L hL hsnc).pullback
        ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F).ι) ≠
        idxHOf T s L hL hsnc :=
      fun h => Sum.inl_ne_inr (toLex.injective h)
    exact (HypersurfaceFamily.emptyMember_hyp_of_ne _ hne).trans
      (congrArg (Set.preimage _)
        (L.toSuccession.hyp_exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 e)).symm
  · -- the emptied slot of `H_r`
    left
    exact HypersurfaceFamily.emptyMember_hyp_self _ _

omit [FiniteDimensional 𝕜 E] in
/-- **A member of the full transformed boundary through a point of order `≥ 1` at the last stage of
the run of Step 2.2 is a member of the boundary of Step 2.2 without `H_r`** (the hypothesis of
`OutputClause.of_forall_mem`): by `originalIdxAux_or_exceptionalEmb` the member is the run's
transform of a member of the full boundary below or an exceptional divisor of the run; a member
below is the chain's transform of an original member, which is excluded, since the point lies over
a point of order `≥ 1` (`ord_markedTransformSeq_stageMapAdd_eq_zero`) on that transform
(`notMem_strictTransformSeq_of_stageMapAdd`), against the chain's cosupport clause `hdis`, or an
exceptional divisor of the chain, a member of the boundary of Step 2.2 (`hyp_originalIdx`,
`hyp_exceptionalEmb`). -/
theorem exists_hyp_emptyMember_eq_of_le_ord (hs : s = 1)
    (hdis : ∀ j, Disjoint
      {x | (s : ℕ∞) ≤ (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).ord x}
      (L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)))
    (S' : FiniteSuccession ((L.stage (Fin.last _)).restrict O))
    (hge : S'.IsOfOrderGe ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).I 1
      (((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf (𝕜 := 𝕜) (E := E)))
    (x : S'.stage (Fin.last _))
    (hord : (1 : ℕ∞) ≤ (S'.markedTransformSeq ((T.induced s L hL).pullback
      ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).I 1
      (Fin.last _)).ord x)
    (k : ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.ι)
    (hk : x ∈ (S'.totalTransformSeqFrom ((T.induced s L hL).pullback
      ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _)).hyp
      (S'.originalIdx _ (Fin.last _) k)) :
    ∃ k', (S'.totalTransformSeqFrom (((step22TripleOf T L hL hsnc).pullback
        ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F.emptyMember
        (idxHOf T s L hL hsnc)) (Fin.last _)).hyp k' =
      (S'.totalTransformSeqFrom ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _)).hyp
        (S'.originalIdx _ (Fin.last _) k) := by
  subst hs
  rcases L.toSuccession.originalIdxAux_or_exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 k with
    ⟨j, rfl⟩ | ⟨e, rfl⟩
  · -- the run's transform of the chain's transform of an original member: excluded
    exfalso
    have e2 : ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.hyp
          (L.toSuccession.originalIdxAux T.F (Fin.last _).1 (Fin.last _).2 j) =
        ⇑((L.stage (Fin.last _)).inclusion O) ⁻¹'
          L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _) :=
      congrArg (Set.preimage _) (L.toSuccession.hyp_originalIdx T.F (Fin.last _) j)
    have e3 := (S'.hyp_originalIdx ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _)
        (L.toSuccession.originalIdxAux T.F (Fin.last _).1 (Fin.last _).2 j)).trans
      (congrArg (fun B => S'.strictTransformSeq B (Fin.last _)) e2)
    have hk1 : x ∈ S'.strictTransformSeq (⇑((L.stage (Fin.last _)).inclusion O) ⁻¹'
        L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)) (Fin.last _) :=
      Eq.mp (congrArg (fun B => x ∈ B) e3) hk
    have hAcl : IsClosed (⇑((L.stage (Fin.last _)).inclusion O) ⁻¹'
        L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)) :=
      (L.toSuccession.isClosed_strictTransformSeq (T.F.hyp j) (T.isSnc.1 j).isClosed _).preimage
        ((L.stage (Fin.last _)).inclusion O).contMDiff.continuous
    -- read the last stage as `0 + length` to use the lemmas along `stageMapAdd`
    have hlast : (Fin.last S'.length : Fin (S'.length + 1)) = ⟨0 + S'.length, by omega⟩ :=
      Fin.ext (Nat.zero_add _).symm
    clear e2 e3
    revert x
    rw [hlast]
    intro x hord hk hk1
    have hlt : 0 + S'.length < S'.length + 1 := by omega
    -- the image `z` of `x` at the stage `0` lies on the chain's transform …
    have hzA : S'.stageMapAdd 0 S'.length hlt x ∈ ⇑((L.stage (Fin.last _)).inclusion O) ⁻¹'
        L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _) := by
      by_contra hz
      exact S'.notMem_strictTransformSeq_of_stageMapAdd hAcl 0 S'.length hlt hz x rfl hk1
    -- … and has order `≥ 1`
    have hordz : (1 : ℕ∞) ≤ (S'.markedTransformSeq ((T.induced 1 L hL).pullback
        ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).I 1
        ⟨0, by omega⟩).ord (S'.stageMapAdd 0 S'.length hlt x) := by
      by_contra h0
      have h0' : (S'.markedTransformSeq ((T.induced 1 L hL).pullback
          ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).I 1
          ⟨0, by omega⟩).ord (S'.stageMapAdd 0 S'.length hlt x) = 0 := by
        by_contra hne
        exact h0 (Order.one_le_iff_ne_zero.mpr hne)
      have := S'.ord_markedTransformSeq_stageMapAdd_eq_zero hge 0 S'.length hlt h0' x rfl
      rw [this] at hord
      exact absurd hord (by simp)
    -- against the chain's cosupport clause, read at the point of the chain's last stage
    have hordz' : (1 : ℕ∞) ≤ (L.toSuccession.markedTransformSeq T.I 1 (Fin.last _)).ord
        ((L.stage (Fin.last _)).inclusion O (S'.stageMapAdd 0 S'.length hlt x)) := by
      have e := IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt
        ⇑((L.stage (Fin.last _)).inclusion O) ((L.stage (Fin.last _)).inclusion O).contMDiff
        (L.toSuccession.markedTransformSeq T.I 1 (Fin.last _))
        (isLocalDiffeomorph_inclusion _ O (S'.stageMapAdd 0 S'.length hlt x))
      exact hordz.trans_eq e
    have hdis' := hdis j
    rw [Nat.cast_one] at hdis'
    exact Set.disjoint_left.mp hdis' hordz' hzA
  · -- an exceptional divisor of the chain: the same set is the positional member `inl e`
    refine ⟨S'.originalIdx _ (Fin.last _) (toLex (Sum.inl e)), ?_⟩
    have hne : (toLex (Sum.inl e) : (((step22TripleOf T L hL hsnc).pullback
        ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F).ι) ≠
        idxHOf T 1 L hL hsnc :=
      fun h => Sum.inl_ne_inr (toLex.injective h)
    have e1 : (((step22TripleOf T L hL hsnc).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.emptyMember (idxHOf T 1 L hL hsnc)).hyp
          (toLex (Sum.inl e)) =
        ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion O)
          (isLocalDiffeomorph_inclusion _ _)).F.hyp
            (L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 e) :=
      (HypersurfaceFamily.emptyMember_hyp_of_ne _ hne).trans
        (congrArg (Set.preimage _)
          (L.toSuccession.hyp_exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 e)).symm
    exact (S'.hyp_originalIdx (((step22TripleOf T L hL hsnc).pullback
        ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F.emptyMember
        (idxHOf T 1 L hL hsnc)) (Fin.last _) (toLex (Sum.inl e))).trans
      ((congrArg (fun B => S'.strictTransformSeq B (Fin.last _)) e1).trans
        (S'.hyp_originalIdx ((T.induced 1 L hL).pullback ((L.stage (Fin.last _)).inclusion O)
          (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _)
          (L.toSuccession.exceptionalEmb T.F (Fin.last _).1 (Fin.last _).2 e)).symm)

omit [FiniteDimensional 𝕜 E] in
/-- `exists_hyp_emptyMember_eq_of_le_ord` for every member index of the run's last boundary (the
exceptional divisors of the run are members of both boundaries at the same index). -/
theorem exists_hyp_emptyMember_eq_of_le_ord' (hs : s = 1)
    (hdis : ∀ j, Disjoint
      {x | (s : ℕ∞) ≤ (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).ord x}
      (L.toSuccession.strictTransformSeq (T.F.hyp j) (Fin.last _)))
    (S' : FiniteSuccession ((L.stage (Fin.last _)).restrict O))
    (hge : S'.IsOfOrderGe ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).I 1
      (((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F.idealSheaf (𝕜 := 𝕜) (E := E)))
    (x : S'.stage (Fin.last _))
    (hord : (1 : ℕ∞) ≤ (S'.markedTransformSeq ((T.induced s L hL).pullback
      ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).I 1
      (Fin.last _)).ord x)
    (m : (S'.totalTransformSeqFrom ((T.induced s L hL).pullback
      ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _)).ι)
    (hm : x ∈ (S'.totalTransformSeqFrom ((T.induced s L hL).pullback
      ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F
      (Fin.last _)).hyp m) :
    ∃ k', (S'.totalTransformSeqFrom (((step22TripleOf T L hL hsnc).pullback
        ((L.stage (Fin.last _)).inclusion O) (isLocalDiffeomorph_inclusion _ _)).F.emptyMember
        (idxHOf T s L hL hsnc)) (Fin.last _)).hyp k' =
      (S'.totalTransformSeqFrom ((T.induced s L hL).pullback ((L.stage (Fin.last _)).inclusion O)
        (isLocalDiffeomorph_inclusion _ _)).F (Fin.last _)).hyp m := by
  rcases S'.originalIdxAux_or_exceptionalEmb _ (Fin.last _).1 (Fin.last _).2 m with
    ⟨k, rfl⟩ | ⟨e', rfl⟩
  · exact exists_hyp_emptyMember_eq_of_le_ord T L hL hsnc O hs hdis S' hge x hord k hm
  · exact ⟨S'.exceptionalEmb _ (Fin.last _).1 (Fin.last _).2 e',
      (S'.hyp_exceptionalEmb _ (Fin.last _).1 (Fin.last _).2 e').trans
        (S'.hyp_exceptionalEmb _ (Fin.last _).1 (Fin.last _).2 e').symm⟩

end Bridges

section Link

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ) (d : HFData ψ₀ s)
  (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
  {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))

/-- **The stopped clause of the link of Step 2.2 for the restricted induced triple** (the mark `1`):
the clause of the data of the step (`HFamData.StoppedClauseFam`) at the re-tuned triple of Step 2.2
(`tuned_one`: the tuning is the identity at the mark `1`) at its greatest member `H_r`
(`greatestIdx_eq`), whose maximal contact is `maximalContact_persistsFam_tuned`; with respect to
the boundary without `H_r`, hence with respect to the full transformed boundary by
`StoppedClause.of_membersSubset` with `membersSubset_emptyMember_idxHOf_induced` and the order
clause at that boundary (`HFamData.IsOfOrderGeEmptyMemberFam`). -/
theorem hfStep22FamOn_stoppedClause_induced (hs : s = 1) (hhf8 : d.hf.StoppedClauseFam)
    (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfStep22FamOn T s d hT U hU hH hle).toSuccession.StoppedClause ψ₀
      (((T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced s (hfStep2FamChain T s d hT U hU).L
        (hfStep2FamChain T s d hT U hU).hge).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I
      (((T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced s (hfStep2FamChain T s d hT U hU).L
        (hfStep2FamChain T s d hT U hU).hge).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).F := by
  subst hs
  have hT₂ := stepHClass_hfStep22TripleFam T 1 d hT U hU hH hle
  have hj : greatestIdx (stepHClass_tuned hT₂) = toLex (Sum.inr PUnit.unit) :=
    greatestIdx_eq _ fun k => le_toLex_inr k
  -- the maximal contact of `H_r` for the re-tuned Step-2.2 triple
  have hmc := maximalContact_persistsFam_tuned
    (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _))
    (boClass_pullback_inclusion_of_boClass T _ hT) (hfStep2FamChain T 1 d hT U hU).L
    (hfStep2FamChain T 1 d hT U hU).hge
    (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
    (idealSheaf_preimage_le_iteratedDeriv_inclusion T 1 hH hle _)
  unfold hfStep22FamOn
  rw [hfStep22Functor_fam_seqOn]
  -- the H-step data's clauses at the re-tuned triple and its greatest member
  have h8 := hhf8 ((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1)
    (AnalyticTriple.boClass_tuned hT₂.1) (greatestIdx (stepHClass_tuned hT₂))
    (by rw [hj]; exact hmc) _ (isCompact_closure_hfStep2ReadOpen T 1 d hT U hU)
  have ho := hhfo ((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1)
    (AnalyticTriple.boClass_tuned hT₂.1) (greatestIdx (stepHClass_tuned hT₂))
    (by rw [hj]; exact hmc) _ (isCompact_closure_hfStep2ReadOpen T 1 d hT U hU)
  rw [hj] at h8 ho ⊢
  -- the ideal: the tuning is the identity at the mark `1`
  have eI : (((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1).pullback
      (((hfStep2FamChain T 1 d hT U hU).L.stage (Fin.last _)).inclusion
        (hfStep2ReadOpen T 1 d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I =
      (((T.pullback (M.inclusion (step2OpenW T 1 hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced 1 (hfStep2FamChain T 1 d hT U hU).L
        (hfStep2FamChain T 1 d hT U hU).hge).pullback
        (((hfStep2FamChain T 1 d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T 1 d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I := by
    rw [AnalyticTriple.tuned_one]
    rfl
  rw [eI] at h8
  -- the boundary: `StoppedClause.of_membersSubset` with `membersSubset_emptyMember_idxHOf_induced`,
  -- the simple normal crossings of the transforms of `E − H_r` from the order clause at `E − H_r`
  have hF₀ : ((((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1).pullback
      (((hfStep2FamChain T 1 d hT U hU).L.stage (Fin.last _)).inclusion
        (hfStep2ReadOpen T 1 d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).F.emptyMember
      (toLex (Sum.inr PUnit.unit))).IsSnc ψ₀ :=
    (((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1).pullback _
      (isLocalDiffeomorph_inclusion _ _)).isSnc.emptyMember _
  refine FiniteSuccession.StoppedClause.of_membersSubset ψ₀ _
    (fun i => (FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq _ hF₀
      (fun j => ho.hasOnlyNormalCrossingsWith j) i).1)
    (membersSubset_emptyMember_idxHOf_induced
      (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _))
      (hfStep2FamChain T 1 d hT U hU).L (hfStep2FamChain T 1 d hT U hU).hge
      (isSnc_step22BoundaryOf _ 1 _ (boClass_pullback_inclusion_of_boClass T _ hT)
        (hfStep2FamChain T 1 d hT U hU).hge
        (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
        (idealSheaf_preimage_le_iteratedDeriv_inclusion T 1 hH hle _))
      (hfStep2ReadOpen T 1 d hT U hU)) h8

/-- **The output clause of the link of Step 2.2 for the restricted induced triple**: the clause of
the data of the step (`HFamData.OutputClauseFam`) as in `hfStep22FamOn_stoppedClause_induced`, with
respect to the full transformed boundary by `OutputClause.of_forall_mem` with
`exists_hyp_emptyMember_eq_of_le_ord'` (the chain's cosupport clause `step21FamAux_cosupp_disjoint`,
an empty member having empty strict transform) and the full-boundary order clause
`hfStep22FamOn_isOfOrderGe_full`. -/
theorem hfStep22FamOn_outputClause_induced (hs : s = 1) (hhf1 : d.hf.OutputClauseFam)
    (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfStep22FamOn T s d hT U hU hH hle).toSuccession.OutputClause ψ₀
      (((T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced s (hfStep2FamChain T s d hT U hU).L
        (hfStep2FamChain T s d hT U hU).hge).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I
      (((T.pullback (M.inclusion (step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced s (hfStep2FamChain T s d hT U hU).L
        (hfStep2FamChain T s d hT U hU).hge).pullback
        (((hfStep2FamChain T s d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T s d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).F := by
  subst hs
  have hT₂ := stepHClass_hfStep22TripleFam T 1 d hT U hU hH hle
  have hj : greatestIdx (stepHClass_tuned hT₂) = toLex (Sum.inr PUnit.unit) :=
    greatestIdx_eq _ fun k => le_toLex_inr k
  have hmc := maximalContact_persistsFam_tuned
    (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _))
    (boClass_pullback_inclusion_of_boClass T _ hT) (hfStep2FamChain T 1 d hT U hU).L
    (hfStep2FamChain T 1 d hT U hU).hge
    (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
    (idealSheaf_preimage_le_iteratedDeriv_inclusion T 1 hH hle _)
  -- the full-boundary order clause of the link, in the same unfolded form
  have hgeF := hfStep22FamOn_isOfOrderGe_full d T hT U hU hH hle
  unfold hfStep22FamOn at hgeF ⊢
  rw [hfStep22Functor_fam_seqOn] at hgeF ⊢
  have h1 := hhf1 ((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1)
    (AnalyticTriple.boClass_tuned hT₂.1) (greatestIdx (stepHClass_tuned hT₂))
    (by rw [hj]; exact hmc) _ (isCompact_closure_hfStep2ReadOpen T 1 d hT U hU)
  rw [hj] at h1 hgeF ⊢
  have eI : (((hfStep22TripleFam T 1 d hT U hU hH hle).tuned 1 hT₂.1.1).pullback
      (((hfStep2FamChain T 1 d hT U hU).L.stage (Fin.last _)).inclusion
        (hfStep2ReadOpen T 1 d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I =
      (((T.pullback (M.inclusion (step2OpenW T 1 hT U hU))
        (isLocalDiffeomorph_inclusion M _)).induced 1 (hfStep2FamChain T 1 d hT U hU).L
        (hfStep2FamChain T 1 d hT U hU).hge).pullback
        (((hfStep2FamChain T 1 d hT U hU).L.stage (Fin.last _)).inclusion
          (hfStep2ReadOpen T 1 d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).I := by
    rw [AnalyticTriple.tuned_one]
    rfl
  rw [eI] at h1
  -- the chain's cosupport clause for every original member
  have hdis : ∀ j, Disjoint
      {x | ((1 : ℕ) : ℕ∞) ≤ ((hfStep2FamChain T 1 d hT U hU).L.toSuccession.markedTransformSeq
        (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _)).I 1
        (Fin.last _)).ord x}
      ((hfStep2FamChain T 1 d hT U hU).L.toSuccession.strictTransformSeq
        ((T.pullback (M.inclusion (step2OpenW T 1 hT U hU))
          (isLocalDiffeomorph_inclusion M _)).F.hyp j) (Fin.last _)) := by
    intro j
    by_cases hj0 : T.F.hyp j = ∅
    · have h0 : (T.pullback (M.inclusion (step2OpenW T 1 hT U hU))
          (isLocalDiffeomorph_inclusion M _)).F.hyp j = ∅ := by
        change ⇑(M.inclusion (step2OpenW T 1 hT U hU)) ⁻¹' T.F.hyp j = ∅
        rw [hj0, Set.preimage_empty]
      rw [h0, FiniteSuccession.strictTransformSeq_empty]
      exact Set.disjoint_empty _
    · exact ChainState.step21FamAux_cosupp_disjoint d.bd₁ T hT
        (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) (memberCount T 1 hT + 1))
        (memberCount T 1 hT + 1) (isCompact_closure_chainOpens _ _ _)
        (fun _ hk => closure_chainOpens_succ_subset _ _ _ hk) (T.F.nonemptyList hT.2.2).reverse
        (Nat.le_succ _) j (List.mem_reverse.mpr ((T.F.mem_nonemptyList hT.2.2 j).mpr hj0))
  -- the simple normal crossings of the full boundary at the last stage
  have hsncF := (FiniteSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq _
    (((T.pullback (M.inclusion (step2OpenW T 1 hT U hU))
      (isLocalDiffeomorph_inclusion M _)).induced 1 (hfStep2FamChain T 1 d hT U hU).L
      (hfStep2FamChain T 1 d hT U hU).hge).pullback
      (((hfStep2FamChain T 1 d hT U hU).L.stage (Fin.last _)).inclusion
        (hfStep2ReadOpen T 1 d hT U hU)) (isLocalDiffeomorph_inclusion _ _)).isSnc
    (fun j => hgeF.hasOnlyNormalCrossingsWith j) (Fin.last _)).1
  -- `OutputClause.of_forall_mem` with `exists_hyp_emptyMember_eq_of_le_ord'`
  refine FiniteSuccession.OutputClause.of_forall_mem ψ₀ _ hsncF
    (fun x hord m hm => exists_hyp_emptyMember_eq_of_le_ord'
      (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _))
      (hfStep2FamChain T 1 d hT U hU).L (hfStep2FamChain T 1 d hT U hU).hge
      (isSnc_step22BoundaryOf _ 1 _ (boClass_pullback_inclusion_of_boClass T _ hT)
        (hfStep2FamChain T 1 d hT U hU).hge
        (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion M _))
        (idealSheaf_preimage_le_iteratedDeriv_inclusion T 1 hH hle _))
      (hfStep2ReadOpen T 1 d hT U hU) rfl hdis _ hgeF x hord m hm) h1

/-- **The stopped clause of the value of Step 2 on the open** (the field `stopped_never_blownUp` of
`BMOmodFam` for the local value of the modified first step): the chain's clause
(`hfStep2FamChain_stoppedClause`) and the link's (`hfStep22FamOn_stoppedClause_induced`) composed
by `stoppedClause_shrinkAppend`, restricted (`stoppedClause_pullback`) and cleaned
(`stoppedClause_eraseEmpty`), the triples rewritten by `pullback_inclusion_restrictLE`, as in
`hfStep2SeqFamOn_isOfOrderGe`. -/
theorem hfStep2SeqFamOn_stoppedClause (hs : s = 1) (hbd : d.bd₁.StoppedClauseFam)
    (hhf8 : d.hf.StoppedClauseFam) (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfStep2SeqFamOn T s d hT U hU hH hle).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  subst hs
  have hchain := hfStep2FamChain_stoppedClause T 1 rfl d hT U hU hbd
  have h22 := hfStep22FamOn_stoppedClause_induced T 1 d hT U hU hH hle rfl hhf8 hhfo
  have hA := (hfStep2FamChain T 1 d hT U hU).L.stoppedClause_shrinkAppend
    (M.restrictLE (step2OpenV_le T 1 hT U hU)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _))
    (hfStep2FamChain T 1 d hT U hU).hge hchain (hfStep22FamOn T 1 d hT U hU hH hle)
    (hfStep22FamOn_isOfOrderGe_full d T hT U hU hH hle) h22
  have hAge := (hfStep2FamChain T 1 d hT U hU).L.isOfOrderGe_shrinkAppend
    (M.restrictLE (step2OpenV_le T 1 hT U hU)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _)) 1
    (hfStep2FamChain T 1 d hT U hU).hge (hfStep22FamOn T 1 d hT U hU hH hle)
    (hfStep22FamOn_isOfOrderGe_full d T hT U hU hH hle)
  have hB := BlowUpSequence.stoppedClause_pullback ψ₀ _ (M.restrictLE (le_step2OpenV T 1 hT U hU))
    (isLocalDiffeomorph_restrictLE _) _ hAge hA
  have hBge := AnalyticTriple.isOfOrderGe_pullback _ 1 _ hAge
    (M.restrictLE (le_step2OpenV T 1 hT U hU)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE T (step2OpenV_le T 1 hT U hU),
    AnalyticTriple.pullback_inclusion_restrictLE T (le_step2OpenV T 1 hT U hU)] at hB hBge
  exact BlowUpSequence.stoppedClause_eraseEmpty ψ₀ _
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) hBge hB

/-- **The output clause of the value of Step 2 on the open** (the field
`output_isSmoothSubmanifoldIdeal` of `BMOmodFam` for the local value of the modified first step):
the link's clause (`hfStep22FamOn_outputClause_induced`) through `outputClause_shrinkAppend`,
`outputClause_pullback` and `outputClause_eraseEmpty`. -/
theorem hfStep2SeqFamOn_outputClause (hs : s = 1) (hhf1 : d.hf.OutputClauseFam)
    (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfStep2SeqFamOn T s d hT U hU hH hle).toSuccession.OutputClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  subst hs
  have h22 := hfStep22FamOn_outputClause_induced T 1 d hT U hU hH hle rfl hhf1 hhfo
  have hA := (hfStep2FamChain T 1 d hT U hU).L.outputClause_shrinkAppend
    (M.restrictLE (step2OpenV_le T 1 hT U hU)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _))
    (hfStep2FamChain T 1 d hT U hU).hge (hfStep22FamOn T 1 d hT U hU hH hle)
    (hfStep22FamOn_isOfOrderGe_full d T hT U hU hH hle) h22
  have hAge := (hfStep2FamChain T 1 d hT U hU).L.isOfOrderGe_shrinkAppend
    (M.restrictLE (step2OpenV_le T 1 hT U hU)) (isLocalDiffeomorph_restrictLE _)
    (T.pullback (M.inclusion (step2OpenW T 1 hT U hU)) (isLocalDiffeomorph_inclusion M _)) 1
    (hfStep2FamChain T 1 d hT U hU).hge (hfStep22FamOn T 1 d hT U hU hH hle)
    (hfStep22FamOn_isOfOrderGe_full d T hT U hU hH hle)
  have hB := BlowUpSequence.outputClause_pullback ψ₀ _ (M.restrictLE (le_step2OpenV T 1 hT U hU))
    (isLocalDiffeomorph_restrictLE _) _ hAge hA
  have hBge := AnalyticTriple.isOfOrderGe_pullback _ 1 _ hAge
    (M.restrictLE (le_step2OpenV T 1 hT U hU)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE T (step2OpenV_le T 1 hT U hU),
    AnalyticTriple.pullback_inclusion_restrictLE T (le_step2OpenV T 1 hT U hU)] at hB hBge
  exact BlowUpSequence.outputClause_eraseEmpty ψ₀ _
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) hBge hB

end Link

section Local

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The stopped clause of Step 2 with the class's hypersurface of maximal contact (`hfStep2FamOn`,
the chosen witness of the class). -/
theorem hfStep2FamOn_stoppedClause (s : ℕ) (hs : s = 1) (d : HFData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.LocalMCClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (hbd : d.bd₁.StoppedClauseFam)
    (hhf8 : d.hf.StoppedClauseFam) (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfStep2FamOn s d T hT U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  unfold hfStep2FamOn
  exact hfStep2SeqFamOn_stoppedClause T s d hT.1 U hU _ _ hs hbd hhf8 hhfo

/-- The output clause of Step 2 with the class's hypersurface of maximal contact. -/
theorem hfStep2FamOn_outputClause (s : ℕ) (hs : s = 1) (d : HFData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.LocalMCClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (hhf1 : d.hf.OutputClauseFam)
    (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfStep2FamOn s d T hT U hU).toSuccession.OutputClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  unfold hfStep2FamOn
  exact hfStep2SeqFamOn_outputClause T s d hT.1 U hU _ _ hs hhf1 hhfo

/-- **The stopped clause of the local functor's value at the mark `1`** (`hfLocalFunctorFamOn 1`):
Step 2 at the mark `1! = 1` on the tuned triple, the tuning being the identity (`tuned_pullback`,
`tuned_one` at the restricted triple, as in `BDanFam_stoppedClause`). -/
theorem hfLocalFunctorFamOn_stoppedClause (d : HFData ψ₀ (tuningParam 1))
    (T : AnalyticTriple ψ₀ M) (hL : AnalyticTriple.LocalMCClass 1 T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M)))
    (hbd : d.bd₁.StoppedClauseFam) (hhf8 : d.hf.StoppedClauseFam)
    (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfLocalFunctorFamOn 1 d T hL U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  have h := hfStep2FamOn_stoppedClause (tuningParam 1) (by decide) d (T.tuned 1 hL.1.1)
    (AnalyticTriple.localMCClass_tuned hL) U hU hbd hhf8 hhfo
  rw [← AnalyticTriple.tuned_pullback] at h
  rw [AnalyticTriple.tuned_one (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))]
    at h
  exact h

/-- **The output clause of the local functor's value at the mark `1`**. -/
theorem hfLocalFunctorFamOn_outputClause (d : HFData ψ₀ (tuningParam 1))
    (T : AnalyticTriple ψ₀ M) (hL : AnalyticTriple.LocalMCClass 1 T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (hhf1 : d.hf.OutputClauseFam)
    (hhfo : d.hf.IsOfOrderGeEmptyMemberFam) :
    (hfLocalFunctorFamOn 1 d T hL U hU).toSuccession.OutputClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  have h := hfStep2FamOn_outputClause (tuningParam 1) (by decide) d (T.tuned 1 hL.1.1)
    (AnalyticTriple.localMCClass_tuned hL) U hU hhf1 hhfo
  rw [← AnalyticTriple.tuned_pullback] at h
  rw [AnalyticTriple.tuned_one (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))]
    at h
  exact h

end Local

end BO

end Hironaka.Manifold

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
  (hRc : R.CommutesWithLocalIsos) (hRi : R.IndifferentToEmptyMembers)
  (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1)

/-- **The stopped clause of the local functor of the modified first step**
(`stepBLocalFunctorFam`): `hfLocalFunctorFamOn_stoppedClause` at the datum `stepBData`, from the
clause of the data of Step 1a (`bdanFamDataOne_stoppedClauseFam`) and that of the data of the
modified step (`hFamDataMod_stoppedClauseFam`, from the clause `hR8` of the functor one dimension
down). -/
theorem stepBLocalFunctorFam_stoppedClauseFam
    (hR8 : R.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁).StoppedClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  unfold AnalyticFamilyFunctor.StoppedClauseFam
  intro N T hL U hU
  rw [stepBLocalFunctorFam_fam_seqOn]
  exact BO.hfLocalFunctorFamOn_stoppedClause (stepBData R hRo hRc hRi bmo₁) T hL U hU
    (bdanFamDataOne_stoppedClauseFam bmo₁) (hFamDataMod_stoppedClauseFam R hRo hRc hRi hR8)
    (hFamDataMod_isOfOrderGeEmptyMemberFam R hRo hRc hRi)

/-- **The output clause of the local functor of the modified first step**:
`hfLocalFunctorFamOn_outputClause` at `stepBData` with `hFamDataMod_outputClauseFam` (from `hR1`).
-/
theorem stepBLocalFunctorFam_outputClauseFam
    (hR1 : R.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁).OutputClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  unfold AnalyticFamilyFunctor.OutputClauseFam
  intro N T hL U hU
  rw [stepBLocalFunctorFam_fam_seqOn]
  exact BO.hfLocalFunctorFamOn_outputClause (stepBData R hRo hRc hRi bmo₁) T hL U hU
    (hFamDataMod_outputClauseFam R hRo hRc hRi hR1)
    (hFamDataMod_isOfOrderGeEmptyMemberFam R hRo hRc hRi)

/-- **The stopped clause of the functor of the modified first step on the class of `BO_{n,1}`**
(`stepBFunctor`): the local clause descended along the maximal-contact cover
(`stoppedClauseFam_of_agreeFam`, as in `stepBFunctor_isOfOrderGe`). -/
theorem stepBFunctor_stoppedClauseFam
    (hR8 : R.StoppedClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (stepBFunctor R hRo hRc hRi bmo₁).StoppedClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  exact AnalyticFamilyFunctor.stoppedClauseFam_of_agreeFam
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁) (stepBFunctor R hRo hRc hRi bmo₁)
    (stepBFunctor_fam_eq R hRo hRc hRi bmo₁) (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFamOn_isOfOrderGe R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFam_stoppedClauseFam R hRo hRc hRi bmo₁ hR8)

/-- **The output clause of the functor of the modified first step on the class of `BO_{n,1}`**
(`outputClauseFam_of_agreeFam`). -/
theorem stepBFunctor_outputClauseFam
    (hR1 : R.OutputClauseFam (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))) :
    (stepBFunctor R hRo hRc hRi bmo₁).OutputClauseFam
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) := by
  exact AnalyticFamilyFunctor.outputClauseFam_of_agreeFam
    (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (stepBLocalFunctorFam R hRo hRc hRi bmo₁) (stepBFunctor R hRo hRc hRi bmo₁)
    (stepBFunctor_fam_eq R hRo hRc hRi bmo₁) (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFamOn_isOfOrderGe R hRo hRc hRi bmo₁)
    (stepBLocalFunctorFam_outputClauseFam R hRo hRc hRi bmo₁ hR1)

end Hironaka.Manifold.BMOmod

end
