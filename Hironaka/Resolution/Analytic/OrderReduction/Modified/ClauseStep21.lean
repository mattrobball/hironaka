/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepBLocal
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseTools
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.OrderReduction.BDBridge
import Hironaka.Resolution.Analytic.OrderReduction.BDCosupp
import Hironaka.Resolution.Analytic.OrderReduction.BDFamOrder
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingPrep
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseCompose
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClausePhaseC
import Hironaka.Resolution.Analytic.OrderReduction.TunedLemmas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# The stopped clause along the chain of Step 2.1

The modified first step of [Wlo09, Theorem 7.4.1] runs Step 1a "as before": the family of the
proof of [Kol07, Lemma 102] at the mark `1`, read from the unmodified marked order reduction one
dimension down (`bdanFamDataOne`), is applied to the nonempty boundary members in turn along a
shrinking chain of relatively compact opens (`step21FamAux`, `hfStep2FamChain`; this is
[Kol07, Theorem 103, Step 2.1]). The stopped clause of `ClauseTools.lean` (the field
`stopped_never_blownUp` of `BMOmodFam`) must hold along that chain. This module proves it.

The core of the proof of [Kol07, Lemma 102] (`BDan.coreOfListOf`, `coreFamOn`) blows up
`Z_{-1} ⊆ Eʲ`, then pushes forward the lower run on `S_0 = π_{-1}^{-1}(Eʲ)`; every centre of the
pushed-forward run lies in the strict transform of `S_0`, which is inside the strict transform of
the member `Eʲ` together with the exceptional divisor. So the centres of the core lie in the
boundary at every stage, and `StoppedClause.of_forall_center_subset_support` gives the stopped
clause (the predicate of the clause, present for the stop rule, is not needed when the centres lie
in the boundary); the deletion of the empty first blow-up keeps the clause
(`stoppedClause_eraseEmpty`).

* `exists_hyp_totalTransformSeqFrom_eq_strictTransformSeq`, `strictTransformSeq_union`,
  `strictTransformSeq_hyp_subset_support`: the iterated strict transform of a member is a member of
  the total-transform boundary; that of a union of two sets is the union.
* `center_support_subset_cons_of_centersIn`: the centres of `cons hZ R` lie in the boundary when
  `Z` lies in a member and the centres of `R` lie in the strict transforms of a subset of that
  member's preimage (`centersIn_pushforward`).
* `BDan.coreOfListOf_transformS_stoppedClause`, `BDan.coreOfListOf_stoppedClause`,
  `BDan.coreFamOn_stoppedClause`: the stopped clause of the core over a list (through the order
  clause `cons_isOfOrder_of_bridge` of the core before the deletion of the empty blow-up), over an
  arbitrary centre and transform, and per open (the transported value of
  `coreFamOn_eq_coreOfListOf`).
* `BDanFamData.StoppedClauseFam`, `BDanFam_stoppedClause`, `BMOmod.bdanFamDataOne_stoppedClauseFam`:
  the clause for the family data of [Kol07, Lemma 102], for `BD^{an}_{n,1,j}` on an open (the
  tuning is the identity at the mark `1`, `tuned_one`, `tuned_pullback`), and for the data of
  Step 1a.
* `ChainState.link_stoppedClause`, `step21FamAux_stoppedClause`, `BO.hfStep2FamChain_stoppedClause`:
  one link keeps the clause (`stoppedClause_shrinkAppend`), the chain by induction on the member
  list, and the chain of Step 2.1 at its state over the open `M_{n₀+1}` of the assembly of Step 2.

Sources: [Kol07, Theorem 103, Step 2.1] and the proof of [Kol07, Lemma 102]; the modified first
step of [Wlo09, Theorem 7.4.1]. The statements themselves are not in the sources.
-/

@[expose] public section


noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Manifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **The strict transforms of a member are members**: at every stage the `i`-fold strict transform
of the member `F.hyp j` is a member of the total-transform boundary (the index `toLex (Sum.inl …)`
iterated; the member of `totalTransform` at `inl` is the strict transform of the member,
`strictTransformSeq_succ`). -/
theorem exists_hyp_totalTransformSeqFrom_eq_strictTransformSeq (S : FiniteSuccession M)
    (F : HypersurfaceFamily M) (j : F.ι) (i : Fin (S.length + 1)) :
    ∃ j', (S.totalTransformSeqFrom F i).hyp j' = S.strictTransformSeq (F.hyp j) i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact ⟨j, rfl⟩
  | succ i ih =>
    obtain ⟨j', hj'⟩ := ih (Nat.lt_of_succ_lt hi)
    exact ⟨toLex (Sum.inl j'), congrArg (strictTransformSet (S.map ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      (S.center ⟨i, Nat.lt_of_succ_lt_succ hi⟩).support) hj'⟩

/-- The iterated strict transform of a union of two sets is the union (`closure_union`,
`Set.union_sdiff_distrib`, `Set.preimage_union` at every stage). -/
theorem strictTransformSeq_union (S : FiniteSuccession M) (A B : Set M) (i : Fin (S.length + 1)) :
    S.strictTransformSeq (A ∪ B) i = S.strictTransformSeq A i ∪ S.strictTransformSeq B i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    have e : ∀ C : Set M, S.strictTransformSeq C ⟨i + 1, hi⟩ =
        closure (S.map ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ⁻¹'
          (S.strictTransformSeq C ⟨i, Nat.lt_of_succ_lt hi⟩ \
            (S.center ⟨i, Nat.lt_of_succ_lt_succ hi⟩).support)) :=
      fun _ => rfl
    rw [e, e, e, ih (Nat.lt_of_succ_lt hi), Set.union_sdiff_distrib, Set.preimage_union,
      closure_union]

/-- The iterated strict transform of a member lies in the support of the total-transform boundary
(`exists_hyp_totalTransformSeqFrom_eq_strictTransformSeq`). -/
theorem strictTransformSeq_hyp_subset_support (S : FiniteSuccession M)
    (F : HypersurfaceFamily M) (j : F.ι) (i : Fin (S.length + 1)) :
    S.strictTransformSeq (F.hyp j) i ⊆ (S.totalTransformSeqFrom F i).support := by
  obtain ⟨j', hj'⟩ := S.exists_hyp_totalTransformSeqFrom_eq_strictTransformSeq F j i
  rw [← hj']
  exact Set.subset_iUnion (fun k => (S.totalTransformSeqFrom F i).hyp k) j'

/-- **The centres of a `cons` over a push-forward lie in the boundary**: for a first centre
`Z ⊆ F.hyp j` and a succession `R` on its blow-up whose centres lie in the strict transforms of a
set `S' ⊆ π⁻¹(F.hyp j)` (`CentersIn`, as in `centersIn_pushforward`), every centre of `cons hZ R`
lies in the support of the total-transform boundary at its stage: at stage `0` by `Z ⊆ F.hyp j`; at
stage `k + 1` since `π⁻¹(F.hyp j)` is the member's strict transform together with the exceptional
divisor (`cons_totalTransformSeqFromAux_succ`, `strictTransformSeq_mono`,
`strictTransformSeq_union`, `strictTransformSeq_hyp_subset_support`). This is the hypothesis of
`StoppedClause.of_forall_center_subset_support`. -/
theorem center_support_subset_cons_of_centersIn {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1)
    (R : FiniteSuccession (blowUp ψ₀ hZ)) (F : HypersurfaceFamily M) (j : F.ι)
    (hZj : Z ⊆ F.hyp j) {S' : Set (blowUp ψ₀ hZ)}
    (hS' : S' ⊆ ⇑(blowUpπ ψ₀ hZ) ⁻¹' F.hyp j) (hc : R.CentersIn S')
    (i : Fin (cons ψ₀ hZ R).length) :
    ((cons ψ₀ hZ R).center i).support ⊆
      ((cons ψ₀ hZ R).totalTransformSeqFrom F i.castSucc).support := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | k
  · -- stage `0`: the first centre `Z` lies in the member `F.hyp j`
    change hZ.idealSheaf.support ⊆ F.support
    rw [hZ.cosupport_idealSheaf]
    exact hZj.trans (Set.subset_iUnion (fun k => F.hyp k) j)
  · -- stage `k + 1`: the centre of `R` lies in the strict transform of `S'`, which lies in the
    -- strict transform of the member together with the exceptional divisor
    have hk : k < R.length := Nat.lt_of_succ_lt_succ hi
    have e := FiniteSuccession.cons_totalTransformSeqFromAux_succ hZ R F k (Nat.lt_succ_of_lt hi)
    change ((cons ψ₀ hZ R).center ⟨k + 1, hi⟩).support ⊆
      ((cons ψ₀ hZ R).totalTransformSeqFromAux F (k + 1) (Nat.lt_succ_of_lt hi)).support
    rw [e, hZ.cosupport_idealSheaf]
    set F' := F.totalTransform (blowUpπ ψ₀ hZ) Z with hF'
    have hS'' : S' ⊆ F'.hyp (toLex (Sum.inl j)) ∪ F'.hyp (toLex (Sum.inr PUnit.unit)) := by
      intro x hx
      by_cases hxZ : blowUpπ ψ₀ hZ x ∈ Z
      · exact Or.inr hxZ
      · exact Or.inl (subset_closure ⟨hS' hx, hxZ⟩)
    have h1 : ((cons ψ₀ hZ R).center ⟨k + 1, hi⟩).support ⊆
        R.strictTransformSeq S' ⟨k, Nat.lt_succ_of_lt hk⟩ :=
      hc ⟨k, hk⟩
    have h2 := R.strictTransformSeq_mono hS'' ⟨k, Nat.lt_succ_of_lt hk⟩
    rw [R.strictTransformSeq_union] at h2
    exact h1.trans (h2.trans (Set.union_subset
      (R.strictTransformSeq_hyp_subset_support F' _ _)
      (R.strictTransformSeq_hyp_subset_support F' _ _)))

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDan

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ) (j : T.F.ι)

/-- **The stopped clause of the core of [Kol07, Lemma 102] over a list**, at the mark `1`: the
centres of the core before the deletion lie in the boundary
(`center_support_subset_cons_of_centersIn` with `Z_{-1} ⊆ Eʲ` and `S_0 = π_{-1}^{-1}(Eʲ)`,
`centersIn_pushforward` through `pushforwardBridge`), so
`StoppedClause.of_forall_center_subset_support` gives the clause (its predicate, present for the
stop rule, is not needed once the centres lie in the boundary), and `stoppedClause_eraseEmpty`
carries it through the deletion of the empty first blow-up (the order clause
`cons_isOfOrder_of_bridge`). -/
theorem coreOfListOf_transformS_stoppedClause (hs : s = 1) (hT : BDClass s T)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (isClosedSubmanifold_transformS T s j).toAnalyticManifold) (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTriple T s j hT).I s
      (restrictedTriple T s j hT).F.idealSheaf) :
    (coreOfListOf (BD.isClosedSubmanifold_Zminus1 T s j) (isClosedSubmanifold_transformS T s j)
      L).toSuccession.StoppedClause ψ₀ T.I T.F := by
  subst hs
  have hbr : PushforwardBridge.{u} ψ₀ := pushforwardBridge ψ₀
  have hcons := cons_isOfOrder_of_bridge T 1 j hT L hbr hLne hL
  -- the stopped clause of the core before the deletion: its centres lie in the boundary
  have hP : (BlowUpSequence.cons (BD.isClosedSubmanifold_Zminus1 T 1 j)
      (BlowUpSequence.pushforward (isClosedSubmanifold_transformS T 1 j)
          L)).toSuccession.StoppedClause
      ψ₀ T.I T.F := by
    have hge := hcons.isOfOrderGe
    rw [BlowUpSequence.toSuccession_cons,
      hbr (isClosedSubmanifold_transformS T 1 j) L hLne] at hge ⊢
    exact FiniteSuccession.StoppedClause.of_forall_center_subset_support _ T.isSnc
      (fun i => hge.hasOnlyNormalCrossingsWith i)
      (FiniteSuccession.center_support_subset_cons_of_centersIn _ _ T.F j (BD.Zminus1_subset T 1 j)
        Set.Subset.rfl (L.toSuccession.centersIn_pushforward _))
  -- the deletion of the empty first blow-up
  exact BlowUpSequence.stoppedClause_eraseEmpty ψ₀ _ T hcons.isOfOrderGe hP

/-- `coreOfListOf_transformS_stoppedClause` over an arbitrary centre and transform (a substitution,
as in `coreOfListOf_isOfOrderGe`). -/
theorem coreOfListOf_stoppedClause {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1)
    {S' : Set (blowUp ψ₀ hZ)} (hS' : IsClosedSubmanifold ψ₀ S' 1) (hs : s = 1) (hT : BDClass s T)
    (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j)) (hSeq : S' = transformSOf T j hZ)
    (L : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hS'.toAnalyticManifold)
    (hLne : L.NoEmptyCenters)
    (hL : L.toSuccession.IsOfOrderGe (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).I s
      (restrictedTripleOf T s j hZ hS' hT hZeq hSeq).F.idealSheaf) :
    (coreOfListOf hZ hS' L).toSuccession.StoppedClause ψ₀ T.I T.F := by
  subst hZeq
  subst hSeq
  exact coreOfListOf_transformS_stoppedClause T s j hs hT L hLne hL

/-- **The stopped clause of the per-open core**, at the mark `1`: the per-open core is the core
over the transported value on the restricted data (`coreFamOn_eq_coreOfListOf`), so
`coreOfListOf_stoppedClause` applies with the transported value's order clause
(`isOfOrderGe_transportedValue`), as in `coreFamOn_isOfOrderGe`. -/
theorem coreFamOn_stoppedClause (hs : s = 1) (inp : BMOanFam 𝕜 (n - 1) s) (hT : BDClass s T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hT' : BDClass s (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))) :
    (coreFamOn T s j inp hT U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  rw [coreFamOn_eq_coreOfListOf]
  exact coreOfListOf_stoppedClause (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))
    s j _ _ hs hT' (Zminus1_restrict T s j U) (transformSU_eq T s j U) _
    (noEmptyCenters_transportedValue T s j inp hT U hU)
    (isOfOrderGe_transportedValue T s j inp hT U hU hT')

end BDan

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- **The stopped clause for the family data of [Kol07, Lemma 102]** (the field
`stopped_never_blownUp` of `BMOmodFam` per triple, member and relatively compact open, in the form
of the data's own clauses). -/
def BDanFamData.StoppedClauseFam {s : ℕ} (bd : BDanFamData ψ₀ s) : Prop :=
  ∀ {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ N) (hT : AnalyticTriple.BOClass s T)
    (j : T.F.ι) (U : Opens N) (hU : IsCompact (closure (U : Set N))),
    ((bd.fam T hT j).seqOn U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).I
      (T.pullback (N.inclusion U) (isLocalDiffeomorph_inclusion N U)).F

/-- **The stopped clause of `BD^{an}_{n,1,j}` on an open**: the core's clause at the mark `1! = 1`
on the tuned triple (`coreFamOn_stoppedClause` with `bdClass_tuned_pullback_inclusion`), the tuning
commuting with the restriction (`tuned_pullback`) and being the identity at the mark `1`
(`tuned_one`), as in `BDanFam_isOfOrder`. -/
theorem BDanFam_stoppedClause {m : ℕ} (hm : m = 1) (inp : BMOanFam 𝕜 (n - 1) (tuningParam m))
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (BDanFam m inp T hT j U hU).toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F := by
  subst hm
  have hP := BDan.coreFamOn_stoppedClause (T.tuned 1 hT.1) (tuningParam 1) j (by decide) inp
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩ U hU
    (bdClass_tuned_pullback_inclusion T hT U)
  rw [← AnalyticTriple.tuned_pullback] at hP
  rw [AnalyticTriple.tuned_one (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U))]
    at hP
  exact hP

end Hironaka.Manifold

namespace Hironaka.Manifold.BMOmod

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

/-- **The stopped clause of the data of Step 1a** (the family of [Kol07, Lemma 102] at the mark `1`
from the unmodified marked order reduction one dimension down, `bdanFamDataOne`):
`BDanFam_stoppedClause` at `m = tuningParam 1 = 1`. -/
theorem bdanFamDataOne_stoppedClauseFam (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1) :
    (bdanFamDataOne bmo₁).StoppedClauseFam := by
  unfold BDanFamData.StoppedClauseFam
  intro N T hT j U hU
  rw [bdanFamDataOne_fam]
  -- `bdanFam_seqOn` is `rfl`; the mark `tuningParam (tuningParam 1)` is `1` by evaluation
  exact BDanFam_stoppedClause (m := tuningParam 1) (by decide) bmo₁ T hT j U hU

end Hironaka.Manifold.BMOmod

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (s : ℕ)

omit [FiniteDimensional 𝕜 E] in
/-- **One link of the chain of Step 2.1 keeps the stopped clause** (the analogue of the order clause
of `ChainState.link`): the member's value on the induced triple at the lifted range has the clause
by the data's clause, the list so far by hypothesis, and `stoppedClause_shrinkAppend` composes
them; the restricted triple is rewritten by `pullback_inclusion_restrictLE`. -/
theorem ChainState.link_stoppedClause (hs : s = 1) (bd : BDanFamData ψ₀ s)
    (hT : AnalyticTriple.BOClass s T) {W : Opens M} (st : ChainState T s W) (j : T.F.ι)
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)
    (hbd : bd.StoppedClauseFam)
    (hst : st.L.toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).I
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F) :
    (st.link T s bd hT j hV hVW).L.toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F := by
  subst hs
  unfold BDanFamData.StoppedClauseFam at hbd
  have hle : V ≤ W := ChainState.le_of_closure_subset hVW
  rw [← AnalyticTriple.pullback_inclusion_restrictLE T hle]
  exact st.L.stoppedClause_shrinkAppend (M.restrictLE hle) (isLocalDiffeomorph_restrictLE hle)
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)) st.hge hst _
    (bd.isOfOrder _ _ _ _ _).isOfOrderGe (hbd _ _ _ _ _)

omit [FiniteDimensional 𝕜 E] in
/-- **The stopped clause along the chain of Step 2.1** (induction on the member list): the initial
state is the empty list, each link is `ChainState.link_stoppedClause`. -/
theorem step21FamAux_stoppedClause (hs : s = 1) (bd : BDanFamData ψ₀ s)
    (hT : AnalyticTriple.BOClass s T) (W : ℕ → Opens M) (r : ℕ)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (hbd : bd.StoppedClauseFam) :
    ∀ (l : List T.F.ι) (hl : l.length ≤ r),
      (step21FamAux T s bd hT W r hW hWsub l hl).L.toSuccession.StoppedClause ψ₀
        (T.pullback (M.inclusion (W l.length))
          (isLocalDiffeomorph_inclusion M (W l.length))).I
        (T.pullback (M.inclusion (W l.length))
          (isLocalDiffeomorph_inclusion M (W l.length))).F := by
  subst hs
  intro l
  induction l with
  | nil =>
    intro hl i k h
    exact absurd h (Nat.not_lt_zero _)
  | cons j l ih =>
    intro hl
    exact (step21FamAux T 1 bd hT W r hW hWsub l (Nat.le_of_succ_le hl)).link_stoppedClause T 1 rfl
      bd hT j (hW _) (hWsub l.length hl) hbd (ih (Nat.le_of_succ_le hl))

/-- **The stopped clause of the chain of Step 2.1 in the assembly of Step 2**, at its state over the
open `M_{n₀+1}` (`step21FamAux_stoppedClause` at the canonical chain of `hfStep2FamChain`, from the
clause of the data `d.bd₁`). -/
theorem BO.hfStep2FamChain_stoppedClause (hs : s = 1) (d : HFData ψ₀ s)
    (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hbd : d.bd₁.StoppedClauseFam) :
    (BO.hfStep2FamChain T s d hT U hU).L.toSuccession.StoppedClause ψ₀
      (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M (BO.step2OpenW T s hT U hU))).I
      (T.pullback (M.inclusion (BO.step2OpenW T s hT U hU))
        (isLocalDiffeomorph_inclusion M (BO.step2OpenW T s hT U hU))).F := by
  exact step21FamAux_stoppedClause T s hs d.bd₁ hT _ _ _ _ hbd _ _

end Hironaka.Manifold

end
