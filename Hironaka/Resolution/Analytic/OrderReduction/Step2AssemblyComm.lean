/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.Step2Along
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.Step21ErasePrep
import Hironaka.Resolution.Analytic.OrderReduction.Step21FamIndep
import Hironaka.Resolution.Analytic.OrderReduction.Step21FamIndiff
import Hironaka.Resolution.Analytic.OrderReduction.Step21Indiff
import Hironaka.Resolution.Analytic.OrderReduction.Step2LinkTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2 on an open: commutation with local analytic isomorphisms and indifference to empty members

The two remaining clauses of Theorem 103 for the value of Step 2 on a relatively compact open
(`step2SeqFamOn`, `Step22Fam.lean`), proved as for Step 2.1 (`Step21FamIndep.lean`,
`Step21FamIndiff.lean`) with the link of Step 2.2 transported by `hfStep22Link_rel`
(`Step2LinkTransport.lean`):

* `hfStep2SeqFamOn_commutesWithLocalIsos` — along a local analytic isomorphism `g : N → M`, Step 2
  of the pulled-back triple on `U'` is the pull-back of Step 2 on `g(U')` with its empty blow-ups
  deleted, the analytic form of the functoriality clause of Step 2.3 of the proof of Theorem 103
  ([Kol07, 104, Step 2.3]; the second clause of [Kol07, 34.1]). The chain of Step 2.1 over `N` for
  the members that stay nonempty is the chain over the full list of members along opens carried
  into the canonical chain of `g(U')` (`step21FamAux_filter_rel`; a member emptied by `g`
  contributes nothing, which needs the hypothesis `hnil` that the data are trivial at an empty
  member), and that chain is the pull-back of the canonical chain of `g(U')` link by link
  (`step21FamAux_rel_along`); the link of Step 2.2 is compared on `N` through the state over the
  intersection (`hfStep22Link_rel` along the identity) and transported along `g` (`hfStep22Link_rel`
  along `g`).
* `hfStep2SeqFamOn_indifferentToEmptyMembers` — deleting empty members of the boundary does not
  change the value ([Kol07, 32]): the chains of Step 2.1 for `(M, 𝓘, E)` and `(M, 𝓘, F')` agree on
  the intersection of the next-to-last opens (`step21FamAux_indiff_rel`), and the triples of
  Step 2.2 over the same sequence for two triples with the same ideal sheaf are the same triple
  (`step22TripleOf_congr_I`: the triple of Step 2.2 does not see the boundary), so the two links
  of Step 2.2 agree (`hfStep22Link_indiff_I`).

The `hf…` declarations are the general forms over data `d : HFData ψ₀ s` of Step 2
(`HFamData.lean`); the plain forms are their instances at Lemma 102's data. These are the clauses
`commutesWithLocalIsos` and `indifferentToEmptyMembers` of the family structure `BOanFam` for the
local functor (`LocalFunctorFam.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace Hironaka.Local
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

namespace BO

open _root_.Manifold

variable (bd : ∀ s : ℕ, BDanFamData ψ₀ s) (d : HFData ψ₀ s)

omit [FiniteDimensional 𝕜 E] in
/-- The triple of Step 2.2 over a sequence, written as a structure literal (one unfolding; kept
separate so that two triples of Step 2.2 with different boundaries are compared through their
ideal sheaves rather than field by field). -/
theorem step22TripleOf_eq_mk {X : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ X)
    (L : AnalyticManifold.BlowUpSequence ψ₀ X) (hL : L.toSuccession.IsOfOrderGe T.I s
        T.F.idealSheaf) {H : Set X}
    (hsnc : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    step22TripleOf T L hL hsnc =
      ⟨L.toSuccession.markedTransformSeq T.I s (Fin.last _),
        isNonzeroEverywhere_markedTransformSeq T.isNonzeroEverywhere hL _,
        (exceptionalOf L).append (transformHOf L H), hsnc⟩ := rfl

omit [FiniteDimensional 𝕜 E] in
/-- Two triples of the shape of Step 2.2 over the same sequence with equal ideal sheaves are
equal. -/
theorem step22Mk_congr_I {X : AnalyticManifold.{u} 𝕜 E} {J₁ J₂ : AnalyticManifold.IdealSheaf X}
    (hJ : J₁ = J₂) (L : AnalyticManifold.BlowUpSequence ψ₀ X) {H : Set X}
    (p₁ : (L.toSuccession.markedTransformSeq J₁ s (Fin.last _)).IsNonzeroEverywhere)
    (p₂ : (L.toSuccession.markedTransformSeq J₂ s (Fin.last _)).IsNonzeroEverywhere)
    (hsnc₁ hsnc₂ : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    (⟨L.toSuccession.markedTransformSeq J₁ s (Fin.last _), p₁,
        (exceptionalOf L).append (transformHOf L H), hsnc₁⟩ :
          AnalyticTriple ψ₀ (L.stage (Fin.last _))) =
      ⟨L.toSuccession.markedTransformSeq J₂ s (Fin.last _), p₂,
        (exceptionalOf L).append (transformHOf L H), hsnc₂⟩ := by
  subst hJ
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- The triple of Step 2.2 over a sequence depends on the triple only through its ideal sheaf
(through the structure literals, so that only the ideal sheaves are compared). -/
theorem step22TripleOf_congr_I {X : AnalyticManifold.{u} 𝕜 E} {T₁ T₂ : AnalyticTriple ψ₀ X}
    (hI : T₁.I = T₂.I) {H : Set X} (L : AnalyticManifold.BlowUpSequence ψ₀ X)
    (hL₁ : L.toSuccession.IsOfOrderGe T₁.I s T₁.F.idealSheaf)
    (hL₂ : L.toSuccession.IsOfOrderGe T₂.I s T₂.F.idealSheaf)
    (hsnc₁ : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀)
    (hsnc₂ : ((exceptionalOf L).append (transformHOf L H)).IsSnc ψ₀) :
    step22TripleOf T₁ L hL₁ hsnc₁ = step22TripleOf T₂ L hL₂ hsnc₂ :=
  (step22TripleOf_eq_mk T₁ L hL₁ hsnc₁).trans
    ((step22Mk_congr_I hI L (isNonzeroEverywhere_markedTransformSeq T₁.isNonzeroEverywhere hL₁ _)
      (isNonzeroEverywhere_markedTransformSeq T₂.isNonzeroEverywhere hL₂ _) hsnc₁ hsnc₂).trans
      (step22TripleOf_eq_mk T₂ L hL₂ hsnc₂).symm)

/-- The link of Step 2.2 does not see the boundary (over data `d`): two states of the chain with
the same sequence, for triples with the same ideal sheaf, append the same value of Step 2.2, since
the triple of Step 2.2 over a sequence depends on the triple only through its ideal sheaf
(`step22TripleOf_congr_I`). -/
theorem hfStep22Link_indiff_I {X : AnalyticManifold.{u} 𝕜 E} (T₁ T₂ : AnalyticTriple ψ₀ X)
    (hI : T₂.I = T₁.I) (hT₁ : AnalyticTriple.BOClass s T₁) (hT₂ : AnalyticTriple.BOClass s T₂)
    {H : Set X} (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle₁ : hH.idealSheaf ≤ T₁.I.iteratedDeriv (s - 1))
    (hle₂ : hH.idealSheaf ≤ T₂.I.iteratedDeriv (s - 1)) {W : Opens X} (st : ChainState T₁ s W)
    (st' : ChainState T₂ s W) (hL : st.L = st'.L) {V : Opens X}
    (hV : IsCompact (closure (V : Set X))) (hVW : closure (V : Set X) ⊆ W) :
    st.L.shrinkAppend (X.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE (ChainState.le_of_closure_subset hVW))
      (hfStep22ValueOf d T₁ hT₁ hH hle₁ st hV hVW) =
    st'.L.shrinkAppend (X.restrictLE (ChainState.le_of_closure_subset hVW))
      (isLocalDiffeomorph_restrictLE (ChainState.le_of_closure_subset hVW))
      (hfStep22ValueOf d T₂ hT₂ hH hle₂ st' hV hVW) := by
  obtain ⟨L, hge⟩ := st
  obtain ⟨L', hge'⟩ := st'
  change L = L' at hL
  subst hL
  -- the two Step-2.2 triples over the list coincide (the boundary is not seen)
  have htr : step22TripleOf (T₁.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)) L hge
      (isSnc_step22BoundaryOf _ s L (boClass_pullback_inclusion_of_boClass T₁ W hT₁) hge
        (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion X W))
        (idealSheaf_preimage_le_iteratedDeriv_inclusion T₁ s hH hle₁ W)) =
      step22TripleOf (T₂.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)) L hge'
      (isSnc_step22BoundaryOf _ s L (boClass_pullback_inclusion_of_boClass T₂ W hT₂) hge'
        (hH.preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_inclusion X W))
        (idealSheaf_preimage_le_iteratedDeriv_inclusion T₂ s hH hle₂ W)) :=
    step22TripleOf_congr_I
      (congrArg (fun J : AnalyticManifold.IdealSheaf X => J.pullback _ (X.inclusion W).contMDiff)
          hI.symm) L
          hge hge' _ _
  unfold hfStep22ValueOf
  exact congrArg (L.shrinkAppend _ _) (hfStep22Fam_seqOn_congr_triple d htr _ _ _ _)

section Indiff

variable (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) {H : Set M}
  (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))
  (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι)
  (he : ∀ i, T.F.hyp (e i) = F'.hyp i) (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
  (hT' : AnalyticTriple.BOClass s (BDan.withBoundary T F' hsnc'))

include he he' in
/-- Step 2 along an admissible chain for `(M, 𝓘, E)` and Step 2 along an admissible chain for
`(M, 𝓘, F')`, where `F'` is `E` with empty members deleted, agree on every common open
([Kol07, 32]; over data `d`): the chains of Step 2.1 agree on the intersection of the next-to-last
opens (`step21FamAux_indiff_rel`), the links of Step 2.2 through the states over that intersection
are the same (`hfStep22Link_indiff_I`: the triple of Step 2.2 does not see the boundary), and the
two links transport to the intersection of the last opens (`hfStep22Link_rel` along the
identity). -/
theorem hfStep2SeqFamAlong_indiff_rel (W : ℕ → Opens M)
    (hWsub : ∀ k, k < memberCount T s hT + 1 → closure (W (k + 1) : Set M) ⊆ W k)
    (hW : ∀ k, IsCompact (closure (W k : Set M))) (W' : ℕ → Opens M)
    (hWsub' : ∀ k, k < memberCount (BDan.withBoundary T F' hsnc') s hT' + 1 →
      closure (W' (k + 1) : Set M) ⊆ W' k)
    (hW' : ∀ k, IsCompact (closure (W' k : Set M))) (U : Opens M)
    (hU₁ : U ≤ W (memberCount T s hT + 1))
    (hU₂ : U ≤ W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1)) :
    hfStep2SeqFamAlong T s hT W hWsub d hW hH hle U hU₁ =
      hfStep2SeqFamAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d hW' hH hle U hU₂ := by
  -- the two Step 2.1 chains agree on the intersection of the next-to-last opens
  have ih := ChainState.step21FamAux_indiff_rel d.bd₁ T hT F' hsnc' e he he' hT' W
    (memberCount T s hT + 1) hW hWsub W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1)
    hW' hWsub' (F'.nonemptyList hT'.2.2).reverse (T.F.nonemptyList hT.2.2).reverse
    (by rw [List.map_reverse, nonemptyList_eq_map T F' e he he' hT.2.2 hT'.2.2]) (Nat.le_succ _)
    (Nat.le_succ _) (W (memberCount T s hT) ⊓ W' (memberCount (BDan.withBoundary T F' hsnc') s hT'))
    inf_le_left inf_le_right
  have hT_id : AnalyticTriple.BOClass s
      (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) :=
    AnalyticTriple.boClass_of_isPullbackOf hT
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
      (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hT'_id : AnalyticTriple.BOClass s
      ((BDan.withBoundary T F' hsnc').pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) :=
    AnalyticTriple.boClass_of_isPullbackOf hT'
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
      (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hI' : IsCompact (closure ((W (memberCount T s hT + 1) ⊓
      W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1) : Opens M) : Set M)) :=
    (hW _).of_isClosed_subset isClosed_closure (closure_mono inf_le_left)
  have hI'I : closure ((W (memberCount T s hT + 1) ⊓
      W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1) : Opens M) : Set M) ⊆
      (W (memberCount T s hT) ⊓ W' (memberCount (BDan.withBoundary T F' hsnc') s hT') :
        Opens M) := by
    rw [Opens.coe_inf, Opens.coe_inf]
    exact Set.subset_inter
      ((closure_mono Set.inter_subset_left).trans (closure_chainLast_subset T s hT W hWsub))
      ((closure_mono Set.inter_subset_right).trans
        (closure_chainLast_subset (BDan.withBoundary T F' hsnc') s hT' W' hWsub'))
  -- the virtual states over the intersection: one per triple, with the same list
  have hrel₁ : ((hfStep2FamChainAlong T s hT W hWsub d hW).restrictEraseId T s
      (inf_le_left : W (memberCount T s hT) ⊓
        W' (memberCount (BDan.withBoundary T F' hsnc') s hT') ≤
        W (memberCount T s hT))).L.eraseEmpty =
      ((hfStep2FamChainAlong T s hT W hWsub d hW).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_left))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          (ChainState.image_id_subset inf_le_left))).eraseEmpty :=
    AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _
  have hrel₂ : ((hfStep2FamChainAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d
      hW').restrictEraseId (BDan.withBoundary T F' hsnc') s
      (inf_le_right : W (memberCount T s hT) ⊓
        W' (memberCount (BDan.withBoundary T F' hsnc') s hT') ≤
        W' (memberCount (BDan.withBoundary T F' hsnc') s hT'))).L.eraseEmpty =
      ((hfStep2FamChainAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d hW').L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_right))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          (ChainState.image_id_subset inf_le_right))).eraseEmpty :=
    AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _
  have hvL : ((hfStep2FamChainAlong T s hT W hWsub d hW).restrictEraseId T s
      (inf_le_left : W (memberCount T s hT) ⊓
        W' (memberCount (BDan.withBoundary T F' hsnc') s hT') ≤ W (memberCount T s hT))).L =
      ((hfStep2FamChainAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d
        hW').restrictEraseId (BDan.withBoundary T F' hsnc') s
        (inf_le_right : W (memberCount T s hT) ⊓
          W' (memberCount (BDan.withBoundary T F' hsnc') s hT') ≤
          W' (memberCount (BDan.withBoundary T F' hsnc') s hT'))).L := by
    rw [ChainState.restrictEraseId_L, ChainState.restrictEraseId_L]
    exact ih
  -- the Step-2.2 links on the two chains, through the virtual states, which agree
  have h₁ := hfStep22Link_rel d T hT hH hle ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
    hT_id (ChainState.image_id_subset inf_le_left) (hfStep2FamChainAlong T s hT W hWsub d hW) _
    hrel₁ (hW _) (closure_chainLast_subset T s hT W hWsub) hI' hI'I
    (ChainState.image_id_subset inf_le_left)
  have h₂ := hfStep22Link_rel d (BDan.withBoundary T F' hsnc') hT' hH hle ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) hT'_id
        (ChainState.image_id_subset inf_le_right)
    (hfStep2FamChainAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d hW') _ hrel₂ (hW' _)
    (closure_chainLast_subset (BDan.withBoundary T F' hsnc') s hT' W' hWsub') hI' hI'I
    (ChainState.image_id_subset inf_le_right)
  have hbr := hfStep22Link_indiff_I d
    (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))
    ((BDan.withBoundary T F' hsnc').pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))
    rfl hT_id hT'_id (hH.preimage_of_isLocalDiffeomorph
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))
    (T.idealSheaf_preimage_le_iteratedDeriv_pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) hH hle)
    ((BDan.withBoundary T F' hsnc').idealSheaf_preimage_le_iteratedDeriv_pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) hH hle) _ _ hvL hI' hI'I
  -- the two appended chains agree on the intersection of the last opens, hence on `U`
  have hI : (((hfStep2FamChainAlong T s hT W hWsub d hW).L.shrinkAppend
      (M.restrictLE (chainLast_le T s hT W hWsub)) (isLocalDiffeomorph_restrictLE _)
      (hfStep22FamOnAlong T s hT W hWsub d hW hH hle)).pullback
      (M.restrictLE (inf_le_left : W (memberCount T s hT + 1) ⊓
        W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1) ≤ W (memberCount T s hT + 1)))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      (((hfStep2FamChainAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d hW').L.shrinkAppend
        (M.restrictLE (chainLast_le (BDan.withBoundary T F' hsnc') s hT' W' hWsub'))
        (isLocalDiffeomorph_restrictLE _)
        (hfStep22FamOnAlong (BDan.withBoundary T F' hsnc') s hT' W' hWsub' d hW' hH hle)).pullback
        (M.restrictLE (inf_le_right : W (memberCount T s hT + 1) ⊓
          W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1) ≤
          W' (memberCount (BDan.withBoundary T F' hsnc') s hT' + 1)))
        (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
    (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
        (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl)
      (isLocalDiffeomorph_restrictLE inf_le_left)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
        (ChainState.image_id_subset inf_le_left)))).trans
      (h₁.symm.trans ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty hbr).trans (h₂.trans
        (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
            (AnalyticManifold.BlowUpSequence.pullback_congr _
          (ContMDiffMap.ext fun _ => rfl)
          (AnalyticMap.isLocalDiffeomorph_restrictMap
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
            (ChainState.image_id_subset inf_le_right))
          (isLocalDiffeomorph_restrictLE inf_le_right))))))
  unfold hfStep2SeqFamAlong
  exact AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_restrict_congr _ _ inf_le_left
      inf_le_right
    (le_inf hU₁ hU₂) hI

end Indiff

end BO

/-- Step 2 on an open does not see empty boundary members (over data `d`): Step 2
along the canonical chains for `(M, 𝓘, E)` and `(M, 𝓘, F')` agree on `U`
(`hfStep2SeqFamAlong_indiff_rel`). -/
theorem hfStep2SeqFamOn_indifferentToEmptyMembers (d : HFData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
    (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1)) (F' : HypersurfaceFamily M)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT' : AnalyticTriple.BOClass s
      (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)) :
    BO.hfStep2SeqFamOn T s d hT U hU hH hle =
      BO.hfStep2SeqFamOn ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ s d hT' U hU hH hle := by
  rw [BO.hfStep2SeqFamOn_eq_along T s hT d hH hle U hU,
    BO.hfStep2SeqFamOn_eq_along ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ s hT' d hH hle U hU]
  exact BO.hfStep2SeqFamAlong_indiff_rel d T hT hH hle F' hsnc' e he he' hT' _ _ _ _ _ _ U
    (BO.le_step2OpenV T s hT U hU) (BO.le_step2OpenV _ s hT' U hU)

/-- Step 2 commutes with local analytic isomorphisms on the opens ([Kol07, 104, Step 2.3]; the
second clause of [Kol07, 34.1]; over data `d`): along `g : N → M`, Step 2 of the pulled-back triple
on `U'` is the pull-back of Step 2 on `g(U')` with its empty blow-ups deleted. The chain of
Step 2.1 over `N` for the members that stay nonempty is the chain over the full list of members
along opens carried into the canonical chain of `g(U')` (`step21FamAux_filter_rel`; a member
emptied by `g` contributes nothing by `hnil`), which is the pull-back of that canonical chain link
by link (`step21FamAux_rel_along`); the link of Step 2.2 is compared on `N` through the state over
the intersection (`hfStep22Link_rel` along the identity) and transported along `g`
(`hfStep22Link_rel` along `g`); restricting to `U'` and deleting the empty blow-ups gives the
statement. -/
theorem hfStep2SeqFamOn_commutesWithLocalIsos (d : HFData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) {H : Set M}
    (hH : IsClosedSubmanifold ψ₀ H 1) (hle : hH.idealSheaf ≤ T.I.iteratedDeriv (s - 1))
    (hnil : ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
      (hT' : AnalyticTriple.BOClass s T') (j : T'.F.ι),
      T'.F.hyp j = ∅ → d.bd₁.fam T' hT' j = CompatibleFamily.nil T')
    {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT' : AnalyticTriple.BOClass s (T.pullback g hg))
    (hH' : IsClosedSubmanifold ψ₀ (⇑g ⁻¹' H) 1)
    (hle' : hH'.idealSheaf ≤ (T.pullback g hg).I.iteratedDeriv (s - 1)) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    BO.hfStep2SeqFamOn (T.pullback g hg) s d hT' U' hU' hH' hle' =
      ((BO.hfStep2SeqFamOn T s d hT (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU') hH hle).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  -- the canonical chain of `g(U')` on `M` (`r + 1` opens) and its trace on `N`, intersected with
  -- the canonical chain of `U'`
  have hW₀ : IsCompact (closure ((AnalyticMap.imageOpens g hg U' : Opens M) : Set M)) :=
    AnalyticMap.isCompact_closure_image g hU'
  let W : ℕ → Opens M := chainOpens (exhaustion M)
    (exhaustionIdx (exhaustion M) hW₀) (memberCount T s hT + 1)
  let W' : ℕ → Opens N := fun k => preimageOpens g g.contMDiff (W k) ⊓
    chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU') (memberCount T s hT + 1) k
  have hW : ∀ k, IsCompact (closure (W k : Set M)) :=
    isCompact_closure_chainOpens (exhaustion M) _ _
  have hWsub : ∀ k, k < memberCount T s hT + 1 → closure (W (k + 1) : Set M) ⊆ W k :=
    fun _ hk => closure_chainOpens_succ_subset (exhaustion M) _ _ hk
  have hW' : ∀ k, IsCompact (closure (W' k : Set N)) := fun k =>
    (isCompact_closure_chainOpens (exhaustion N) _ _ k).of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.2)
  have hWsub' : ∀ k, k < memberCount T s hT + 1 → closure (W' (k + 1) : Set N) ⊆ W' k := by
    intro k hk x hx
    have hx' := closure_inter_subset_inter_closure _ _ hx
    exact ⟨(g.contMDiff.continuous.closure_preimage_subset _).trans
      (Set.preimage_mono (closure_chainOpens_succ_subset (exhaustion M) _ _ hk)) hx'.1,
      closure_chainOpens_succ_subset (exhaustion N) _ _ hk hx'.2⟩
  have hWW' : ∀ k, ⇑g '' (W' k : Set N) ⊆ W k := by
    rintro k _ ⟨x, hx, rfl⟩
    exact hx.1
  have hU'W' : U' ≤ W' (memberCount T s hT + 1) := fun x hx =>
    ⟨le_chainOpens_last (exhaustion M) hW₀ (memberCount T s hT + 1) ⟨x, hx, rfl⟩,
      le_chainOpens_last (exhaustion N) hU' (memberCount T s hT + 1) hx⟩
  -- the canonical chain of `U'` on `N` (`r' + 1` opens) and the filtered member list
  let W'' : ℕ → Opens N := chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU')
    (memberCount (T.pullback g hg) s hT' + 1)
  have hW'' : ∀ k, IsCompact (closure (W'' k : Set N)) :=
    isCompact_closure_chainOpens (exhaustion N) _ _
  have hWsub'' : ∀ k, k < memberCount (T.pullback g hg) s hT' + 1 →
      closure (W'' (k + 1) : Set N) ⊆ W'' k :=
    fun _ hk => closure_chainOpens_succ_subset (exhaustion N) _ _ hk
  have hfilter : (T.F.nonemptyList hT.2.2).reverse.filter
      (fun j => decide ((T.pullback g hg).F.hyp j ≠ ∅)) =
      ((T.pullback g hg).F.nonemptyList hT'.2.2).reverse :=
    List.filter_reverse.trans (congrArg List.reverse
      (HypersurfaceFamily.nonemptyList_comap_eq_filter T.F ⇑g hT.2.2 hT'.2.2).symm)
  -- (1) on `N`: the chain over `W'` for the full list and the canonical chain for the filtered
  -- list agree on the intersection of the next-to-last opens
  have h₁ := ChainState.step21FamAux_filter_rel (T.pullback g hg) s d.bd₁ hT' W'
    (memberCount T s hT + 1) hW' hWsub' W'' (memberCount (T.pullback g hg) s hT' + 1) hW'' hWsub''
    (T.F.nonemptyList hT.2.2).reverse _ (fun _ _ _ => hnil) hfilter (Nat.le_succ _)
    (Nat.le_succ _) (W' (memberCount T s hT) ⊓ W'' (memberCount (T.pullback g hg) s hT'))
    inf_le_left inf_le_right
  have hT'_id : AnalyticTriple.BOClass s
      ((T.pullback g hg).pullback ContMDiffMap.id
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)) :=
    AnalyticTriple.boClass_of_isPullbackOf hT'
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)
      (AnalyticTriple.isPullbackOf_pullback _ _ _)
  have hI' : IsCompact (closure ((W' (memberCount T s hT + 1) ⊓
      W'' (memberCount (T.pullback g hg) s hT' + 1) : Opens N) : Set N)) :=
    (hW' _).of_isClosed_subset isClosed_closure (closure_mono inf_le_left)
  have hI'I : closure ((W' (memberCount T s hT + 1) ⊓
      W'' (memberCount (T.pullback g hg) s hT' + 1) : Opens N) : Set N) ⊆
      (W' (memberCount T s hT) ⊓ W'' (memberCount (T.pullback g hg) s hT') : Opens N) := by
    rw [Opens.coe_inf, Opens.coe_inf]
    exact Set.subset_inter
      ((closure_mono Set.inter_subset_left).trans (hWsub' _ (Nat.lt_succ_self _)))
      ((closure_mono Set.inter_subset_right).trans (hWsub'' _ (Nat.lt_succ_self _)))
  -- the virtual state over that intersection and its relations to the two chains on `N`
  have hrel₂ : ((step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW'
      hWsub' (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)).restrictEraseId (T.pullback g hg) s
      (inf_le_left : W' (memberCount T s hT) ⊓ W'' (memberCount (T.pullback g hg) s hT') ≤
        W' (memberCount T s hT))).L.eraseEmpty =
      ((step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW' hWsub'
        (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)).L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_left))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) _ _
          (ChainState.image_id_subset inf_le_left))).eraseEmpty :=
    AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _
  have hrel₃ : ((step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW'
      hWsub' (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)).restrictEraseId (T.pullback g hg) s
      (inf_le_left : W' (memberCount T s hT) ⊓ W'' (memberCount (T.pullback g hg) s hT') ≤
        W' (memberCount T s hT))).L.eraseEmpty =
      ((BO.hfStep2FamChainAlong (T.pullback g hg) s hT' W'' hWsub'' d hW'').L.pullback
        (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_right))
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) _ _
          (ChainState.image_id_subset inf_le_right))).eraseEmpty :=
    hrel₂.trans ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
        (AnalyticManifold.BlowUpSequence.pullback_congr
      (step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW' hWsub'
        (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)).L (ContMDiffMap.ext fun _ => rfl) _
      (isLocalDiffeomorph_restrictLE inf_le_left))).trans
      (h₁.trans (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
          (AnalyticManifold.BlowUpSequence.pullback_congr
        (BO.hfStep2FamChainAlong (T.pullback g hg) s hT' W'' hWsub'' d hW'').L
        (ContMDiffMap.ext fun _ => rfl) (isLocalDiffeomorph_restrictLE inf_le_right) _))))
  have h₃ := BO.hfStep22Link_rel d (T.pullback g hg) hT' hH' hle' ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) hT'_id
        (ChainState.image_id_subset inf_le_left)
    (step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW' hWsub'
      (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)) _ hrel₂ (hW' _)
    (hWsub' _ (Nat.lt_succ_self _)) hI' hI'I (ChainState.image_id_subset inf_le_left)
  have h₄ := BO.hfStep22Link_rel d (T.pullback g hg) hT' hH' hle' ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) hT'_id
        (ChainState.image_id_subset inf_le_right)
    (BO.hfStep2FamChainAlong (T.pullback g hg) s hT' W'' hWsub'' d hW'') _ hrel₃ (hW'' _)
    (BO.closure_chainLast_subset (T.pullback g hg) s hT' W'' hWsub'') hI' hI'I
    (ChainState.image_id_subset inf_le_right)
  -- (2) the chain over `W'` is the pull-back of the canonical chain of `g(U')`, and so is the
  -- Step-2.2 link along `g`
  have h₂ := step21FamAux_rel_along T d.bd₁ hT g hg hT' W (memberCount T s hT + 1) hW hWsub W'
    hW' hWsub' hWW' (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)
  have h₅ := BO.hfStep22Link_rel d T hT hH hle g hg hT' (hWW' (memberCount T s hT))
    (BO.hfStep2FamChainAlong T s hT W hWsub d hW)
    (step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW' hWsub'
      (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)) h₂ (hW _)
    (BO.closure_chainLast_subset T s hT W hWsub) (hW' _) (hWsub' _ (Nat.lt_succ_self _))
    (hWW' (memberCount T s hT + 1))
  -- the two appended chains on `N` agree on the intersection of the last opens
  have hI : (((step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW' hWsub'
      (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)).L.shrinkAppend
      (N.restrictLE (ChainState.le_of_closure_subset (hWsub' _ (Nat.lt_succ_self _))))
      (isLocalDiffeomorph_restrictLE _)
      (BO.hfStep22ValueOf d (T.pullback g hg) hT' hH' hle'
        (step21FamAux (T.pullback g hg) s d.bd₁ hT' W' (memberCount T s hT + 1) hW' hWsub'
          (T.F.nonemptyList hT.2.2).reverse (Nat.le_succ _)) (hW' _)
        (hWsub' _ (Nat.lt_succ_self _)))).pullback
      (N.restrictLE (inf_le_left : W' (memberCount T s hT + 1) ⊓
        W'' (memberCount (T.pullback g hg) s hT' + 1) ≤ W' (memberCount T s hT + 1)))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      (((BO.hfStep2FamChainAlong (T.pullback g hg) s hT' W'' hWsub'' d hW'').L.shrinkAppend
        (N.restrictLE (BO.chainLast_le (T.pullback g hg) s hT' W'' hWsub''))
        (isLocalDiffeomorph_restrictLE _)
        (BO.hfStep22FamOnAlong (T.pullback g hg) s hT' W'' hWsub'' d hW'' hH' hle')).pullback
        (N.restrictLE (inf_le_right : W' (memberCount T s hT + 1) ⊓
          W'' (memberCount (T.pullback g hg) s hT' + 1) ≤
          W'' (memberCount (T.pullback g hg) s hT' + 1)))
        (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
    (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
        (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl)
      (isLocalDiffeomorph_restrictLE inf_le_left)
      (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) _ _
        (ChainState.image_id_subset inf_le_left)))).trans
      (h₃.symm.trans (h₄.trans (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
          (AnalyticManifold.BlowUpSequence.pullback_congr _
        (ContMDiffMap.ext fun _ => rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) _ _
          (ChainState.image_id_subset inf_le_right))
        (isLocalDiffeomorph_restrictLE inf_le_right)))))
  -- assemble
  have hc₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((AnalyticMap.restrictMap g (W' (memberCount T s hT + 1)) (W (memberCount T s hT + 1))
        (hWW' _)).comp (N.restrictLE hU'W')) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg _ _ (hWW' _))
      (isLocalDiffeomorph_restrictLE hU'W')
  have hc₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((M.restrictLE (le_chainOpens_last (exhaustion M) hW₀ (memberCount T s hT + 1))).comp
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
        Set.Subset.rfl)
  have hmaps : (AnalyticMap.restrictMap g (W' (memberCount T s hT + 1))
      (W (memberCount T s hT + 1)) (hWW' _)).comp (N.restrictLE hU'W') =
      (M.restrictLE (le_chainOpens_last (exhaustion M) hW₀ (memberCount T s hT + 1))).comp
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  rw [BO.hfStep2SeqFamOn_eq_along (T.pullback g hg) s hT' d hH' hle' U' hU',
    BO.hfStep2SeqFamOn_eq_along T s hT d hH hle (AnalyticMap.imageOpens g hg U') hW₀]
  unfold BO.hfStep2SeqFamAlong
  exact (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_restrict_congr _ _ inf_le_right
      inf_le_left
      (le_inf hU'W' (BO.le_step2OpenV (T.pullback g hg) s hT' U' hU')) hI.symm).trans
    ((AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
      (isLocalDiffeomorph_restrictLE hU'W')).symm.trans
      ((congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ (N.restrict (W'
          (memberCount T s hT + 1))) =>
          (X.pullback (N.restrictLE hU'W') (isLocalDiffeomorph_restrictLE hU'W')).eraseEmpty)
          h₅).trans
        ((AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
            (isLocalDiffeomorph_restrictLE hU'W')).trans
          ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
              (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).trans
            ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
                (AnalyticManifold.BlowUpSequence.pullback_congr _ hmaps hc₁ hc₂)).trans
              ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
                  (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).symm.trans
                (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
                  (AnalyticMap.isLocalDiffeomorph_restrictMap hg U'
                    (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)).symm))))))

end Hironaka.Manifold
