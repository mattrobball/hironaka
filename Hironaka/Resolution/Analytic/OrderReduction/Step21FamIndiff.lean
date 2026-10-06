/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransport
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.InducedValue
import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedConcat
import Hironaka.Resolution.Analytic.OrderReduction.Step21Indiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 on an open is indifferent to empty boundary members

The empty blow-up convention of [Kol07, 32] in the compatible-family form of Step 2.1
(`Step21Fam.lean`): when the nonempty members of `E` are the members of `F'` along an order
embedding `e : F'.ι ↪o E.ι` (matched members, the others empty), Step 2.1 on `U` for `(M, 𝓘, E)`
is Step 2.1 on `U` for `(M, 𝓘, F')` (`step21FamOn_indifferentToEmptyMembers`):

* `BDanFamData.fam_seqOn_induced_indiff` — Lemma 102's family at the member `i` of the induced
  boundary from `F'` is the family at the member `e i` of the induced boundary from `E`, read on any
  open: the family's `indifferentToEmptyMembers` along the index correspondence `corrIdx` of the
  induced boundaries;
* `ChainState.link_L_indiff` — two chain states with the same sequence, for the two triples, link
  to the same sequence at corresponding members (the pulled-back triples over the open are again a
  boundary change along `e`);
* `ChainState.step21FamAux_indiff_rel` — the chains over corresponding member lists, along any two
  admissible chains of opens, agree on every common open up to empty blow-ups: the two-chain
  argument of `ChainIndep.lean` through the virtual chain over the intersections (`link_rel` twice,
  `restrictEraseId`), the two virtual links identified by `link_L_indiff`;
* `step21FamOn_indifferentToEmptyMembers` — the list of nonempty members of `E` is the image along
  `e` of that of `F'` (`nonemptyList_eq_map`), so the two chains agree on `U`.

Its chain argument (`step21FamAux_indiff_rel`) enters the indifference of Step 2 on an open
(`Step2AssemblyComm.lean`).
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ} (bd : BDanFamData ψ₀ s)

omit [FiniteDimensional 𝕜 E] in
/-- **The value of one link is indifferent to empty members**: Lemma 102's family at the member `i`
of the induced boundary from `F'` equals the family at the member `e i` of the induced boundary from
`E`, read on any relatively compact open of the last stage. This is the family's
`indifferentToEmptyMembers` along the index correspondence `corrIdx e` of the induced boundaries,
whose members are matched (`hyp_corrIdxAux_of_forall`) and empty outside the range
(`hyp_eq_empty_of_notMem_range_corrIdx`), the member index corresponding
(`corrIdxAux_originalIdxAux`). -/
theorem BDanFamData.fam_seqOn_induced_indiff {X : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ X) (hT : AnalyticTriple.BOClass s T) (F' : HypersurfaceFamily X)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT' : AnalyticTriple.BOClass s (BDan.withBoundary T F' hsnc'))
        (L : AnalyticManifold.BlowUpSequence ψ₀ X)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL' : L.toSuccession.IsOfOrderGe (BDan.withBoundary T F' hsnc').I s
      (BDan.withBoundary T F' hsnc').F.idealSheaf) (i : F'.ι)
    (O : Opens (L.stage (Fin.last _)))
    (hO : IsCompact (closure (O : Set (L.stage (Fin.last _))))) :
    (bd.fam (T.induced s L hL) (AnalyticTriple.boClass_induced T s L hL hT)
        (L.toSuccession.originalIdx T.F (Fin.last _) (e i))).seqOn O hO =
      (bd.fam ((BDan.withBoundary T F' hsnc').induced s L hL')
        (AnalyticTriple.boClass_induced _ s L hL' hT')
        (L.toSuccession.originalIdx F' (Fin.last _) i)).seqOn O hO := by
  have hidx : (L.toSuccession.corrIdx e (Fin.last _))
        (L.toSuccession.originalIdx F' (Fin.last _) i) =
      L.toSuccession.originalIdx T.F (Fin.last _) (e i) :=
    L.toSuccession.corrIdxAux_originalIdxAux e _ _ i
  have hX := bd.indifferentToEmptyMembers (T.induced s L hL)
    ((BDan.withBoundary T F' hsnc').induced s L hL').F
    ((BDan.withBoundary T F' hsnc').induced s L hL').isSnc
    (L.toSuccession.corrIdx e (Fin.last _))
    (fun k => (L.toSuccession.hyp_corrIdxAux_of_forall ⇑e (fun j => (he j).symm) (Fin.last _)
      k).symm)
    (fun b hb => L.toSuccession.hyp_eq_empty_of_notMem_range_corrIdx e he' (Fin.last _) b hb)
    (AnalyticTriple.boClass_induced T s L hL hT) (AnalyticTriple.boClass_induced _ s L hL' hT')
    (L.toSuccession.originalIdx F' (Fin.last _) i) O hO
  exact (bd.fam_seqOn_congr rfl _ _ _ _ (heq_of_eq hidx.symm) O hO).trans hX

omit [FiniteDimensional 𝕜 E] in
/-- **One link of the chain is indifferent to empty members**: two chain states with the same
sequence, for a triple `T` and for a triple `T'` with the same ideal sheaf whose boundary members
are members of `T.F` along `e` (the others empty), link to the same sequence at the members `e i`
and `i`. The triples pulled back to the open are again such a pair (`AnalyticTriple.ext'`), and the
link's value is `fam_seqOn_induced_indiff` at the induced triples. -/
theorem ChainState.link_L_indiff {X : AnalyticManifold.{u} 𝕜 E} (T T' : AnalyticTriple ψ₀ X)
    (hI : T'.I = T.I) (e : T'.F.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = T'.F.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅) (hT : AnalyticTriple.BOClass s T)
    (hT' : AnalyticTriple.BOClass s T') {W : Opens X} (st : ChainState T s W)
    (st' : ChainState T' s W) (hL : st.L = st'.L) (i : T'.F.ι) {V : Opens X}
    (hV : IsCompact (closure (V : Set X))) (hVW : closure (V : Set X) ⊆ W) :
    (st.link T s bd hT (e i) hV hVW).L = (st'.link T' s bd hT' i hV hVW).L := by
  obtain ⟨L, hge⟩ := st
  obtain ⟨L', hge'⟩ := st'
  change L = L' at hL
  subst hL
  -- the triples pulled back to `W`: the same boundary change along `e`
  have hTW : AnalyticTriple.BOClass s
      (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)) :=
    boClass_pullback_inclusion_of_boClass T W hT
  have hTW' : AnalyticTriple.BOClass s
      (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)) :=
    boClass_pullback_inclusion_of_boClass T' W hT'
  have hTWeq : BDan.withBoundary (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W))
      (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F
      (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).isSnc =
      T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W) :=
    AnalyticTriple.ext'
      (congrArg (fun J : AnalyticManifold.IdealSheaf X => J.pullback _ (X.inclusion W).contMDiff)
          hI.symm) rfl
  have hge'' : L.toSuccession.IsOfOrderGe
      (BDan.withBoundary (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W))
        (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F
        (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).isSnc).I s
      (BDan.withBoundary (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W))
        (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F
        (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).isSnc).F.idealSheaf := by
    rw [hTWeq]
    exact hge'
  have hT'' : AnalyticTriple.BOClass s
      (BDan.withBoundary (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W))
        (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F
        (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).isSnc) := by
    rw [hTWeq]
    exact hTW'
  have heW : ∀ k, (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F.hyp (e k) =
      (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F.hyp k :=
    fun k => congrArg (fun S => ⇑(X.inclusion W) ⁻¹' S) (he k)
  have heW' : ∀ b, b ∉ Set.range e →
      (T.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F.hyp b = ∅ :=
    fun b hb => (congrArg (fun S => ⇑(X.inclusion W) ⁻¹' S) (he' b hb)).trans Set.preimage_empty
  rw [ChainState.link_L, ChainState.link_L]
  exact congrArg (L.shrinkAppend _ _)
    ((bd.fam_seqOn_induced_indiff _ hTW
      (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).F
      (T'.pullback (X.inclusion W) (isLocalDiffeomorph_inclusion X W)).isSnc e heW heW' hT'' L hge
      hge'' i _ _).trans
      (bd.fam_seqOn_congr (AnalyticTriple.induced_congr hTWeq s L hge'' hge') _ _ _ _
        (AnalyticManifold.FiniteSuccession.heq_originalIdx_congr L.toSuccession
          (congrArg AnalyticTriple.F hTWeq) (Fin.last _) HEq.rfl) _ _))

section TwoChains

variable (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) (F' : HypersurfaceFamily M)
  (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
  (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
  (hT' : AnalyticTriple.BOClass s (BDan.withBoundary T F' hsnc'))

include he he' in
/-- **The two chains over corresponding member lists agree on every common open**: the chain for
`(M, 𝓘, E)` over a list `l'.map e` along one admissible chain of opens and the chain for
`(M, 𝓘, F')` over `l'` along another, restricted to a common open and with the empty blow-ups
deleted, are equal. By induction on `l'`: the states so far agree on the intersection of the two
opens (the induction hypothesis), the two links are compared through the virtual chain over the
intersections (`link_rel` twice, `restrictEraseId`), where they are the same link at corresponding
members (`link_L_indiff`), then restricted to the smaller open
(`eraseEmpty_pullback_restrict_congr`). -/
theorem ChainState.step21FamAux_indiff_rel (W : ℕ → Opens M) (r : ℕ)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (W' : ℕ → Opens M) (r' : ℕ)
    (hW' : ∀ k, IsCompact (closure (W' k : Set M)))
    (hWsub' : ∀ k, k < r' → closure (W' (k + 1) : Set M) ⊆ W' k) :
    ∀ (l' : List F'.ι) (l : List T.F.ι), l'.map e = l →
      ∀ (hl : l.length ≤ r) (hl' : l'.length ≤ r') (U : Opens M) (hU₁ : U ≤ W l.length)
        (hU₂ : U ≤ W' l'.length),
      ((step21FamAux T s bd hT W r hW hWsub l hl).L.pullback (M.restrictLE hU₁)
        (isLocalDiffeomorph_restrictLE hU₁)).eraseEmpty =
      ((step21FamAux (BDan.withBoundary T F' hsnc') s bd hT' W' r' hW' hWsub' l' hl').L.pullback
        (M.restrictLE hU₂) (isLocalDiffeomorph_restrictLE hU₂)).eraseEmpty
  | [], l, hleq, hl, hl', U, hU₁, hU₂ => by
    subst hleq
    change ((AnalyticManifold.BlowUpSequence.nil _).pullback _ _).eraseEmpty =
      ((AnalyticManifold.BlowUpSequence.nil _).pullback _ _).eraseEmpty
    simp
  | i :: l', l, hleq, hl, hl', U, hU₁, hU₂ => by
    subst hleq
    -- the states so far and the intersections
    have hlm : (l'.map e).length ≤ r := Nat.le_of_succ_le hl
    have hlm' : l'.length ≤ r' := Nat.le_of_succ_le hl'
    have ih := step21FamAux_indiff_rel W r hW hWsub W' r' hW' hWsub' l' _ rfl hlm hlm'
      (W (l'.map e).length ⊓ W' l'.length) inf_le_left inf_le_right
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
    have hI' : IsCompact (closure ((W ((l'.map e).length + 1) ⊓ W' (l'.length + 1) : Opens M) :
        Set M)) :=
      (hW ((l'.map e).length + 1)).of_isClosed_subset isClosed_closure (closure_mono inf_le_left)
    have hI'I : closure ((W ((l'.map e).length + 1) ⊓ W' (l'.length + 1) : Opens M) : Set M) ⊆
        (W (l'.map e).length ⊓ W' l'.length : Opens M) := by
      rw [Opens.coe_inf, Opens.coe_inf]
      exact Set.subset_inter
        ((closure_mono Set.inter_subset_left).trans (hWsub (l'.map e).length hl))
        ((closure_mono Set.inter_subset_right).trans (hWsub' l'.length hl'))
    -- the virtual states and their relations to the two chains
    set st₁ := step21FamAux T s bd hT W r hW hWsub (l'.map e) hlm with hst₁
    set st₂ := step21FamAux (BDan.withBoundary T F' hsnc') s bd hT' W' r' hW' hWsub' l' hlm'
      with hst₂
    have hrel₁ : (st₁.restrictEraseId T s (inf_le_left : W (l'.map e).length ⊓ W' l'.length ≤
        W (l'.map e).length)).L.eraseEmpty =
        (st₁.L.pullback
          (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_left))
          (AnalyticMap.isLocalDiffeomorph_restrictMap
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
            (ChainState.image_id_subset inf_le_left))).eraseEmpty :=
      AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _
    have hrel₂ : (st₂.restrictEraseId (BDan.withBoundary T F' hsnc') s
        (inf_le_right : W (l'.map e).length ⊓ W' l'.length ≤ W' l'.length)).L.eraseEmpty =
        (st₂.L.pullback
          (AnalyticMap.restrictMap ContMDiffMap.id _ _ (ChainState.image_id_subset inf_le_right))
          (AnalyticMap.isLocalDiffeomorph_restrictMap
              (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
            (ChainState.image_id_subset inf_le_right))).eraseEmpty :=
      AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty _
    have h₁ := ChainState.link_rel T s bd hT ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
      hT_id (ChainState.image_id_subset inf_le_left) st₁ _ hrel₁ (e i) (hW _)
      (hWsub (l'.map e).length hl) hI' hI'I (ChainState.image_id_subset inf_le_left)
    have h₂ := ChainState.link_rel (BDan.withBoundary T F' hsnc') s bd hT' ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) hT'_id
          (ChainState.image_id_subset inf_le_right) st₂ _
      hrel₂ i (hW' _) (hWsub' l'.length hl') hI' hI'I (ChainState.image_id_subset inf_le_right)
    -- the two virtual states carry the same list, so their links agree
    have hvL : (st₁.restrictEraseId T s (inf_le_left : W (l'.map e).length ⊓ W' l'.length ≤
        W (l'.map e).length)).L =
        (st₂.restrictEraseId (BDan.withBoundary T F' hsnc') s
          (inf_le_right : W (l'.map e).length ⊓ W' l'.length ≤ W' l'.length)).L := by
      rw [ChainState.restrictEraseId_L, ChainState.restrictEraseId_L]
      exact ih
    have hbr := ChainState.link_L_indiff bd
      (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))
      ((BDan.withBoundary T F' hsnc').pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) rfl e
      (fun k => congrArg (fun S => ⇑(ContMDiffMap.id : AnalyticMap M M) ⁻¹' S) (he k))
      (fun b hb => (congrArg (fun S => ⇑(ContMDiffMap.id : AnalyticMap M M) ⁻¹' S)
        (he' b hb)).trans Set.preimage_empty)
      hT_id hT'_id _ _ hvL i hI' hI'I
    -- the two linked states agree on the intersection, hence on `U`
    have hI : ((st₁.link T s bd hT (e i) (hW _) (hWsub (l'.map e).length hl)).L.pullback
        (M.restrictLE (inf_le_left : W ((l'.map e).length + 1) ⊓ W' (l'.length + 1) ≤
          W ((l'.map e).length + 1))) (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
        ((st₂.link (BDan.withBoundary T F' hsnc') s bd hT' i (hW' _)
          (hWsub' l'.length hl')).L.pullback
          (M.restrictLE (inf_le_right : W ((l'.map e).length + 1) ⊓ W' (l'.length + 1) ≤
            W' (l'.length + 1))) (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
      (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
          (AnalyticManifold.BlowUpSequence.pullback_congr
        (st₁.link T s bd hT (e i) (hW _) (hWsub (l'.map e).length hl)).L
        (ContMDiffMap.ext fun _ => rfl) (isLocalDiffeomorph_restrictLE inf_le_left)
        (AnalyticMap.isLocalDiffeomorph_restrictMap
            (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
          (ChainState.image_id_subset inf_le_left)))).trans
        (h₁.symm.trans ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty hbr).trans (h₂.trans
          (congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
              (AnalyticManifold.BlowUpSequence.pullback_congr
            (st₂.link (BDan.withBoundary T F' hsnc') s bd hT' i (hW' _)
              (hWsub' l'.length hl')).L
            (ContMDiffMap.ext fun _ => rfl)
            (AnalyticMap.isLocalDiffeomorph_restrictMap
                (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _
              (ChainState.image_id_subset inf_le_right))
            (isLocalDiffeomorph_restrictLE inf_le_right))))))
    exact AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_restrict_congr _ _ inf_le_left
        inf_le_right
      (le_inf hU₁ hU₂) hI

end TwoChains

/-- **Step 2.1 on `U` is indifferent to empty boundary members** (Step 2.1 of the
proof of [Kol07, Theorem 103] applies Lemma 102 to the nonempty members): the list of nonempty
members of `E` is the image along `e` of that of `F'` (`nonemptyList_eq_map`, reversed), and the two
chains agree on `U` (`step21FamAux_indiff_rel`). -/
theorem step21FamOn_indifferentToEmptyMembers (bd : BDanFamData ψ₀ s)
    (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc ψ₀)
    (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT' : AnalyticTriple.BOClass s
      (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)) :
    step21FamOn T s bd hT U hU =
      step21FamOn ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ s bd hT' U hU := by
  unfold step21FamOn step21FamChain
  exact ChainState.step21FamAux_indiff_rel bd T hT F' hsnc' e he he' hT' _ (memberCount T s hT)
    _ _ _ (memberCount _ s hT') _ _ (F'.nonemptyList hT'.2.2).reverse
    (T.F.nonemptyList hT.2.2).reverse
    (by rw [List.map_reverse, BO.nonemptyList_eq_map T F' e he he' hT.2.2 hT'.2.2])
    le_rfl le_rfl U (le_chainOpens_last (exhaustion M) hU (memberCount T s hT))
    (le_chainOpens_last (exhaustion M) hU (memberCount _ s hT'))

end Hironaka.Manifold
