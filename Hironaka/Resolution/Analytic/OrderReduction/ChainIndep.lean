/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Functor.EraseEmptyOrder
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransport
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Hironaka.Resolution.Analytic.OrderReduction.Step21ErasePrep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The chain of Step 2.1 does not depend on the chain of opens

The value of Step 2.1 of the proof of [Kol07, Theorem 103] in the compatible-family form
(`Step21Fam.lean`) is computed along a fixed shrinking chain of relatively compact opens. By the
second clause of [Kol07, 34.1] and the compatibility of [Wlo09, Theorem 2.0.3 (4)] it should not
depend on the chain: **two chains over two admissible chains of opens, processing the same members,
agree on a common smaller open up to empty blow-ups** (`ChainState.step21FamAux_filter_rel`). The
proof goes link by link through a virtual chain over the intersections of the opens, the chain of
the triple pulled back along the identity (`ChainState.restrictEraseId`), to which both chains are
related by the transport of one link (`link_rel` of `ChainTransport.lean`, twice); the states are
compared by "the sequence over the smaller open, with the empty blow-ups deleted, is the pull-back
of the sequence over the larger one, with the empty blow-ups deleted". A member whose boundary
hypersurface is empty contributes nothing (`link_L_of_hyp_eq_empty`: the induced member is the
strict transform of `∅`, and the family's value at an empty member is the trivial family, the
hypothesis `hnil`, which the concrete data satisfy), which identifies the chain over a member list
filtered of its empty members with the chain over the full list.

The consequences, the independence of the chain, the compatibility under restriction and the
commutation with local analytic isomorphisms, are drawn in `Step21FamIndep.lean`; the same
two-chain argument gives the indifference to empty boundary members in `Step21FamIndiff.lean`.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace ChainState

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ) (bd : BDanFamData ψ₀ s)
  (hT : AnalyticTriple.BOClass s T)

omit [FiniteDimensional 𝕜 E] in
/-- **A link at a member whose hypersurface is empty is the restriction of the sequence to the
smaller open** (the counterpart for boundary members of [Kol07, 32]): the induced member is the
strict
transform of `∅` (`hyp_originalIdx`, `strictTransformSeq_empty`), the family's value there is the
trivial family (`hnil`), and appending the empty sequence is the identity (`concat_nil_right`). -/
theorem link_L_of_hyp_eq_empty
    (hnil : ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
      (hT' : AnalyticTriple.BOClass s T') (j : T'.F.ι),
      T'.F.hyp j = ∅ → bd.fam T' hT' j = CompatibleFamily.nil T')
    {W : Opens M} (st : ChainState T s W) {j : T.F.ι} (hj : T.F.hyp j = ∅) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) :
    (st.link T s bd hT j hV hVW).L =
      st.L.pullback (M.restrictLE (le_of_closure_subset hVW))
        (isLocalDiffeomorph_restrictLE _) := by
  have hj' : ((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).induced s st.L
      st.hge).F.hyp (st.L.toSuccession.originalIdx
        (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F (Fin.last _) j) = ∅ :=
    (FiniteSuccession.hyp_originalIdx (S := st.L.toSuccession)
      (F := (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F) (Fin.last _) j).trans
      (by
        change st.L.toSuccession.strictTransformSeq (⇑(M.inclusion W) ⁻¹' T.F.hyp j)
          (Fin.last _) = ∅
        rw [hj, Set.preimage_empty, FiniteSuccession.strictTransformSeq_empty])
  rw [link_L]
  unfold linkValue
  rw [hnil _ _ _ hj']
  unfold BlowUpSequence.shrinkAppend
  change (st.L.pullback _ _).concat ((BlowUpSequence.nil _).pullback _ _) = _
  rw [BlowUpSequence.pullback_nil, BlowUpSequence.concat_nil_right]

end ChainState

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M : AnalyticManifold.{u} 𝕜 E}

omit [FiniteDimensional 𝕜 E] in
/-- Two sequences over opens `X`, `Y` whose restrictions to a common open `I` agree up to empty
blow-ups agree, up to empty blow-ups, on every `U ≤ I` (`pullback_comp`,
`eraseEmpty_pullback_eraseEmpty`). -/
theorem eraseEmpty_pullback_restrict_congr {X Y I U : Opens M} (A : BlowUpSequence ψ₀
    (M.restrict X))
    (B : BlowUpSequence ψ₀ (M.restrict Y)) (hIX : I ≤ X) (hIY : I ≤ Y) (hUI : U ≤ I)
    (h : (A.pullback (M.restrictLE hIX) (isLocalDiffeomorph_restrictLE hIX)).eraseEmpty =
      (B.pullback (M.restrictLE hIY) (isLocalDiffeomorph_restrictLE hIY)).eraseEmpty) :
    (A.pullback (M.restrictLE (hUI.trans hIX)) (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      (B.pullback (M.restrictLE (hUI.trans hIY)) (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  have e₁ : A.pullback (M.restrictLE (hUI.trans hIX)) (isLocalDiffeomorph_restrictLE _) =
      (A.pullback (M.restrictLE hIX) (isLocalDiffeomorph_restrictLE hIX)).pullback
        (M.restrictLE hUI) (isLocalDiffeomorph_restrictLE hUI) := by
    rw [pullback_comp _ _ _ _ _]
    exact pullback_congr A (ContMDiffMap.ext fun _ => rfl) _ _
  have e₂ : B.pullback (M.restrictLE (hUI.trans hIY)) (isLocalDiffeomorph_restrictLE _) =
      (B.pullback (M.restrictLE hIY) (isLocalDiffeomorph_restrictLE hIY)).pullback
        (M.restrictLE hUI) (isLocalDiffeomorph_restrictLE hUI) := by
    rw [pullback_comp _ _ _ _ _]
    exact pullback_congr B (ContMDiffMap.ext fun _ => rfl) _ _
  rw [e₁, e₂, ← eraseEmpty_pullback_eraseEmpty (A.pullback (M.restrictLE hIX) _) (M.restrictLE hUI)
    (isLocalDiffeomorph_restrictLE hUI), h, eraseEmpty_pullback_eraseEmpty]

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace ChainState

open _root_.Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)

omit [FiniteDimensional 𝕜 E] in
/-- The image of an open under the identity is the open (as sets). -/
theorem image_id_subset {I W : Opens M} (hIW : I ≤ W) :
    ⇑(ContMDiffMap.id : AnalyticMap M M) '' (I : Set M) ⊆ W := by
  rintro _ ⟨x, hx, rfl⟩
  exact hIW hx

omit [FiniteDimensional 𝕜 E] in
/-- The triple over a smaller open `I ≤ W`, as the pull-back along `I → W` of the triple over `W`,
is the triple over `I` of the triple pulled back along the identity (`pullback_pullback`). -/
theorem pullback_inclusion_pullback_restrictMap_id {I W : Opens M} (hIW : I ≤ W) :
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
        (AnalyticMap.restrictMap ContMDiffMap.id I W (image_id_subset hIW))
        (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) I W
          (image_id_subset hIW)) =
      (T.pullback ContMDiffMap.id (BlowUpSequence.isLocalDiffeomorph_id M)).pullback (M.inclusion I)
        (isLocalDiffeomorph_inclusion M I) := by
  rw [AnalyticTriple.pullback_pullback _ _ _ _ _,
    AnalyticTriple.pullback_pullback _ _ _ _ _]
  exact AnalyticTriple.pullback_eq_of_eq T (ContMDiffMap.ext fun _ => rfl) _ _

/-- **The virtual state over a smaller open**: the state's sequence restricted to `I ≤ W`, with the
empty blow-ups deleted, as a chain state of the triple pulled back along the identity (its order
clause by `isOfOrderGe_pullback` and `isOfOrderGe_eraseEmpty`). -/
noncomputable def restrictEraseId {W : Opens M} (st : ChainState T s W) {I : Opens M}
    (hIW : I ≤ W) :
    ChainState (T.pullback ContMDiffMap.id (BlowUpSequence.isLocalDiffeomorph_id M)) s I where
  L := (st.L.pullback (AnalyticMap.restrictMap ContMDiffMap.id I W (image_id_subset hIW))
    (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) I W
      (image_id_subset hIW))).eraseEmpty
  hge := by
    have h := BlowUpSequence.isOfOrderGe_eraseEmpty _ _ _
      ((T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).pullback
        (AnalyticMap.restrictMap ContMDiffMap.id I W (image_id_subset hIW))
        (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) I W
          (image_id_subset hIW))).isSnc
      (AnalyticTriple.isOfOrderGe_pullback _ s st.L st.hge
        (AnalyticMap.restrictMap ContMDiffMap.id I W (image_id_subset hIW))
        (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) I W
          (image_id_subset hIW)))
    rwa [pullback_inclusion_pullback_restrictMap_id T hIW] at h

omit [FiniteDimensional 𝕜 E] in
/-- The virtual state's sequence is the restricted sequence with the empty blow-ups deleted (the
restriction written as `restrictLE`). -/
theorem restrictEraseId_L {W : Opens M} (st : ChainState T s W) {I : Opens M} (hIW : I ≤ W) :
    (st.restrictEraseId T s hIW).L =
      (st.L.pullback (M.restrictLE hIW) (isLocalDiffeomorph_restrictLE hIW)).eraseEmpty :=
  congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
      rfl) _ _)

variable (bd : BDanFamData ψ₀ s) (hT : AnalyticTriple.BOClass s T)

/-- The second clause of [Kol07, 34.1] for the chain of Step 2.1: **two chains over two admissible
chains of opens, the second processing the members of the first with nonempty hypersurface, agree
on every common smaller open up to empty blow-ups**. By induction on the member list: a member with
empty hypersurface is a restriction on the first chain and is dropped by the second
(`link_L_of_hyp_eq_empty`); a kept member is linked on both chains and compared through the virtual
chain over the intersections (`link_rel` twice, `restrictEraseId`), then restricted to the smaller
open (`eraseEmpty_pullback_restrict_congr`). -/
theorem step21FamAux_filter_rel (W : ℕ → Opens M) (r : ℕ)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (W' : ℕ → Opens M) (r' : ℕ)
    (hW' : ∀ k, IsCompact (closure (W' k : Set M)))
    (hWsub' : ∀ k, k < r' → closure (W' (k + 1) : Set M) ⊆ W' k) :
    ∀ (l l' : List T.F.ι),
      (∀ j ∈ l, T.F.hyp j = ∅ → ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
        (hT' : AnalyticTriple.BOClass s T') (j' : T'.F.ι),
        T'.F.hyp j' = ∅ → bd.fam T' hT' j' = CompatibleFamily.nil T') →
      l.filter (fun j => decide (T.F.hyp j ≠ ∅)) = l' →
      ∀ (hl : l.length ≤ r) (hl' : l'.length ≤ r') (U : Opens M) (hU₁ : U ≤ W l.length)
        (hU₂ : U ≤ W' l'.length),
      ((step21FamAux T s bd hT W r hW hWsub l hl).L.pullback (M.restrictLE hU₁)
        (isLocalDiffeomorph_restrictLE hU₁)).eraseEmpty =
      ((step21FamAux T s bd hT W' r' hW' hWsub' l' hl').L.pullback (M.restrictLE hU₂)
        (isLocalDiffeomorph_restrictLE hU₂)).eraseEmpty
  | [], l', _, hl'eq, hl, hl', U, hU₁, hU₂ => by
    subst hl'eq
    change ((BlowUpSequence.nil _).pullback _ _).eraseEmpty =
      ((BlowUpSequence.nil _).pullback _ _).eraseEmpty
    simp
  | j :: l, l', hnil, hl'eq, hl, hl', U, hU₁, hU₂ => by
    by_cases hj : T.F.hyp j = ∅
    · -- an empty member: a restriction on the first chain, dropped by the second
      have hfe : (j :: l).filter (fun j => decide (T.F.hyp j ≠ ∅)) =
          l.filter (fun j => decide (T.F.hyp j ≠ ∅)) := by
        simp [hj]
      rw [hfe] at hl'eq
      have hU₁' : U ≤ W l.length := hU₁.trans fun _ hx => hWsub l.length hl (subset_closure hx)
      rw [← step21FamAux_filter_rel W r hW hWsub W' r' hW' hWsub' l l'
        (fun j' hj' => hnil j' (List.mem_cons.mpr (Or.inr hj'))) hl'eq (Nat.le_of_succ_le hl) hl' U
        hU₁' hU₂]
      change (((step21FamAux T s bd hT W r hW hWsub l (Nat.le_of_succ_le hl)).link T s bd hT j
        (hW _) (hWsub l.length hl)).L.pullback _ _).eraseEmpty = _
      rw [link_L_of_hyp_eq_empty T s bd hT (hnil j (List.mem_cons.mpr (Or.inl rfl)) hj) _ hj,
        BlowUpSequence.pullback_comp _ _ _ _ _]
      exact congrArg BlowUpSequence.eraseEmpty
        (BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)
    · -- a kept member: linked on both chains, compared through the virtual chain
      have hfe : (j :: l).filter (fun j => decide (T.F.hyp j ≠ ∅)) =
          j :: l.filter (fun j => decide (T.F.hyp j ≠ ∅)) := by
        simp [hj]
      rw [hfe] at hl'eq
      subst hl'eq
      -- the states so far and the intersections
      have hlm : l.length ≤ r := Nat.le_of_succ_le hl
      have hlm' : (l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length ≤ r' := Nat.le_of_succ_le hl'
      have ih := step21FamAux_filter_rel W r hW hWsub W' r' hW' hWsub' l _
        (fun j' hj' => hnil j' (List.mem_cons.mpr (Or.inr hj'))) rfl hlm hlm'
        (W l.length ⊓ W' (l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length) inf_le_left
        inf_le_right
      have hT_id : AnalyticTriple.BOClass s
          (T.pullback ContMDiffMap.id (BlowUpSequence.isLocalDiffeomorph_id M)) :=
        AnalyticTriple.boClass_of_isPullbackOf hT (BlowUpSequence.isLocalDiffeomorph_id M)
          (AnalyticTriple.isPullbackOf_pullback _ _ _)
      have hI' : IsCompact (closure ((W (l.length + 1) ⊓
          W' ((l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length + 1) : Opens M) : Set M)) :=
        (hW (l.length + 1)).of_isClosed_subset isClosed_closure (closure_mono inf_le_left)
      have hI'I : closure ((W (l.length + 1) ⊓
          W' ((l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length + 1) : Opens M) : Set M) ⊆
          (W l.length ⊓ W' (l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length : Opens M) := by
        rw [Opens.coe_inf, Opens.coe_inf]
        exact Set.subset_inter ((closure_mono Set.inter_subset_left).trans (hWsub l.length hl))
          ((closure_mono Set.inter_subset_right).trans (hWsub' _ hl'))
      -- the virtual state and its two relations
      set st₁ := step21FamAux T s bd hT W r hW hWsub l hlm with hst₁
      set st₂ := step21FamAux T s bd hT W' r' hW' hWsub'
        (l.filter (fun j => decide (T.F.hyp j ≠ ∅))) hlm' with hst₂
      have hrel₁ : (st₁.restrictEraseId T s (inf_le_left : W l.length ⊓
          W' (l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length ≤ W l.length)).L.eraseEmpty =
          (st₁.L.pullback
            (AnalyticMap.restrictMap ContMDiffMap.id _ _ (image_id_subset inf_le_left))
            (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) _ _
              (image_id_subset inf_le_left))).eraseEmpty :=
        BlowUpSequence.eraseEmpty_eraseEmpty _
      have hrel₂ : (st₁.restrictEraseId T s (inf_le_left : W l.length ⊓
          W' (l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length ≤ W l.length)).L.eraseEmpty =
          (st₂.L.pullback
            (AnalyticMap.restrictMap ContMDiffMap.id _ _ (image_id_subset inf_le_right))
            (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) _ _
              (image_id_subset inf_le_right))).eraseEmpty :=
        hrel₁.trans ((congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_congr st₁.L
          (ContMDiffMap.ext fun _ => rfl) _ (isLocalDiffeomorph_restrictLE inf_le_left))).trans
          (ih.trans (congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_congr st₂.L
            (ContMDiffMap.ext fun _ => rfl) (isLocalDiffeomorph_restrictLE inf_le_right) _))))
      have h₁ := link_rel T s bd hT ContMDiffMap.id (BlowUpSequence.isLocalDiffeomorph_id M) hT_id
        (image_id_subset inf_le_left) st₁ _ hrel₁ j (hW _) (hWsub l.length hl) hI' hI'I
        (image_id_subset inf_le_left)
      have h₂ := link_rel T s bd hT ContMDiffMap.id (BlowUpSequence.isLocalDiffeomorph_id M) hT_id
        (image_id_subset inf_le_right) st₂ _ hrel₂ j (hW' _) (hWsub' _ hl') hI' hI'I
        (image_id_subset inf_le_right)
      -- the two linked states agree on the intersection, hence on `U`
      have hI : ((st₁.link T s bd hT j (hW _) (hWsub l.length hl)).L.pullback
          (M.restrictLE (inf_le_left : W (l.length + 1) ⊓
            W' ((l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length + 1) ≤ W (l.length + 1)))
          (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
          ((st₂.link T s bd hT j (hW' _) (hWsub' _ hl')).L.pullback
            (M.restrictLE (inf_le_right : W (l.length + 1) ⊓
              W' ((l.filter (fun j => decide (T.F.hyp j ≠ ∅))).length + 1) ≤ W' _))
            (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
        (congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_congr
          (st₁.link T s bd hT j (hW _) (hWsub l.length hl)).L (ContMDiffMap.ext fun _ => rfl)
          (isLocalDiffeomorph_restrictLE inf_le_left)
          (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) _ _
            (image_id_subset inf_le_left)))).trans
          (h₁.symm.trans (h₂.trans (congrArg BlowUpSequence.eraseEmpty
              (BlowUpSequence.pullback_congr
            (st₂.link T s bd hT j (hW' _) (hWsub' _ hl')).L (ContMDiffMap.ext fun _ => rfl)
            (AnalyticMap.isLocalDiffeomorph_restrictMap (BlowUpSequence.isLocalDiffeomorph_id M) _ _
              (image_id_subset inf_le_right)) (isLocalDiffeomorph_restrictLE inf_le_right)))))
      exact BlowUpSequence.eraseEmpty_pullback_restrict_congr _ _ inf_le_left inf_le_right
        (le_inf hU₁ hU₂) hI

end ChainState

end Hironaka.Manifold
