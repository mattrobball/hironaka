/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAFamily
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAAlign
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: compatibility and independence of the value

The compatibility of the values on relatively compact opens ([Wlo09, Theorem 2.0.3 (4)],
[Wlo09, Definition 3.2.6]; [Kol07, 34.1]) for the rounds on the nonmonomial part: **the value on
`U ≤ V` is the value on `V` restricted to `U` and cleaned of empty blow-ups** (`stepAFamOn_compat`).
The independence of the value from the outer open on which the bound was read is proved by the
same device in `StepAIndep.lean` (`stepAFamOnAux_eq`, `stepAFamOn_eq_of_outer`).

Both are the alignment of two descents (`descentStateAux_rel`) through a third, **virtual** descent
for the triple pulled back along the identity: its chain is the intersection of the two chains
(`joinChain` for the chains of two compact sets in two outer opens, `stepAJoin` for the canonical
chains: relatively compact, shrinking, containing `closure U`), its bound the larger of the
two bounds (the index of the canonical exhaustion open is a choice, so the two bounds are not
comparable a priori). Aligned with either descent, the final list of the virtual descent restricted
to `U` is the final list of that descent restricted to `U`, up to empty blow-ups
(`descent_restrict_eq`, `descentValueAt_eq_join_left`, `descentValueAt_eq_join_right`); hence the
two values agree.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t)

/-! ### The triple pulled back along the identity -/

include hT in
/-- The marked class passes to the triple pulled back along the identity (the triple of the virtual
descent). -/
theorem bmoClass_pullback_id :
    AnalyticTriple.BMOClass m (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) :=
  ⟨hT.1, finite_nonempty_hyp_comap T.F _ hT.2⟩

/-! ### A descent restricted to a smaller open, through the virtual descent -/

section Restrict

variable (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))
  (X : ℕ → Opens M) (hX : ∀ j, IsCompact (closure (X j : Set M))) (rX : ℕ)
  (hXsub : ∀ j, j < rX → closure (X (j + 1) : Set M) ⊆ X j) (DX : ℕ)
  (hDX : ∀ x ∈ (X 0 : Set M),
      (nonmonomialTriple
      (T.pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))).I.ord x
        ≤ (DX : ℕ∞))
  (hDD : D ≤ DX) (hrr : rX ≤ (DX - D) + r) (hXW : ∀ j, X j ≤ W (j - (DX - D)))

/-- **A descent restricted to a smaller open equals the virtual descent restricted there**, up to
empty blow-ups: the alignment `descentStateAux_rel` along the identity, then the restriction to `U'`
composed with the inclusion (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`). -/
theorem descent_restrict_eq (hrXt : rX ≤ DX + 1 - t) {U' : Opens M} (hU'X : U' ≤ X rX) :
    ((descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD (rX - (DX - D)) (by omega)
        (by omega)).L.pullback (M.restrictLE (hU'X.trans (hXW rX)))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
    ((descentStateAux (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
        (bmoClass_pullback_id T m hT) bo hcomp hid t hm hmt X hX rX hXsub DX hDX rX le_rfl
        hrXt).L.pullback (M.restrictLE hU'X) (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  have hal := descentStateAux_rel T m hT bo hcomp hid t hm hmt ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
        (bmoClass_pullback_id T m hT) W hW r hWsub D hD X hX rX
    hXsub DX hDX hDD hrr (fun j => ChainState.image_id_subset (hXW j)) rX le_rfl hrXt
  unfold alignRHS at hal
  have hc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((AnalyticMap.restrictMap ContMDiffMap.id (X rX) (W (rX - (DX - D)))
        (ChainState.image_id_subset (hXW rX))).comp (M.restrictLE hU'X)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticMap.isLocalDiffeomorph_restrictMap
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) _ _ _)
      (isLocalDiffeomorph_restrictLE _)
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
      (isLocalDiffeomorph_restrictLE hU'X), hal,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
        AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

end Restrict

/-! ### The value with the bound as a parameter -/

section ValueAt

variable (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M)))

/-- The final list of the descent along `W` from the bound `D` after `k` links, restricted to an
open `U' ≤ W k` and cleaned of empty blow-ups, with the bound as an explicit parameter (its type
does not depend on `D` or `k`). -/
def valueAt (D : ℕ) (hWsub : ∀ k, k < D + 1 - t → closure (W (k + 1) : Set M) ⊆ W k)
    (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) (k : ℕ)
    (hk : k ≤ D + 1 - t) {U' : Opens M} (hU'k : U' ≤ W k) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U') :=
  ((descentStateAux T m hT bo hcomp hid t hm hmt W hW (D + 1 - t) hWsub D hD k hk hk).L.pullback
    (M.restrictLE hU'k) (isLocalDiffeomorph_restrictLE _)).eraseEmpty

/-- `valueAt` depends on the bound and the index only through their values (a substitution). -/
theorem valueAt_congr {D D' k k' : ℕ} (eD : D = D') (ek : k = k')
    (hWsub : ∀ k, k < D + 1 - t → closure (W (k + 1) : Set M) ⊆ W k)
    (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) (hk : k ≤ D + 1 - t)
    (hWsub' : ∀ k, k < D' + 1 - t → closure (W (k + 1) : Set M) ⊆ W k)
    (hD' : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D' : ℕ∞)) (hk' : k' ≤ D' + 1 - t)
    {U' : Opens M} (hU'k : U' ≤ W k) (hU'k' : U' ≤ W k') :
    valueAt T m hT bo hcomp hid t hm hmt W hW D hWsub hD k hk hU'k =
      valueAt T m hT bo hcomp hid t hm hmt W hW D' hWsub' hD' k' hk' hU'k' := by
  subst eD
  subst ek
  rfl

end ValueAt

/-! ### Descents along the chains of a compact set, and their virtual join -/

/-- The number of links of a descent from the smaller bound `DU ≤ DX` is the number of links of the
descent from `DX` past its first `DX − DU` links. -/
theorem sub_links_eq {DU DX t : ℕ} (h : DU ≤ DX) : DU + 1 - t = DX + 1 - t - (DX - DU) := by
  omega

/-- The descent from `DX` is no longer than its first `DX − DU` links plus the descent from `DU`. -/
theorem links_le_sub_add {DU DX t : ℕ} (h : DU ≤ DX) : DX + 1 - t ≤ DX - DU + (DU + 1 - t) := by
  omega

section Aux

variable (K : Set M) (hK : IsCompact K) (O : Opens M) (hO : IsCompact (closure (O : Set M)))
  (hKO : K ⊆ O)

include hO in
/-- The bound on the first open of the chain of `K` inside `O` is `roundOrderOn T O`. -/
theorem shrinkChain_zero_bound (x : M) (hx : x ∈ (shrinkChain K O hK hKO 0 : Set M)) :
    (nonmonomialTriple T).I.ord x ≤ (roundOrderOn T O : ℕ∞) := by
  rw [nonmonomialTriple_I]
  exact ord_le_roundOrderOn T O hO (closure_shrinkChain_zero_subset hK hKO (subset_closure hx))

/-- The final list of the descent of `K` inside `O` after `k` links, restricted to `U' ≤ W k` and
cleaned of empty blow-ups (its type does not depend on `k`). -/
def descentValueAt (k : ℕ) (hk : k ≤ roundOrderOn T O + 1 - t) {U' : Opens M}
    (hU'k : U' ≤ shrinkChain K O hK hKO k) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U') :=
  valueAt T m hT bo hcomp hid t hm hmt (shrinkChain K O hK hKO)
    (fun k => isCompact_closure_shrinkChain hK hKO k) (roundOrderOn T O)
    (fun k _ => closure_shrinkChain_succ_subset hK hKO k) (shrinkChain_zero_bound T K hK O hO hKO) k
    hk hU'k

theorem descentValueAt_congr {k k' : ℕ} (e : k = k') (hk : k ≤ roundOrderOn T O + 1 - t)
    (hk' : k' ≤ roundOrderOn T O + 1 - t) {U' : Opens M} (hU'k : U' ≤ shrinkChain K O hK hKO k)
    (hU'k' : U' ≤ shrinkChain K O hK hKO k') :
    descentValueAt T m hT bo hcomp hid t hm hmt K hK O hO hKO k hk hU'k =
      descentValueAt T m hT bo hcomp hid t hm hmt K hK O hO hKO k' hk' hU'k' := by
  subst e
  rfl

end Aux

section JoinChain

variable (K₁ : Set M) (hK₁ : IsCompact K₁) (O₁ : Opens M) (hO₁ : IsCompact (closure (O₁ : Set M)))
  (hK₁O₁ : K₁ ⊆ O₁) (K₂ : Set M) (hK₂ : IsCompact K₂) (O₂ : Opens M)
  (hO₂ : IsCompact (closure (O₂ : Set M))) (hK₂O₂ : K₂ ⊆ O₂)

/-- The intersection of the two chains. -/
abbrev joinChain (j : ℕ) : Opens M :=
  shrinkChain K₁ O₁ hK₁ hK₁O₁ j ⊓ shrinkChain K₂ O₂ hK₂ hK₂O₂ j

theorem isCompact_closure_joinChain (j : ℕ) :
    IsCompact (closure (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j : Set M)) :=
  (isCompact_closure_shrinkChain hK₁ hK₁O₁ j).of_isClosed_subset isClosed_closure
    (closure_mono (SetLike.coe_subset_coe.mpr inf_le_left))

theorem closure_joinChain_succ_subset (j : ℕ) :
    closure (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ (j + 1) : Set M) ⊆
      joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j :=
  (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
    (closure_shrinkChain_succ_subset hK₁ hK₁O₁ j) (closure_shrinkChain_succ_subset hK₂ hK₂O₂ j))

theorem joinChain_le_left (j k : ℕ) (hkj : k ≤ j) :
    joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j ≤ shrinkChain K₁ O₁ hK₁ hK₁O₁ k :=
  inf_le_left.trans (shrinkChain_antitone hK₁ hK₁O₁ hkj)

theorem joinChain_le_right (j k : ℕ) (hkj : k ≤ j) :
    joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j ≤ shrinkChain K₂ O₂ hK₂ hK₂O₂ k :=
  inf_le_right.trans (shrinkChain_antitone hK₂ hK₂O₂ hkj)

/-- The larger of the two bounds. -/
abbrev joinBound : ℕ := max (roundOrderOn T O₁) (roundOrderOn T O₂)

include hcomp hO₁ in
theorem joinChain_bound (x : M) (hx : x ∈ (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ 0 : Set M)) :
    (nonmonomialTriple
        (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))).I.ord x ≤
      (joinBound T O₁ O₂ : ℕ∞) := by
  rw [hcomp T _ _]
  change ((nonmonomialTriple T).I.pullback _ _).ord x ≤ _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M x)]
  exact (shrinkChain_zero_bound T K₁ hK₁ O₁ hO₁ hK₁O₁ x hx.1).trans
    (by exact_mod_cast le_max_left _ _)

/-- The descent of the first chain, aligned with the virtual descent and restricted to an open `U'`
inside the last open of the virtual chain. -/
theorem descentValueAt_eq_join_left {U' : Opens M}
    (hU' : U' ≤ joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ (joinBound T O₁ O₂ + 1 - t)) :
    descentValueAt T m hT bo hcomp hid t hm hmt K₁ hK₁ O₁ hO₁ hK₁O₁ (roundOrderOn T O₁ + 1 - t)
      le_rfl (hU'.trans (joinChain_le_left K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ _ _
        (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_left _ _) 1) t))) =
    ((descentStateAux (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
        (bmoClass_pullback_id T m hT) bo hcomp hid t hm hmt
        (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂)
        (isCompact_closure_joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂) (joinBound T O₁ O₂ + 1 - t)
        (fun j _ => closure_joinChain_succ_subset K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j)
        (joinBound T O₁ O₂) (joinChain_bound T hcomp K₁ hK₁ O₁ hO₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂)
        (joinBound T O₁ O₂ + 1 - t) le_rfl le_rfl).L.pullback (M.restrictLE hU')
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  have hle : roundOrderOn T O₁ ≤ joinBound T O₁ O₂ := le_max_left _ _
  rw [descentValueAt_congr T m hT bo hcomp hid t hm hmt K₁ hK₁ O₁ hO₁ hK₁O₁
    (sub_links_eq (t := t) hle) le_rfl (sub_links_eq (t := t) hle).symm.le _
    (hU'.trans (joinChain_le_left K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ _ _ (Nat.sub_le _ _)))]
  exact descent_restrict_eq T m hT bo hcomp hid t hm hmt (shrinkChain K₁ O₁ hK₁ hK₁O₁) _ _ _ _ _
    (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂)
    (isCompact_closure_joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂) _
    (fun j _ => closure_joinChain_succ_subset K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j) (joinBound T O₁ O₂)
    (joinChain_bound T hcomp K₁ hK₁ O₁ hO₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂) hle
    (links_le_sub_add (t := t) hle)
    (fun j => joinChain_le_left K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ _ _ (Nat.sub_le _ _)) le_rfl _

/-- The descent of the second chain, aligned with the virtual descent and restricted to an open
`U'`. -/
theorem descentValueAt_eq_join_right {U' : Opens M}
    (hU' : U' ≤ joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ (joinBound T O₁ O₂ + 1 - t)) :
    descentValueAt T m hT bo hcomp hid t hm hmt K₂ hK₂ O₂ hO₂ hK₂O₂ (roundOrderOn T O₂ + 1 - t)
      le_rfl (hU'.trans (joinChain_le_right K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ _ _
        (Nat.sub_le_sub_right (Nat.add_le_add_right (le_max_right _ _) 1) t))) =
    ((descentStateAux (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
        (bmoClass_pullback_id T m hT) bo hcomp hid t hm hmt
        (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂)
        (isCompact_closure_joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂) (joinBound T O₁ O₂ + 1 - t)
        (fun j _ => closure_joinChain_succ_subset K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j)
        (joinBound T O₁ O₂) (joinChain_bound T hcomp K₁ hK₁ O₁ hO₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂)
        (joinBound T O₁ O₂ + 1 - t) le_rfl le_rfl).L.pullback (M.restrictLE hU')
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  have hle : roundOrderOn T O₂ ≤ joinBound T O₁ O₂ := le_max_right _ _
  rw [descentValueAt_congr T m hT bo hcomp hid t hm hmt K₂ hK₂ O₂ hO₂ hK₂O₂
    (sub_links_eq (t := t) hle) le_rfl (sub_links_eq (t := t) hle).symm.le _
    (hU'.trans (joinChain_le_right K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ _ _ (Nat.sub_le _ _)))]
  exact descent_restrict_eq T m hT bo hcomp hid t hm hmt (shrinkChain K₂ O₂ hK₂ hK₂O₂) _ _ _ _ _
    (joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂)
    (isCompact_closure_joinChain K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂) _
    (fun j _ => closure_joinChain_succ_subset K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ j) (joinBound T O₁ O₂)
    (joinChain_bound T hcomp K₁ hK₁ O₁ hO₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂) hle
    (links_le_sub_add (t := t) hle)
    (fun j => joinChain_le_right K₁ hK₁ O₁ hK₁O₁ K₂ hK₂ O₂ hK₂O₂ _ _ (Nat.sub_le _ _)) le_rfl _

end JoinChain

/-! ### The virtual chain of two canonical chains -/

section Join

variable (U : Opens M) (hU : IsCompact (closure (U : Set M))) (V : Opens M)
  (hV : IsCompact (closure (V : Set M)))

/-- The intersection of the canonical chains of `U` and of `V`: a shrinking chain of relatively
compact opens containing `closure U ∩ closure V` (`joinChain` of the two canonical chains). -/
abbrev stepAJoin (j : ℕ) : Opens M :=
  joinChain (closure (U : Set M)) hU (stepAOuter U hU) (closure_subset_stepAOuter U hU)
    (closure (V : Set M)) hV (stepAOuter V hV) (closure_subset_stepAOuter V hV) j

theorem isCompact_closure_stepAJoin (j : ℕ) :
    IsCompact (closure (stepAJoin U hU V hV j : Set M)) :=
  isCompact_closure_joinChain _ hU _ _ _ hV _ _ j

theorem closure_stepAJoin_succ_subset (j : ℕ) :
    closure (stepAJoin U hU V hV (j + 1) : Set M) ⊆ stepAJoin U hU V hV j :=
  closure_joinChain_succ_subset _ hU _ _ _ hV _ _ j

theorem stepAJoin_le_left (j k : ℕ) (hkj : k ≤ j) :
    stepAJoin U hU V hV j ≤ stepAChainOpens U hU k :=
  joinChain_le_left _ hU _ _ _ hV _ _ j k hkj

theorem stepAJoin_le_right (j k : ℕ) (hkj : k ≤ j) :
    stepAJoin U hU V hV j ≤ stepAChainOpens V hV k :=
  joinChain_le_right _ hU _ _ _ hV _ _ j k hkj

/-- The larger of the two bounds. -/
abbrev stepAJoinBound : ℕ := joinBound T (stepAOuter U hU) (stepAOuter V hV)

include hcomp in
/-- The larger bound holds on the first open of the virtual chain, for the triple pulled back along
the identity. -/
theorem stepAJoin_bound (x : M) (hx : x ∈ (stepAJoin U hU V hV 0 : Set M)) :
    (nonmonomialTriple
        (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))).I.ord x ≤
      (stepAJoinBound T U hU V hV : ℕ∞) :=
  joinChain_bound T hcomp _ hU _ (isCompact_closure_stepAOuter U hU) _ _ hV _ _ x hx

end Join

/-! ### The value with a re-indexed final state -/

section Value

variable (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The final list of the canonical descent of `U` after `k` links, restricted to an open `U'` and
cleaned of empty blow-ups (its type does not depend on `k`). -/
def stepAValueAt (k : ℕ) (hk : k ≤ stepALinks T t U hU) {U' : Opens M}
    (hU'k : U' ≤ stepAChainOpens U hU k) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (M.restrict U') :=
  valueAt T m hT bo hcomp hid t hm hmt (stepAChainOpens U hU)
    (fun k => isCompact_closure_shrinkChain hU (closure_subset_stepAOuter U hU) k)
    (stepABound T U hU)
    (fun k _ => closure_shrinkChain_succ_subset hU (closure_subset_stepAOuter U hU) k)
    (stepABound_bound T U hU) k hk hU'k

theorem stepAValueAt_congr {k k' : ℕ} (e : k = k') (hk : k ≤ stepALinks T t U hU)
    (hk' : k' ≤ stepALinks T t U hU) {U' : Opens M}
    (hU'k : U' ≤ stepAChainOpens U hU k) (hU'k' : U' ≤ stepAChainOpens U hU k') :
    stepAValueAt T m hT bo hcomp hid t hm hmt U hU k hk hU'k =
      stepAValueAt T m hT bo hcomp hid t hm hmt U hU k' hk' hU'k' := by
  subst e
  rfl

/-- The value on `U` is the final list restricted to `U` (by definition). -/
theorem stepAFamOn_eq_stepAValueAt :
    stepAFamOn T m hT bo hcomp hid t hm hmt U hU =
      stepAValueAt T m hT bo hcomp hid t hm hmt U hU (stepALinks T t U hU) le_rfl
        (le_stepAChainOpens U hU _) := rfl

/-- The value on `V` restricted to `U ≤ V` and cleaned is the final list restricted to `U`
(`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`). -/
theorem stepAFamOn_pullback_eraseEmpty_eq {V : Opens M} (hV : IsCompact (closure (V : Set M)))
    (hUV : U ≤ V) :
    ((stepAFamOn T m hT bo hcomp hid t hm hmt V hV).pullback (M.restrictLE hUV)
      (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty =
    stepAValueAt T m hT bo hcomp hid t hm hmt V hV (stepALinks T t V hV) le_rfl
      (hUV.trans (le_stepAChainOpens V hV _)) := by
  unfold stepAFamOn stepAValueAt valueAt stepAChainState descentState
  have hc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE (le_stepAChainOpens V hV (stepALinks T t V hV))).comp (M.restrictLE hUV)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

end Value

/-! ### Compatibility -/

section Compat

variable (U : Opens M) (hU : IsCompact (closure (U : Set M))) (V : Opens M)
  (hV : IsCompact (closure (V : Set M)))

/-- The canonical descent of `U`, aligned with the virtual descent of the pair `U, V` and restricted
to an open `U' ≤ U` (`descentValueAt_eq_join_left` at the canonical chains). -/
theorem stepAValueAt_eq_join_left {U' : Opens M} (hU'U : U' ≤ U) (hU'V : U' ≤ V) :
    stepAValueAt T m hT bo hcomp hid t hm hmt U hU (stepALinks T t U hU) le_rfl
      (hU'U.trans (le_stepAChainOpens U hU _)) =
    ((descentStateAux (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
        (bmoClass_pullback_id T m hT) bo hcomp hid t hm hmt (stepAJoin U hU V hV)
        (isCompact_closure_stepAJoin U hU V hV) (stepAJoinBound T U hU V hV + 1 - t)
        (fun j _ => closure_stepAJoin_succ_subset U hU V hV j) (stepAJoinBound T U hU V hV)
        (stepAJoin_bound T hcomp U hU V hV) (stepAJoinBound T U hU V hV + 1 - t) le_rfl
        le_rfl).L.pullback
      (M.restrictLE (le_inf (hU'U.trans (le_stepAChainOpens U hU _))
        (hU'V.trans (le_stepAChainOpens V hV _))))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
  descentValueAt_eq_join_left T m hT bo hcomp hid t hm hmt _ hU _
    (isCompact_closure_stepAOuter U hU) (closure_subset_stepAOuter U hU) _ hV _
    (closure_subset_stepAOuter V hV)
    (le_inf (hU'U.trans (le_stepAChainOpens U hU _)) (hU'V.trans (le_stepAChainOpens V hV _)))

/-- The canonical descent of `V`, aligned with the virtual descent of the pair `U, V` and restricted
to an open `U' ≤ U` (`descentValueAt_eq_join_right` at the canonical chains). -/
theorem stepAValueAt_eq_join_right {U' : Opens M} (hU'U : U' ≤ U) (hU'V : U' ≤ V) :
    stepAValueAt T m hT bo hcomp hid t hm hmt V hV (stepALinks T t V hV) le_rfl
      (hU'V.trans (le_stepAChainOpens V hV _)) =
    ((descentStateAux (T.pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)) m
        (bmoClass_pullback_id T m hT) bo hcomp hid t hm hmt (stepAJoin U hU V hV)
        (isCompact_closure_stepAJoin U hU V hV) (stepAJoinBound T U hU V hV + 1 - t)
        (fun j _ => closure_stepAJoin_succ_subset U hU V hV j) (stepAJoinBound T U hU V hV)
        (stepAJoin_bound T hcomp U hU V hV) (stepAJoinBound T U hU V hV + 1 - t) le_rfl
        le_rfl).L.pullback
      (M.restrictLE (le_inf (hU'U.trans (le_stepAChainOpens U hU _))
        (hU'V.trans (le_stepAChainOpens V hV _))))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty :=
  descentValueAt_eq_join_right T m hT bo hcomp hid t hm hmt _ hU _
    (isCompact_closure_stepAOuter U hU) (closure_subset_stepAOuter U hU) _ hV _
    (isCompact_closure_stepAOuter V hV) (closure_subset_stepAOuter V hV)
    (le_inf (hU'U.trans (le_stepAChainOpens U hU _)) (hU'V.trans (le_stepAChainOpens V hV _)))

/-- **The compatibility of the values of the rounds** ([Wlo09, Theorem 2.0.3 (4)],
[Wlo09, Definition 3.2.6]; [Kol07, 34.1]): the value on `U ≤ V` is the value on `V` restricted to
`U` and cleaned of empty blow-ups. Both are the virtual descent of the pair restricted to `U`
(`stepAValueAt_eq_join_left`, `stepAValueAt_eq_join_right`). -/
theorem stepAFamOn_compat (hUV : U ≤ V) :
    stepAFamOn T m hT bo hcomp hid t hm hmt U hU =
      ((stepAFamOn T m hT bo hcomp hid t hm hmt V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  rw [stepAFamOn_pullback_eraseEmpty_eq T m hT bo hcomp hid t hm hmt U hV hUV,
    stepAFamOn_eq_stepAValueAt T m hT bo hcomp hid t hm hmt U hU,
    stepAValueAt_eq_join_left T m hT bo hcomp hid t hm hmt U hU V hV le_rfl hUV,
    stepAValueAt_eq_join_right T m hT bo hcomp hid t hm hmt U hU V hV le_rfl hUV]

end Compat

end Hironaka.Manifold.BMOmod

end
