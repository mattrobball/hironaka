/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAIndep
public import Hironaka.Manifold.Germ.StalkMap
public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepACompat
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAAlign
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part: commutation with local analytic isomorphisms

Clause (2) of [Kol07, Theorem 103] and the second condition of [Kol07, 34.1] for the value of the
rounds on the nonmonomial part: along a local analytic isomorphism `g : N → M` and a relatively
compact open `U' ⊆ N`, the value for the pulled-back triple on `U'` is the value for `T` on `g(U')`
pulled back along `g|_{U'}` and cleaned of empty blow-ups (`stepAFamOn_pullback`), the shape of
`AnalyticFamilyFunctor.CommutesWithLocalIsos`. The family functor of the rounds on the marked class
`BMOClass m` is `stepAFunctor`, and its commutation is `stepAFunctor_commutesWithLocalIsos`.

The proof aligns the two canonical descents through a third, virtual descent over `N` (the device of
`StepACompat.lean` and `StepAIndep.lean`): its chain `preJoin` is the canonical chain of `U'` met
with the `g`-preimage of the canonical chain of `V ⊇ g(U')` (relatively compact, shrinking,
containing `U'`), its bound the larger of the two bounds, its triple the pulled-back triple pulled
back once more along the identity, so that the descent over `M` compares with it along `g`
(`descent_restrictMap_eq`, the form of `descent_restrict_eq` for a general `g`) and the canonical
descent over `N` compares with it along the identity (`descent_restrict_eq` itself). The two
comparisons read the same list on `U'` (`imageValueAt_eq_preJoin`,
`stepAFamOn_pullback_eq_preJoin`), with the deletion of empty blow-ups once at the end.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t)

/-! ### A descent pulled back along a local isomorphism, through the virtual descent -/

section RestrictMap

variable (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω h)
  {T₂ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N} (e : T₂ = T.pullback h hh)
  (hT₂ : AnalyticTriple.BMOClass m T₂)
  (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))
  (X : ℕ → Opens N) (hX : ∀ j, IsCompact (closure (X j : Set N))) (rX : ℕ)
  (hXsub : ∀ j, j < rX → closure (X (j + 1) : Set N) ⊆ X j) (DX : ℕ)
  (hDX : ∀ x ∈ (X 0 : Set N), (nonmonomialTriple T₂).I.ord x ≤ (DX : ℕ∞))
  (hDD : D ≤ DX) (hrr : rX ≤ (DX - D) + r) (hXW : ∀ j, ⇑h '' (X j : Set N) ⊆ W (j - (DX - D)))

include e in
/-- **A descent over `M`, pulled back along `h` to an open `U'` inside the last open of a chain over
`N`, equals the descent over `N` (for a triple equal to the pulled-back one) restricted to `U'`**,
up to empty blow-ups: the alignment `descentStateAux_rel` along `h`, then the restriction composed
with the inclusion (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`). The form of
`descent_restrict_eq` for a general `h`. -/
theorem descent_restrictMap_eq (hrXt : rX ≤ DX + 1 - t) {U' : Opens N} (hU'X : U' ≤ X rX) :
    ((descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD (rX - (DX - D)) (by omega)
        (by omega)).L.pullback (AnalyticMap.restrictMap h U' (W (rX - (DX - D)))
          ((Set.image_mono hU'X).trans (hXW rX)))
      (AnalyticMap.isLocalDiffeomorph_restrictMap hh _ _ _)).eraseEmpty =
    ((descentStateAux T₂ m hT₂ bo hcomp hid t hm hmt X hX rX hXsub DX hDX rX le_rfl
        hrXt).L.pullback (N.restrictLE hU'X) (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  subst e
  have hal := descentStateAux_rel T m hT bo hcomp hid t hm hmt h hh hT₂ W hW r hWsub D hD X hX rX
    hXsub DX hDX hDD hrr hXW rX le_rfl hrXt
  unfold alignRHS at hal
  have hc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((AnalyticMap.restrictMap h (X rX) (W (rX - (DX - D))) (hXW rX)).comp (N.restrictLE hU'X)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh _ _ _)
      (isLocalDiffeomorph_restrictLE _)
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
      (isLocalDiffeomorph_restrictLE hU'X), hal,
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
        AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

end RestrictMap

/-! ### The virtual chain of a chain over `N` and the preimage of a chain over `M` -/

section PreJoin

variable (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
  (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) (V : Opens M)
  (hV : IsCompact (closure (V : Set M)))

/-- The virtual chain: the canonical chain of `U'` met with the `g`-preimage of the canonical chain
of `V`. -/
abbrev preJoin (j : ℕ) : Opens N :=
  stepAChainOpens U' hU' j ⊓ preimageOpens ⇑g g.contMDiff (stepAChainOpens V hV j)

theorem isCompact_closure_preJoin (j : ℕ) :
    IsCompact (closure (preJoin g U' hU' V hV j : Set N)) :=
  (isCompact_closure_shrinkChain hU' (closure_subset_stepAOuter U' hU') j).of_isClosed_subset
    isClosed_closure (closure_mono (SetLike.coe_subset_coe.mpr inf_le_left))

theorem closure_preJoin_succ_subset (j : ℕ) :
    closure (preJoin g U' hU' V hV (j + 1) : Set N) ⊆ preJoin g U' hU' V hV j := by
  refine (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter
    (closure_shrinkChain_succ_subset hU' (closure_subset_stepAOuter U' hU') j) ?_)
  have h1 : closure (⇑g ⁻¹' (stepAChainOpens V hV (j + 1) : Set M)) ⊆
      ⇑g ⁻¹' closure (stepAChainOpens V hV (j + 1) : Set M) :=
    closure_minimal (Set.preimage_mono subset_closure)
      (isClosed_closure.preimage g.contMDiff.continuous)
  exact h1.trans (Set.preimage_mono
    (closure_shrinkChain_succ_subset hV (closure_subset_stepAOuter V hV) j))

theorem preJoin_le_left (j k : ℕ) (hkj : k ≤ j) :
    preJoin g U' hU' V hV j ≤ stepAChainOpens U' hU' k :=
  inf_le_left.trans (shrinkChain_antitone hU' (closure_subset_stepAOuter U' hU') hkj)

theorem image_preJoin_subset (j k : ℕ) (hkj : k ≤ j) :
    ⇑g '' (preJoin g U' hU' V hV j : Set N) ⊆ stepAChainOpens V hV k := by
  rintro _ ⟨x, hx, rfl⟩
  exact shrinkChain_antitone hV (closure_subset_stepAOuter V hV) hkj hx.2

/-- `U'` lies in every open of the virtual chain (when `g(U') ⊆ V`). -/
theorem le_preJoin (hUV : ⇑g '' (U' : Set N) ⊆ V) (j : ℕ) : U' ≤ preJoin g U' hU' V hV j :=
  le_inf (le_stepAChainOpens U' hU' j)
    (fun _ hx => le_stepAChainOpens V hV j (hUV (Set.mem_image_of_mem g hx)))

/-- The larger of the two bounds. -/
abbrev preJoinBound : ℕ := max (stepABound (T.pullback g hg) U' hU') (stepABound T V hV)

include hcomp in
/-- The larger bound holds on the first open of the virtual chain, for the pulled-back triple pulled
back once more along the identity (the triple of the virtual descent). -/
theorem preJoin_bound (x : N) (hx : x ∈ (preJoin g U' hU' V hV 0 : Set N)) :
    (nonmonomialTriple
        ((T.pullback g hg).pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N))).I.ord x ≤
          (preJoinBound T g hg U' hU' V hV : ℕ∞) := by
  rw [hcomp (T.pullback g hg) _ _]
  change ((nonmonomialTriple (T.pullback g hg)).I.pullback _ _).ord x ≤ _
  rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N x),
    nonmonomialTriple_I]
  exact (ord_le_roundOrderOn (T.pullback g hg) (stepAOuter U' hU')
    (isCompact_closure_stepAOuter U' hU') (closure_shrinkChain_zero_subset hU'
      (closure_subset_stepAOuter U' hU') (subset_closure hx.1))).trans
    (by exact_mod_cast le_max_left _ _)

/-! ### The value of `V` pulled back along `g|_{U'}`, with a re-indexed final state -/

/-- The `k`-th state of the canonical descent of `V` over `M`, pulled back along `g|_{U'}` and
cleaned of empty blow-ups (its type does not depend on `k`). -/
def imageValueAt (k : ℕ) (hk : k ≤ stepALinks T t V hV) (hkt : k ≤ stepABound T V hV + 1 - t)
    (hk' : ⇑g '' (U' : Set N) ⊆ stepAChainOpens V hV k) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (N.restrict U') :=
  ((descentStateAux T m hT bo hcomp hid t hm hmt (stepAChainOpens V hV)
      (fun k => isCompact_closure_shrinkChain hV (closure_subset_stepAOuter V hV) k)
      (stepALinks T t V hV)
      (fun k _ => closure_shrinkChain_succ_subset hV (closure_subset_stepAOuter V hV) k)
      (stepABound T V hV) (stepABound_bound T V hV) k hk hkt).L.pullback
      (AnalyticMap.restrictMap g U' (stepAChainOpens V hV k) hk')
    (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' _ hk')).eraseEmpty

theorem imageValueAt_congr {k k' : ℕ} (e : k = k') (hk : k ≤ stepALinks T t V hV)
    (hkt : k ≤ stepABound T V hV + 1 - t) (hk' : k' ≤ stepALinks T t V hV)
    (hkt' : k' ≤ stepABound T V hV + 1 - t) (hsub : ⇑g '' (U' : Set N) ⊆ stepAChainOpens V hV k)
    (hsub' : ⇑g '' (U' : Set N) ⊆ stepAChainOpens V hV k') :
    imageValueAt T m hT bo hcomp hid t hm hmt g hg U' V hV k hk hkt hsub =
      imageValueAt T m hT bo hcomp hid t hm hmt g hg U' V hV k' hk' hkt' hsub' := by
  subst e
  rfl

/-- The value on `V` pulled back along `g|_{U'}` and cleaned is the final state pulled back along
`g|_{U'}` (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`). -/
theorem stepAFamOn_pullback_restrictMap_eq (hUV : ⇑g '' (U' : Set N) ⊆ V) :
    ((stepAFamOn T m hT bo hcomp hid t hm hmt V hV).pullback (AnalyticMap.restrictMap g U' V hUV)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' V hUV)).eraseEmpty =
    imageValueAt T m hT bo hcomp hid t hm hmt g hg U' V hV (stepALinks T t V hV) le_rfl le_rfl
      (fun _ hy => le_stepAChainOpens V hV _ (hUV hy)) := by
  unfold stepAFamOn imageValueAt stepAChainState descentState
  have hc : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      ((M.restrictLE (le_stepAChainOpens V hV (stepALinks T t V hV))).comp
        (AnalyticMap.restrictMap g U' V hUV)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' V hUV)
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ =>
        Subtype.ext rfl) _ _)

/-! ### The two alignments with the virtual descent -/

/-- The canonical descent of `V` over `M`, pulled back along `g|_{U'}`, aligned with the virtual
descent of the pair `U', V` over `N` and read on `U'`. -/
theorem imageValueAt_eq_preJoin (hT' : AnalyticTriple.BMOClass m (T.pullback g hg))
    (hUV : ⇑g '' (U' : Set N) ⊆ V) :
    imageValueAt T m hT bo hcomp hid t hm hmt g hg U' V hV (stepALinks T t V hV) le_rfl le_rfl
      (fun _ hy => le_stepAChainOpens V hV _ (hUV hy)) =
    ((descentStateAux ((T.pullback g hg).pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)) m (bmoClass_pullback_id
            (T.pullback g hg) m hT') bo
        hcomp hid t hm hmt (preJoin g U' hU' V hV) (isCompact_closure_preJoin g U' hU' V hV)
        (preJoinBound T g hg U' hU' V hV + 1 - t)
        (fun j _ => closure_preJoin_succ_subset g U' hU' V hV j) (preJoinBound T g hg U' hU' V hV)
        (preJoin_bound T hcomp g hg U' hU' V hV) (preJoinBound T g hg U' hU' V hV + 1 - t) le_rfl
        le_rfl).L.pullback (N.restrictLE (le_preJoin g U' hU' V hV hUV _))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  have hle : stepABound T V hV ≤ preJoinBound T g hg U' hU' V hV := le_max_right _ _
  have e : (T.pullback g hg).pullback ContMDiffMap.id
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N) =
      T.pullback g hg :=
    AnalyticTriple.IsPullbackOf.eq
      ((T.isPullbackOf_pullback g hg).comp ((T.pullback g hg).isPullbackOf_pullback
        ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)))
      (T.isPullbackOf_pullback g hg)
  refine (imageValueAt_congr T m hT bo hcomp hid t hm hmt g hg U' V hV (sub_links_eq (t := t) hle)
    le_rfl le_rfl (sub_links_eq (t := t) hle).symm.le (sub_links_eq (t := t) hle).symm.le _
    ((Set.image_mono (le_preJoin g U' hU' V hV hUV _)).trans
      (image_preJoin_subset g U' hU' V hV _ _ (Nat.sub_le _ _)))).trans ?_
  exact descent_restrictMap_eq T m hT bo hcomp hid t hm hmt g hg e
    (bmoClass_pullback_id (T.pullback g hg) m hT') (stepAChainOpens V hV) _ _ _ _ _
    (preJoin g U' hU' V hV) (isCompact_closure_preJoin g U' hU' V hV) _
    (fun j _ => closure_preJoin_succ_subset g U' hU' V hV j) (preJoinBound T g hg U' hU' V hV)
    (preJoin_bound T hcomp g hg U' hU' V hV) hle (links_le_sub_add (t := t) hle)
    (fun j => image_preJoin_subset g U' hU' V hV _ _ (Nat.sub_le _ _)) le_rfl _

/-- The canonical descent of `U'` over `N` for the pulled-back triple, aligned with the virtual
descent of the pair `U', V` and read on `U'`. -/
theorem stepAFamOn_pullback_eq_preJoin (hT' : AnalyticTriple.BMOClass m (T.pullback g hg))
    (hUV : ⇑g '' (U' : Set N) ⊆ V) :
    stepAFamOn (T.pullback g hg) m hT' bo hcomp hid t hm hmt U' hU' =
    ((descentStateAux ((T.pullback g hg).pullback ContMDiffMap.id
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id N)) m (bmoClass_pullback_id
            (T.pullback g hg) m hT') bo
        hcomp hid t hm hmt (preJoin g U' hU' V hV) (isCompact_closure_preJoin g U' hU' V hV)
        (preJoinBound T g hg U' hU' V hV + 1 - t)
        (fun j _ => closure_preJoin_succ_subset g U' hU' V hV j) (preJoinBound T g hg U' hU' V hV)
        (preJoin_bound T hcomp g hg U' hU' V hV) (preJoinBound T g hg U' hU' V hV + 1 - t) le_rfl
        le_rfl).L.pullback (N.restrictLE (le_preJoin g U' hU' V hV hUV _))
      (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
  have hle : stepABound (T.pullback g hg) U' hU' ≤ preJoinBound T g hg U' hU' V hV :=
    le_max_left _ _
  rw [stepAFamOn_eq_stepAValueAt (T.pullback g hg) m hT' bo hcomp hid t hm hmt U' hU',
    stepAValueAt_congr (T.pullback g hg) m hT' bo hcomp hid t hm hmt U' hU'
      (sub_links_eq (t := t) hle) le_rfl (sub_links_eq (t := t) hle).symm.le _
      ((le_preJoin g U' hU' V hV hUV _).trans (preJoin_le_left g U' hU' V hV _ _ (Nat.sub_le _ _)))]
  exact descent_restrict_eq (T.pullback g hg) m hT' bo hcomp hid t hm hmt (stepAChainOpens U' hU')
    _ _ _ _ _ (preJoin g U' hU' V hV) (isCompact_closure_preJoin g U' hU' V hV) _
    (fun j _ => closure_preJoin_succ_subset g U' hU' V hV j) (preJoinBound T g hg U' hU' V hV)
    (preJoin_bound T hcomp g hg U' hU' V hV) hle (links_le_sub_add (t := t) hle)
    (fun j => preJoin_le_left g U' hU' V hV _ _ (Nat.sub_le _ _)) le_rfl _

end PreJoin

/-! ### Commutation with local isomorphisms -/

/-- **The value of the rounds commutes with local analytic isomorphisms** (the analogue of
[Kol07, Theorem 103 (2)]; [Kol07, 34.1]): for `T'` a pull-back of `T` along `g`, the value on `U'`
is the value on `g(U')`
pulled back along `g|_{U'}` and cleaned of empty blow-ups. Both sides are the virtual descent of the
pair `U', g(U')` read on `U'` (`stepAFamOn_pullback_eq_preJoin`, `imageValueAt_eq_preJoin`). -/
theorem stepAFamOn_pullback (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g)
    {T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N} (hpull : T'.IsPullbackOf T g)
    (hT' : AnalyticTriple.BMOClass m T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))) :
    stepAFamOn T' m hT' bo hcomp hid t hm hmt U' hU' =
      ((stepAFamOn T m hT bo hcomp hid t hm hmt (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  obtain rfl := hpull.eq (T.isPullbackOf_pullback g hg)
  refine (stepAFamOn_pullback_eq_preJoin T m bo hcomp hid t hm hmt g hg U' hU'
    (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU') hT'
    Set.Subset.rfl).trans ?_
  refine Eq.trans ?_ (stepAFamOn_pullback_restrictMap_eq T m hT bo hcomp hid t hm hmt g hg U'
    (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU')
    Set.Subset.rfl).symm
  exact (imageValueAt_eq_preJoin T m hT bo hcomp hid t hm hmt g hg U' hU'
    (AnalyticMap.imageOpens g hg U') (AnalyticMap.isCompact_closure_image g hU') hT'
    Set.Subset.rfl).symm

/-! ### The family functor of the rounds -/

/-- **The family functor of the rounds on the nonmonomial part** on the marked class `BMOClass m`:
the compatible family `stepAFam` for every triple of the class. -/
def stepAFunctor :
    AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (AnalyticTriple.BMOClass m) where
  fam T hT := stepAFam T m hT bo hcomp hid t hm hmt

@[simp] theorem stepAFunctor_fam_seqOn {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((stepAFunctor m bo hcomp hid t hm hmt).fam T hT).seqOn U hU =
      stepAFamOn T m hT bo hcomp hid t hm hmt U hU := rfl

/-- The family functor of the rounds commutes with local analytic isomorphisms (the analogue of
[Kol07, Theorem 103 (2)]). -/
theorem stepAFunctor_commutesWithLocalIsos :
    (stepAFunctor m bo hcomp hid t hm hmt).CommutesWithLocalIsos := by
  intro M N T T' g hg hpull hT hT' U' hU'
  exact stepAFamOn_pullback T m hT bo hcomp hid t hm hmt g hg hpull hT' U' hU'

end Hironaka.Manifold.BMOmod

end
