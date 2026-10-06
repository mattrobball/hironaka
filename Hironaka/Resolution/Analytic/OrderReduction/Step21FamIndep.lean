/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Resolution.Analytic.OrderReduction.ChainIndep
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransport
import Hironaka.Resolution.Analytic.OrderReduction.Step21ErasePrep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 on an open: independence of the chain, compatibility, functoriality

Three clauses of Step 2.1 of the proof of [Kol07, Theorem 103] in the compatible-family form
(`Step21Fam.lean`), all from the two-chain lemma `step21FamAux_filter_rel` of `ChainIndep.lean`:

* `step21FamOn_chain_indep` — the value of Step 2.1 on `U` does not depend on the admissible chain
  of opens along which it is computed: the fixed chain of `step21FamOn` and any other, over the same
  member list, agree on `U` up to empty blow-ups;
* `step21FamOn_compat` — the compatibility under restriction of [Wlo09, Theorem 2.0.3 (4)]: for
  `U ≤ V`, the value on `U` is the value on `V` restricted to `U` with the empty blow-ups deleted
  (the independence of the chain for the chain of `V`, read on `U`);
* `step21FamOn_commutesWithLocalIsos` — the commutation with local analytic isomorphisms in the
  form of `AnalyticFamilyFunctor.CommutesWithLocalIsos` (the functoriality of Step 2.1 noted in
  [Kol07, 104, Step 2.3]): along a local analytic isomorphism `g : N → M`, the chain over `N` for
  the pulled-back triple over the member list filtered of the members emptied by `g` is, up to empty
  blow-ups, the chain over the full member list along a chain of opens carried into the chain of
  `g(U')` (`step21FamAux_filter_rel`; a member emptied by `g` contributes nothing, given that the
  family's value at an empty member is the trivial family, the hypothesis `hnil`), which is the
  pull-back of the chain over `M` link by link (`step21FamAux_rel_along`, `link_rel`).

The three clauses enter the compatible family of Step 2.1 and its functor in `Step22Fam.lean`.
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {s : ℕ}

omit [FiniteDimensional 𝕜 E] in
/-- The list of nonempty members has no empty member: filtering keeps it. -/
theorem nonemptyList_reverse_filter (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T) :
    (T.F.nonemptyList hT.2.2).reverse.filter (fun j => decide (T.F.hyp j ≠ ∅)) =
      (T.F.nonemptyList hT.2.2).reverse :=
  List.filter_eq_self.mpr fun j hj => decide_eq_true
    ((HypersurfaceFamily.mem_nonemptyList (F := T.F) (hF := hT.2.2) j).mp (List.mem_reverse.mp hj))

omit [FiniteDimensional 𝕜 E] in
/-- The members of the list of nonempty members are nonempty, so the hypothesis on empty members
of the two-chain lemma is never needed for it. -/
theorem nonemptyList_reverse_hnil (T : AnalyticTriple ψ₀ M) (hT : AnalyticTriple.BOClass s T)
    (bd : BDanFamData ψ₀ s) :
    ∀ j ∈ (T.F.nonemptyList hT.2.2).reverse, T.F.hyp j = ∅ →
      ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
        (hT' : AnalyticTriple.BOClass s T') (j' : T'.F.ι),
        T'.F.hyp j' = ∅ → bd.fam T' hT' j' = CompatibleFamily.nil T' := fun j hj h =>
  absurd h ((HypersurfaceFamily.mem_nonemptyList (F := T.F) (hF := hT.2.2) j).mp
    (List.mem_reverse.mp hj))

/-- **Step 2.1 on `U` does not depend on the chain of opens**: the two-chain lemma
(`step21FamAux_filter_rel`) for the given chain and the fixed one, over the list of nonempty
members, read on `U`. -/
theorem step21FamOn_chain_indep (bd : BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < memberCount T s hT → closure (W (k + 1) : Set M) ⊆ W k)
    (hUW : U ≤ W (memberCount T s hT)) :
    ((step21FamAux T s bd hT W (memberCount T s hT) hW hWsub (T.F.nonemptyList hT.2.2).reverse
        le_rfl).L.pullback (M.restrictLE hUW) (isLocalDiffeomorph_restrictLE hUW)).eraseEmpty =
      step21FamOn T s bd hT U hU := by
  unfold step21FamOn step21FamChain
  exact ChainState.step21FamAux_filter_rel T s bd hT W (memberCount T s hT) hW hWsub _
    (memberCount T s hT) _ _ _ _ (nonemptyList_reverse_hnil T hT bd)
    (nonemptyList_reverse_filter T hT) le_rfl le_rfl U hUW
    (le_chainOpens_last (exhaustion M) hU (memberCount T s hT))

/-- **Compatibility of Step 2.1 under restriction** ([Wlo09, Theorem 2.0.3 (4)]): for `U ≤ V` the
value on `U` is the value on `V` restricted to `U` with the empty blow-ups deleted; the independence
of the chain (`step21FamOn_chain_indep`) for the chain of `V`, read on `U`. -/
theorem step21FamOn_compat (bd : BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    {V : Opens M} (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    step21FamOn T s bd hT U hU =
      ((step21FamOn T s bd hT V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  have h := step21FamOn_chain_indep bd T hT U hU
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hV) (memberCount T s hT))
    (isCompact_closure_chainOpens (exhaustion M) _ _)
    (fun _ hk => closure_chainOpens_succ_subset (exhaustion M) _ _ hk)
    (hUV.trans (le_chainOpens_last (exhaustion M) hV (memberCount T s hT)))
  rw [← h]
  unfold step21FamOn step21FamChain
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)

section Along

variable {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (bd : BDanFamData ψ₀ s)
  (hT : AnalyticTriple.BOClass s T) (g : AnalyticMap N M)
  (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
  (hT' : AnalyticTriple.BOClass s (T.pullback g hg))

/-- **Along `g`, the chain over `N` for the pulled-back triple is, up to empty blow-ups, the
pull-back of the chain over `M`**, link by link (`link_rel`), for chains of opens with
`g(W'_k) ⊆ W_k` processing the same members (the functoriality of Step 2.1,
[Kol07, 104, Step 2.3]). -/
theorem step21FamAux_rel_along (W : ℕ → Opens M) (r : ℕ)
    (hW : ∀ k, IsCompact (closure (W k : Set M)))
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (W' : ℕ → Opens N)
    (hW' : ∀ k, IsCompact (closure (W' k : Set N)))
    (hWsub' : ∀ k, k < r → closure (W' (k + 1) : Set N) ⊆ W' k)
    (hWW' : ∀ k, ⇑g '' (W' k : Set N) ⊆ W k) :
    ∀ (l : List T.F.ι) (hl : l.length ≤ r),
      (step21FamAux (T.pullback g hg) s bd hT' W' r hW' hWsub' l hl).L.eraseEmpty =
        ((step21FamAux T s bd hT W r hW hWsub l hl).L.pullback
          (AnalyticMap.restrictMap g (W' l.length) (W l.length) (hWW' _))
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg _ _ (hWW' _))).eraseEmpty
  | [], _ => by
    change (AnalyticManifold.BlowUpSequence.nil _).eraseEmpty =
        ((AnalyticManifold.BlowUpSequence.nil _).pullback _ _).eraseEmpty
    simp
  | j :: l, hl =>
    ChainState.link_rel T s bd hT g hg hT' (hWW' l.length) _ _
      (step21FamAux_rel_along W r hW hWsub W' hW' hWsub' hWW' l (Nat.le_of_succ_le hl)) j (hW _)
      (hWsub l.length hl) (hW' _) (hWsub' l.length hl) (hWW' (l.length + 1))

end Along

/-- **Step 2.1 commutes with local analytic isomorphisms** on the opens (the functoriality of
[Kol07, 104, Step 2.3] in the form of `AnalyticFamilyFunctor.CommutesWithLocalIsos`): the chain
over `N` for the filtered member list is the chain over the full list along opens carried into the
chain of `g(U')` (`step21FamAux_filter_rel`), which is the pull-back of that chain
(`step21FamAux_rel_along`); restricting to `U'` and deleting the empty blow-ups gives the
statement. -/
theorem step21FamOn_commutesWithLocalIsos (bd : BDanFamData ψ₀ s) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass s T)
    (hnil : ∀ {M' : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ M')
      (hT' : AnalyticTriple.BOClass s T') (j : T'.F.ι),
      T'.F.hyp j = ∅ → bd.fam T' hT' j = CompatibleFamily.nil T')
    {N : AnalyticManifold.{u} 𝕜 E} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g)
    (hT' : AnalyticTriple.BOClass s (T.pullback g hg)) (U' : Opens N)
    (hU' : IsCompact (closure (U' : Set N))) :
    step21FamOn (T.pullback g hg) s bd hT' U' hU' =
      ((step21FamOn T s bd hT (AnalyticMap.imageOpens g hg U')
          (AnalyticMap.isCompact_closure_image g hU')).pullback
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
          Set.Subset.rfl)).eraseEmpty := by
  -- the canonical chain of `g(U')` on `M` and its trace on `N`, intersected with the canonical
  -- chain of `U'`
  have hW₀ : IsCompact (closure ((AnalyticMap.imageOpens g hg U' : Opens M) : Set M)) :=
    AnalyticMap.isCompact_closure_image g hU'
  let W : ℕ → Opens M := chainOpens (exhaustion M)
    (exhaustionIdx (exhaustion M) hW₀) (memberCount T s hT)
  let W' : ℕ → Opens N := fun k => preimageOpens g g.contMDiff (W k) ⊓
    chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU') (memberCount T s hT) k
  have hW' : ∀ k, IsCompact (closure (W' k : Set N)) := fun k =>
    (isCompact_closure_chainOpens (exhaustion N) _ _ k).of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.2)
  have hWsub' : ∀ k, k < memberCount T s hT → closure (W' (k + 1) : Set N) ⊆ W' k := by
    intro k hk x hx
    have hx' := closure_inter_subset_inter_closure _ _ hx
    exact ⟨(g.contMDiff.continuous.closure_preimage_subset _).trans
      (Set.preimage_mono (closure_chainOpens_succ_subset (exhaustion M) _ _ hk)) hx'.1,
      closure_chainOpens_succ_subset (exhaustion N) _ _ hk hx'.2⟩
  have hWW' : ∀ k, ⇑g '' (W' k : Set N) ⊆ W k := by
    rintro k _ ⟨x, hx, rfl⟩
    exact hx.1
  have hU'W' : U' ≤ W' (memberCount T s hT) := fun x hx =>
    ⟨le_chainOpens_last (exhaustion M) hW₀ (memberCount T s hT) ⟨x, hx, rfl⟩,
      le_chainOpens_last (exhaustion N) hU' (memberCount T s hT) hx⟩
  -- the filtered member list
  have hfilter : (T.F.nonemptyList hT.2.2).reverse.filter
      (fun j => decide ((T.pullback g hg).F.hyp j ≠ ∅)) =
      ((T.pullback g hg).F.nonemptyList hT'.2.2).reverse :=
    List.filter_reverse.trans (congrArg List.reverse
      (HypersurfaceFamily.nonemptyList_comap_eq_filter T.F ⇑g hT.2.2 hT'.2.2).symm)
  -- (1) the chain of `N` over its canonical opens = the chain over `W'` with the full list, on `U'`
  have h₁ := ChainState.step21FamAux_filter_rel (T.pullback g hg) s bd hT' W' (memberCount T s hT)
    hW' hWsub'
    (chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU')
      (memberCount (T.pullback g hg) s hT'))
    (memberCount (T.pullback g hg) s hT') (isCompact_closure_chainOpens (exhaustion N) _ _)
    (fun _ hk => closure_chainOpens_succ_subset (exhaustion N) _ _ hk)
    (T.F.nonemptyList hT.2.2).reverse _ (fun _ _ _ => hnil) hfilter le_rfl le_rfl U' hU'W'
    (le_chainOpens_last (exhaustion N) hU' (memberCount (T.pullback g hg) s hT'))
  -- (2) the chain over `W'` is the pull-back of the canonical chain of `g(U')`
  have h₂ := step21FamAux_rel_along T bd hT g hg hT' W (memberCount T s hT)
    (isCompact_closure_chainOpens (exhaustion M) _ _)
    (fun _ hk => closure_chainOpens_succ_subset (exhaustion M) _ _ hk) W' hW' hWsub' hWW'
    (T.F.nonemptyList hT.2.2).reverse le_rfl
  -- assemble (as a chain of equalities: the goal reads the chains through their definitions)
  have hc₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((AnalyticMap.restrictMap g (W' (memberCount T s hT)) (W (memberCount T s hT))
        (hWW' _)).comp (N.restrictLE hU'W')) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg _ _ (hWW' _))
      (isLocalDiffeomorph_restrictLE hU'W')
  have hc₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((M.restrictLE (le_chainOpens_last (exhaustion M) hW₀ (memberCount T s hT))).comp
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
        Set.Subset.rfl)
  have hmaps : (AnalyticMap.restrictMap g (W' (memberCount T s hT)) (W (memberCount T s hT))
      (hWW' _)).comp (N.restrictLE hU'W') =
      (M.restrictLE (le_chainOpens_last (exhaustion M) hW₀ (memberCount T s hT))).comp
        (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl) :=
    ContMDiffMap.ext fun _ => Subtype.ext rfl
  exact h₁.symm.trans ((AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
      (isLocalDiffeomorph_restrictLE hU'W')).symm.trans
    ((congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ (N.restrict (W' (memberCount T s hT))) =>
        (X.pullback (N.restrictLE hU'W')
          (isLocalDiffeomorph_restrictLE hU'W')).eraseEmpty) h₂).trans
      ((AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
          (isLocalDiffeomorph_restrictLE hU'W')).trans
        ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
            (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).trans
          ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
              (AnalyticManifold.BlowUpSequence.pullback_congr _ hmaps hc₁ hc₂)).trans
            ((congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
                (AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _)).symm.trans
              (AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _
                (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
                  Set.Subset.rfl)).symm))))))

end Hironaka.Manifold
