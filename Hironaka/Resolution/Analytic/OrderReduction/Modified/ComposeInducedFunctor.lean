/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ComposeInduced
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAIndiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The composite of two family functors along induced triples: the functor

`ComposeInduced.lean` built the **link** of the composite of `F : AnalyticFamilyFunctor ψ₀ Dom₁`
with `G : AnalyticFamilyFunctor ψ₀ Dom₂` at the induced triples (`alongList` over a pair of opens
`closure V ⊆ W`, its order clause, its relation `alongList_rel` along a local analytic
isomorphism). This module makes the composite a **family functor** on `Dom₁`, following the
assembly of the second step of the order reduction (`Step2Assembly.lean`, `Step2AssemblyComm.lean`)
with its link replaced by the generic one:

* `composeAlong F G s … T hT W V hW hV hVW U hUV : CenterList ψ₀ (M.restrict U)`, the composite over
  `(W, V)` restricted to `U ≤ V`, with the empty blow-ups deleted; `composeAlong_eq_join` and
  `composeAlong_rel`, **the independence from the chain**: two pairs of opens above `U` give the
  same value (`alongList_rel` at the identity, against the common refinement `(W ⊓ W′, V ⊓ V′)`);
* `composeOn F G s … T hT U hU`, the value on `U` along the **canonical** pair
  `(chainOpens (exhaustion M) n₀ 1 0, chainOpens (exhaustion M) n₀ 1 1)` with
  `n₀ = exhaustionIdx _ hU` (the exhaustion index of `hfStep2FamOn`); `composeOn_compat` (the second
  condition of [Kol07, 34.1], [Wlo09, Theorem 2.0.3 (4)]) by the independence from the chain for the
  canonical pair of the larger open read on the smaller;
* `composeInduced F G s … : AnalyticFamilyFunctor ψ₀ Dom₁`, the functor, with
  `composeInduced_isOfOrderGe` (the order clause at the mark `s`, from `alongList_isOfOrderGe`),
  `composeInduced_commutesWithLocalIsos` (`alongList_rel` along `g` against the trace of the
  canonical pair of `g(U′)` intersected with the canonical pair of `U′`) and
  `composeInduced_indifferentToEmptyMembers` (the indifference of `F` for the first list, that of
  `G` through `IndifferentToEmptyMembers.seqOn_induced_indiff` for the appended value:
  `alongList_indiff`).

The hypotheses are the properties of the two functors and the class hypotheses of
`ComposeInduced.lean`: `hF`, `hFG`, `hFc`, `hG`, `hG'`, `hDom`, `hDomE`, and
`hDom₁ : ClassPullbackClosed Dom₁` (the triple pulled back along the identity, the pivot of the
argument for the independence from the chain, stays in the class of `F`).
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.AnalyticFamilyFunctor

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom₁ Dom₂ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  (F : AnalyticFamilyFunctor ψ₀ Dom₁) (G : AnalyticFamilyFunctor ψ₀ Dom₂) (s : ℕ)
  (hF : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    ((F.fam T hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf)
  (hFG : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))),
    Dom₂ ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).induced s
      ((F.fam T hT).seqOn U hU) (hF T hT U hU)))
  (hFc : F.CommutesWithLocalIsos) (hG : G.CommutesWithLocalIsos)
  (hG' : G.IndifferentToEmptyMembers) (hDom : ClassPullbackClosed (ψ₀ := ψ₀) Dom₂)
  (hDomE : ClassInducedEraseEmptyClosed (ψ₀ := ψ₀) s Dom₂)
  (hDom₁ : ClassPullbackClosed (ψ₀ := ψ₀) Dom₁)

section Along

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T)

/-- **The composite over `(W, V)` read on `U ≤ V`**, with the empty blow-ups deleted. -/
def composeAlong (W V : Opens M) (hW : IsCompact (closure (W : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) (U : Opens M)
    (hUV : U ≤ V) : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  ((alongList F G s hF hFG T hT W hW V hV hVW).pullback (M.restrictLE hUV)
    (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty

omit [FiniteDimensional 𝕜 E] in
include hF hFG hFc hG hG' hDom hDomE hDom₁ in
/-- The composite over `(W, V)` read on `U` is the composite over any smaller pair `(W₀, V₀)` above
`U`, for the triple pulled back along the identity, pulled back to `U` and cleaned: `alongList_rel`
at the identity. -/
theorem composeAlong_eq_join (W V : Opens M) (hW : IsCompact (closure (W : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) (W₀ V₀ : Opens M)
    (hW₀ : IsCompact (closure (W₀ : Set M))) (hV₀ : IsCompact (closure (V₀ : Set M)))
    (hW₀W : W₀ ≤ W) (hV₀V : V₀ ≤ V) (hV₀W₀ : closure (V₀ : Set M) ⊆ W₀) (U : Opens M)
    (hUV₀ : U ≤ V₀) :
    composeAlong F G s hF hFG T hT W V hW hV hVW U (hUV₀.trans hV₀V) =
      ((alongList F G s hF hFG (T.pullback ContMDiffMap.id
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))
          (hDom₁ T ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) hT) W₀
              hW₀ V₀ hV₀
          hV₀W₀).eraseEmpty.pullback (M.restrictLE hUV₀)
        (isLocalDiffeomorph_restrictLE hUV₀)).eraseEmpty := by
  have hWW₀ : ⇑(ContMDiffMap.id : AnalyticMap M M) '' (W₀ : Set M) ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hW₀W hx
  have hVV₀ : ⇑(ContMDiffMap.id : AnalyticMap M M) '' (V₀ : Set M) ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hV₀V hx
  rw [alongList_rel F G s hF hFG hFc hG hG' hDom hDomE T hT ContMDiffMap.id
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M)
    (T.pullback ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M))
    (AnalyticTriple.isPullbackOf_pullback T _ _)
    (hDom₁ T ContMDiffMap.id (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M) hT) hW hW₀
        hWW₀ hV hVW hV₀
    hV₀W₀ hVV₀, AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)

omit [FiniteDimensional 𝕜 E] in
include hF hFG hFc hG hG' hDom hDomE hDom₁ in
/-- **Independence from the chain**: two pairs of opens above `U` give the same composite on `U`,
both being the composite over the common refinement `(W ⊓ W′, V ⊓ V′)` (`composeAlong_eq_join`). -/
theorem composeAlong_rel (W V : Opens M) (hW : IsCompact (closure (W : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) (W' V' : Opens M)
    (hW' : IsCompact (closure (W' : Set M))) (hV' : IsCompact (closure (V' : Set M)))
    (hV'W' : closure (V' : Set M) ⊆ W') (U : Opens M) (hUV : U ≤ V) (hUV' : U ≤ V') :
    composeAlong F G s hF hFG T hT W V hW hV hVW U hUV =
      composeAlong F G s hF hFG T hT W' V' hW' hV' hV'W' U hUV' := by
  have hW₀ : IsCompact (closure ((W ⊓ W' : Opens M) : Set M)) :=
    hW.of_isClosed_subset isClosed_closure (closure_mono fun _ hx => hx.1)
  have hV₀ : IsCompact (closure ((V ⊓ V' : Opens M) : Set M)) :=
    hV.of_isClosed_subset isClosed_closure (closure_mono fun _ hx => hx.1)
  have hV₀W₀ : closure ((V ⊓ V' : Opens M) : Set M) ⊆ (W ⊓ W' : Opens M) := fun _ hx =>
    ⟨hVW (closure_mono (fun _ h => h.1) hx), hV'W' (closure_mono (fun _ h => h.2) hx)⟩
  exact (composeAlong_eq_join F G s hF hFG hFc hG hG' hDom hDomE hDom₁ T hT W V hW hV hVW
      (W ⊓ W') (V ⊓ V') hW₀ hV₀ inf_le_left inf_le_left hV₀W₀ U (le_inf hUV hUV')).trans
    (composeAlong_eq_join F G s hF hFG hFc hG hG' hDom hDomE hDom₁ T hT W' V' hW' hV' hV'W'
      (W ⊓ W') (V ⊓ V') hW₀ hV₀ inf_le_right inf_le_right hV₀W₀ U (le_inf hUV hUV')).symm

/-- **The composite on `U`**, along the canonical pair of opens above `U`,
`chainOpens (exhaustion M) n₀ 1 0 ⊇ closure (chainOpens (exhaustion M) n₀ 1 1) ⊇ … ⊇ U` with
`n₀ = exhaustionIdx (exhaustion M) hU` (the exhaustion index of `hfStep2FamOn`). -/
def composeOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    AnalyticManifold.BlowUpSequence ψ₀ (M.restrict U) :=
  composeAlong F G s hF hFG T hT (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1)
    (isCompact_closure_chainOpens _ _ _ _) (isCompact_closure_chainOpens _ _ _ _)
    (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one) U (le_chainOpens_last _ hU 1)

/-- The value of the composite has no empty centres [Kol07, 32]. -/
theorem composeOn_noEmptyCenters (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (composeOn F G s hF hFG T hT U hU).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

include hF hFG hFc hG hG' hDom hDomE hDom₁ in
/-- **The compatibility of the composite under restriction** (the second condition of
[Kol07, 34.1]; [Wlo09, Theorem 2.0.3 (4)]): for `U ≤ V` the value on `U` is the value on `V`
restricted to `U` with its empty blow-ups deleted (the independence from the chain, for the
canonical pair of `V` read on `U`). -/
theorem composeOn_compat (U V : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    composeOn F G s hF hFG T hT U hU =
      ((composeOn F G s hF hFG T hT V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  unfold composeOn
  rw [composeAlong_rel F G s hF hFG hFc hG hG' hDom hDomE hDom₁ T hT
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1) _ _ _
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hV) 1 0)
    (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hV) 1 1)
    (isCompact_closure_chainOpens _ _ _ _) (isCompact_closure_chainOpens _ _ _ _)
    (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one) U _
    (hUV.trans (le_chainOpens_last _ hV 1))]
  unfold composeAlong
  rw [AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)

include hF hFG in
/-- The order clause of the value of the composite at the mark `s`, from those of `F` (`hF`) and `G`
(`hGo`): `alongList_isOfOrderGe` pulled back to `U` (`isOfOrderGe_pullback`,
`pullback_inclusion_restrictLE`) and cleaned (`isOfOrderGe_eraseEmpty`). -/
theorem composeOn_isOfOrderGe
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I s
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (composeOn F G s hF hFG T hT U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf := by
  have h := AnalyticTriple.isOfOrderGe_pullback
    (T.pullback (M.inclusion (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1))
      (isLocalDiffeomorph_inclusion M _)) s _
    (alongList_isOfOrderGe F G s hF hFG T hT
      (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
      (isCompact_closure_chainOpens _ _ _ _)
      (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1)
      (isCompact_closure_chainOpens _ _ _ _)
      (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one) hGo)
    (M.restrictLE (le_chainOpens_last (exhaustion M) hU 1)) (isLocalDiffeomorph_restrictLE _)
  rw [AnalyticTriple.pullback_inclusion_restrictLE T (le_chainOpens_last (exhaustion M) hU 1)] at h
  exact AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty _ _ s
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc h

omit [FiniteDimensional 𝕜 E] in
include hF hFG hG' in
/-- The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the
composite over `(W, V)`: **deleting empty boundary members of `T` does not change the composite**.
The indifference of `F` identifies the first lists, that of `G`
(`IndifferentToEmptyMembers.seqOn_induced_indiff`) the appended values at the induced triples of the
common first list (the restricted triple of `T` with its boundary replaced is the restricted triple
with the restricted replacement, definitionally). -/
theorem alongList_indiff (hFi : F.IndifferentToEmptyMembers) (F' : HypersurfaceFamily M)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
    (hT' : Dom₁ (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M)) (W V : Opens M)
    (hW : IsCompact (closure (W : Set M))) (hV : IsCompact (closure (V : Set M)))
    (hVW : closure (V : Set M) ⊆ W) :
    alongList F G s hF hFG T hT W hW V hV hVW =
      alongList F G s hF hFG (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M) hT'
        W hW V hV hVW := by
  set T' : AnalyticTriple ψ₀ M := ⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ with hT'def
  set TW := T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) with hTWdef
  set TW' := T'.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) with hTW'def
  set ρ := M.restrictLE (ChainState.le_of_closure_subset hVW) with hρdef
  have hL : (F.fam T' hT').seqOn W hW = (F.fam T hT).seqOn W hW :=
    (hFi T F' hsnc' e he he' hT hT' W hW).symm
  have key : ∀ (L' : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict W))
      (hL' : L'.toSuccession.IsOfOrderGe TW'.I s TW'.F.idealSheaf)
      (hD' : Dom₂ (TW'.induced s L' hL')), L' = (F.fam T hT).seqOn W hW →
      L'.shrinkAppend ρ (isLocalDiffeomorph_restrictLE _)
        ((G.fam (TW'.induced s L' hL') hD').seqOn (L'.liftRange ρ (isLocalDiffeomorph_restrictLE _))
          (L'.isCompact_closure_liftRange ρ (isLocalDiffeomorph_restrictLE _)
            (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) hV hVW))) =
      alongList F G s hF hFG T hT W hW V hV hVW := by
    intro L' hL' hD' hLL'
    subst hLL'
    exact congrArg (AnalyticManifold.BlowUpSequence.shrinkAppend _ ρ
        (isLocalDiffeomorph_restrictLE _))
      (hG'.seqOn_induced_indiff TW (F'.comap ⇑(M.inclusion W))
        (HypersurfaceFamily.isSnc_comap hsnc' _ (isLocalDiffeomorph_inclusion M W)) e
        (fun i => by
          change ⇑(M.inclusion W) ⁻¹' T.F.hyp (e i) = ⇑(M.inclusion W) ⁻¹' F'.hyp i
          rw [he i])
        (fun b hb => by
          change ⇑(M.inclusion W) ⁻¹' T.F.hyp b = ∅
          rw [he' b hb, Set.preimage_empty])
        s _ (hF T hT W hW) hL' (hFG T hT W hW) hD' _ _).symm
  exact (key ((F.fam T' hT').seqOn W hW) (hF T' hT' W hW) (hFG T' hT' W hW) hL).symm

end Along

/-! ### The functor and its clauses -/

/-- **The composite family functor** on `Dom₁`: `composeOn` on every relatively compact open,
without empty centres, compatible under restriction (`composeOn_compat`). -/
def composeInduced : AnalyticFamilyFunctor ψ₀ Dom₁ where
  fam T hT :=
    ⟨fun U hU => composeOn F G s hF hFG T hT U hU,
      fun U hU => composeOn_noEmptyCenters F G s hF hFG T hT U hU,
      fun U V hU hV hUV =>
        composeOn_compat F G s hF hFG hFc hG hG' hDom hDomE hDom₁ T hT U V hU hV hUV⟩

theorem composeInduced_fam_seqOn {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : Dom₁ T) (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((composeInduced F G s hF hFG hFc hG hG' hDom hDomE hDom₁).fam T hT).seqOn U hU =
      composeOn F G s hF hFG T hT U hU := rfl

/-- The order clause of the composite functor at the mark `s` (`composeOn_isOfOrderGe`). -/
theorem composeInduced_isOfOrderGe
    (hGo : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I s
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
    {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (((composeInduced F G s hF hFG hFc hG hG' hDom hDomE hDom₁).fam T
        hT).seqOn U hU).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I s
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.idealSheaf :=
  composeOn_isOfOrderGe F G s hF hFG T hT hGo U hU

/-- [Kol07, 34.1] for the composite functor: **it commutes with local analytic isomorphisms**; the
value on `U′` for the pulled-back triple is the value on `g(U′)` pulled back along `g|_{U′}` and
cleaned. The independence from the chain on the source manifold moves the canonical pair of `U′`
to the trace `(g⁻¹(W) ⊓ W₁, g⁻¹(V) ⊓ V₁)` of the canonical pair `(W, V)` of `g(U′)`;
`alongList_rel` along `g` relates the composites over the two pairs; the pull-backs are composed
(`pullback_comp`) and compared (`pullback_congr`). -/
theorem composeInduced_commutesWithLocalIsos :
    (composeInduced F G s hF hFG hFc hG hG' hDom hDomE hDom₁).CommutesWithLocalIsos := by
  intro M N T T' g hg hT'g hT hT' U' hU'
  change composeOn F G s hF hFG T' hT' U' hU' =
    ((composeOn F G s hF hFG T hT (AnalyticMap.imageOpens g hg U')
        (AnalyticMap.isCompact_closure_image g hU')).pullback
      (AnalyticMap.restrictMap g U' (AnalyticMap.imageOpens g hg U') Set.Subset.rfl)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg U' (AnalyticMap.imageOpens g hg U')
        Set.Subset.rfl)).eraseEmpty
  have hU₀ : IsCompact (closure ((AnalyticMap.imageOpens g hg U' : Opens M) : Set M)) :=
    AnalyticMap.isCompact_closure_image g hU'
  -- the canonical pair of `g(U')` on `M`, its trace on `N` intersected with the canonical pair of
  -- `U'`
  set W := chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU₀) 1 0 with hWdef
  set V := chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU₀) 1 1 with hVdef
  set W'' : Opens N := preimageOpens g g.contMDiff W ⊓
    chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU') 1 0 with hW''def
  set V'' : Opens N := preimageOpens g g.contMDiff V ⊓
    chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU') 1 1 with hV''def
  have hW'' : IsCompact (closure (W'' : Set N)) :=
    (isCompact_closure_chainOpens (exhaustion N) _ _ _).of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.2)
  have hV'' : IsCompact (closure (V'' : Set N)) :=
    (isCompact_closure_chainOpens (exhaustion N) _ _ _).of_isClosed_subset isClosed_closure
      (closure_mono fun _ hx => hx.2)
  have hV''W'' : closure (V'' : Set N) ⊆ W'' := by
    intro x hx
    have hx' := closure_inter_subset_inter_closure _ _ hx
    exact ⟨(g.contMDiff.continuous.closure_preimage_subset _).trans
      (Set.preimage_mono (closure_chainOpens_succ_subset (exhaustion M) _ _ Nat.zero_lt_one))
      hx'.1, closure_chainOpens_succ_subset (exhaustion N) _ _ Nat.zero_lt_one hx'.2⟩
  have hWW'' : ⇑g '' (W'' : Set N) ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hVV'' : ⇑g '' (V'' : Set N) ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hU'V'' : U' ≤ V'' := fun x hx =>
    ⟨le_chainOpens_last (exhaustion M) hU₀ 1 ⟨x, hx, rfl⟩,
      le_chainOpens_last (exhaustion N) hU' 1 hx⟩
  -- chain independence on `N`, then the relation along `g`
  rw [composeOn, composeAlong_rel F G s hF hFG hFc hG hG' hDom hDomE hDom₁ T' hT'
    (chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU') 1 0)
    (chainOpens (exhaustion N) (exhaustionIdx (exhaustion N) hU') 1 1) _ _ _ W'' V'' hW'' hV''
    hV''W'' U' _ hU'V'']
  unfold composeOn composeAlong
  rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty
      (alongList F G s hF hFG T' hT' W'' hW'' V'' hV'' hV''W''),
    alongList_rel F G s hF hFG hFc hG hG' hDom hDomE T hT g hg T' hT'g hT'
      (isCompact_closure_chainOpens _ _ _ _) hW'' hWW'' (isCompact_closure_chainOpens _ _ _ _)
      (closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one) hV'' hV''W'' hVV'',
    AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
        AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
    AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
  exact congrArg AnalyticManifold.BlowUpSequence.eraseEmpty
    (AnalyticManifold.BlowUpSequence.pullback_congr _ (ContMDiffMap.ext fun _ => rfl) _ _)

/-- The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the
composite functor: **indifference to empty boundary members**, from that of `F` (`hFi`) and of `G`
(`hG'`) through `alongList_indiff` (the canonical pair depends on the open only). -/
theorem composeInduced_indifferentToEmptyMembers (hFi : F.IndifferentToEmptyMembers) :
    (composeInduced F G s hF hFG hFc hG hG' hDom hDomE hDom₁).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e he he' hT hT' U hU
  change composeOn F G s hF hFG T hT U hU =
    composeOn F G s hF hFG (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ M) hT' U hU
  unfold composeOn composeAlong
  rw [alongList_indiff F G s hF hFG hG' T hT hFi F' hsnc' e he he' hT']

end Hironaka.Manifold.AnalyticFamilyFunctor

end
