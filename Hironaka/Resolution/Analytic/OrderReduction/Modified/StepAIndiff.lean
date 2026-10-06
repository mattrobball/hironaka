/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepAComm
public import Hironaka.Resolution.Analytic.OrderReduction.BDIndiff
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.NonmonomialIndiff
import Hironaka.Resolution.Analytic.OrderReduction.Modified.StepATransport
import Hironaka.Resolution.Analytic.OrderReduction.Step21Indiff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds on the nonmonomial part are indifferent to empty boundary members

The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the value of
the rounds on the nonmonomial part: when
the nonempty members of `E` are the members of `F'` along an order embedding `e : F'.ι ↪o E.ι`
(matched members, the others empty), the value on every relatively compact open for `(M, 𝓘, E)` is
its value for `(M, 𝓘, F')` (`stepAFamOn_indiff`, packaged as
`stepAFunctor_indifferentToEmptyMembers`, the shape of
`AnalyticFamilyFunctor.IndifferentToEmptyMembers`).

The proof follows the descent link by link: the two descents run along the same canonical chain
from the same bound, since the round order does not see empty members (`roundOrderOn_withBoundary`,
from `nonmonomialPart_eq_of_isEmptyExtension`), and two states with the same list link to the same
list (`BState.descentLink_L_indiff`): the restricted triples over the open are again related by a
boundary change along `e`, and the value of the round is the value of the functor
`nonmonomialFunctor (bo d)` at the induced triples, which is indifferent to empty members along the
index correspondence of the induced boundaries
(`AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_induced_indiff`, stated for an arbitrary
family functor). The final values are read with the bound as an explicit parameter (`valueAt`,
`StepACompat.lean`), so that the equal bounds are identified by a substitution (`valueAt_congr`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### A functor indifferent to empty members is indifferent at the induced triples -/

section Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}

omit [FiniteDimensional 𝕜 E] in
/-- Indifference to empty boundary members along a list: a family functor indifferent to empty
members takes the same value at the induced triples of `T` and of `T` with its boundary replaced by
`F'` along the same list `L`, the induced boundaries being matched along the index correspondence
`corrIdx e` (`hyp_corrIdxAux_of_forall`, `hyp_eq_empty_of_notMem_range_corrIdx`); the counterpart,
for boundary members, of [Kol07, 32]. -/
theorem AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_induced_indiff
    {B : AnalyticFamilyFunctor ψ₀ Dom} (hB : B.IndifferentToEmptyMembers)
    {X : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ X) (F' : HypersurfaceFamily X)
    (hsnc' : F'.IsSnc ψ₀) (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
    (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅) (s : ℕ) (L : AnalyticManifold.BlowUpSequence ψ₀ X)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL' : L.toSuccession.IsOfOrderGe (BDan.withBoundary T F' hsnc').I s
      (BDan.withBoundary T F' hsnc').F.idealSheaf)
    (hD : Dom (T.induced s L hL)) (hD' : Dom ((BDan.withBoundary T F' hsnc').induced s L hL'))
    (O : Opens (L.stage (Fin.last _)))
    (hO : IsCompact (closure (O : Set (L.stage (Fin.last _))))) :
    (B.fam (T.induced s L hL) hD).seqOn O hO =
      (B.fam ((BDan.withBoundary T F' hsnc').induced s L hL') hD').seqOn O hO := by
  have heq : (BDan.withBoundary T F' hsnc').induced s L hL' =
      ⟨(T.induced s L hL).I, (T.induced s L hL).isNonzeroEverywhere,
        ((BDan.withBoundary T F' hsnc').induced s L hL').F,
        ((BDan.withBoundary T F' hsnc').induced s L hL').isSnc⟩ :=
    AnalyticTriple.ext' rfl rfl
  have hD'' : Dom (⟨(T.induced s L hL).I, (T.induced s L hL).isNonzeroEverywhere,
      ((BDan.withBoundary T F' hsnc').induced s L hL').F,
      ((BDan.withBoundary T F' hsnc').induced s L hL').isSnc⟩ :
        AnalyticTriple ψ₀ (L.stage (Fin.last _))) := by
    rw [← heq]
    exact hD'
  refine (hB (T.induced s L hL) ((BDan.withBoundary T F' hsnc').induced s L hL').F
    ((BDan.withBoundary T F' hsnc').induced s L hL').isSnc (L.toSuccession.corrIdx e (Fin.last _))
    (fun k => (L.toSuccession.hyp_corrIdxAux_of_forall ⇑e (fun j => (he j).symm) (Fin.last _)
      k).symm)
    (fun b hb => L.toSuccession.hyp_eq_empty_of_notMem_range_corrIdx e he' (Fin.last _) b hb)
    hD hD'' O hO).trans ?_
  exact B.fam_seqOn_congr_triple heq.symm hD'' hD' O hO

end Generic

namespace BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
  (hT : AnalyticTriple.BMOClass m T) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t)
  (F' : HypersurfaceFamily M) (hsnc' : F'.IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (e : F'.ι ↪o T.F.ι) (he : ∀ i, T.F.hyp (e i) = F'.hyp i)
  (he' : ∀ b, b ∉ Set.range e → T.F.hyp b = ∅)
  (hT' : AnalyticTriple.BMOClass m (BDan.withBoundary T F' hsnc'))

/-! ### The bound does not see empty members -/

include he he' in
/-- The nonmonomial part of the boundary change is the nonmonomial part
(`nonmonomialPart_eq_of_isEmptyExtension`), read on the triples. -/
theorem nonmonomialTriple_withBoundary_I :
    (nonmonomialTriple (BDan.withBoundary T F' hsnc')).I = (nonmonomialTriple T).I := by
  rw [nonmonomialTriple_I, nonmonomialTriple_I]
  dsimp only [BDan.withBoundary]
  exact (nonmonomialPart_eq_of_isEmptyExtension (⟨he, he'⟩ : HypersurfaceFamily.IsEmptyExtension e)
    hsnc' T.isSnc T.I).symm

include he he' in
/-- The round order (`roundOrderOn`, the maximum of `ord N(𝓘)` on the closure of an open) does not
see empty members. -/
theorem roundOrderOn_withBoundary (O : Opens M) :
    roundOrderOn (BDan.withBoundary T F' hsnc') O = roundOrderOn T O := by
  unfold roundOrderOn
  dsimp only [BDan.withBoundary]
  rw [nonmonomialPart_eq_of_isEmptyExtension (⟨he, he'⟩ : HypersurfaceFamily.IsEmptyExtension e)
    hsnc' T.isSnc T.I]

/-! ### One link is indifferent to empty members -/

include he he' in
/-- **One link of the descent is indifferent to empty members**: two states with the same list, for
`T` and for the boundary change, link to the same list. The restricted triples over the open are
again related by a boundary change along `e` (`AnalyticTriple.ext'`), and the value of the round is
the value of the functor at the induced triples (`seqOn_induced_indiff` with
`nonmonomialFunctor_indifferentToEmptyMembers`). -/
theorem BState.descentLink_L_indiff {W : Opens M} {d : ℕ} (st : BState T m W d)
    (st' : BState (BDan.withBoundary T F' hsnc') m W d) (hL : st.L = st'.L) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) (hmd : m ≤ d) :
    (st.descentLink hcomp bo hid hV hVW hT hm hmd).L =
      (st'.descentLink hcomp bo hid hV hVW hT' hm hmd).L := by
  obtain ⟨⟨L, hge⟩, bound⟩ := st
  obtain ⟨⟨L', hge'⟩, bound'⟩ := st'
  change L = L' at hL
  subst hL
  rw [BState.descentLink_L, BState.descentLink_L]
  refine congrArg (L.shrinkAppend _ _) ?_
  rw [BState.roundValue_eq_nonmonomialFunctor, BState.roundValue_eq_nonmonomialFunctor]
  -- the restricted triples over `W`: the same boundary change along `e`
  have hTWeq : BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).F
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).isSnc =
      (BDan.withBoundary T F' hsnc').pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) :=
    AnalyticTriple.ext' rfl rfl
  have hge'' : L.toSuccession.IsOfOrderGe
      (BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).I m
      (BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).F.idealSheaf := by
    rw [hTWeq]
    exact hge'
  have hDw : NonmonomialClass d
      ((BDan.withBoundary (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).F
        ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
          (isLocalDiffeomorph_inclusion M W)).isSnc).induced m L hge'') := by
    rw [AnalyticTriple.induced_congr hTWeq m L hge'' hge']
    exact BState.nonmonomialClass hT' ⟨⟨L, hge'⟩, bound'⟩ (hm.trans hmd)
  have heW : ∀ k, (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.hyp (e k) =
      ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
        (isLocalDiffeomorph_inclusion M W)).F.hyp k :=
    fun k => congrArg (fun S => ⇑(M.inclusion W) ⁻¹' S) (he k)
  have heW' : ∀ b, b ∉ Set.range e →
      (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F.hyp b = ∅ :=
    fun b hb => (congrArg (fun S => ⇑(M.inclusion W) ⁻¹' S) (he' b hb)).trans Set.preimage_empty
  exact (AnalyticFamilyFunctor.IndifferentToEmptyMembers.seqOn_induced_indiff
    (nonmonomialFunctor_indifferentToEmptyMembers (bo d))
    (T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W))
    ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)).F
    ((BDan.withBoundary T F' hsnc').pullback (M.inclusion W)
      (isLocalDiffeomorph_inclusion M W)).isSnc e heW heW' m L hge hge'' _ hDw _ _).trans
    ((nonmonomialFunctor (bo d)).fam_seqOn_congr_triple
      (AnalyticTriple.induced_congr hTWeq m L hge'' hge') hDw _ _ _)

/-! ### The descent along the same chain from the same bound -/

section Descent

variable (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
  (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
  (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))
  (hD' : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple (BDan.withBoundary T F' hsnc')).I.ord x ≤ (D : ℕ∞))

include he he' hD hD' in
/-- **The two descents along the same chain from the same bound have the same lists**, link by link
(`descentLink_L_indiff`; both initial states have the empty list). -/
theorem descentStateAux_L_indiff : ∀ j (hj : j ≤ r) (hjt : j ≤ D + 1 - t),
    (descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD j hj hjt).L =
      (descentStateAux (BDan.withBoundary T F' hsnc') m hT' bo hcomp hid t hm hmt W hW r hWsub D
        hD' j hj hjt).L
  | 0, _, _ =>
    (BState.initialOf_L T m hcomp D hD).trans
      (BState.initialOf_L (BDan.withBoundary T F' hsnc') m hcomp D hD').symm
  | j + 1, hj, hjt =>
    BState.descentLink_L_indiff T m hT bo hcomp hid hm F' hsnc' e he he' hT' _ _
      (descentStateAux_L_indiff j (Nat.le_of_succ_le hj) (Nat.le_of_succ_le hjt)) (hW (j + 1))
      (hWsub j hj) (by omega)

end Descent

/-! ### The value with the bound as a parameter -/

section Value

variable (W : ℕ → Opens M) (hW : ∀ k, IsCompact (closure (W k : Set M)))

include he he' in
/-- The value along the same chain from the same bound is indifferent to empty members
(`descentStateAux_L_indiff`). -/
theorem valueAt_indiff (D : ℕ) (hWsub : ∀ k, k < D + 1 - t → closure (W (k + 1) : Set M) ⊆ W k)
    (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞))
    (hD' : ∀ x ∈ (W 0 : Set M),
      (nonmonomialTriple (BDan.withBoundary T F' hsnc')).I.ord x ≤ (D : ℕ∞))
    (k : ℕ) (hk : k ≤ D + 1 - t) {U' : Opens M} (hU'k : U' ≤ W k) :
    valueAt T m hT bo hcomp hid t hm hmt W hW D hWsub hD k hk hU'k =
      valueAt (BDan.withBoundary T F' hsnc') m hT' bo hcomp hid t hm hmt W hW D hWsub hD' k hk
        hU'k :=
  congrArg (fun L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (M.restrict (W k)) =>
    (L.pullback (M.restrictLE hU'k) (isLocalDiffeomorph_restrictLE _)).eraseEmpty)
    (descentStateAux_L_indiff T m hT bo hcomp hid t hm hmt F' hsnc' e he he' hT' W hW (D + 1 - t)
      hWsub D hD hD' k hk hk)

end Value

/-! ### Indifference of the value of the rounds -/

include he he' in
/-- **The value of the rounds is indifferent to empty boundary members** (the counterpart, for
boundary members, of [Kol07, 32]): the canonical
chain does not see the boundary, the canonical bound does not see empty members
(`roundOrderOn_withBoundary`), and the two descents along that chain from that bound have the same
lists (`valueAt_indiff`). -/
theorem stepAFamOn_indiff (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    stepAFamOn T m hT bo hcomp hid t hm hmt U hU =
      stepAFamOn (BDan.withBoundary T F' hsnc') m hT' bo hcomp hid t hm hmt U hU := by
  have eD : stepABound T U hU = stepABound (BDan.withBoundary T F' hsnc') U hU :=
    (roundOrderOn_withBoundary T F' hsnc' e he he' (stepAOuter U hU)).symm
  have ek : stepALinks T t U hU = stepALinks (BDan.withBoundary T F' hsnc') t U hU := by
    unfold stepALinks
    rw [eD]
  have hD'' : ∀ x ∈ (stepAChainOpens U hU 0 : Set M),
      (nonmonomialTriple (BDan.withBoundary T F' hsnc')).I.ord x ≤
        (stepABound (BDan.withBoundary T F' hsnc') U hU : ℕ∞) :=
    shrinkChain_zero_bound (BDan.withBoundary T F' hsnc') (closure (U : Set M)) hU
      (stepAOuter U hU) (isCompact_closure_stepAOuter U hU) (closure_subset_stepAOuter U hU)
  have hDT' : ∀ x ∈ (stepAChainOpens U hU 0 : Set M),
      (nonmonomialTriple T).I.ord x ≤ (stepABound (BDan.withBoundary T F' hsnc') U hU : ℕ∞) := by
    intro x hx
    rw [← nonmonomialTriple_withBoundary_I T F' hsnc' e he he']
    exact hD'' x hx
  rw [stepAFamOn_eq_stepAValueAt, stepAFamOn_eq_stepAValueAt]
  unfold stepAValueAt
  refine (valueAt_congr T m hT bo hcomp hid t hm hmt (stepAChainOpens U hU) _ eD ek _ _ le_rfl
    (fun k _ => closure_shrinkChain_succ_subset hU (closure_subset_stepAOuter U hU) k) hDT'
    le_rfl (le_stepAChainOpens U hU _) (le_stepAChainOpens U hU _)).trans ?_
  exact valueAt_indiff T m hT bo hcomp hid t hm hmt F' hsnc' e he he' hT' (stepAChainOpens U hU) _
    (stepABound (BDan.withBoundary T F' hsnc') U hU) _ hDT' hD'' _ le_rfl _

/-- The family functor of the rounds is indifferent to empty boundary members (the counterpart, for
boundary members, of [Kol07, 32]). -/
theorem stepAFunctor_indifferentToEmptyMembers :
    (stepAFunctor m bo hcomp hid t hm hmt).IndifferentToEmptyMembers := by
  intro M T F' hsnc' e he he' hT hT' U hU
  exact stepAFamOn_indiff T m hT bo hcomp hid t hm hmt F' hsnc' e he he' hT' U hU

end BMOmod

end Hironaka.Manifold

end
