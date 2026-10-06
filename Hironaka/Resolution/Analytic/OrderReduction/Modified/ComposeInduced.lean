/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedValueFunctor
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.OrderReduction.Modified.InducedConcat
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The composite of two family functors along induced triples: the link

The modified marked resolution of [Wlo09, Theorem 7.4.1] runs its phases in succession on every
relatively compact open: the rounds on the nonmonomial part, the monomial phase, and the modified
first step; each is a family functor with the two naturality properties, and each is applied to the
triple **induced** by the value of the previous phase at its last stage (the triple
`(X_j, I_j, E_j)` carried along a composite sequence in [Kol07, 104, Step 2.1]). This module is the
generic **link** of such a composite, for two arbitrary family functors
`F : AnalyticFamilyFunctor ψ₀ Dom₁` and `G : AnalyticFamilyFunctor ψ₀ Dom₂` whose classes are
related by a transport hypothesis (`hFG`: the induced triple of a value of `F` lies in `Dom₂`). It
is the link of the second step of the order reduction (`ChainTransport.lean`: `linkValue`,
`link_rel`) with the family of one boundary member replaced by the functor `G`, whose transport
lemmas are those of `InducedValueFunctor.lean`:

* `alongList F G s hF hFG T hT W hW V hV hVW : CenterList ψ₀ (M.restrict V)`: the value of `F` on
  the outer open `W`, restricted to `V ⊆ W` (`closure V ⊆ W`), followed by the value of `G` at the
  induced triple, read on the lifted range of `V` (`shrinkAppend`); `alongList_isOfOrderGe` is the
  order clause at the mark `s`, from those of `F` and `G` (`isOfOrderGe_shrinkAppend`);
* `alongList_rel`, **the relation of the link along a local analytic isomorphism** `h : N → M` with
  `h(W') ⊆ W`, `h(V') ⊆ V`: the composite over `(W', V')` for the pulled-back triple, with empty
  blow-ups deleted, is the composite over `(W, V)` pulled back along `h|_{V'}` and cleaned (the
  second condition of [Kol07, 34.1], on each open). The list algebra is
  `shrinkAppend_eraseEmpty_pullback`; the two appended values are compared by `inducedValue_rel`
  (the two naturality properties of `G` at the induced triples); the values of `F` are related by
  its own commutation and compatibility (`seqOn_pullback_eq_of_image_subset`);
* `ClassInducedEraseEmptyClosed s Dom`, the property of the class of `G` which the relation needs
  beyond its closure under pull-back: the induced triple of the **cleaned** list lies in the class
  when the induced triple of the list does [Kol07, 32]; `BMOClass m` and `BOClass m` have it
  (`bmoClass_induced_eraseEmpty`, `boClass_induced_eraseEmpty`: the order read through
  `eraseEmptyLast⁻¹`, the nonempty members embedded by `eraseEmptyIdx`).

The functor itself, its compatibility (the relation at the identity along a common refinement of
two canonical chains), commutation and indifference are in `ComposeInducedFunctor.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold.AnalyticTriple

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The class of the induced triple at the cleaned list -/

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (s : ℕ)
    (L : AnalyticManifold.BlowUpSequence ψ₀ M)
  (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
  (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)

/-- **The order of the marked transform at the last stage of the cleaned list is its order at the
last stage of the list**, read through `eraseEmptyLast⁻¹` (`markedTransformSeq_last_eraseEmpty`; the
order of an inverse-image ideal sheaf at a point where the map is a local isomorphism)
[Kol07, 34.1]. -/
theorem ord_induced_eraseEmpty (y : L.eraseEmpty.stage (Fin.last _)) :
    (T.induced s L.eraseEmpty hLe).I.ord y =
      (T.induced s L hL).I.ord (L.eraseEmptyLast.symm y) := by
  change (L.eraseEmpty.toSuccession.markedTransformSeq T.I s (Fin.last _)).ord y =
    (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).ord (L.eraseEmptyLast.symm y)
  rw [AnalyticManifold.BlowUpSequence.markedTransformSeq_last_eraseEmpty L T.I T.F.idealSheaf s hL]
  exact IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
    (Diffeomorph.isLocalDiffeomorph L.eraseEmptyLast.symm y)

/-- **Finitely many nonempty boundary members survive the deletion of empty blow-ups** [Kol07, 32]:
the nonempty members of the boundary of the cleaned list embed into those of the list through
`eraseEmptyIdx` (`hyp_eraseEmptyIdx`: the member `eraseEmptyIdx i`, pulled back to the last stage of
the cleaned list, is the member `i`). -/
theorem finite_nonempty_induced_eraseEmpty
    (hfin : Finite {j // (T.induced s L hL).F.hyp j ≠ ∅}) :
    Finite {j // (T.induced s L.eraseEmpty hLe).F.hyp j ≠ ∅} := by
  have hF : ∀ k, IsClosed (T.F.hyp k) := fun k => (T.isSnc.1 k).isClosed
  refine Finite.of_injective
    (fun j : {j // (T.induced s L.eraseEmpty hLe).F.hyp j ≠ ∅} =>
      (⟨AnalyticManifold.BlowUpSequence.eraseEmptyIdx L T.F hF j.1, fun h0 => j.2 ?_⟩ :
        {b // (T.induced s L hL).F.hyp b ≠ ∅})) ?_
  · change (L.eraseEmpty.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).hyp j.1 = ∅
    rw [← AnalyticManifold.BlowUpSequence.hyp_eraseEmptyIdx L T.F hF j.1,
        HypersurfaceFamily.comap_hyp]
    change ⇑(Diffeomorph.toAnalyticMap L.eraseEmptyLast.symm) ⁻¹'
      (T.induced s L hL).F.hyp (AnalyticManifold.BlowUpSequence.eraseEmptyIdx L T.F hF j.1) = ∅
    rw [h0, Set.preimage_empty]
  · intro a b hab
    exact Subtype.ext ((AnalyticManifold.BlowUpSequence.eraseEmptyIdx L T.F hF).injective
        (congrArg Subtype.val hab))

/-- The class of `BMO_{n,m}` (`BMOClass m`) at an induced triple is kept by the cleaning of the
inducing list: the mark is the same, the nonempty members finite by
`finite_nonempty_induced_eraseEmpty`. -/
theorem bmoClass_induced_eraseEmpty {m : ℕ} (hT : BMOClass m (T.induced s L hL)) :
    BMOClass m (T.induced s L.eraseEmpty hLe) :=
  ⟨hT.1, finite_nonempty_induced_eraseEmpty T s L hL hLe hT.2⟩

/-- The class of `BO_{n,m}` (`BOClass m`) at an induced triple is kept by the cleaning of the
inducing list: the order bound through `ord_induced_eraseEmpty`, the finiteness through
`finite_nonempty_induced_eraseEmpty`. -/
theorem boClass_induced_eraseEmpty {m : ℕ}
    (hT : BOClass m (T.induced s L hL)) :
    BOClass m (T.induced s L.eraseEmpty hLe) :=
  ⟨hT.1, fun y => (ord_induced_eraseEmpty T s L hL hLe y).trans_le (hT.2.1 _),
    finite_nonempty_induced_eraseEmpty T s L hL hLe hT.2.2⟩

end Manifold.AnalyticTriple

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticFamilyFunctor

open _root_.Manifold

/-- A class of triples **closed under the deletion of empty blow-ups from the inducing list at the
mark `s`**: the induced triple of the cleaned list lies in the class when the induced triple of the
list does ([Kol07, 32]). It supplies the class proof `hDe₂` of `inducedValue_rel` in
the relation of the link of the composite; `BMOClass m` and `BOClass m` have it
(`bmoClass_induced_eraseEmpty`, `boClass_induced_eraseEmpty`). -/
def ClassInducedEraseEmptyClosed (s : ℕ)
    (Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) : Prop :=
  ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (L : AnalyticManifold.BlowUpSequence
      ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hLe : L.eraseEmpty.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf),
    Dom (T.induced s L hL) → Dom (T.induced s L.eraseEmpty hLe)

/-- `BMOClass m` is closed under pull-back along local analytic isomorphisms: the mark is kept, the
nonempty members of the inverse image family are among the nonempty members. -/
theorem bmoClass_classPullbackClosed (m : ℕ) :
    ClassPullbackClosed (ψ₀ := ψ₀) (AnalyticTriple.BMOClass m) := by
  intro M N T h hh hT
  have hfin := hT.2
  refine ⟨hT.1, Finite.of_injective
    (fun j : {j // (T.pullback h hh).F.hyp j ≠ ∅} =>
      (⟨j.1, fun he => j.2 ?_⟩ : {j // T.F.hyp j ≠ ∅}))
    fun j₁ j₂ hj => Subtype.ext (Subtype.mk.inj hj)⟩
  change ⇑h ⁻¹' T.F.hyp j.1 = ∅
  rw [he, Set.preimage_empty]

/-- `BOClass m` is closed under pull-back along local analytic isomorphisms
(`boClass_of_isPullbackOf` at the pulled-back triple). -/
theorem boClass_classPullbackClosed [FiniteDimensional 𝕜 E] (m : ℕ) :
    ClassPullbackClosed (ψ₀ := ψ₀) (AnalyticTriple.BOClass m) :=
  fun T g hg hT =>
    AnalyticTriple.boClass_of_isPullbackOf hT hg (AnalyticTriple.isPullbackOf_pullback T g hg)

/-- `BMOClass m` is closed under the cleaning of the inducing list at every mark. -/
theorem bmoClass_classInducedEraseEmptyClosed (s m : ℕ) :
    ClassInducedEraseEmptyClosed (ψ₀ := ψ₀) s (AnalyticTriple.BMOClass m) :=
  fun T L hL hLe hT => AnalyticTriple.bmoClass_induced_eraseEmpty T s L hL hLe hT

/-- `BOClass m` is closed under the cleaning of the inducing list at every mark. -/
theorem boClass_classInducedEraseEmptyClosed (s m : ℕ) :
    ClassInducedEraseEmptyClosed (ψ₀ := ψ₀) s (AnalyticTriple.BOClass m) :=
  fun T L hL hLe hT => AnalyticTriple.boClass_induced_eraseEmpty T s L hL hLe hT

end AnalyticFamilyFunctor

end Hironaka.Manifold

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

section Link

variable {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M))) (V : Opens M)
  (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W)

/-- The restricted triple over the outer open `W`. -/
abbrev firstTriple : AnalyticTriple ψ₀ (M.restrict W) :=
  T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W)

/-- The value of `F` on the outer open `W` (the first factor of the link). -/
abbrev firstList : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict W) := (F.fam T hT).seqOn W hW

/-- The triple induced by the value of `F` at its last stage. -/
abbrev inducedOfFirst : AnalyticTriple ψ₀ ((firstList F T hT W hW).stage (Fin.last _)) :=
  (firstTriple T W).induced s (firstList F T hT W hW) (hF T hT W hW)

/-- The reading open of the link: the lifted range of `V ⊆ W` at the last stage of the value of
`F`. -/
abbrev firstReadOpen : Opens ((firstList F T hT W hW).stage (Fin.last _)) :=
  (firstList F T hT W hW).liftRange (M.restrictLE (ChainState.le_of_closure_subset hVW))
    (isLocalDiffeomorph_restrictLE _)

omit [FiniteDimensional 𝕜 E] in
include hV in
theorem isCompact_closure_firstReadOpen :
    IsCompact (closure (firstReadOpen F T hT W hW V hVW :
      Set ((firstList F T hT W hW).stage (Fin.last _)))) :=
  (firstList F T hT W hW).isCompact_closure_liftRange _ _
    (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) hV hVW)

include hF hFG hV in
/-- **The appended value of the link**: `G` at the triple induced by the value of `F`, read on the
lifted range of `V ⊆ W`. -/
def appendValue : AnalyticManifold.BlowUpSequence ψ₀
    (((firstList F T hT W hW).stage (Fin.last _)).restrict (firstReadOpen F T hT W hW V hVW)) :=
  (G.fam (inducedOfFirst F s hF T hT W hW) (hFG T hT W hW)).seqOn (firstReadOpen F T hT W hW V hVW)
    (isCompact_closure_firstReadOpen F T hT W hW V hV hVW)

include hF hFG hV in
/-- **The composite over `(W, V)`**: the value of `F` on `W` restricted to `V`, followed by the
value of `G` at the induced triple on the lifted range (`shrinkAppend`). -/
def alongList : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict V) :=
  (firstList F T hT W hW).shrinkAppend (M.restrictLE (ChainState.le_of_closure_subset hVW))
    (isLocalDiffeomorph_restrictLE _) (appendValue F G s hF hFG T hT W hW V hV hVW)

omit [FiniteDimensional 𝕜 E] in
include hF hFG hV in
/-- The order clause of the composite at the mark `s`, from those of `F` (`hF`) and `G` (`hG`):
`isOfOrderGe_shrinkAppend`, the restricted triple rewritten by `pullback_inclusion_restrictLE`. -/
theorem alongList_isOfOrderGe
    (hG : ∀ {N : AnalyticManifold.{u} 𝕜 E} (T' : AnalyticTriple ψ₀ N) (hT' : Dom₂ T')
      (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
      ((G.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I s
        (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf) :
    (alongList F G s hF hFG T hT W hW V hV hVW).toSuccession.IsOfOrderGe
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I s
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).F.idealSheaf := by
  have h := (firstList F T hT W hW).isOfOrderGe_shrinkAppend
    (M.restrictLE (ChainState.le_of_closure_subset hVW)) (isLocalDiffeomorph_restrictLE _)
    (firstTriple T W) s (hF T hT W hW) (appendValue F G s hF hFG T hT W hW V hV hVW)
    (hG (inducedOfFirst F s hF T hT W hW) (hFG T hT W hW) (firstReadOpen F T hT W hW V hVW)
      (isCompact_closure_firstReadOpen F T hT W hW V hV hVW))
  rwa [AnalyticTriple.pullback_inclusion_restrictLE T (ChainState.le_of_closure_subset hVW)] at h

end Link

section Rel

omit [FiniteDimensional 𝕜 E]

variable (hFc : F.CommutesWithLocalIsos) (hG : G.CommutesWithLocalIsos)
  (hG' : G.IndifferentToEmptyMembers) (hDom : ClassPullbackClosed (ψ₀ := ψ₀) Dom₂)
  (hDomE : ClassInducedEraseEmptyClosed (ψ₀ := ψ₀) s Dom₂)
  {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (hT : Dom₁ T)
  (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
  (hT' : Dom₁ (T.pullback h hh))

include hFc in
/-- The value of `F` on `W' ⊆ N` for the pulled-back triple, cleaned, is the value of `F` on
`W ⊇ h(W')` pulled back along `h|_{W'}` and cleaned (the commutation and compatibility of `F`,
`seqOn_pullback_eq_of_image_subset`; the deletion of empty blow-ups is idempotent). -/
theorem firstList_pullback_rel {W : Opens M} (hW : IsCompact (closure (W : Set M)))
    {W' : Opens N} (hW' : IsCompact (closure (W' : Set N))) (hWW' : ⇑h '' (W' : Set N) ⊆ W) :
    (firstList F (T.pullback h hh) hT' W' hW').eraseEmpty =
      ((firstList F T hT W hW).pullback (AnalyticMap.restrictMap h W' W hWW')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW')).eraseEmpty := by
  rw [firstList, hFc.seqOn_pullback_eq_of_image_subset hh
    (AnalyticTriple.isPullbackOf_pullback T h hh) hT hT' hW' hW hWW',
    AnalyticManifold.BlowUpSequence.eraseEmpty_eraseEmpty]

include hF hFG hFc hG hG' hDom hDomE in
/-- The second condition of [Kol07, 34.1] for one link of the composite: **the composite over
`(W', V')` for the pulled-back triple, cleaned, is the composite over `(W, V)` pulled back along
`h|_{V'}` and cleaned**, for `h(W') ⊆ W`, `h(V') ⊆ V`. This is `link_rel` with the family of one
boundary member replaced by `G`: the list algebra `shrinkAppend_eraseEmpty_pullback`, the two
appended values compared by `inducedValue_rel` (the naturality of `G` at the induced triples), the
values of `F` related by `firstList_pullback_rel`. -/
theorem alongList_rel (T' : AnalyticTriple ψ₀ N) (hT'g : T'.IsPullbackOf T h) (hT'' : Dom₁ T')
    {W : Opens M} (hW : IsCompact (closure (W : Set M))) {W' : Opens N}
    (hW' : IsCompact (closure (W' : Set N))) (hWW' : ⇑h '' (W' : Set N) ⊆ W) {V : Opens M}
    (hV : IsCompact (closure (V : Set M))) (hVW : closure (V : Set M) ⊆ W) {V' : Opens N}
    (hV' : IsCompact (closure (V' : Set N))) (hV'W' : closure (V' : Set N) ⊆ W')
    (hVV' : ⇑h '' (V' : Set N) ⊆ V) :
    (alongList F G s hF hFG T' hT'' W' hW' V' hV' hV'W').eraseEmpty =
      ((alongList F G s hF hFG T hT W hW V hV hVW).pullback (AnalyticMap.restrictMap h V' V hVV')
        (AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV')).eraseEmpty := by
  obtain rfl : T' = T.pullback h hh := AnalyticTriple.ext' hT'g.1 hT'g.2
  -- the square of restrictions
  set TW := T.pullback (M.inclusion W) (isLocalDiffeomorph_inclusion M W) with hTWdef
  set TW' := (T.pullback h hh).pullback (N.inclusion W') (isLocalDiffeomorph_inclusion N W')
    with hTW'def
  set gW := AnalyticMap.restrictMap h W' W hWW' with hgWdef
  have hgW : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω gW :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hh W' W hWW'
  set gV := AnalyticMap.restrictMap h V' V hVV' with hgVdef
  have hgV : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω gV :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hh V' V hVV'
  set ρ := M.restrictLE (ChainState.le_of_closure_subset hVW) with hρdef
  set ρ' := N.restrictLE (ChainState.le_of_closure_subset hV'W') with hρ'def
  have hsq : ρ.comp gV = gW.comp ρ' := ContMDiffMap.ext fun _ => Subtype.ext rfl
  have hc₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ρ.comp gV) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE _) hgV
  have hc₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (gW.comp ρ') :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hgW (isLocalDiffeomorph_restrictLE _)
  set L₁ := firstList F T hT W hW with hL₁def
  set L₂ := firstList F (T.pullback h hh) hT'' W' hW' with hL₂def
  have hrel : L₂.eraseEmpty = (L₁.pullback gW hgW).eraseEmpty :=
    firstList_pullback_rel F hFc T hT h hh hT'' hW hW' hWW'
  have e₀ : (L₁.pullback ρ (isLocalDiffeomorph_restrictLE _)).pullback gV hgV =
      (L₁.pullback gW hgW).pullback ρ' (isLocalDiffeomorph_restrictLE _) := by
    rw [AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
        AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _]
    exact AnalyticManifold.BlowUpSequence.pullback_congr _ hsq hc₁ hc₂
  have hA : (L₂.pullback ρ' (isLocalDiffeomorph_restrictLE _)).eraseEmpty =
      ((L₁.pullback gW hgW).pullback ρ' (isLocalDiffeomorph_restrictLE _)).eraseEmpty := by
    rw [← AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty L₂ _
        (isLocalDiffeomorph_restrictLE _), hrel,
      AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty]
  -- the triple over `W'` is the pull-back of the triple over `W` along `h|_{W'}`
  have hmap : (M.inclusion W).comp gW = h.comp (N.inclusion W') := ContMDiffMap.ext fun _ => rfl
  have hTWeq : TW.pullback gW hgW = TW' := by
    rw [hTWdef, hTW'def, AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_pullback _ _ _ _ _]
    exact AnalyticTriple.pullback_eq_of_eq T hmap _ _
  have hL₂ : L₂.toSuccession.IsOfOrderGe (TW.pullback gW hgW).I s
      (TW.pullback gW hgW).F.idealSheaf := by
    rw [hTWeq]
    exact hF (T.pullback h hh) hT'' W' hW'
  have hD₂ : Dom₂ ((TW.pullback gW hgW).induced s L₂ hL₂) := by
    rw [AnalyticTriple.induced_congr hTWeq s L₂ hL₂ (hF (T.pullback h hh) hT'' W' hW')]
    exact hFG (T.pullback h hh) hT'' W' hW'
  have hDe₂ : Dom₂ ((TW.pullback gW hgW).induced s L₂.eraseEmpty
      (AnalyticManifold.BlowUpSequence.isOfOrderGe_eraseEmpty L₂ _ s
          (TW.pullback gW hgW).isSnc hL₂)) :=
    hDomE (TW.pullback gW hgW) L₂ hL₂ _ hD₂
  -- the appended value over `W'`, read at the pulled-back triple
  have hF₂ : appendValue F G s hF hFG (T.pullback h hh) hT'' W' hW' V' hV' hV'W' =
      (G.fam ((TW.pullback gW hgW).induced s L₂ hL₂) hD₂).seqOn
        (L₂.liftRange ρ' (isLocalDiffeomorph_restrictLE _))
        (L₂.isCompact_closure_liftRange ρ' (isLocalDiffeomorph_restrictLE _)
          (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W')) :=
    G.fam_seqOn_congr_triple (AnalyticTriple.induced_congr hTWeq.symm s L₂
      (hF (T.pullback h hh) hT'' W' hW') hL₂) _ _ _ _
  have hκ₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      ((L₂.liftCorestrict ρ' (isLocalDiffeomorph_restrictLE _)).comp (Diffeomorph.toAnalyticMap
        (L₂.pullback ρ' (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.symm)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)
      (Diffeomorph.isLocalDiffeomorph _)
  have hκ₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (((L₁.liftCorestrict ρ (isLocalDiffeomorph_restrictLE _)).comp
        ((L₁.pullback ρ (isLocalDiffeomorph_restrictLE _)).pullbackLiftLast gV hgV)).comp
        (Diffeomorph.toAnalyticMap ((AnalyticManifold.BlowUpSequence.stageOfEq e₀).trans
          (((L₁.pullback gW hgW).pullback ρ' (isLocalDiffeomorph_restrictLE _)).eraseEmptyLast.trans
            (AnalyticManifold.BlowUpSequence.stageOfEq hA.symm))).symm)) :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
          (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _))
      (Diffeomorph.isLocalDiffeomorph _)
  have hFv := (congrArg (fun X : AnalyticManifold.BlowUpSequence ψ₀ (((L₂.stage
      (Fin.last _)).restrict
      (L₂.liftRange ρ' (isLocalDiffeomorph_restrictLE _)))) => (X.pullback _ hκ₂).eraseEmpty)
      hF₂).trans
    (G.inducedValue_rel TW s gW hgW L₁ (hF T hT W hW) (hFG T hT W hW) ρ
      (isLocalDiffeomorph_restrictLE _) ρ' (isLocalDiffeomorph_restrictLE _) gV hgV hsq hG hG' hDom
      L₂ hL₂ hD₂ hDe₂ hrel
      (L₁.isCompact_closure_liftRange ρ (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hVW) hV hVW))
      (L₂.isCompact_closure_liftRange ρ' (isLocalDiffeomorph_restrictLE _)
        (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W'))
      (isCompact_closure_range_restrictLE (ChainState.le_of_closure_subset hV'W') hV' hV'W') e₀ hA
      hκ₂ hκ₁)
  exact AnalyticManifold.BlowUpSequence.shrinkAppend_eraseEmpty_pullback L₁ L₂ gW hgW ρ
      (isLocalDiffeomorph_restrictLE _)
    ρ' (isLocalDiffeomorph_restrictLE _) gV hgV
    (appendValue F G s hF hFG T hT W hW V hV hVW)
    (appendValue F G s hF hFG (T.pullback h hh) hT'' W' hW' V' hV' hV'W') e₀ hA hκ₂ hκ₁ hFv

end Rel

end Hironaka.Manifold.AnalyticFamilyFunctor

end
