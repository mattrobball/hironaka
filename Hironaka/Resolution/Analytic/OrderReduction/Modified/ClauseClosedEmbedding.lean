/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseModFunctor
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.IdealSheaf.DerivLemmas
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.OrderReduction.BMO.SplitOrder
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingPrep
import Hironaka.Resolution.Analytic.OrderReduction.FamilyIndependence
import Hironaka.Resolution.Analytic.Principalization.ShrinkAppendLemmas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic


/-!
# The modified functor commutes with closed embeddings of empty divisor in codimension one

Włodarczyk proves that the modified resolution commutes with closed embeddings by running the
algorithm's own descent ([Wlo09, §7.1]): for `τ : S ↪ M` a closed hypersurface with `𝓘 ⊇ I_S` and
the empty boundary, the coordinates defining `S` are tangent directions of the ideal, the algorithm
passes to the hypersurface `V(u₁)` and replaces the ideal with its restriction, so the run on `M`
is the run on `S` pushed forward. In codimension one no cover and no induction enter: `S` itself
is a global hypersurface of maximal contact of `(M, 𝓘, ∅)`, so the value of the modified functor
is the value of the modified first step with the class's hypersurface replaced by `S`, and that
value is the push-forward of the value of the functor one dimension down. This is the argument of
`BOanFamOfInput_commutesWithClosedEmbeddingsOfEmptyDivisorFam` (`ClosedEmbeddingFam.lean`; Kollár's
[Kol07, Theorem 103 (3)], proved in [Kol07, Theorem 103, Step 2.4]), both being instances of
`BO.hfStep2FamOn_eq_pushforwardRestrict_of_global`, at the modified datum `stepBData`, plus two
facts about the modified run. The general codimension is the chaining
along a flag of hypersurfaces of [Kol07, 108] (`Functor/ChainClosedEmbeddingChain.lean`); its
corollary for a tower, `BMOmodFam_commutesWithClosedEmbeddingsOfEmptyDivisorFam_all` in
`Functor/ChainClosedEmbeddingZero.lean`, takes the codimension-one commutation as a hypothesis,
which `Hironaka/Resolution/Analytic/Wlo09/Concrete.lean` supplies from this module.

* `IsClosedSubmanifold.ord_le_one_of_idealSheaf_le`, `AnalyticTriple.boClass_one_of_idealSheaf_le`:
  an ideal sheaf containing the ideal of a smooth hypersurface has order `≤ 1` everywhere (off `S`
  it is the unit ideal, on `S` it contains a local equation of order `1`; the remark in the proof
  of [Kol07, 108]), so `(M, 𝓘 ⊇ I_S, ∅)` is in the class `BO_{n,1}`.
* `descentStateAux_L_eq_nil_of_eq_zero`, `BMOmod.stepAFamOn_eq_nil`,
  `BMOmod.stepACFunctor_seqOn_eq_nil`: the rounds on the nonmonomial part and the monomial phase
  are idle on `(M, 𝓘, ∅)` with `ord 𝓘 ≤ 1`: with the empty boundary the nonmonomial part is `𝓘`
  itself, the round bound is `≤ 1 < 2 = t` and the descent has no link; the monomial phase has no
  active member. `AnalyticFamilyFunctor.composeOn_eq_of_firstList_eq_nil` is the generic fact: the
  composite along induced triples with the first functor idle is the second functor's value
  (`shrinkAppend_nil`, `induced_nil`, the commutation with the outer open's inclusion, `compat`).
* `BMOmod.coreModOn_eq_pushforwardRestrict_of_isNonzeroEverywhere`: the modified core at a member
  `S` (the other members empty) whose trace ideal is nonzero everywhere: the stopped locus is empty
  (`Zminus1_one_eq_empty_of_isNonzeroEverywhere`: a stopped point would make the trace the zero
  ideal), `H⁺ = S`, and the core is the push-forward of the value of `R` on `(S, J, ∅)`
  (indifference to the all-empty trace boundary). This is simpler than the family of
  [Kol07, Lemma 102]: there is no empty first blow-up.
* `BMOmod.stepBFunctor_seqOn_eq_pushforwardRestrict_of_global`: the modified first step on
  `(M, 𝓘 ⊇ I_S, ∅)` with `S` a global hypersurface: the functor's value is the local functor's
  (`stepBFunctor_fam_eq`), Step 2 at the mark `1` along `S`
  (`BO.hfStep2FamOn_eq_pushforwardRestrict_of_global`), Step 2.2 at the single member `S` of
  `∅ + S` being the modified core.
* `BMOmod.modFunctor_commutesWithClosedEmbeddings_one`,
  `BMOmod.BMOmodFamOfInput_of_hid_commutesWithClosedEmbeddings_one`: the commutation in
  codimension one for the modified functor at dimension `n` (through the functor one dimension
  down `R`) and for every level of the tower (level `n + 1` through level `n`; level `0` the empty
  list on both sides). Stated for `BMOmodFamOfInput_of_hid`, generic in the transform identity
  `hid`.

Sources: [Wlo09, §7.1]; [Kol07, 34.3] (commutation with closed embeddings), [Kol07, 108] (the
reduction to a hypersurface; every local equation of `S` lies in `𝓘`, so the maximal order is
`1`), [Kol07, Theorem 103 (3)] and [Kol07, Theorem 103, Step 2.4], the proof of
[Kol07, Lemma 102]. The statements themselves are not in the sources.
-/

public section


noncomputable section

open Set Topology TopologicalSpace Hironaka.Manifold Hironaka.Local
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

section Tools

variable {M : AnalyticManifold.{u} 𝕜 E}

omit [FiniteDimensional 𝕜 E] in
/-- The value of the data of the step depends on the triple and the member only (a substitution;
the analogue of `BDanFamData.fam_seqOn_congr`). -/
theorem HFamData.fam_seqOn_congr {s : ℕ} (hf : HFamData ψ₀ s) {T₁ T₂ : AnalyticTriple ψ₀ M}
    (e : T₁ = T₂) (h₁ : AnalyticTriple.BOClass s T₁) (h₂ : AnalyticTriple.BOClass s T₂)
    (j₁ : T₁.F.ι) (j₂ : T₂.F.ι) (hj : HEq j₁ j₂) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) :
    (hf.fam T₁ h₁ j₁).seqOn U hU = (hf.fam T₂ h₂ j₂).seqOn U hU := by
  subst e
  cases hj
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- The per-open push-forward of the empty list is the empty list (`pushforwardRestrict_eq`,
`pullback_nil`, `pushforward_nil`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.pushforwardRestrict_nil {S : Set M} {s : ℕ}
    (hS : IsClosedSubmanifold ψ₀ S s)
    (U : Opens M) :
    AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
        (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜))
          ((hS.toAnalyticManifold).restrict (hS.preimageOpens U))) =
      AnalyticManifold.BlowUpSequence.nil (ψ₀ := ψ₀) (M.restrict U) := by
  rfl

omit [FiniteDimensional 𝕜 E] in
/-- An ideal sheaf containing the ideal of a smooth hypersurface has order `≤ 1` everywhere (the
remark in the proof of [Kol07, 108]: every local equation of `S` lies in `𝓘`, so the maximal order
is `1`): off `S` it is the unit ideal (`stalkIdeal_idealSheaf_of_notMem`), on `S` it contains a
local equation, of order `1`. -/
theorem _root_.Manifold.IsClosedSubmanifold.ord_le_one_of_idealSheaf_le {S : Set M}
    (hS : IsClosedSubmanifold ψ₀ S 1) (I : AnalyticManifold.IdealSheaf M)
        (hle : hS.idealSheaf ≤ I)
    (x : M) : I.ord x ≤ (1 : ℕ∞) := by
  refine (IdealSheaf.ord_anti hle x).trans ?_
  change IsLocalRing.ord (hS.idealSheaf.stalkIdeal x) ≤ 1
  by_cases hx : x ∈ S
  · -- on `S`: a local equation of `S` lies in `I_S` and is not in `𝔪²`, so the order is `< 2`
    obtain ⟨φ, σ, hxφ, hφ⟩ := hS.exists_adaptedChart x hx
    have hu : coord E ψ₀ φ hφ.1 hxφ (σ 0) ∈ hS.idealSheaf.stalkIdeal x := by
      rw [hS.stalkIdeal_idealSheaf_of_mem hx, hS.ker_restrictStalk_eq_span hx hφ hxφ]
      exact Ideal.subset_span ⟨0, rfl⟩
    have hnot : ¬ hS.idealSheaf.stalkIdeal x ≤ IsLocalRing.maximalIdeal _ ^ 2 := fun h =>
      coord_notMem_maximalIdeal_sq φ hφ.1 hxφ (h hu)
    have h2 : ¬ ((2 : ℕ) : ℕ∞) ≤ IsLocalRing.ord (hS.idealSheaf.stalkIdeal x) := fun h =>
      hnot (IsLocalRing.le_ord_iff.mp h)
    have h3 := not_le.mp h2
    have e2 : ((2 : ℕ) : ℕ∞) = 1 + 1 := by norm_num
    rw [e2] at h3
    exact (ENat.lt_add_one_iff ENat.one_ne_top).mp h3
  · rw [hS.stalkIdeal_idealSheaf_of_notMem hx, IsLocalRing.ord_top]
    exact zero_le

omit [FiniteDimensional 𝕜 E] in
/-- The triple `(M, 𝓘 ⊇ I_S, ∅)` is in the class `BO_{n,1}` (`ord_le_one_of_idealSheaf_le` for the
order clause; no member). -/
theorem _root_.Manifold.AnalyticTriple.boClass_one_of_idealSheaf_le {S : Set M}
    (hS : IsClosedSubmanifold ψ₀ S 1)
    (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere) (hle : hS.idealSheaf ≤ I) :
    AnalyticTriple.BOClass 1
      (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ :
        AnalyticTriple ψ₀ M) := by
  have : Finite (HypersurfaceFamily.empty M).ι := inferInstanceAs (Finite PEmpty)
  exact ⟨le_rfl, fun x => hS.ord_le_one_of_idealSheaf_le I hle x, Subtype.finite⟩

end Tools

namespace AnalyticFamilyFunctor

open _root_.Manifold

variable {Dom₁ Dom₂ : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
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

/-- **The composite when the first functor is idle**: if the value of `F` on the outer chain open is
the empty list, the composite's value on `U` is the value of `G` on `U`: `shrinkAppend_nil`,
`induced_nil`, the commutation of `G` with the inclusion of the outer open
(`CommutesWithLocalIsos.seqOn_eq_of_image_eq`), the composite restriction `U ≤ W 1`, the
compatibility `compat` of `G`, and the deletions of empty blow-ups (the end of the proof of
`BOanFamOfInput_commutesWithClosedEmbeddingsOfEmptyDivisorFam` in `ClosedEmbeddingFam.lean`, made
generic). -/
theorem composeOn_eq_of_firstList_eq_nil (hG : G.CommutesWithLocalIsos)
    (hDom : ClassPullbackClosed Dom₂) {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (hT : Dom₁ T) (hT₂ : Dom₂ T) (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hnil : (F.fam T hT).seqOn (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
      (isCompact_closure_chainOpens _ _ _ _) = AnalyticManifold.BlowUpSequence.nil _) :
    composeOn F G s hF hFG T hT U hU = (G.fam T hT₂).seqOn U hU := by
  -- the two chain opens and the outer inclusion
  set W₀ := chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0 with hW₀
  set W₁ := chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 1 with hW₁
  have hW₀c : IsCompact (closure (W₀ : Set M)) := isCompact_closure_chainOpens _ _ _ _
  have hW₁c : IsCompact (closure (W₁ : Set M)) := isCompact_closure_chainOpens _ _ _ _
  have hVW : closure (W₁ : Set M) ⊆ W₀ := closure_chainOpens_succ_subset _ _ _ Nat.zero_lt_one
  have hUW₁ : U ≤ W₁ := le_chainOpens_last _ hU 1
  have hW₁₀ : W₁ ≤ W₀ := ChainState.le_of_closure_subset hVW
  have hg₀ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (M.inclusion W₀) :=
    isLocalDiffeomorph_inclusion M W₀
  have hnil' : firstList F T hT W₀ hW₀c = AnalyticManifold.BlowUpSequence.nil _ := hnil
  -- the maps: the lifted range of `W₁ ⊆ W₀`, its corestriction, the restriction of the inclusion
  set O : Opens (M.restrict W₀) :=
    (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ψ₀) (M.restrict W₀)).liftRange (M.restrictLE hW₁₀)
      (isLocalDiffeomorph_restrictLE _) with hO
  have hOc : IsCompact (closure (O : Set (M.restrict W₀))) :=
    (AnalyticManifold.BlowUpSequence.nil _).isCompact_closure_liftRange _ _
      (isCompact_closure_range_restrictLE hW₁₀ hW₁c hVW)
  have himg : ⇑(M.inclusion W₀) '' (O : Set (M.restrict W₀)) = (W₁ : Set M) :=
    (congrArg (fun s : Set (M.restrict W₀) => (Subtype.val : M.restrict W₀ → M) '' s)
      (range_restrictLE hW₁₀)).trans
      (Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hW₁₀ hx⟩, rfl⟩)
  set c : AnalyticMap (M.restrict W₁) ((M.restrict W₀).restrict O) :=
    (AnalyticManifold.BlowUpSequence.nil (ψ₀ := ψ₀) (M.restrict W₀)).liftCorestrict
        (M.restrictLE hW₁₀)
      (isLocalDiffeomorph_restrictLE _) with hcdef
  have hc : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω c :=
    AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftCorestrict _ _ _
  set rm := AnalyticMap.restrictMap (M.inclusion W₀) O W₁ himg.le with hrmdef
  have hrm : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω rm :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hg₀ O W₁ himg.le
  have hT₂W : Dom₂ (T.pullback (M.inclusion W₀) hg₀) := hDom T _ hg₀ hT₂
  -- rewrite the composite with the first list as a parameter (a `subst` of the empty list)
  have key : ∀ (L₁ : AnalyticManifold.BlowUpSequence ψ₀ (M.restrict W₀))
      (hL₁ : L₁.toSuccession.IsOfOrderGe (firstTriple T W₀).I s (firstTriple T W₀).F.idealSheaf)
      (hD₁ : Dom₂ ((firstTriple T W₀).induced s L₁ hL₁)),
      L₁ = AnalyticManifold.BlowUpSequence.nil _ →
      ((L₁.shrinkAppend (M.restrictLE hW₁₀) (isLocalDiffeomorph_restrictLE _)
        ((G.fam ((firstTriple T W₀).induced s L₁ hL₁) hD₁).seqOn
          (L₁.liftRange (M.restrictLE hW₁₀) (isLocalDiffeomorph_restrictLE _))
          (L₁.isCompact_closure_liftRange _ _
            (isCompact_closure_range_restrictLE hW₁₀ hW₁c hVW)))).pullback
        (M.restrictLE hUW₁) (isLocalDiffeomorph_restrictLE hUW₁)).eraseEmpty =
      (G.fam T hT₂).seqOn U hU := by
    intro L₁ hL₁ hD₁ hL₁nil
    subst hL₁nil
    rw [AnalyticManifold.BlowUpSequence.shrinkAppend_nil]
    -- `G` at the induced triple of the empty list is `G` at the restricted triple
    rw [AnalyticFamilyFunctor.fam_seqOn_congr_triple G (AnalyticTriple.induced_nil _ s hL₁) hD₁
      hT₂W]
    change ((((G.fam (T.pullback (M.inclusion W₀) hg₀) hT₂W).seqOn O hOc).pullback c hc).pullback
      (M.restrictLE hUW₁) (isLocalDiffeomorph_restrictLE hUW₁)).eraseEmpty = _
    -- `G` on the restricted triple over the lifted range is `G` on `T` at `W₁`, pulled back
    rw [AnalyticFamilyFunctor.CommutesWithLocalIsos.seqOn_eq_of_image_eq hG hg₀
      (AnalyticTriple.isPullbackOf_pullback T _ hg₀) hT₂ hT₂W hOc hW₁c himg]
    -- assemble the maps: corestriction, restriction of the inclusion, inclusion `U ⊆ W₁`
    have hcr : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.comp (M.restrictLE hUW₁)) :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hc (isLocalDiffeomorph_restrictLE _)
    have hcomp : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (rm.comp (c.comp (M.restrictLE hUW₁))) :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hrm hcr
    have hmap : rm.comp (c.comp (M.restrictLE hUW₁)) = M.restrictLE hUW₁ :=
      ContMDiffMap.ext fun x => Subtype.ext rfl
    rw [AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
        AnalyticManifold.BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ hcr,
      AnalyticManifold.BlowUpSequence.pullback_comp _ _ _ _ _,
      AnalyticManifold.BlowUpSequence.pullback_congr _ hmap hcomp
          (isLocalDiffeomorph_restrictLE hUW₁),
      (G.fam T hT₂).compat U W₁ hU hW₁c hUW₁]
  exact key (firstList F T hT W₀ hW₀c) (hF T hT W₀ hW₀c) (hFG T hT W₀ hW₀c) hnil'

end AnalyticFamilyFunctor

end Hironaka.Manifold

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO Hironaka.Manifold.BO

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

section PhaseAC

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The descent with `0` links is the initial state: its list is empty (`BState.initialOf_L`; the
index is kept as a variable for the dependent rewrite). -/
theorem descentStateAux_L_eq_nil_of_eq_zero
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (m : ℕ)
    (hT : AnalyticTriple.BMOClass m T) (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (W : ℕ → Opens M)
    (hW : ∀ k, IsCompact (closure (W k : Set M))) (r : ℕ)
    (hWsub : ∀ k, k < r → closure (W (k + 1) : Set M) ⊆ W k) (D : ℕ)
    (hD : ∀ x ∈ (W 0 : Set M), (nonmonomialTriple T).I.ord x ≤ (D : ℕ∞)) (j : ℕ) (hj : j ≤ r)
    (hjt : j ≤ D + 1 - t) (h : j = 0) :
    (descentStateAux T m hT bo hcomp hid t hm hmt W hW r hWsub D hD j hj hjt).L =
      AnalyticManifold.BlowUpSequence.nil _ := by
  subst h
  rfl

/-- **The rounds are idle when the bound is below the first round**: the descent has
`D + 1 − t = 0` links, the chain state is the initial state and the value is the empty list
(`BState.initialOf_L`, `pullback_nil`, `eraseEmpty_nil`). -/
theorem stepAFamOn_eq_nil (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (m : ℕ) (hT : AnalyticTriple.BMOClass m T) (t : ℕ) (hm : 1 ≤ m) (hmt : m ≤ t) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (h : stepABound T U hU + 1 ≤ t) :
    stepAFamOn T m hT bo hcomp hid t hm hmt U hU = AnalyticManifold.BlowUpSequence.nil _ := by
  have h0 : descentLength t (stepABound T U hU) = 0 := by
    unfold descentLength
    omega
  unfold stepAFamOn stepAChainState descentState
  rw [descentStateAux_L_eq_nil_of_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0,
    AnalyticManifold.BlowUpSequence.pullback_nil, AnalyticManifold.BlowUpSequence.eraseEmpty_nil]

/-- **The rounds and the monomial phase are idle on `(M, 𝓘, ∅)` with `ord 𝓘 ≤ 1`** (the situation of
[Wlo09, §7.1], where the maximal order is `1` by the remark of [Kol07, 108]): with the empty
boundary the nonmonomial part is `𝓘` itself (`monomialPart_eq_top_of_activeMembers_eq_empty`,
`monomialPart_mul_nonmonomialPart`), so the round bound is `≤ 1 < 2 = t` and the rounds give the
empty list (`stepAFamOn_eq_nil`); the monomial phase has no active member
(`step2bPhase_of_not_nonempty`); the composite is the second functor's value
(`composeOn_eq_of_firstList_eq_nil`), the empty list. -/
theorem stepACFunctor_seqOn_eq_nil (I : AnalyticManifold.IdealSheaf M)
    (hI : I.IsNonzeroEverywhere)
    (hord : ∀ x, I.ord x ≤ (1 : ℕ∞))
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((stepACFunctor bo hcomp hid).fam _ (AnalyticTriple.bmoClass_one_empty I hI)).seqOn U hU =
      AnalyticManifold.BlowUpSequence.nil _ := by
  set T₀ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
    ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ with hT₀
  have hT : AnalyticTriple.BMOClass 1 T₀ := AnalyticTriple.bmoClass_one_empty I hI
  have hε : IsEmpty T₀.F.ι := inferInstanceAs (IsEmpty PEmpty)
  -- with the empty boundary the nonmonomial part is `𝓘` itself
  have hM : monomialPart T₀.F T₀.isSnc T₀.I = ⊤ :=
    monomialPart_eq_top_of_activeMembers_eq_empty T₀
      (Set.eq_empty_of_forall_notMem fun j _ => (IsEmpty.false j).elim)
  have hN : nonmonomialPart T₀.F T₀.isSnc T₀.I = I := by
    refine IdealSheaf.ext fun x => ?_
    have h := stalkIdeal_monomialPart_mul_nonmonomialPart T₀.F T₀.isSnc T₀.I x
    rw [hM, IdealSheaf.stalkIdeal_top, Ideal.top_mul] at h
    exact h
  -- the round bound is at most `1`
  have hbound : ∀ (O : Opens M), IsCompact (closure (O : Set M)) → roundOrderOn T₀ O ≤ 1 := by
    intro O hO
    have h : (roundOrderOn T₀ O : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by
      rw [coe_roundOrderOn T₀ O hO]
      exact iSup_le fun x => by rw [hN]; exact hord x
    exact_mod_cast h
  -- the composite: the rounds are idle on the outer chain open, so the value is the monomial
  -- phase's, which is
  -- idle too
  change AnalyticFamilyFunctor.composeOn (stepAFunctor 1 bo hcomp hid 2 le_rfl one_le_two)
    (step2bFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))) 1
    (fun T hT U hU => stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)
    (fun T hT U hU => AnalyticTriple.bmoClass_inducedTriple _ (bmoClass_restrict T hT U) 1 _
      (stepAFamOn_isOfOrderGe T 1 hT bo hcomp hid 2 le_rfl one_le_two U hU)) T₀ hT U hU = _
  refine (AnalyticFamilyFunctor.composeOn_eq_of_firstList_eq_nil _ _ _ _ _
    step2bFunctor_commutesWithLocalIsos (AnalyticFamilyFunctor.bmoClass_classPullbackClosed 1)
    T₀ hT hT U hU ?_).trans ?_
  · rw [stepAFunctor_fam_seqOn]
    refine stepAFamOn_eq_nil bo hcomp hid T₀ 1 hT 2 le_rfl one_le_two _ _ ?_
    have := hbound (stepAOuter (chainOpens (exhaustion M) (exhaustionIdx (exhaustion M) hU) 1 0)
      (isCompact_closure_chainOpens _ _ _ _)) (isCompact_closure_stepAOuter _ _)
    unfold stepABound
    omega
  · rw [step2bFunctor_fam]
    change step2bPhase (famFuel T₀ hT U) (T₀.pullback _ _) (bmoClass_restrict T₀ hT U) = _
    exact step2bPhase_of_not_nonempty
      (T₀.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)) (bmoClass_restrict T₀ hT U)
      (fun ⟨j, _⟩ => (hε.false j).elim) _

end PhaseAC

variable (R : AnalyticFamilyFunctor.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
    (AnalyticTriple.BMOClass 1))
  (hRo : ∀ {N : AnalyticManifold.{u} 𝕜 (Fin (n - 1) → 𝕜)}
    (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) N)
    (hT' : AnalyticTriple.BMOClass 1 T') (U' : Opens N) (hU' : IsCompact (closure (U' : Set N))),
    ((R.fam T' hT').seqOn U' hU').toSuccession.IsOfOrderGe
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).I 1
      (T'.pullback (N.inclusion U') (isLocalDiffeomorph_inclusion N U')).F.idealSheaf)
  (hRc : R.CommutesWithLocalIsos) (hRi : R.IndifferentToEmptyMembers)
  (bmo₁ : BMOanFam.{u} 𝕜 (n - 1) 1) {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

include hRi in
/-- **The modified core at a member with empty stopped locus is the push-forward of the value of
the functor one dimension down on the member** (the proof of [Kol07, Lemma 102] in the modified
form; the recursion of [Wlo09, Theorem 7.4.1]): on the member `S := Eʲ` of a boundary all of whose
other members are empty, with the trace `J := 𝓘|_S` nonzero everywhere, the stopped locus
`Z_{−1}(𝓘, 1)(S)` is empty (`Zminus1_one_eq_empty_of_isNonzeroEverywhere`: a stopped point would
make `J` the zero ideal), so `H⁺ = S` (`coreModOn_eq_of_eq`) and the core is the value of `R` on the
restricted triple pushed forward. The value of `R` on `(S, J, ∅ + all-empty trace)` is its value on
`(S, J, ∅)` (`hRi`), and the push-forward of a list without empty centres, cleaned, is itself
(`noEmptyCenters_pushforwardRestrict`). -/
theorem coreModOn_eq_pushforwardRestrict_of_isNonzeroEverywhere
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (j : T.F.ι)
    (hT : AnalyticTriple.BMOClass 1 T) {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1) (hSj : T.F.hyp j = S)
    (hemp : ∀ k, k ≠ j → T.F.hyp k = ∅)
    (hJ : (T.I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    coreModOn R T j hT U hU =
      AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
        ((R.fam _ (AnalyticTriple.bmoClass_one_empty _ hJ)).seqOn (hS.preimageOpens U)
          (hS.isCompact_closure_preimageOpens U hU)) := by
  have hT' := AnalyticTriple.bmoClass_one_empty (ψ₀ := ContinuousLinearEquiv.refl 𝕜
    (Fin (n - 1) → 𝕜)) _ hJ
  -- the stop locus is empty under `hJ`, so `H⁺ = S`
  have hZ : stopLocus T j = ∅ := by
    change BD.Zminus1 T.I 1 (T.F.hyp j) = ∅
    rw [hSj]
    exact BD.Zminus1_one_eq_empty_of_isNonzeroEverywhere hS T.I hJ
  have hSeq : S = hplus T j := by
    unfold hplus
    rw [hZ, Set.sdiff_empty, hSj]
  rw [coreModOn_eq_of_eq R T j hT hS hSeq U hU]
  -- `R`'s value on the restricted triple is its value on `(S, J, ∅)`: every member of the trace
  -- boundary is empty
  have hε : IsEmpty (HypersurfaceFamily.empty hS.toAnalyticManifold).ι :=
    inferInstanceAs (IsEmpty PEmpty)
  have he' : ∀ b, b ∉ Set.range (OrderEmbedding.ofIsEmpty :
      (HypersurfaceFamily.empty hS.toAnalyticManifold).ι ↪o
        (restrictedTripleModOf T j hS hSeq).F.ι) →
      (restrictedTripleModOf T j hS hSeq).F.hyp b = ∅ := by
    intro b _
    change hS.preimageVal ((T.F.emptyMember j).hyp b) = ∅
    by_cases hb : b = j
    · rw [hb, HypersurfaceFamily.emptyMember_hyp_self]
      exact Set.eq_empty_of_forall_notMem fun p hp => hp
    · rw [HypersurfaceFamily.emptyMember_hyp_of_ne T.F hb, hemp b hb]
      exact Set.eq_empty_of_forall_notMem fun p hp => hp
  have hV : (R.fam (restrictedTripleModOf T j hS hSeq)
      (bmoClass_restrictedTripleModOf T j hT hS hSeq)).seqOn (hS.preimageOpens U)
        (hS.isCompact_closure_preimageOpens U hU) =
      (R.fam _ hT').seqOn (hS.preimageOpens U) (hS.isCompact_closure_preimageOpens U hU) :=
    hRi (restrictedTripleModOf T j hS hSeq) (HypersurfaceFamily.empty _)
      HypersurfaceFamily.isSnc_empty OrderEmbedding.ofIsEmpty (fun i => i.elim) he'
      (bmoClass_restrictedTripleModOf T j hT hS hSeq) hT' (hS.preimageOpens U)
      (hS.isCompact_closure_preimageOpens U hU)
  rw [hV]
  exact AnalyticManifold.BlowUpSequence.eraseEmpty_of_noEmptyCenters _
    (AnalyticManifold.BlowUpSequence.noEmptyCenters_pushforwardRestrict hS U _
        ((R.fam _ hT').noEmptyCenters _ _))

/-- **The modified first step commutes with a global hypersurface of codimension one** ([Kol07,
Theorem 103 (3)] and [Kol07, Theorem 103, Step 2.4]; [Wlo09, §7.1]): on `(M, 𝓘 ⊇ I_S, ∅)` with `S` a
closed hypersurface and `J := 𝓘|_S` nonzero everywhere, the value of `stepBFunctor R …` on `U` is
the per-open push-forward of the value of `R` on `(S, J, ∅)` at `U_S`: the functor's value is the
local functor's (`stepBFunctor_fam_eq`: `S` is a global hypersurface of maximal contact), and
`BO.hfStep2FamOn_eq_pushforwardRestrict_of_global` applies at the datum `stepBData`, Step 2.2 at
the single member `S` of `∅ + S` being the modified core (`greatestIdx_eq`,
`HFamData.fam_seqOn_congr`), which is the push-forward
(`coreModOn_eq_pushforwardRestrict_of_isNonzeroEverywhere`). -/
theorem stepBFunctor_seqOn_eq_pushforwardRestrict_of_global {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere) (hle : hS.idealSheaf ≤ I)
    (hJ : (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere)
    (hT : AnalyticTriple.BOClass 1
      (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ :
        AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M))
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((stepBFunctor R hRo hRc hRi bmo₁).fam _ hT).seqOn U hU =
      AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
        ((R.fam _ (AnalyticTriple.bmoClass_one_empty _ hJ)).seqOn (hS.preimageOpens U)
          (hS.isCompact_closure_preimageOpens U hU)) := by
  have hT' := AnalyticTriple.bmoClass_one_empty (ψ₀ := ContinuousLinearEquiv.refl 𝕜
    (Fin (n - 1) → 𝕜)) _ hJ
  -- the triple `(M, 𝓘, ∅)` is in the local class, with `H := S`
  have hle0 : hS.idealSheaf ≤ I.iteratedDeriv (1 - 1) := by
    rw [Nat.sub_self, IdealSheaf.iteratedDeriv_zero]
    exact hle
  set T₀ : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M :=
    ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ with hT₀
  have hL : AnalyticTriple.LocalMCClass 1 T₀ := ⟨hT, S, hS, hle0⟩
  -- the functor's value is the local functor's (no cover descent: `S` is global); Step 2.2 at the
  -- single member `S` of `∅ + S` is the modified core, the tuning being the identity at mark `1`
  set d := stepBData R hRo hRc hRi bmo₁ with hd
  rw [stepBFunctor_fam_eq R hRo hRc hRi bmo₁ T₀ hL, stepBLocalFunctorFam_fam_seqOn]
  refine BO.hfStep2FamOn_eq_pushforwardRestrict_of_global d hS I hI hle hL (R.fam _ hT')
    (fun hge hsnc hX W hW => ?_) U hU
  exact (HFamData.fam_seqOn_congr d.hf (AnalyticTriple.tuned_one _)
    (AnalyticTriple.boClass_tuned hX.1) hX.1 (greatestIdx (stepHClass_tuned hX))
    (toLex (Sum.inr PUnit.unit)) (heq_of_eq (greatestIdx_eq _ fun k => le_toLex_inr k)) W hW).trans
    (coreModOn_eq_pushforwardRestrict_of_isNonzeroEverywhere R hRi _ _ ⟨hX.1.1, hX.1.2.2⟩ hS rfl
      (fun k hk => absurd (HypersurfaceFamily.eq_toLex_inr_of_append_empty S k) hk) hJ W hW)

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  (hcomp : NonmonomialComap.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))
  (hid : NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-- **The modified functor at dimension `n` commutes with closed embeddings of empty divisor in
codimension one** ([Wlo09, §7.1]; [Kol07, 108]; the predicate
`CommutesWithClosedEmbeddingsOfEmptyDivisorFam` at `s := 1`, through the functor one dimension down
`R`): for `(M, 𝓘 ⊇ I_S, ∅)` with `S` a closed hypersurface and `J = 𝓘|_S`, the value of
`modFunctor R …` on `U` is the push-forward of the value of `R` on `U_S`. The order of `𝓘` is at
most `1` by `I_S ≤ 𝓘` (`ord_le_one_of_idealSheaf_le`, `boClass_one_of_idealSheaf_le`), the rounds
and the monomial phase are idle (`stepACFunctor_seqOn_eq_nil`), so the composite is the value of
the modified first step (`composeOn_eq_of_firstList_eq_nil`), which is the push-forward
(`stepBFunctor_seqOn_eq_pushforwardRestrict_of_global`). -/
theorem modFunctor_commutesWithClosedEmbeddings_one :
    (modFunctor R hRo hRc hRi bmo₁ bo hcomp hid).CommutesWithClosedEmbeddingsOfEmptyDivisorFam
      (s := 1) R := by
  intro M S hS I hI J hJ hle hJI hT _ U hU
  subst hJI
  have hT₂ := AnalyticTriple.boClass_one_of_idealSheaf_le hS I hI hle
  change AnalyticFamilyFunctor.composeOn (stepACFunctor bo hcomp hid)
    (stepBFunctor R hRo hRc hRi bmo₁) 1
    (fun T hT U hU => stepACFunctor_isOfOrderGe T hT bo hcomp hid U hU)
    (fun T hT U hU => boClass_one_induced_stepACFunctor T hT bo hcomp hid U hU) _ hT U hU = _
  refine (AnalyticFamilyFunctor.composeOn_eq_of_firstList_eq_nil _ _ _ _ _
    (stepBFunctor_commutesWithLocalIsos R hRo hRc hRi bmo₁)
    (AnalyticFamilyFunctor.boClass_classPullbackClosed 1) _ hT hT₂ U hU
    (stepACFunctor_seqOn_eq_nil bo hcomp hid I hI (hS.ord_le_one_of_idealSheaf_le I hle) _
      _)).trans ?_
  exact stepBFunctor_seqOn_eq_pushforwardRestrict_of_global R hRo hRc hRi bmo₁ hS I hI hle hJ hT₂
    U hU

end Hironaka.Manifold.BMOmod

namespace Hironaka.Manifold.BMOmod

variable (𝕜 : Type) [RCLike 𝕜] (bo : ∀ n d : ℕ, BOanFam.{u} 𝕜 n d)
  (bmo : ∀ n : ℕ, BMOanFam.{u} 𝕜 n 1)
  (hid : ∀ n : ℕ, NonmonomialTransformIdentity.{u} (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)))

/-- **Every level of the tower commutes with closed embeddings of empty divisor in codimension one**
([Wlo09, §7.1], the passage to the hypersurface `V(u₁)`; [Kol07, 34.3], [Kol07, 108]; the predicate
`CommutesWithClosedEmbeddingsOfEmptyDivisorFam` at `s := 1`): the level-`n` structure commutes
through the level-`(n − 1)` structure. Level `n + 1` is
`modFunctor_commutesWithClosedEmbeddings_one` with `R :=` the level-`n` functor (`modTower_succ`, by
definition); level `0` is the empty list on both sides (`S = ∅` in dimension `0`;
`pushforwardRestrict_nil`). Stated for `BMOmodFamOfInput_of_hid`, generic in the transform identity
`hid`, and with no hypothesis on `bo` and `bmo`, the argument being the construction's own descent.
-/
theorem BMOmodFamOfInput_of_hid_commutesWithClosedEmbeddings_one (n : ℕ) :
    (BMOmodFamOfInput_of_hid 𝕜 bo bmo hid n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam
      (s := 1) (BMOmodFamOfInput_of_hid 𝕜 bo bmo hid (n - 1)).functor := by
  cases n with
  | zero =>
    intro M S hS I hI J hJ hle hJI hT hT' U hU
    change ((AnalyticFamilyFunctor.nilFamilyFunctor _ _).fam _ hT).seqOn U hU =
      AnalyticManifold.BlowUpSequence.pushforwardRestrict hS U
        (((AnalyticFamilyFunctor.nilFamilyFunctor _ _).fam _ hT').seqOn _ _)
    rw [AnalyticFamilyFunctor.nilFamilyFunctor_seqOn, AnalyticFamilyFunctor.nilFamilyFunctor_seqOn,
      AnalyticManifold.BlowUpSequence.pushforwardRestrict_nil]
  | succ n =>
    exact modFunctor_commutesWithClosedEmbeddings_one (modTower bo bmo hid n).functor
      (modTower bo bmo hid n).isOfOrderGe (modTower bo bmo hid n).commutesWithLocalIsos
      (modTower bo bmo hid n).indifferentToEmptyMembers (bmo n) (bo (n + 1))
      nonmonomialComap_inhabitant (hid (n + 1))

end Hironaka.Manifold.BMOmod

end
