/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.ClosedEmbedding
public import Hironaka.Resolution.Analytic.Wlo09.PullbackFibre
public import Hironaka.Resolution.Analytic.Wlo09.FamilyExt
public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
public import Hironaka.Resolution.Analytic.Functor.PullbackUpToEmpty
public import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardOfStageIncl
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Hom
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Modified.ClauseClosedEmbedding
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The push-forward relation of the glued families along a closed embedding

Kollár's commutation of a blow-up sequence functor with closed embeddings over the compact sets,
for the glued families: for family functors `B` in dimension `n` and `B'` in dimension `n − s` on
the standard models with `B(M, I, ∅) = τ_* B'(S, I|_S, ∅)` over every relatively compact open
(`AnalyticFamilyFunctor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam`, [Kol07, 34.3]) and `B'`
commuting with local analytic isomorphisms, the succession of the glued family of `B(M, I, ∅)` over
the neighbourhood of a compact `K ⊆ M` is the push-forward along a closed embedding `τ : N → M`
with image `S` of the succession of the glued family of `B'(N, τ^*I, ∅)` over the neighbourhood of
a compact `K' ⊆ N` with `τ(U_{K'}) ⊆ U_K`, up to blow-ups whose centres lie outside the part over
`τ(U_{K'})` (`FiniteSuccession.IsPushforwardUpToEmptyAlong`):
`isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily`.

The argument: with `L` the value of `B'` on the trace `U_S` of `U_K` on the bundled submanifold `S`,
the value of `B` on `U_K` is the push-forward of `L` from the stage `(U_K, S ∩ U_K, e)`
(`IsClosedSubmanifold.restrictStageOf`), whose stages receive the inclusions
`PushforwardStage.inclStage`; the value of `B'` on `U_{K'}` is, through the identification
`e : N ≃ S` over `τ`, the pull-back of `L` up to empty blow-ups
(`CompatibleFamily.isPullbackUpToEmptyAlong_seqOn`), with lifts `f_k` bijective on the fibres
(`bijOn_fiber_of_isPullbackUpToEmptyAlong_clauses`). The embeddings of the relation are the
inclusions after the lifts; the fibre bijections make them embeddings with image the part of the
strict transform over `τ(U_{K'})`, and the centres of the push-forward are the images of the
centres of `L`.

For an empty `N` the two successions are empty (`length_eq_zero_of_isEmpty`,
`eq_nil_of_isEmpty`) and the relation holds for any model space of `N`
(`isPushforwardUpToEmptyAlong_seqOn_of_isEmpty`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### Successions over an empty manifold -/

section Empty

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {X : AnalyticManifold.{u} 𝕜 E} [IsEmpty X]

/-- A finite succession over an empty manifold with no empty centre has length `0`: every stage is
empty, so every centre is the unit ideal sheaf. -/
theorem length_eq_zero_of_isEmpty (S : FiniteSuccession X) (h : S.NoEmptyCenters) :
    S.length = 0 := by
  by_contra hne
  refine h ⟨0, Nat.pos_of_ne_zero hne⟩ ?_
  refine IdealSheaf.ext fun x => ?_
  exact (IsEmpty.false (S.stageMap _ x)).elim

/-- A list of centres on an empty manifold with no empty centre is the empty list. -/
theorem eq_nil_of_isEmpty {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} (L : BlowUpSequence ψ₀ X)
    (h : L.NoEmptyCenters) : L = BlowUpSequence.nil X := by
  cases L with
  | nil => rfl
  | cons hY rest =>
    exfalso
    exact ((BlowUpSequence.noEmptyCenters_cons_iff hY rest).mp h).1 (Set.eq_empty_of_isEmpty _)

end Empty

/-! ### The push-forward relation of the glued families -/

section Pushforward

variable {𝕜 : Type} [RCLike 𝕜] {n s : ℕ}
  {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)},
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M → Prop}
  {Dom' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M' → Prop}
  {B : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Dom}
  {B' : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom'}
  (hBB' : B.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B')
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

include hBB' in
/-- **The push-forward relation for an empty `N`**: both successions are empty, and the relation
holds with the restriction of `τ` as the only embedding. The class `Dom'` is required only at the
pull-back of `I` to the bundled submanifold `τ(N)`. -/
theorem isPushforwardUpToEmptyAlong_seqOn_of_isEmpty_of_dom {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {N : AnalyticManifold.{u} 𝕜 E'} [IsEmpty N]
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (I : IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (hT : Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
    (hT'S : ∀ h : (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere,
      Dom' ⟨I.pullback hS.inclusionMap hS.inclusionMap.contMDiff, h,
        HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    {U' : Opens N} (R : FiniteSuccession (N.restrict U')) (hR : R.NoEmptyCenters)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((B.fam _ hT).seqOn U hU).toSuccession.IsPushforwardUpToEmptyAlong R τ := by
  have : IsEmpty (N.restrict U') := ⟨fun p => IsEmpty.false p.1⟩
  have : IsEmpty hS.toAnalyticManifold := ⟨fun p => by
    obtain ⟨x, -⟩ := (p : Set.range τ).2
    exact IsEmpty.false x⟩
  have : IsEmpty (hS.toAnalyticManifold.restrict (hS.preimageOpens U)) :=
    ⟨fun p => IsEmpty.false p.1⟩
  set J_S : IdealSheaf hS.toAnalyticManifold := I.pullback hS.inclusionMap hS.inclusionMap.contMDiff
  have hJ_S : J_S.IsNonzeroEverywhere := fun x => isEmptyElim x
  have hSeq := hBB' hS I hI J_S hJ_S (IdealSheaf.le_def.mpr hle) rfl hT (hT'S hJ_S) U hU
  rw [eq_nil_of_isEmpty _ ((B'.fam _ (hT'S hJ_S)).noEmptyCenters _ _),
    BlowUpSequence.pushforwardRestrict_nil] at hSeq
  have hR0 : R.length = 0 := length_eq_zero_of_isEmpty R hR
  have hS0 : ((B.fam _ hT).seqOn U hU).toSuccession.length = 0 := by
    rw [hSeq]
    rfl
  refine FiniteSuccession.isPushforwardUpToEmptyAlong_iff.mpr
    ⟨fun _ => 0, fun k => ⟨fun p => (IsEmpty.false (R.stageMap _ p)).elim,
      fun p => (IsEmpty.false (R.stageMap _ p)).elim⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext
    simp [hR0]
  · exact fun k => (Nat.not_lt_zero k.1 (hS0 ▸ k.2)).elim
  · intro k
    have : IsEmpty (R.stage 0) := ⟨fun p => IsEmpty.false (R.stageMap _ p)⟩
    exact Topology.IsEmbedding.of_subsingleton _
  · intro k q hq _
    have : IsEmpty (R.stage 0) := ⟨fun p => IsEmpty.false (R.stageMap _ p)⟩
    rw [Set.range_eq_empty, closure_empty] at hq
    exact hq.elim
  · exact fun k p => (IsEmpty.false (R.stageMap _ p)).elim
  · exact fun k => (Nat.not_lt_zero k.1 (hS0 ▸ k.2)).elim
  · exact fun k => (Nat.not_lt_zero k.1 (hS0 ▸ k.2)).elim
  · exact fun k => (Nat.not_lt_zero k.1 (hS0 ▸ k.2)).elim
  · exact fun k => (Nat.not_lt_zero k.1 (hS0 ▸ k.2)).elim

variable (hDom' : ∀ {N' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)} (J' : IdealSheaf N')
  (hJ' : J'.IsNonzeroEverywhere),
  Dom' ⟨J', hJ', HypersurfaceFamily.empty N', HypersurfaceFamily.isSnc_empty⟩)

include hBB' hDom' in
/-- **The push-forward relation for an empty `N`**: both successions are empty, and the relation
holds with the restriction of `τ` as the only embedding
(`isPushforwardUpToEmptyAlong_seqOn_of_isEmpty_of_dom`, for a class `Dom'` containing every
triple with nonzero stalks and empty boundary). -/
theorem isPushforwardUpToEmptyAlong_seqOn_of_isEmpty {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {N : AnalyticManifold.{u} 𝕜 E'} [IsEmpty N]
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (I : IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (hT : Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
    {U' : Opens N} (R : FiniteSuccession (N.restrict U')) (hR : R.NoEmptyCenters)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    ((B.fam _ hT).seqOn U hU).toSuccession.IsPushforwardUpToEmptyAlong R τ :=
  isPushforwardUpToEmptyAlong_seqOn_of_isEmpty_of_dom hBB' τ hS I hI hle hT
    (fun h => hDom' _ h) R hR U hU

variable (hB' : B'.CommutesWithLocalIsos)

include hBB' hB' in
/-- **The succession of the glued family of `B(M, I, ∅)` over `U_K` is the push-forward along the
closed embedding `τ : N → M` of the succession of the glued family of `B'(N, τ^*I, ∅)` over
`U_{K'}`**, up to blow-ups whose centres lie outside the part over `τ(U_{K'})`
([Kol07, 34.3] over the compact sets), for `τ(U_{K'}) ⊆ U_K`, `I ⊇ I_S` with `S = τ(N)`, and `N`
identified with the bundled `S` by `e` over `τ`. The value of `B` on `U_K` is the push-forward of
the value `L` of `B'` on the trace `U_S` from the stage `(U_K, S ∩ U_K, e)`; the value of `B'` on
`U_{K'}` is the pull-back of `L` along `e` up to empty blow-ups; the embeddings are the stage
inclusions of the push-forward after the lifts of the pull-back, which are bijective on the fibres
over `U_{K'}`. The class `Dom'` is required at `J` and at the pull-back of `I` to the bundled
submanifold `τ(N)`. -/
theorem isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily_of_dom
    {N : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (τ : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (I : IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hJI : J = I.pullback τ τ.contMDiff)
    (hT : Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
    (hT' : Dom' ⟨J, hJ, HypersurfaceFamily.empty N, HypersurfaceFamily.isSnc_empty⟩)
    (hT'S : ∀ h : (I.pullback hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere,
      Dom' ⟨I.pullback hS.inclusionMap hS.inclusionMap.contMDiff, h,
        HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩)
    (K' : Compacts N) (K : Compacts M)
    (hK : ⇑τ '' ((B'.fam _ hT').toExtensionCompatibleFamily.nhd K' : Set N) ⊆
      (B.fam _ hT).toExtensionCompatibleFamily.nhd K) :
    ((B.fam _ hT).toExtensionCompatibleFamily.seq K).IsPushforwardUpToEmptyAlong
      ((B'.fam _ hT').toExtensionCompatibleFamily.seq K') τ := by
  -- the opens
  set U : Opens M := (B.fam _ hT).toExtensionCompatibleFamily.nhd K with hUdef
  set U' : Opens N := (B'.fam _ hT').toExtensionCompatibleFamily.nhd K' with hU'def
  have hU : IsCompact (closure (U : Set M)) := isCompact_closure_relCompactOpen _ _
  have hU' : IsCompact (closure (U' : Set N)) := isCompact_closure_relCompactOpen _ _
  change ((B.fam _ hT).seqOn U hU).toSuccession.IsPushforwardUpToEmptyAlong
    ((B'.fam _ hT').seqOn U' hU').toSuccession τ
  -- the identification `e` as an analytic map, and the ideal sheaf on the bundled submanifold
  let eA : AnalyticMap N hS.toAnalyticManifold := ⟨e, e.contMDiff⟩
  have heA : IsLocalDiffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) ω eA :=
    e.isLocalDiffeomorph
  set J_S : IdealSheaf hS.toAnalyticManifold :=
    I.pullback hS.inclusionMap hS.inclusionMap.contMDiff with hJ_Sdef
  have hτe : ⇑τ = ⇑hS.inclusionMap ∘ ⇑e := funext fun x => (he x).symm
  have hJeq : J = J_S.pullback ⇑e e.contMDiff := by
    rw [hJI, hJ_Sdef, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ hτe
  have hJ_S : J_S.IsNonzeroEverywhere := by
    have h1 : (J_S.pullbackDiffeomorph e).IsNonzeroEverywhere := by
      change (J_S.pullback ⇑e e.contMDiff).IsNonzeroEverywhere
      rw [← hJeq]
      exact hJ
    exact (IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff e J_S).mp h1
  have hT'S := hT'S hJ_S
  have hpb : (⟨J, hJ, HypersurfaceFamily.empty N, HypersurfaceFamily.isSnc_empty⟩ :
      AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) N).IsPullbackOf
      ⟨J_S, hJ_S, HypersurfaceFamily.empty _, HypersurfaceFamily.isSnc_empty⟩ eA :=
    ⟨hJeq, (HypersurfaceFamily.empty_comap ⇑eA).symm⟩
  -- the trace of `U` on the bundled submanifold, which contains the image of `U'`
  set U_S : Opens hS.toAnalyticManifold := hS.preimageOpens U with hU_Sdef
  have hU_S : IsCompact (closure (U_S : Set hS.toAnalyticManifold)) :=
    hS.isCompact_closure_preimageOpens U hU
  have heU : ⇑eA '' (U' : Set N) ⊆ U_S := by
    rintro _ ⟨y, hy, rfl⟩
    change (e y : Set.range τ).1 ∈ U
    rw [he y]
    exact hK ⟨y, hy, rfl⟩
  set L := (B'.fam _ hT'S).seqOn U_S hU_S with hLdef
  -- the value on `U'` is the pull-back of `L` up to empty blow-ups
  have hR : ((B'.fam _ hT').seqOn U' hU').toSuccession.IsPullbackUpToEmptyAlong
      L.toSuccession eA :=
    CompatibleFamily.isPullbackUpToEmptyAlong_seqOn (B'.fam _ hT'S) (B'.fam _ hT') eA heA U' hU'
      (hB' _ _ eA heA hpb hT'S hT' U' hU') U_S hU_S heU
  -- the value on `U` is the push-forward of `L` from the stage of `U`
  have hSeq : (B.fam _ hT).seqOn U hU = BlowUpSequence.pushforwardRestrict hS U L :=
    hBB' hS I hI J_S hJ_S (IdealSheaf.le_def.mpr hle) rfl hT hT'S U hU
  set P : PushforwardStage (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) s
    (hS.toAnalyticManifold.restrict U_S) := hS.restrictStageOf U U_S rfl with hPdef
  have hSsucc : ((B.fam _ hT).seqOn U hU).toSuccession =
      PushforwardStage.pushforwardOfStage P L.toSuccession := by
    rw [hSeq]
    exact BlowUpSequence.toSuccession_pushforwardAux P L ((B'.fam _ hT'S).noEmptyCenters U_S hU_S)
  rw [hSsucc]
  set T := L.toSuccession with hTdef
  set R := ((B'.fam _ hT').seqOn U' hU').toSuccession with hRdef
  obtain ⟨blk, f, h0, hl, hs, hld, hov, hm, hcj, hcn⟩ :=
    FiniteSuccession.isPullbackUpToEmptyAlong_iff.mp hR
  -- the lifts are bijective on the fibres
  have hbij : ∀ (k : Fin (T.length + 1)) (y : N.restrict U'),
      BijOn (f k) (FiniteSuccession.fiberR R (blk k) y) (FiniteSuccession.fiberS T eA k y) :=
    fun k y => FiniteSuccession.bijOn_fiber_of_isPullbackUpToEmptyAlong_clauses blk f h0 hs hld hov
      hm hcj hcn k y
  -- a point of a stage of `L` over `τ(U')` is a lift
  have hmem : ∀ (k : Fin (T.length + 1)) (p : T.stage k),
      M.inclusion U (P.incl (T.stageMap k p)) ∈ ⇑τ '' (U' : Set N) → p ∈ Set.range (f k) := by
    intro k p hp
    obtain ⟨y, hy, hyp⟩ := hp
    have hy' : (e y : Set.range τ).1 = ((T.stageMap k p).1 : Set.range τ).1 := by
      rw [he y]
      exact hyp
    have hfib : p ∈ FiniteSuccession.fiberS T eA k ⟨y, hy⟩ := (Subtype.ext hy').symm
    obtain ⟨r, -, hr⟩ := (hbij k ⟨y, hy⟩).surjOn hfib
    exact ⟨r, hr⟩
  -- the lifts are injective
  have hinj : ∀ k, Function.Injective (f k) := by
    intro k p p' hpp'
    have h1 := hov k p
    have h2 := hov k p'
    rw [hpp'] at h1
    have h3 : R.stageMap (blk k) p' = R.stageMap (blk k) p :=
      Subtype.ext (e.injective (h2.symm.trans h1))
    exact (hbij k (R.stageMap (blk k) p)).injOn rfl h3 hpp'
  refine FiniteSuccession.isPushforwardUpToEmptyAlong_iff.mpr
    ⟨blk, fun k => (PushforwardStage.inclStage P T k).comp (f k), h0, hl, hs, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · -- embeddings: a closed embedding after an open embedding
    intro k
    exact (PushforwardStage.isClosedEmbedding_inclStage P T k).isEmbedding.comp
      (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (f k).contMDiff.continuous
        (hinj k) (hld k).isOpenMap).isEmbedding
  · -- the range is closed in the part over `τ(U')`
    intro k q hq hqU
    have hcl : q ∈ Set.range (PushforwardStage.inclStage P T k) :=
      (PushforwardStage.isClosedEmbedding_inclStage P T k).isClosed_range.closure_subset_iff.mpr
        (Set.range_comp_subset_range (f k) (PushforwardStage.inclStage P T k)) hq
    obtain ⟨p, rfl⟩ := hcl
    erw [PushforwardStage.stageMap_inclStage'] at hqU
    obtain ⟨r, hr⟩ := hmem k p hqU
    exact ⟨r, congrArg (PushforwardStage.inclStage P T k) hr⟩
  · -- over `τ`
    intro k p
    change M.inclusion U ((PushforwardStage.pushforwardOfStage P T).stageMap k
      (PushforwardStage.inclStage P T k (f k p))) = τ (N.inclusion U' (R.stageMap (blk k) p))
    erw [PushforwardStage.stageMap_inclStage']
    rw [← he]
    exact congrArg (fun z : hS.toAnalyticManifold => (z : Set.range τ).1) (hov k p)
  · -- the blow-downs
    intro (k : Fin T.length) hle' p
    exact (PushforwardStage.inclStage_map P T k (f k.succ p)).symm.trans
      (congrArg (PushforwardStage.inclStage P T k.castSucc) (hm k hle' p))
  · -- the centres at a jump
    intro (k : Fin T.length) ha hj
    have ha' : (blk k.castSucc : ℕ) < R.length := ha
    have h1 := PushforwardStage.support_center_pushforwardOfStage P T k
    have h2 : ⇑(f k.castSucc) ⁻¹' (⇑(PushforwardStage.inclStage P T k.castSucc) ⁻¹'
        (⇑(PushforwardStage.inclStage P T k.castSucc) '' (T.center k).support)) =
        ⇑(f k.castSucc) ⁻¹' (T.center k).support :=
      congrArg _
        ((PushforwardStage.isClosedEmbedding_inclStage P T k.castSucc).injective.preimage_image _)
    have h3 : ⇑(f k.castSucc) ⁻¹' (T.center k).support =
        (R.centerAt (blk k.castSucc) ha').support := by
      rw [hcj k ha' hj, _root_.Manifold.IdealSheaf.support_pullback]
    exact (congrArg
      (fun Z => ⇑(f k.castSucc) ⁻¹' (⇑(PushforwardStage.inclStage P T k.castSucc) ⁻¹' Z)) h1).trans
      (h2.trans h3)
  · -- the centres at a non-jump
    intro (k : Fin T.length) hj
    have h1 := PushforwardStage.support_center_pushforwardOfStage P T k
    have h2 : ⇑(f k.castSucc) ⁻¹' (⇑(PushforwardStage.inclStage P T k.castSucc) ⁻¹'
        (⇑(PushforwardStage.inclStage P T k.castSucc) '' (T.center k).support)) =
        ⇑(f k.castSucc) ⁻¹' (T.center k).support :=
      congrArg _
        ((PushforwardStage.isClosedEmbedding_inclStage P T k.castSucc).injective.preimage_image _)
    have h3 : ⇑(f k.castSucc) ⁻¹' (T.center k).support = ∅ := by
      have h := hcn k hj
      rwa [_root_.Manifold.IdealSheaf.support_pullback] at h
    exact (congrArg
      (fun Z => ⇑(f k.castSucc) ⁻¹' (⇑(PushforwardStage.inclStage P T k.castSucc) ⁻¹' Z)) h1).trans
      (h2.trans h3)
  · -- the centre points over `τ(U')` lie in the range
    intro (k : Fin T.length) q hq hqU
    erw [PushforwardStage.support_center_pushforwardOfStage] at hq
    obtain ⟨p, -, rfl⟩ := hq
    erw [PushforwardStage.stageMap_inclStage'] at hqU
    obtain ⟨r, hr⟩ := hmem k.castSucc p hqU
    exact ⟨r, congrArg (PushforwardStage.inclStage P T k.castSucc) hr⟩

include hBB' hB' hDom' in
/-- `isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily_of_dom` for a class `Dom'`
containing every triple with nonzero stalks and empty boundary. -/
theorem isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily
    {N : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)}
    (τ : C^ω⟮𝓘(𝕜, Fin (n - s) → 𝕜), N; 𝓘(𝕜, Fin n → 𝕜), M⟯)
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (Set.range τ) s)
    (e : Diffeomorph 𝓘(𝕜, Fin (n - s) → 𝕜) 𝓘(𝕜, Fin (n - s) → 𝕜) N hS.toAnalyticManifold ω)
    (he : ∀ x, (e x : Set.range τ).1 = τ x)
    (I : IdealSheaf M) (hI : I.IsNonzeroEverywhere)
    (hle : ∀ x, hS.idealSheaf.stalkIdeal x ≤ I.stalkIdeal x)
    (J : IdealSheaf N) (hJ : J.IsNonzeroEverywhere) (hJI : J = I.pullback τ τ.contMDiff)
    (hT : Dom ⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩)
    (hT' : Dom' ⟨J, hJ, HypersurfaceFamily.empty N, HypersurfaceFamily.isSnc_empty⟩)
    (K' : Compacts N) (K : Compacts M)
    (hK : ⇑τ '' ((B'.fam _ hT').toExtensionCompatibleFamily.nhd K' : Set N) ⊆
      (B.fam _ hT).toExtensionCompatibleFamily.nhd K) :
    ((B.fam _ hT).toExtensionCompatibleFamily.seq K).IsPushforwardUpToEmptyAlong
      ((B'.fam _ hT').toExtensionCompatibleFamily.seq K') τ :=
  isPushforwardUpToEmptyAlong_toExtensionCompatibleFamily_of_dom hBB' hB' τ hS e he I hI hle J hJ
    hJI hT hT' (fun h => hDom' _ h) K' K hK

end Pushforward

end Hironaka.Manifold

end

end
