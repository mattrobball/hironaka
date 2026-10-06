/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductExceptionalFamily
public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionOn
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalFamilyGlue
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictInclusion
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The run's exceptional members and their restriction along an open embedding of inputs

The empty blow-up convention [Kol07, 32] and the commutation with smooth morphisms [Kol07, 34.1],
read on the family functor: for ANY open embedding `g : N → M` of admissible inputs (`T' = g⁻¹T`,
`DomBEDan` on both sides) and relatively compact opens `W' ⊆ N`, `W ⊆ M` with `g(W') ⊆ W`, the
functor's value on `T'` over `W'` is the value on `T` over `W` pulled back and cleaned of its empty
blow-ups (`BEDanFamStar.seqOn_eq_of_isAnalyticOpenEmbedding`, `LocalResolutionOn.lean`) — so the
last-stage boundary members of the run on `T'` are the members of the run on `T` of the stages
that survive over `W'`, read through the lift `liftOn` of the last stages (`pullbackLiftLast` after
the inverse of `eraseEmptyLast` and the cast `stageOfEq`), and the members of the deleted stages
are EMPTY over `W'`. For the run's members as CLOSED SUBSPACES of its local resolution
(`runMembers`, for any admissible input, and its coproduct instance `sigmaMembers`, both in
`CoproductExceptionalFamily.lean`) this module proves the identity along the open immersion
`localResolutionHomOn` of the local resolutions:

* an ORDER EMBEDDING `lab` of the stage set of the run on `T'` into that of the run on `T` — the
  `BoundaryCorr` correspondence of `Functor/EraseEmptyBoundary.lean` composed along
  `eraseEmptyLast` and `stageOfEq`, then `totalTransformSeqFrom_last_pullbackLiftLast` along
  `pullbackLiftLast`;
* the inverse image along `localResolutionHomOn` of the member of label `lab k` IS the member `k`
  of the run on `T'` — the square `homOfPullbackEq_comp_toAnalyticSpaceι` (the closed inclusions
  commute with the lift), the bridge `comap_ofManifoldHom_eq_pullback` and
  `comap_idealSheaf_of_isLocalDiffeomorph` (the ideal sheaf of a preimage hypersurface);
* the inverse image of every member OFF the range of `lab` is the unit ideal `⊤` (the empty
  subspace; the deleted blow-ups have empty centres over `W'`).

The summand inclusions of a datum's coproduct ambient into the COMMON datum of two adjacent levels
of the exhaustion use it (the label maps of the common run, `CoproductSumData.lean`); at the
summand inclusion `sigmaMk i` of a piece's ambient into a datum's coproduct ambient it says that
within one datum the pieces share the single run's stage set as their LABEL SET.
`hbed : bed.IsEmbeddedDesing` is the only hypothesis. Not in the sources beyond the convention
cited; bookkeeping.
-/

public section

noncomputable section

open TopologicalSpace Set AnalyticManifold BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

/-- The cast `stageOfEq` along `e.symm`, inverted, is the cast along `e` (both are the
identity). -/
theorem _root_.AnalyticManifold.BlowUpSequence.stageOfEq_symm_symm {n : ℕ}
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    {L₁ L₂ : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} (e : L₁ = L₂) :
    ⇑(stageOfEq e.symm).symm = ⇑(stageOfEq e) := by
  subst e
  rw [stageOfEq_rfl]
  funext x
  rfl

/-- The inverse image of the unit ideal — the empty subspace — is the unit ideal. -/
theorem comap_top_closedSubspace {Y Z : AnalyticSpace.{u} 𝕜}
    (f : Y ⟶ Z) :
    (⊤ : AnalyticSpace.ClosedSubspace Z).comap f = ⊤ := by
  apply IdealSheaf.ext
  intro x
  unfold AnalyticSpace.ClosedSubspace.comap
  rw [AnalyticSpace.QuotientSpace.stalkIdeal_comap]
  change Ideal.map _
      (IdealSheaf.stalkIdeal (⊤ : AnalyticSpace.ClosedSubspace Z) _) =
    IdealSheaf.stalkIdeal (⊤ : AnalyticSpace.ClosedSubspace Y) x
  rw [IdealSheaf.stalkIdeal_top, IdealSheaf.stalkIdeal_top]
  exact Ideal.map_top _

namespace BEDanFamStar

open _root_.Manifold

variable (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M))) (hbed : bed.IsEmbeddedDesing)

variable {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N) (hT' : DomBEDan 𝕜 T')
  (g : AnalyticMap N M) (hg : IsAnalyticOpenEmbedding g)
      (hpb : T'.IsPullbackOf T g)
  (W' : Opens N) (hW' : IsCompact (closure (W' : Set N))) (hle : ⇑g '' (W' : Set N) ⊆ (W : Set M))

/-- **The boundary members of the run on `T'` are the preimages along the lift of the members of
the run on `T`** ([Kol07, 32], [Kol07, 34.1]), through an ORDER EMBEDDING of the stage sets, the
members off its range pulling back to `∅` — the `BoundaryCorr` correspondence composed along
`eraseEmptyLast` (`boundaryCorr_eraseEmpty_self`) and the cast (`boundaryCorr_of_eq`), read
through `totalTransformSeqFrom_last_pullbackLiftLast`. -/
theorem exists_orderEmbedding_hyp_runFamily_eq_preimage_liftOn :
    ∃ lab : (bed.runFamily T' hT' W' hW').ι ↪o (bed.runFamily T hT W hW).ι,
      (∀ k, (bed.runFamily T' hT' W' hW').hyp k =
          bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed ⁻¹'
            (bed.runFamily T hT W hW).hyp (lab k)) ∧
      ∀ σ, σ ∉ Set.range lab →
        bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed ⁻¹'
          (bed.runFamily T hT W hW).hyp σ = ∅ := by
  set R := bed.seqOn T hT W hW with hR
  set ρ := AnalyticMap.restrictMap g W' W hle with hρdef
  have hρ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ρ :=
    AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle
  have hγ : bed.seqOn T' hT' W' hW' = (R.pullback ρ hρ).eraseEmpty :=
    bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle hbed
  have h1 := boundaryCorr_eraseEmpty_self (R.pullback ρ hρ)
    (HypersurfaceFamily.empty (N.restrict W')) (fun j => PEmpty.elim j)
  have h2 := boundaryCorr_of_eq hγ.symm (HypersurfaceFamily.empty (N.restrict W')) h1
  have hP : (R.pullback ρ hρ).toSuccession.totalTransformSeqFrom
        (HypersurfaceFamily.empty (N.restrict W')) (Fin.last _) =
      HypersurfaceFamily.comap ⇑(R.pullbackLiftLast ρ hρ)
        (R.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (M.restrict W))
          (Fin.last _)) := by
    have := totalTransformSeqFrom_last_pullbackLiftLast R ρ hρ
      (HypersurfaceFamily.empty (M.restrict W))
    rwa [HypersurfaceFamily.empty_comap] at this
  have h3 : BoundaryCorr ((R.pullback ρ hρ).eraseEmptyLast.trans (stageOfEq hγ.symm))
      (HypersurfaceFamily.comap ⇑(R.pullbackLiftLast ρ hρ)
        (R.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (M.restrict W))
          (Fin.last _)))
      ((bed.seqOn T' hT' W' hW').toSuccession.totalTransformSeqFrom
        (HypersurfaceFamily.empty (N.restrict W')) (Fin.last _))
      (fun j => PEmpty.elim j)
      ((bed.seqOn T' hT' W' hW').toSuccession.originalIdx
        (HypersurfaceFamily.empty (N.restrict W')) (Fin.last _)) :=
    BoundaryCorr.congr hP rfl (fun j => PEmpty.elim j) (fun j => HEq.rfl) h2
  obtain ⟨e', he1, he2, -⟩ := h3
  have hfun : ⇑(bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) =
      ⇑(R.pullbackLiftLast ρ hρ) ∘
        ⇑((R.pullback ρ hρ).eraseEmptyLast.trans (stageOfEq hγ.symm)).symm := by
    funext x
    change (R.pullbackLiftLast ρ hρ) ((R.pullback ρ hρ).eraseEmptyLast.symm
        (stageOfEq hγ x)) =
      (R.pullbackLiftLast ρ hρ) ((R.pullback ρ hρ).eraseEmptyLast.symm
        ((stageOfEq hγ.symm).symm x))
    rw [stageOfEq_symm_symm]
  refine ⟨e', fun k => ?_, fun σ hσ => ?_⟩
  · refine ((he1 k).symm.trans ?_)
    rw [hfun, Set.preimage_comp]
    rfl
  · rw [hfun, Set.preimage_comp]
    have h0 : ⇑(R.pullbackLiftLast ρ hρ) ⁻¹' (bed.runFamily T hT W hW).hyp σ = ∅ := he2 σ hσ
    rw [h0, Set.preimage_empty]

/-- **The inverse image of a member of the run on `T` along `localResolutionHomOn` is the trace of
the preimage hypersurface along the lift** — the square
`homOfPullbackEq_comp_toAnalyticSpaceι`, the bridge `comap_ofManifoldHom_eq_pullback` and
`comap_idealSheaf_of_isLocalDiffeomorph`. -/
theorem comap_localResolutionHomOn_runMembers (σ : (bed.runFamily T hT W hW).ι) :
    AnalyticSpace.QuotientSpace.comap
        (bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).1
        (bed.runMembers T hT W hW hbed σ) =
      AnalyticSpace.ClosedSubspace.comap
        (X := AnalyticSpace.toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) _)
        ((bed.isClosedSubmanifold_runFamily T hT W hW hbed σ).preimage_of_isLocalDiffeomorph
          (bed.isLocalDiffeomorph_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)).idealSheaf
        (IdealSheaf.toAnalyticSpaceι (bed.lastIdealOn T' hT' W' hW')) := by
  have hres : bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed =
      IdealSheaf.homOfPullbackEq _ _
        (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) := rfl
  change (AnalyticSpace.ClosedSubspace.comap _ _).comap
    (bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) = _
  refine (AnalyticSpace.ClosedSubspace.comap_comp_hom
    (X := bed.localResolutionOn T' hT' W' hW') (Y := bed.localResolutionOn T hT W hW)
    (bed.lastIdealOn T hT W hW).toAnalyticSpaceι
    (bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) _).symm.trans ?_
  rw [hres]
  have hsq := homOfPullbackEq_comp_toAnalyticSpaceι
    (⇑(bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed))
    (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).contMDiff
    (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
  refine (congrArg
      (fun φ => ((bed.runFamily T hT W hW).toClosedSubspaces
      (bed.isClosedSubmanifold_runFamily T hT W hW hbed) σ).comap φ) hsq).trans ?_
  refine (AnalyticSpace.ClosedSubspace.comap_comp_hom _ _ _).trans ?_
  congr 1
  change AnalyticSpace.QuotientSpace.comap
      (AnalyticSpace.KLocallyRingedSpace.ofManifoldHom _ _).1
      (bed.isClosedSubmanifold_runFamily T hT W hW hbed σ).idealSheaf = _
  rw [AnalyticSpace.KLocallyRingedSpace.comap_ofManifoldHom_eq_pullback]
  exact comap_idealSheaf_of_isLocalDiffeomorph (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.isLocalDiffeomorph_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.isClosedSubmanifold_runFamily T hT W hW hbed σ)

/-- **The restriction identity of the exceptional members along an open embedding of admissible
inputs** ([Kol07, 34.1]) — an order embedding `lab` of the stage set of the run on `T'` into that
of the run on `T` such that the member of label `lab k` pulls back along `localResolutionHomOn` to
the member `k` of the run on `T'`, and every member off the range of `lab` pulls back to the unit
ideal `⊤`. The summand inclusions of the common datum of two adjacent levels of the exhaustion are
the instances that give the label maps of the common run (`CoproductSumData.lean`). -/
theorem exists_orderEmbedding_comap_localResolutionHomOn_runMembers :
    ∃ lab : (bed.runFamily T' hT' W' hW').ι ↪o (bed.runFamily T hT W hW).ι,
      (∀ k, AnalyticSpace.QuotientSpace.comap
          (bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).1
          (bed.runMembers T hT W hW hbed (lab k)) = bed.runMembers T' hT' W' hW' hbed k) ∧
      ∀ σ, σ ∉ Set.range lab →
        AnalyticSpace.QuotientSpace.comap
          (bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).1
          (bed.runMembers T hT W hW hbed σ) = ⊤ := by
  obtain ⟨lab, h1, h2⟩ :=
    bed.exists_orderEmbedding_hyp_runFamily_eq_preimage_liftOn T hT W hW hbed T' hT' g hg hpb W' hW'
      hle
  refine ⟨lab, fun k => ?_, fun σ hσ => ?_⟩
  · rw [bed.comap_localResolutionHomOn_runMembers T hT W hW hbed T' hT' g hg hpb W' hW' hle]
    change _ = AnalyticSpace.ClosedSubspace.comap
      (HypersurfaceFamily.toClosedSubspaces (bed.runFamily T' hT' W' hW') _ k) _
    congr 1
    exact IsClosedSubmanifold.idealSheaf_congr _ _ (h1 k).symm
  · rw [bed.comap_localResolutionHomOn_runMembers T hT W hW hbed T' hT' g hg hpb W' hW' hle,
      IsClosedSubmanifold.idealSheaf_eq_top_of_eq_empty _ (h2 σ hσ)]
    exact comap_top_closedSubspace _

section Sync

variable (g₁ g₂ : AnalyticMap N M) (hg₁ : IsAnalyticOpenEmbedding g₁)
  (hg₂ : IsAnalyticOpenEmbedding g₂) (hpb₁ : T'.IsPullbackOf T g₁) (hpb₂ : T'.IsPullbackOf T g₂)
  (hle₁ : ⇑g₁ '' (W' : Set N) ⊆ (W : Set M)) (hle₂ : ⇑g₂ '' (W' : Set N) ⊆ (W : Set M))

/-- **The fixed-run synchronisation at the level of the boundary families** ((37.2) in
[Kol07, Proposition 37, proof]) — two open embeddings `g₁`, `g₂` of one admissible input into
`(T, W)` with EQUAL pulled-back runs pull every member of the run's boundary family back along
their lifts to the same set: both lifts read the same `totalTransformSeqFrom` of the same list
(`totalTransformSeqFrom_last_pullbackLiftLast` twice, `preimage_eq_of_comap_eq`). -/
theorem preimage_liftOn_runFamily_eq_of_pullback_eq
    (hrun : (bed.seqOn T hT W hW).pullback (AnalyticMap.restrictMap g₁ W' W hle₁)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg₁.1 W' W hle₁) =
      (bed.seqOn T hT W hW).pullback (AnalyticMap.restrictMap g₂ W' W hle₂)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg₂.1 W' W hle₂))
    (σ : (bed.runFamily T hT W hW).ι) :
    ⇑(bed.liftOn T hT W hW T' hT' g₁ hg₁ hpb₁ W' hW' hle₁ hbed) ⁻¹'
        (bed.runFamily T hT W hW).hyp σ =
      ⇑(bed.liftOn T hT W hW T' hT' g₂ hg₂ hpb₂ W' hW' hle₂ hbed) ⁻¹'
        (bed.runFamily T hT W hW).hyp σ := by
  set R := bed.seqOn T hT W hW with hR
  have key : ∀ (g : AnalyticMap N M) (hg : IsAnalyticOpenEmbedding g)
      (hpb : T'.IsPullbackOf T g) (hle : ⇑g '' (W' : Set N) ⊆ (W : Set M)),
      ⇑(bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) ⁻¹'
          (bed.runFamily T hT W hW).hyp σ =
        (⇑(R.pullback (AnalyticMap.restrictMap g W' W hle)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).eraseEmptyLast.symm ∘
          ⇑(stageOfEq
            (bed.seqOn_eq_of_isAnalyticOpenEmbedding T hT W hW T' hT' g hg hpb W' hW' hle
              hbed))) ⁻¹'
          (⇑(R.pullbackLiftLast (AnalyticMap.restrictMap g W' W hle)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)) ⁻¹'
            (bed.runFamily T hT W hW).hyp σ) := by
    intro g hg hpb hle
    rw [← Set.preimage_comp]
    rfl
  have hP : ∀ (g : AnalyticMap N M) (hg : IsAnalyticOpenEmbedding g)
      (hle : ⇑g '' (W' : Set N) ⊆ (W : Set M)),
      FiniteSuccession.totalTransformSeqFrom (R.pullback (AnalyticMap.restrictMap g W' W hle)
          (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)).toSuccession
          (HypersurfaceFamily.empty (N.restrict W')) (Fin.last _) =
        (R.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (M.restrict W))
          (Fin.last _)).comap ⇑(R.pullbackLiftLast (AnalyticMap.restrictMap g W' W hle)
            (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)) := by
    intro g hg hle
    have := totalTransformSeqFrom_last_pullbackLiftLast R (AnalyticMap.restrictMap g W' W hle)
      (AnalyticMap.isLocalDiffeomorph_restrictMap hg.1 W' W hle)
      (HypersurfaceFamily.empty (M.restrict W))
    rwa [HypersurfaceFamily.empty_comap] at this
  rw [key g₁ hg₁ hpb₁ hle₁, key g₂ hg₂ hpb₂ hle₂]
  have gen : ∀ (L₁ L₂ : BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (N.restrict W'))
      (_ : L₁ = L₂) (hγ₁ : bed.seqOn T' hT' W' hW' = L₁.eraseEmpty)
      (hγ₂ : bed.seqOn T' hT' W' hW' = L₂.eraseEmpty)
      (l₁ : L₁.toSuccession.stage (Fin.last _) → R.toSuccession.stage (Fin.last _))
      (l₂ : L₂.toSuccession.stage (Fin.last _) → R.toSuccession.stage (Fin.last _))
      (h₁ : L₁.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (N.restrict W'))
          (Fin.last _) =
        (R.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (M.restrict W))
          (Fin.last _)).comap l₁)
      (h₂ : L₂.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (N.restrict W'))
          (Fin.last _) =
        (R.toSuccession.totalTransformSeqFrom (HypersurfaceFamily.empty (M.restrict W))
          (Fin.last _)).comap l₂),
      (⇑L₁.eraseEmptyLast.symm ∘ ⇑(stageOfEq hγ₁)) ⁻¹'
          (l₁ ⁻¹' (bed.runFamily T hT W hW).hyp σ) =
        (⇑L₂.eraseEmptyLast.symm ∘ ⇑(stageOfEq hγ₂)) ⁻¹'
          (l₂ ⁻¹' (bed.runFamily T hT W hW).hyp σ) := by
    rintro L₁ L₂ rfl hγ₁ hγ₂ l₁ l₂ h₁ h₂
    exact congrArg (fun s => (⇑L₁.eraseEmptyLast.symm ∘ ⇑(stageOfEq hγ₁)) ⁻¹' s)
      (HypersurfaceFamily.preimage_eq_of_comap_eq _ (h₁.symm.trans h₂) σ)
  exact gen _ _ hrun _ _ _ _ (hP g₁ hg₁ hle₁) (hP g₂ hg₂ hle₂)

/-- **The fixed-run synchronisation** ((37.2) in [Kol07, Proposition 37, proof]) — two open
embeddings `g₁`, `g₂` of one admissible input `(T', W')` into `(T, W)` with EQUAL pulled-back runs
(the conclusion of `seqOn_pullback_eq_of_pullback_eq`, `ExceptionalFamilyGlue.lean`) pull every
member of the run on `T` back along the two open immersions of local resolutions to the SAME
closed subspace: the stage-`σ` member on one side IS the stage-`σ` member on the other — no label
is chosen, the label is a stage of the one run. -/
theorem comap_localResolutionHomOn_runMembers_eq_of_pullback_eq
    (hrun : (bed.seqOn T hT W hW).pullback (AnalyticMap.restrictMap g₁ W' W hle₁)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg₁.1 W' W hle₁) =
      (bed.seqOn T hT W hW).pullback (AnalyticMap.restrictMap g₂ W' W hle₂)
        (AnalyticMap.isLocalDiffeomorph_restrictMap hg₂.1 W' W hle₂))
    (σ : (bed.runFamily T hT W hW).ι) :
    AnalyticSpace.QuotientSpace.comap
        (bed.localResolutionHomOn T hT W hW T' hT' g₁ hg₁ hpb₁ W' hW' hle₁ hbed).1
        (bed.runMembers T hT W hW hbed σ) =
      AnalyticSpace.QuotientSpace.comap
        (bed.localResolutionHomOn T hT W hW T' hT' g₂ hg₂ hpb₂ W' hW' hle₂ hbed).1
        (bed.runMembers T hT W hW hbed σ) := by
  rw [bed.comap_localResolutionHomOn_runMembers T hT W hW hbed T' hT' g₁ hg₁ hpb₁ W' hW' hle₁,
    bed.comap_localResolutionHomOn_runMembers T hT W hW hbed T' hT' g₂ hg₂ hpb₂ W' hW' hle₂]
  congr 1
  exact IsClosedSubmanifold.idealSheaf_congr _ _
    (bed.preimage_liftOn_runFamily_eq_of_pullback_eq T hT W hW hbed T' hT' W' hW' g₁ g₂ hg₁ hg₂
      hpb₁ hpb₂ hle₁ hle₂ hrun σ)

end Sync

end BEDanFamStar

end Hironaka.Manifold

end
