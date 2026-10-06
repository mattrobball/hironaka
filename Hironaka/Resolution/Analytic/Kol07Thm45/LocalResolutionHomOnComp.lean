/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientLift
public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductSumData
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.Kol07Thm45.ShearOverX
import Hironaka.Resolution.Analytic.OrderReduction.LiftUnique
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# Functoriality of `localResolutionHomOn` along a composite

The sequence functor commutes with open embeddings, whose pull-back lifts them stage by stage
([Kol07, Definition 30.1]; [Kol07, 34.1]); the lift is unique in the library's sense — a
continuous map over the embedding that pulls dense opens back to dense sets is the lift
(`eq_of_stageMap_last_comp_eq`, `OrderReduction/LiftUnique.lean`; not in the sources). Applied to
a COMPOSITE `g ∘ k` of two open embeddings of admissible inputs this gives the functoriality of
the lift and the open immersion of `LocalResolutionOn.lean`:

* `BEDanFamStar.liftOn_comp`: `liftOn (g ∘ k) = liftOn g ∘ liftOn k` on the last stages — both
  are continuous lifts of `g ∘ k` pulling dense opens back to dense sets
  (`isLocalDiffeomorph_liftOn`), and they agree after the last blow-down (`stageMap_last_liftOn'`
  three times);
* `BEDanFamStar.localResolutionHomOn_comp`: `localResolutionHomOn g ∘ localResolutionHomOn k =
  localResolutionHomOn (g ∘ k)` (`≫`) — `homOfPullbackEq_comp_of_comp_eq`
  (`ShearOverX.lean`) at `liftOn_comp`;
* the congruences `liftOn_congr`, `localResolutionHomOn_congr` in the embedding (the first has no
  user and is stated for the symmetry with the second);
* the INSTANCES `LocalEmbeddingData.resIn_sumPadData_inl` / `_inr`: for the common padded datum
  `S = sumPadData D₁ D₂`, `S.resIn (inl i) = sumInlResIn ∘ D₁⁺.resIn i` (and `inr`) — the
  composites `sumPadInlAmbient ∘ sigmaMk i = sigmaMk (inl i)` and
  `sumInrAmbient ∘ sigmaMk j = sigmaMk (inr j)` (`sumPadInlAmbient_comp_sigmaMk`,
  `sumInrAmbient_comp_sigmaMk`). Both instances are equations of morphisms of analytic spaces
  (`≫`) with the piece spelled once, as the sum's; the identities to use are
  `comap_resIn_sumPadData_inl` / `_inr`, where the two spellings of the piece meet as ideal
  sheaves.

These identities let the members of the common run pulled back along `S.resIn (inl i)` be read
through `sumInlResIn` and then through the padded piece's `resIn i`, which the comparison of two
adjacent levels (`CoproductLevelPair.lean`) and the compatibility of the piece traces
(`CoproductGluedFamilyCompat.lean`) need. Not in the sources beyond the pull-back of blow-up
sequences; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace Hironaka.Manifold
open AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BEDanFamStar

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] (bed : BEDanFamStar.{u} 𝕜) {n : ℕ}
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (W : Opens M) (hW : IsCompact (closure (W : Set M)))
  {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) N) (hT' : DomBEDan 𝕜 T')
  (g : AnalyticMap N M) (hg : IsAnalyticOpenEmbedding g)
      (hpb : T'.IsPullbackOf T g)
  (W' : Opens N) (hW' : IsCompact (closure (W' : Set N))) (hle : ⇑g '' (W' : Set N) ⊆ (W : Set M))

/-- The lift depends on the embedding only through its value — congruence in `g` (the proofs are
irrelevant). -/
theorem liftOn_congr (hbed : bed.IsEmbeddedDesing) (g' : AnalyticMap N M)
    (hg' : IsAnalyticOpenEmbedding g') (hpb' : T'.IsPullbackOf T g')
    (hle' : ⇑g' '' (W' : Set N) ⊆ (W : Set M)) (hgg' : g = g') :
    bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed =
      bed.liftOn T hT W hW T' hT' g' hg' hpb' W' hW' hle' hbed := by
  subst hgg'
  rfl

/-- The open immersion depends on the embedding only through its value — congruence in `g`. -/
theorem localResolutionHomOn_congr (hbed : bed.IsEmbeddedDesing)
    (g' : AnalyticMap N M)
    (hg' : IsAnalyticOpenEmbedding g') (hpb' : T'.IsPullbackOf T g')
    (hle' : ⇑g' '' (W' : Set N) ⊆ (W : Set M)) (hgg' : g = g') :
    bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed =
      bed.localResolutionHomOn T hT W hW T' hT' g' hg' hpb' W' hW' hle' hbed := by
  subst hgg'
  rfl

variable {P : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T'' : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) P) (hT'' : DomBEDan 𝕜 T'')
  (k : AnalyticMap P N) (hk : IsAnalyticOpenEmbedding k)
      (hpbk : T''.IsPullbackOf T' k)
  (W'' : Opens P) (hW'' : IsCompact (closure (W'' : Set P)))
  (hlek : ⇑k '' (W'' : Set P) ⊆ (W' : Set N))
  (hgk : IsAnalyticOpenEmbedding (g.comp k)) (hpbgk : T''.IsPullbackOf T (g.comp k))
  (hlegk : ⇑(g.comp k) '' (W'' : Set P) ⊆ (W : Set M))

/-- **The lift of a composite of open embeddings is the composite of the lifts**
([Kol07, Definition 30.1]) — both are continuous maps of the last
stages over `g ∘ k` that pull dense opens back to dense sets (local analytic isomorphisms,
`isLocalDiffeomorph_liftOn`), and they agree after the last blow-down (`stageMap_last_liftOn'`),
so the uniqueness of the lift (`eq_of_stageMap_last_comp_eq`) identifies them. -/
theorem liftOn_comp (hbed : bed.IsEmbeddedDesing) :
    ⇑(bed.liftOn T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed) =
      ⇑(bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed) ∘
        ⇑(bed.liftOn T' hT' W' hW' T'' hT'' k hk hpbk W'' hW'' hlek hbed) := by
  refine eq_of_stageMap_last_comp_eq (bed.seqOn T hT W hW)
    (bed.liftOn T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed).contMDiff.continuous
    ((bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed).contMDiff.continuous.comp
      (bed.liftOn T' hT' W' hW' T'' hT'' k hk hpbk W'' hW'' hlek hbed).contMDiff.continuous)
    (fun _ _ hD => dense_preimage_of_isLocalDiffeomorph _
      (bed.isLocalDiffeomorph_liftOn T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed)
      hD)
    fun z => ?_
  rw [bed.stageMap_last_liftOn' T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed z,
    Function.comp_apply, bed.stageMap_last_liftOn' T hT W hW T' hT' g hg hpb W' hW' hle hbed,
    bed.stageMap_last_liftOn' T' hT' W' hW' T'' hT'' k hk hpbk W'' hW'' hlek hbed]
  exact Subtype.ext rfl

/-- **Functoriality of the open immersion of local resolutions along a composite of open
embeddings** ([Kol07, Definition 30.1]) — `localResolutionHomOn` at `g ∘ k` is the composite of the
two; `homOfPullbackEq_comp_of_comp_eq` at `liftOn_comp`. -/
theorem localResolutionHomOn_comp (hbed : bed.IsEmbeddedDesing) :
    bed.localResolutionHomOn T' hT' W' hW' T'' hT'' k hk hpbk W'' hW'' hlek hbed ≫
        bed.localResolutionHomOn T hT W hW T' hT' g hg hpb W' hW' hle hbed =
      bed.localResolutionHomOn T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed :=
  IdealSheaf.homOfPullbackEq_comp_of_comp_eq
    (bed.liftOn T' hT' W' hW' T'' hT'' k hk hpbk W'' hW'' hlek hbed)
    (bed.liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.liftOn T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed)
    (bed.liftOn_comp T hT W hW T' hT' g hg hpb W' hW' hle T'' hT'' k hk hpbk W'' hW'' hlek hgk
      hpbgk hlegk hbed).symm
    (bed.lastIdealOn_eq_pullback_liftOn T' hT' W' hW' T'' hT'' k hk hpbk W'' hW'' hlek hbed)
    (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T' hT' g hg hpb W' hW' hle hbed)
    (bed.lastIdealOn_eq_pullback_liftOn T hT W hW T'' hT'' (g.comp k) hgk hpbgk W'' hW'' hlegk hbed)

end Hironaka.Manifold.BEDanFamStar

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U₁ U₂ : Set X}
  (D₁ : LocalEmbeddingData 𝕜 X U₁) (D₂ : LocalEmbeddingData 𝕜 X U₂)
  (W₁ : ∀ i : D₁.ι, Opens (pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G))
  (W₂ : ∀ j : D₂.ι, Opens (pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G))
  (bed : BEDanFamStar.{u} 𝕜)
  (hW₁ : ∀ i, IsCompact (closure (W₁ i : Set (pieceAmbient.{u} 𝕜
    ((D₁.padLeftData D₂.n).embedding i).G))))
  (hW₂ : ∀ j, IsCompact (closure (W₂ j : Set (pieceAmbient.{u} 𝕜
    ((D₂.padRightData D₁.n).embedding j).G))))
  (hbed : bed.IsEmbeddedDesing)

/-- **The common datum's open immersion at an `inl` piece factors through the first padded
level's** ([Kol07, Definition 30.1]; [Kol07, 34.1]) —
`S.resIn (inl i) = sumInlResIn ∘ (D₁⁺.resIn i read at the sum's piece)`, the functoriality
`localResolutionHomOn_comp` along `sigmaMk (inl i) = sumPadInlAmbient ∘ sigmaMk i`
(`sumPadInlAmbient_comp_sigmaMk`, the datum's specific `inl` inclusion). The second factor is
`D₁⁺.resIn i` with the piece spelled as the sum's (`(sumPadData D₁ D₂).embedding (Sum.inl i)`,
`sumPadOpens … (Sum.inl i)`): the statement keeps ONE spelling of the piece, and the identity to
use is `comap_resIn_sumPadData_inl`, where the two spellings meet as ideal sheaves. -/
theorem resIn_sumPadData_inl (i : D₁.ι) :
    (sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i) =
      bed.localResolutionHomOn (D₁.padLeftData D₂.n).sigmaTriple
          (D₁.padLeftData D₂.n).domBEDan_sigmaTriple ((D₁.padLeftData D₂.n).ambImage W₁)
          ((D₁.padLeftData D₂.n).isCompact_closure_ambImage W₁ hW₁)
          ((sumPadData D₁ D₂).embedding (Sum.inl i)).ambientTriple
          ((sumPadData D₁ D₂).embedding (Sum.inl i)).domBEDan_ambientTriple
          (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i)
          (isAnalyticOpenEmbedding_sigmaMk _ i)
          ((D₁.padLeftData D₂.n).isPullbackOf_ambientTriple_sigmaTriple i)
          (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inl i))
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂ (Sum.inl i))
          ((D₁.padLeftData D₂.n).image_subset_ambImage W₁ i) hbed ≫
          sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed := by
  have hgk : IsAnalyticOpenEmbedding ((sumPadInlAmbient D₁ D₂).comp
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i)) := by
    rw [sumPadInlAmbient_comp_sigmaMk]
    exact isAnalyticOpenEmbedding_sigmaMk _ _
  have hlegk : ⇑((sumPadInlAmbient D₁ D₂).comp
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i)) ''
        (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inl i) :
          Set (pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding (Sum.inl i)).G)) ⊆
      ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂) :
        Set (sumPadData D₁ D₂).sigmaAmbient) := by
    rw [sumPadInlAmbient_comp_sigmaMk]
    exact (sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inl i)
  have hpbgk : ((sumPadData D₁ D₂).embedding (Sum.inl i)).ambientTriple.IsPullbackOf (sumPadData D₁
    D₂).sigmaTriple
      ((sumPadInlAmbient D₁ D₂).comp
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i)) :=
    (isPullbackOf_sigmaTriple_sumPad_inl D₁ D₂).comp ((D₁.padLeftData
      D₂.n).isPullbackOf_ambientTriple_sigmaTriple i)
  -- the composite lemma, at the sum's spelling of the piece, every argument explicit
  have e1 := bed.localResolutionHomOn_comp (sumPadData D₁ D₂).sigmaTriple
    (sumPadData D₁ D₂).domBEDan_sigmaTriple ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
    ((sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
    (D₁.padLeftData D₂.n).sigmaTriple (D₁.padLeftData D₂.n).domBEDan_sigmaTriple (sumPadInlAmbient
      D₁ D₂) (isAnalyticOpenEmbedding_sumPadInlAmbient D₁ D₂) (isPullbackOf_sigmaTriple_sumPad_inl
      D₁ D₂)
    ((D₁.padLeftData D₂.n).ambImage W₁) ((D₁.padLeftData D₂.n).isCompact_closure_ambImage W₁ hW₁)
      (image_sumInlAmbient_ambImage_subset D₁ D₂ W₁ W₂)
    ((sumPadData D₁ D₂).embedding (Sum.inl i)).ambientTriple ((sumPadData D₁ D₂).embedding (Sum.inl
      i)).domBEDan_ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i)
    (isAnalyticOpenEmbedding_sigmaMk _ i) ((D₁.padLeftData
      D₂.n).isPullbackOf_ambientTriple_sigmaTriple i)
    (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inl i))
    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂ (Sum.inl i))
    ((D₁.padLeftData D₂.n).image_subset_ambImage W₁ i) hgk hpbgk hlegk hbed
  -- the congruence from the composite embedding to `sigmaMk (inl i)`
  have e2 := bed.localResolutionHomOn_congr (sumPadData D₁ D₂).sigmaTriple
    (sumPadData D₁ D₂).domBEDan_sigmaTriple ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
    ((sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
    ((sumPadData D₁ D₂).embedding (Sum.inl i)).ambientTriple ((sumPadData D₁ D₂).embedding (Sum.inl
      i)).domBEDan_ambientTriple
    ((sumPadInlAmbient D₁ D₂).comp
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D₁.padLeftData D₂.n).embedding i).G) i)) hgk hpbgk
          (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inl i))
    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂ (Sum.inl i)) hlegk hbed
    (sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inl i))
    (isAnalyticOpenEmbedding_sigmaMk _ (Sum.inl i))
    ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inl i))
    ((sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inl i))
    (sumPadInlAmbient_comp_sigmaMk D₁ D₂ i)
  exact (e1.trans e2).symm

/-- **The common datum's open immersion at an `inr` piece factors through the second padded
level's** — `S.resIn (inr j) = sumInrResIn ∘ (D₂⁺.resIn j read at the sum's piece)`
(`sumInrAmbient_comp_sigmaMk`); the spelling as for `inl`. -/
theorem resIn_sumPadData_inr (j : D₂.ι) :
    (sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j) =
      bed.localResolutionHomOn (D₂.padRightData D₁.n).sigmaTriple
          (D₂.padRightData D₁.n).domBEDan_sigmaTriple ((D₂.padRightData D₁.n).ambImage W₂)
          ((D₂.padRightData D₁.n).isCompact_closure_ambImage W₂ hW₂)
          ((sumPadData D₁ D₂).embedding (Sum.inr j)).ambientTriple
          ((sumPadData D₁ D₂).embedding (Sum.inr j)).domBEDan_ambientTriple
          (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j)
          (isAnalyticOpenEmbedding_sigmaMk _ j)
          ((D₂.padRightData D₁.n).isPullbackOf_ambientTriple_sigmaTriple j)
          (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inr j))
          (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂ (Sum.inr j))
          ((D₂.padRightData D₁.n).image_subset_ambImage W₂ j) hbed ≫
          sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed := by
  have hgk : IsAnalyticOpenEmbedding ((sumInrAmbient D₁ D₂).comp
        (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j)) := by
    rw [sumInrAmbient_comp_sigmaMk]
    exact isAnalyticOpenEmbedding_sigmaMk _ _
  have hlegk : ⇑((sumInrAmbient D₁ D₂).comp
        (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j)) ''
        (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inr j) :
          Set (pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding (Sum.inr j)).G)) ⊆
      ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂) :
        Set (sumPadData D₁ D₂).sigmaAmbient) := by
    rw [sumInrAmbient_comp_sigmaMk]
    exact (sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inr j)
  have hpbgk : ((sumPadData D₁ D₂).embedding (Sum.inr j)).ambientTriple.IsPullbackOf (sumPadData D₁
    D₂).sigmaTriple
      ((sumInrAmbient D₁ D₂).comp
        (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j)) :=
    (isPullbackOf_sigmaTriple_sumPad_inr D₁ D₂).comp ((D₂.padRightData
      D₁.n).isPullbackOf_ambientTriple_sigmaTriple j)
  -- the composite lemma, at the sum's spelling of the piece, every argument explicit
  have e1 := bed.localResolutionHomOn_comp (sumPadData D₁ D₂).sigmaTriple
    (sumPadData D₁ D₂).domBEDan_sigmaTriple ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
    ((sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
    (D₂.padRightData D₁.n).sigmaTriple (D₂.padRightData D₁.n).domBEDan_sigmaTriple (sumInrAmbient
      D₁ D₂) (isAnalyticOpenEmbedding_sumInrAmbient D₁ D₂) (isPullbackOf_sigmaTriple_sumPad_inr D₁
      D₂)
    ((D₂.padRightData D₁.n).ambImage W₂) ((D₂.padRightData D₁.n).isCompact_closure_ambImage W₂ hW₂)
      (image_sumInrAmbient_ambImage_subset D₁ D₂ W₁ W₂)
    ((sumPadData D₁ D₂).embedding (Sum.inr j)).ambientTriple ((sumPadData D₁ D₂).embedding (Sum.inr
      j)).domBEDan_ambientTriple
    (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j)
    (isAnalyticOpenEmbedding_sigmaMk _ j) ((D₂.padRightData
      D₁.n).isPullbackOf_ambientTriple_sigmaTriple j)
    (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inr j))
    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂ (Sum.inr j))
    ((D₂.padRightData D₁.n).image_subset_ambImage W₂ j) hgk hpbgk hlegk hbed
  -- the congruence from the composite embedding to `sigmaMk (inr j)`
  have e2 := bed.localResolutionHomOn_congr (sumPadData D₁ D₂).sigmaTriple
    (sumPadData D₁ D₂).domBEDan_sigmaTriple ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁ W₂))
    ((sumPadData D₁ D₂).isCompact_closure_ambImage _
      (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))
    ((sumPadData D₁ D₂).embedding (Sum.inr j)).ambientTriple ((sumPadData D₁ D₂).embedding (Sum.inr
      j)).domBEDan_ambientTriple
    ((sumInrAmbient D₁ D₂).comp
        (sigmaMk (fun j => pieceAmbient.{u} 𝕜 ((D₂.padRightData D₁.n).embedding j).G) j)) hgk hpbgk
          (sumPadOpens D₁ D₂ W₁ W₂ (Sum.inr j))
    (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂ (Sum.inr j)) hlegk hbed
    (sigmaMk (fun k => pieceAmbient.{u} 𝕜 ((sumPadData D₁ D₂).embedding k).G) (Sum.inr j))
    (isAnalyticOpenEmbedding_sigmaMk _ (Sum.inr j))
    ((sumPadData D₁ D₂).isPullbackOf_ambientTriple_sigmaTriple (Sum.inr j))
    ((sumPadData D₁ D₂).image_subset_ambImage (sumPadOpens D₁ D₂ W₁ W₂) (Sum.inr j))
    (sumInrAmbient_comp_sigmaMk D₁ D₂ j)
  exact (e1.trans e2).symm

/-- **The pull-back form at `inl`** — pulling a closed subspace of the common run's local
resolution back along `S.resIn (inl i)` is pulling it back along `sumInlResIn` and then along
`D₁⁺.resIn i` (`resIn_sumPadData_inl`, `QuotientSpace.comap_comp`; the two spellings of the piece
meet here, as ideal sheaves, where they are definitionally equal at once). -/
theorem comap_resIn_sumPadData_inl (i : D₁.ι)
    (M : IdealSheaf (bed.localResolutionOn (sumPadData D₁ D₂).sigmaTriple
      (sumPadData D₁ D₂).domBEDan_sigmaTriple ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁
        W₂))
      ((sumPadData D₁ D₂).isCompact_closure_ambImage _
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))).toLocallyRingedSpace.𝒪) :
    QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inl i)).1 M =
      QuotientSpace.comap ((D₁.padLeftData D₂.n).resIn bed W₁ hW₁ hbed i).1
        (QuotientSpace.comap (sumInlResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 M) := by
  rw [resIn_sumPadData_inl]
  exact QuotientSpace.comap_comp _ _ _

/-- **The pull-back form at `inr`** — pulling back along `S.resIn (inr j)` is pulling back along
`sumInrResIn` and then along `D₂⁺.resIn j`. -/
theorem comap_resIn_sumPadData_inr (j : D₂.ι)
    (M : IdealSheaf (bed.localResolutionOn (sumPadData D₁ D₂).sigmaTriple
      (sumPadData D₁ D₂).domBEDan_sigmaTriple ((sumPadData D₁ D₂).ambImage (sumPadOpens D₁ D₂ W₁
        W₂))
      ((sumPadData D₁ D₂).isCompact_closure_ambImage _
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂))).toLocallyRingedSpace.𝒪) :
    QuotientSpace.comap ((sumPadData D₁ D₂).resIn bed (sumPadOpens D₁ D₂ W₁ W₂)
        (isCompact_closure_sumPadOpens D₁ D₂ W₁ W₂ hW₁ hW₂) hbed (Sum.inr j)).1 M =
      QuotientSpace.comap ((D₂.padRightData D₁.n).resIn bed W₂ hW₂ hbed j).1
        (QuotientSpace.comap (sumInrResIn D₁ D₂ W₁ W₂ bed hW₁ hW₂ hbed).1 M) := by
  rw [resIn_sumPadData_inr]
  exact QuotientSpace.comap_comp _ _ _

end Hironaka.Manifold.LocalEmbeddingData

end
