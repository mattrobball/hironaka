/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientTransport
public import Hironaka.Resolution.Analytic.Kol07Thm45.SigmaCoordMap
public import Hironaka.Resolution.Analytic.Kol07Thm45.SigmaSummandHom
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum
public import Hironaka.AnalyticSpace.Resolution.Defs
public import Hironaka.Resolution.Analytic.Kol07Thm45.OpenEmbeddingLift
import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The embeddings of the pieces into the disjoint-union model, at a gluing datum

Kollár's local model `Y₀ = ⊔ᵢ X|Uᵢ ⊆ X' = ⊔ᵢ Uᵢ` [Kol07, Proposition 37, proof]: for a gluing
datum and any family of relatively compact opens `Wᵢ ⋐ Gᵢ` of the pieces' ambients (a gluing
datum's, or a shrinking of it for the locally finite factorization), the ambient opens
`Gᵢ' = pieceCoord '' Wᵢ` (`ambOpens`), the ambient `⊔ᵢ Gᵢ'` (`ambSpace`, a `sigmaOpens`),
`Θ₀ : ⊔ᵢ Gᵢ' → ⊔ᵢ Sp(Gᵢ)` with its image `U_Σ` and the analytic isomorphism
`Θ : ⊔ᵢ Gᵢ' ≅ (⊔ᵢ Sp(Gᵢ))|U_Σ` (`SigmaCoordMap.lean` at the datum), the transported data of
`AmbientTransport.lean` at `T := D.sigmaTriple`, `W := U_Σ` (`glueIdeal`, `glueSeq`, `glueLast`,
`glueMap`), and the embeddings `emb i : X|pieceDom i Wᵢ ≅ (Sp(⊔ⱼ Gⱼ')/J₀)|overPiece i`
(`glueEmb`) of the `AmbientBlowUpFactorization`: `X|pieceDom i Wᵢ ≅ Sp(Wᵢ)/𝓘ᵢ|Wᵢ` (the inverse of
the open immersion of the piece over `Wᵢ`, named `pieceOverHom`), into `Sp(⊔ⱼ Gⱼ)/𝓘_Σ` by the
restriction-of-a-quotient map and the summand inclusion of `SigmaSummandHom.lean` (`sumIn`), matched
against the part over `Gᵢ'` sent into `Sp(⊔ⱼ Gⱼ)/𝓘_Σ` by `ambIdealIso` and the restriction open
immersion over `U_Σ` (`ambIn`) — `isoOfRangeEq` on two open immersions with the same range (the
summand characterisation `ambTheta₀_mem_image_iff`). General tools: `IdealSheaf.restrictOpensHom`
(`homOfPullbackEq` along `W ↪ M`) and `IdealSheaf.isOpen_overPiece`.

Not in the sources beyond Kollár's model; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

section General

variable {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- **The open immersion `Sp(W)/J|W → Sp(M)/J` of the restricted closed subspace**:
`homOfPullbackEq` along the inclusion `W ↪ M` (the general form of `restrictedIdealHom`). -/
def _root_.Manifold.IdealSheaf.restrictOpensHom (J : AnalyticManifold.IdealSheaf M) (W : Opens M) :
    (J.restrict W).toAnalyticSpace ⟶ J.toAnalyticSpace :=
  IdealSheaf.homOfPullbackEq (J' := J.restrict W) (J := J) ⇑(M.inclusion W)
    (M.inclusion W).contMDiff rfl

theorem _root_.Manifold.IdealSheaf.isOpenImmersion_restrictOpensHom
    (J : AnalyticManifold.IdealSheaf M)
    (W : Opens M) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (IdealSheaf.restrictOpensHom J W).1 := by
  unfold IdealSheaf.restrictOpensHom
  exact isOpenImmersion_homOfPullbackEq_of_injective (M.inclusion W)
    (isLocalDiffeomorph_inclusion M W) Subtype.val_injective rfl

theorem _root_.Manifold.IdealSheaf.range_toFun_restrictOpensHom (J : AnalyticManifold.IdealSheaf M)
    (W : Opens M) :
    Set.range ⇑(IdealSheaf.restrictOpensHom J W) =
      {z | J.toAnalyticSpaceι z ∈ W} := by
  unfold IdealSheaf.restrictOpensHom
  rw [range_toFun_homOfPullbackEq (M.inclusion W) (isLocalDiffeomorph_inclusion M W) rfl]
  exact Set.ext fun z => ⟨fun ⟨w, hw⟩ =>
    show J.toAnalyticSpaceι z ∈ W from hw ▸ w.2,
    fun hz => ⟨⟨_, hz⟩, rfl⟩⟩

theorem _root_.Manifold.IdealSheaf.toFun_toAnalyticSpaceι_restrictOpensHom
    (J : AnalyticManifold.IdealSheaf M)
    (W : Opens M) (z : (J.restrict W).toAnalyticSpace) :
    J.toAnalyticSpaceι
        (IdealSheaf.restrictOpensHom J W z) =
      ((J.restrict W).toAnalyticSpaceι z).1 :=
  rfl

/-- The part of `Sp(⊔ Gᵢ)/J` over a summand is open (the `overPiece` of
`AmbientBlowUpFactorization`): the preimage of the clopen summand under the continuous canonical
map. -/
theorem _root_.Manifold.IdealSheaf.isOpen_overPiece {ι : Type u} [Countable ι] {G : ι → Opens
    (Fin n → 𝕜)}
    (J : AnalyticManifold.IdealSheaf (AnalyticManifold.sigmaOpens G))
        (i : ι) :
    IsOpen (J.overPiece i) := by
  have h : IsOpen (Sigma.fst ⁻¹' {i} : Set (Σ j, ↥(G j))) :=
    Set.range_sigmaMk i ▸ isOpen_range_sigmaMk
  exact h.preimage (Hom.continuous_toFun J.toAnalyticSpaceι)

end General

section Piece

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}

/-- **The open immersion of the piece over `W` into `X`** — the `q` of
`exists_openImmersion_toSpaceMap_eq` (`ResolutionSnc.lean`), named: the restriction-of-a-quotient
map, the inverse of the embedding, the inclusion of the piece. -/
def PieceEmbedding.pieceOverHom (E : PieceEmbedding 𝕜 n X V)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace :=
  (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace) ≫
    (E.embInv : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
      X.toKLocallyRingedSpace.restrictOpen (openOf X V)) ≫
    ofRestrict X.toKLocallyRingedSpace (openOf X V)

theorem PieceEmbedding.isOpenImmersion_pieceOverHom (E : PieceEmbedding 𝕜 n X V)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (E.pieceOverHom W).1 := by
  have hE : IsIso E.emb := E.emb_isIso
  have h₁ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.restrictedIdealHom W : (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        E.ideal.toAnalyticSpace.toKLocallyRingedSpace).1 :=
    E.isOpenImmersion_restrictedIdealHom W
  have h₂ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (E.embInv : E.ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
        X.toKLocallyRingedSpace.restrictOpen (openOf X V)).1 :=
    E.isOpenImmersion_inv_emb
  have hoR : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict X.toKLocallyRingedSpace (openOf X V)).1 :=
    inferInstance
  unfold PieceEmbedding.pieceOverHom
  exact @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (E.restrictedIdealHom W).1 h₁
    (E.embInv.1 ≫ (ofRestrict X.toKLocallyRingedSpace
      (openOf X V)).1)
    (@AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.embInv.1 h₂
      (ofRestrict X.toKLocallyRingedSpace (openOf X V)).1 hoR)

theorem PieceEmbedding.toFun_pieceOverHom (E : PieceEmbedding 𝕜 n X V)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    KLocallyRingedSpace.Hom.toFun (E.pieceOverHom W) = E.pieceOverIncl W :=
  rfl

theorem PieceEmbedding.range_toFun_pieceOverHom (E : PieceEmbedding 𝕜 n X V)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    Set.range (KLocallyRingedSpace.Hom.toFun (E.pieceOverHom W)) = (E.domOpens W : Set X) := by
  rw [E.toFun_pieceOverHom W]
  exact E.range_pieceOverIncl W

theorem PieceEmbedding.toSpaceMap_eq_comp_pieceOverHom (E : PieceEmbedding 𝕜 n X V)
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    E.toSpaceMap bed W hW =
      (E.localResolutionMap bed W hW : (E.localResolution bed W hW).toKLocallyRingedSpace ⟶
          (E.restrictedIdeal W).toAnalyticSpace.toKLocallyRingedSpace) ≫
        E.pieceOverHom W := by
  unfold PieceEmbedding.pieceOverHom PieceEmbedding.toSpaceMap
  rw [E.localResolutionToPiece_eq bed W hW]
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

end Piece

namespace LocalEmbeddingData

open _root_.Manifold

variable {X : AnalyticSpace.{u} 𝕜} {U : Set X} (D : LocalEmbeddingData 𝕜 X U)

/-- The summand inclusion on points lies over `sigmaMk i`. Internal. -/
theorem toFun_toAnalyticSpaceι_sigmaSummandHom (i : D.ι)
    (z : (D.embedding i).ideal.toAnalyticSpace) :
    D.sigmaTriple.I.toAnalyticSpaceι
        (D.sigmaSummandHom i z) =
      sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i
        ((D.embedding i).ideal.toAnalyticSpaceι z) :=
  toFun_homOfPullbackEq_val (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).contMDiff
    (D.isPullbackOf_ambientTriple_sigmaTriple i).1 z

variable (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))

/-! The constructions below are parametrised by an ARBITRARY family `W` of relatively compact opens
of the pieces' ambients (`hW`), not only by a gluing datum's `W`: the locally finite factorization
needs pieces `pieceDom i (W i)` INSIDE a prescribed open of `X`, which is reached by shrinking `W`
(`AmbientFactorization.lean`). -/

/-- The ambient opens of the model: the coordinate images `Gᵢ' = pieceCoord '' Wᵢ ⊆ 𝕜ⁿ` of the
opens `Wᵢ` (`coordImageOpens`). -/
def ambOpens (i : D.ι) : Opens (Fin D.n → 𝕜) := coordImageOpens (D.embedding i).G (W i)

/-- The ambient `⊔ᵢ Gᵢ'` of the model (a `sigmaOpens`). -/
abbrev ambSpace : AnalyticManifold.{u} 𝕜 (Fin D.n → 𝕜) :=
  AnalyticManifold.sigmaOpens (D.ambOpens W)

/-- `Θ₀ : ⊔ᵢ Gᵢ' → ⊔ᵢ Sp(Gᵢ)` at the gluing datum (`sigmaCoordMap`). -/
def ambTheta₀ : AnalyticMap (D.ambSpace W) D.sigmaAmbient :=
  sigmaCoordMap (fun i => (D.embedding i).G) W

/-- `U_Σ = ⋃ᵢ sigmaMk i '' Wᵢ`, the image of `Θ₀` (`sigmaCoordImage`). -/
def ambImage : Opens D.sigmaAmbient := sigmaCoordImage (fun i => (D.embedding i).G) W

theorem isCompact_closure_ambImage
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) :
    IsCompact (closure (D.ambImage W : Set D.sigmaAmbient)) :=
  isCompact_closure_sigmaCoordImage _ _ hW

theorem image_subset_ambImage (i : D.ι) :
    ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
        (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)) ⊆
      (D.ambImage W : Set D.sigmaAmbient) := by
  unfold ambImage
  rw [coe_sigmaCoordImage]
  exact Set.subset_iUnion (fun j => ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) j) ''
    (W j : Set (pieceAmbient.{u} 𝕜 (D.embedding j).G))) i

/-- **`Θ : ⊔ᵢ Gᵢ' ≅ (⊔ᵢ Sp(Gᵢ))|U_Σ`**, the analytic isomorphism onto the image
(`diffeomorphOntoImage`). -/
def ambTheta : Diffeomorph 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin D.n → 𝕜) (D.ambSpace W)
    (D.sigmaAmbient.restrict (D.ambImage W)) ω :=
  AnalyticMap.diffeomorphOntoImage (D.ambTheta₀ W)
    (isAnalyticOpenEmbedding_sigmaCoordMap _ _).1 (isAnalyticOpenEmbedding_sigmaCoordMap _ _).2

/-- The summand characterisation: `Θ₀ a` lies over the `i`-th piece's open iff `a` is in the
`i`-th summand. -/
theorem ambTheta₀_mem_image_iff (i : D.ι) (a : D.ambSpace W) :
    D.ambTheta₀ W a ∈ ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
        (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)) ↔ a.1 = i := by
  obtain ⟨j, z⟩ := a
  constructor
  · rintro ⟨w, -, hw⟩
    have h := congrArg Sigma.fst
      (hw.trans (sigmaCoordMap_apply (fun i => (D.embedding i).G) W j z))
    exact h.symm
  · intro h
    obtain rfl : j = i := h
    obtain ⟨w, hw, hwz⟩ := (mem_coordImageOpens (D.embedding j).G (W j) z.1).mp z.2
    refine ⟨w, hw, ?_⟩
    exact (sigmaCoordMap_mk_of_mem (fun i => (D.embedding i).G) W j w hw).symm.trans
      (congrArg (⇑(D.ambTheta₀ W)) (Sigma.ext rfl (heq_of_eq (Subtype.ext hwz))))

/-- The data of the factorization at the gluing datum: `AmbientTransport.lean` at
`T := D.sigmaTriple`, `W := U_Σ`, `Θ := ambTheta` — the ideal `J₀`, … -/
abbrev glueIdeal : AnalyticManifold.IdealSheaf (D.ambSpace W) :=
  BEDanFamStar.ambIdealOn D.sigmaTriple (D.ambImage W) (D.ambTheta W)

/-- … the blow-up sequence, … -/
abbrev glueSeq (bed : BEDanFamStar.{u} 𝕜)
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜)) (D.ambSpace W) :=
  BEDanFamStar.ambSeqOn bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.ambTheta W)

/-- … the last strict transform `Y_r`, … -/
abbrev glueLast (bed : BEDanFamStar.{u} 𝕜)
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) :
    AnalyticManifold.IdealSheaf ((D.glueSeq W bed hW).toSuccession.stage (Fin.last _)) :=
  BEDanFamStar.ambLastOn bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.ambTheta W)

/-- … and `Π_r|_{Y_r}`. -/
abbrev glueMap (bed : BEDanFamStar.{u} 𝕜)
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) :
    (D.glueLast W bed hW).toAnalyticSpace ⟶ (D.glueIdeal W).toAnalyticSpace :=
  BEDanFamStar.ambMapOn bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.ambTheta W)

/-- The inclusion of the open `pieceDom i Wᵢ` is an open immersion (the instance, named so that it
can be passed explicitly). Internal. -/
theorem isOpenImmersion_ofRestrict_pieceDom (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (ofRestrict X.toKLocallyRingedSpace
      (openOf X (D.pieceDom i (W i) : Set X))).1 :=
  inferInstance

/-- The open immersion of the piece over `Wᵢ` and the inclusion of the open `pieceDom i Wᵢ` have
the same range (`domOpens Wᵢ` IS `pieceDom i Wᵢ`). Internal. -/
theorem range_toFun_ofRestrict_pieceDom_eq (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict X.toKLocallyRingedSpace
        (openOf X (D.pieceDom i (W i) : Set X)))) =
      Set.range (KLocallyRingedSpace.Hom.toFun ((D.embedding i).pieceOverHom (W i))) := by
  rw [(D.embedding i).range_toFun_pieceOverHom, range_toFun_ofRestrict,
    openOf_of_isOpen X (D.pieceDom i (W i)).isOpen]
  rfl

/-- `X|pieceDom i (W i) ≅ Sp(Wᵢ)/𝓘ᵢ|Wᵢ`: the inclusion of the open `pieceDom i Wᵢ` against the
open immersion of the piece over `Wᵢ`, onto the same range (`isoOfRangeEq`). -/
def pieceIso (i : D.ι) :
    (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace ≅
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace :=
  @isoOfRangeEq _ _ _ _ _
    (ofRestrict X.toKLocallyRingedSpace
      (openOf X (D.pieceDom i (W i) : Set X)))
    ((D.embedding i).pieceOverHom (W i)) (D.isOpenImmersion_ofRestrict_pieceDom W i)
    ((D.embedding i).isOpenImmersion_pieceOverHom (W i))
    (D.range_toFun_ofRestrict_pieceDom_eq W i)

theorem pieceIso_hom_comp_pieceOverHom (i : D.ι) :
    (D.pieceIso W i).hom ≫ (D.embedding i).pieceOverHom (W i) =
      ofRestrict X.toKLocallyRingedSpace
        (openOf X (D.pieceDom i (W i) : Set X)) := by
  unfold pieceIso
  exact @isoOfRangeEq_hom_comp _ _ _ _ _
    (ofRestrict X.toKLocallyRingedSpace
      (openOf X (D.pieceDom i (W i) : Set X)))
    ((D.embedding i).pieceOverHom (W i)) (D.isOpenImmersion_ofRestrict_pieceDom W i)
    ((D.embedding i).isOpenImmersion_pieceOverHom (W i))
    (D.range_toFun_ofRestrict_pieceDom_eq W i)

/-- `Sp(Wᵢ)/𝓘ᵢ|Wᵢ → Sp(⊔ⱼ Gⱼ)/𝓘_Σ`: the restriction-of-a-quotient map followed by the summand
inclusion (`sigmaSummandHom`). -/
def sumIn (i : D.ι) :
    ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
      D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace :=
  ((D.embedding i).restrictedIdealHom (W i) :
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (D.embedding i).ideal.toAnalyticSpace.toKLocallyRingedSpace) ≫
    (D.sigmaSummandHom i : (D.embedding i).ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
      D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace)

theorem isOpenImmersion_sumIn (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.sumIn W i).1 := by
  unfold sumIn
  exact @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    ((D.embedding i).restrictedIdealHom (W i)).1
    ((D.embedding i).isOpenImmersion_restrictedIdealHom (W i))
    (D.sigmaSummandHom i).1 (D.isOpenImmersion_sigmaSummandHom i)

theorem range_toFun_sumIn (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun (D.sumIn W i)) =
      {z | D.sigmaTriple.I.toAnalyticSpaceι z ∈
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
          (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(D.embedding i).ideal.toAnalyticSpaceι
      (((D.embedding i).restrictedIdealHom (W i)) y),
      (((D.embedding i).restrictedIdeal (W i)).toAnalyticSpaceι y).2, ?_⟩
    exact (D.toFun_toAnalyticSpaceι_sigmaSummandHom i _).symm
  · rintro ⟨w, hw, hz⟩
    have hz1 : z ∈
        Set.range ⇑(D.sigmaSummandHom i) := by
      rw [D.range_toFun_sigmaSummandHom i]
      exact ⟨w, hz⟩
    obtain ⟨x, rfl⟩ := hz1
    have hx :
        (D.embedding i).ideal.toAnalyticSpaceι x = w :=
      sigma_mk_injective (β := fun j => (pieceAmbient.{u} 𝕜 (D.embedding j).G : Type u))
        ((D.toFun_toAnalyticSpaceι_sigmaSummandHom i x).symm.trans hz.symm)
    have hx2 : x ∈ Set.range
        ⇑((D.embedding i).restrictedIdealHom (W i)) := by
      rw [(D.embedding i).range_toFun_restrictedIdealHom (W i)]
      exact
          (hx ▸ hw :
              (D.embedding i).ideal.toAnalyticSpaceι x
                  ∈
        W i)
    obtain ⟨y, rfl⟩ := hx2
    exact ⟨y, rfl⟩

/-- `Sp(⊔ᵢ Gᵢ')/J₀ → Sp(⊔ⱼ Gⱼ)/𝓘_Σ`: the identification `ambIdealIso` along `Θ` followed by the
open immersion of the restricted closed subspace over `U_Σ`. -/
def ambIn : (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
    D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace :=
  (BEDanFamStar.ambIdealIso D.sigmaTriple (D.ambImage W) (D.ambTheta W) :
      (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (BEDanFamStar.restrictedIdealOn D.sigmaTriple
          (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace) ≫
    (IdealSheaf.restrictOpensHom D.sigmaTriple.I (D.ambImage W) :
      (BEDanFamStar.restrictedIdealOn D.sigmaTriple
          (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace ⟶
        D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace)

theorem isOpenImmersion_ambIn :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.ambIn W).1 := by
  unfold ambIn
  exact @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (BEDanFamStar.ambIdealIso D.sigmaTriple (D.ambImage W) (D.ambTheta W)).1
    (isOpenImmersion_homOfPullbackEq_of_injective (Diffeomorph.toAnalyticMap (D.ambTheta W))
      (D.ambTheta W).isLocalDiffeomorph (D.ambTheta W).bijective.1 rfl)
    (IdealSheaf.restrictOpensHom D.sigmaTriple.I (D.ambImage W)).1
    (IdealSheaf.isOpenImmersion_restrictOpensHom _ _)

theorem toFun_toAnalyticSpaceι_ambIn (y : (D.glueIdeal W).toAnalyticSpace) :
    D.sigmaTriple.I.toAnalyticSpaceι
        (KLocallyRingedSpace.Hom.toFun (D.ambIn W) y) =
      D.ambTheta₀ W
        ((D.glueIdeal W).toAnalyticSpaceι y) :=
  rfl

theorem range_toFun_ambIn :
    Set.range (KLocallyRingedSpace.Hom.toFun (D.ambIn W)) =
      {z | D.sigmaTriple.I.toAnalyticSpaceι z ∈
        D.ambImage W} := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    change D.sigmaTriple.I.toAnalyticSpaceι
      (KLocallyRingedSpace.Hom.toFun (D.ambIn W) y) ∈ D.ambImage W
    rw [D.toFun_toAnalyticSpaceι_ambIn W y]
    exact ⟨_, rfl⟩
  · intro hz
    have hz1 : z ∈ Set.range ⇑(IdealSheaf.restrictOpensHom D.sigmaTriple.I (D.ambImage W)) := by
      rw [IdealSheaf.range_toFun_restrictOpensHom]
      exact hz
    obtain ⟨x, rfl⟩ := hz1
    have hx : x ∈
        Set.range ⇑(BEDanFamStar.ambIdealIso D.sigmaTriple (D.ambImage W) (D.ambTheta W)) :=
      (Set.ext_iff.mp (range_toFun_homOfPullbackEq (Diffeomorph.toAnalyticMap (D.ambTheta W))
        (D.ambTheta W).isLocalDiffeomorph
        (rfl : BEDanFamStar.ambIdealOn D.sigmaTriple (D.ambImage W) (D.ambTheta W) = _))
        x).mpr ⟨(D.ambTheta W).symm _, (D.ambTheta W).apply_symm_apply _⟩
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl⟩

/-- The two open immersions into `Sp(⊔ⱼ Gⱼ)/𝓘_Σ` have the same range: the points over
`sigmaMk i '' Wᵢ` (the summand characterisation). Internal. -/
theorem range_toFun_sumIn_eq (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun (D.sumIn W i)) =
      Set.range (KLocallyRingedSpace.Hom.toFun
        (ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
          (openOf _ ((D.glueIdeal W).overPiece i)) ≫
        D.ambIn W)) := by
  rw [D.range_toFun_sumIn W i, Hom.toFun_comp, Set.range_comp, range_toFun_ofRestrict,
    openOf_of_isOpen _ (IdealSheaf.isOpen_overPiece _ i)]
  ext z
  constructor
  · intro hz
    have hz1 : z ∈ Set.range (KLocallyRingedSpace.Hom.toFun (D.ambIn W)) := by
      rw [D.range_toFun_ambIn W]
      exact D.image_subset_ambImage W i hz
    obtain ⟨y, rfl⟩ := hz1
    refine ⟨y, ?_, rfl⟩
    exact (D.ambTheta₀_mem_image_iff W i _).mp
      ((D.toFun_toAnalyticSpaceι_ambIn W y).symm ▸ hz)
  · rintro ⟨y, hy, rfl⟩
    change D.sigmaTriple.I.toAnalyticSpaceι
      (KLocallyRingedSpace.Hom.toFun (D.ambIn W) y) ∈
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
          (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    rw [D.toFun_toAnalyticSpaceι_ambIn W y]
    exact (D.ambTheta₀_mem_image_iff W i _).mpr hy

/-- The inclusion of the part over `Gᵢ'` followed by `ambIn` is an open immersion. Internal. -/
theorem isOpenImmersion_ofRestrict_comp_ambIn (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
          (openOf _ ((D.glueIdeal W).overPiece i)) ≫
        D.ambIn W).1 :=
  @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _
    (ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
      (openOf _ ((D.glueIdeal W).overPiece i))).1
    inferInstance (D.ambIn W).1 (D.isOpenImmersion_ambIn W)

/-- The isomorphism behind `emb i`: `pieceIso` followed by the `isoOfRangeEq` of `sumIn` and of
the part's inclusion followed by `ambIn`. Internal. -/
def glueEmbIso (i : D.ι) :
    (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace ≅
      ((D.glueIdeal W).toAnalyticSpace.restrictSet
        ((D.glueIdeal W).overPiece i)).toKLocallyRingedSpace :=
  (D.pieceIso W i).trans
    (@isoOfRangeEq _ _ _ _ _ (D.sumIn W i)
      (ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
          (openOf _ ((D.glueIdeal W).overPiece i)) ≫
        D.ambIn W)
      (D.isOpenImmersion_sumIn W i) (D.isOpenImmersion_ofRestrict_comp_ambIn W i)
      (D.range_toFun_sumIn_eq W i))

/-- **`X|Uᵢ ≅` the part of `Sp(⊔ᵢ Gᵢ')/J₀ over `Gᵢ'`** (the field `emb` of the factorization;
[Kol07, Proposition 37, proof]), `Uᵢ = pieceDom i (W i)`: through `Sp(Wᵢ)/𝓘ᵢ|Wᵢ` and
`Sp(⊔ⱼ Gⱼ)/𝓘_Σ` (`isoOfRangeEq` of `sumIn` and of the part's inclusion followed by `ambIn`). -/
def glueEmb (i : D.ι) :
    (X.restrictSet (D.pieceDom i (W i)) ⟶ (D.glueIdeal W).toAnalyticSpace.restrictSet
        ((D.glueIdeal W).overPiece i)) :=
  (D.glueEmbIso W i).hom

theorem isIso_glueEmb (i : D.ι) : IsIso (D.glueEmb W i) :=
  isIso_of_isIso_toKLocallyRingedSpace _
    (D.glueEmbIso W i).isIso_hom

/-- `emb i` lies under `sumIn` (used by the compatibility `map_lift`). -/
theorem glueEmb_comp_ambIn (i : D.ι) :
    (D.glueEmb W i : (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace ⟶
        ((D.glueIdeal W).toAnalyticSpace.restrictSet
          ((D.glueIdeal W).overPiece i)).toKLocallyRingedSpace) ≫
      ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
        (openOf _ ((D.glueIdeal W).overPiece i)) ≫
      D.ambIn W =
    (D.pieceIso W i).hom ≫ D.sumIn W i := by
  unfold glueEmb glueEmbIso
  exact (Category.assoc _ _ _).trans
    (congrArg (fun k => (D.pieceIso W i).hom ≫ k)
      (@isoOfRangeEq_hom_comp _ _ _ _ _ (D.sumIn W i)
        (ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
            (openOf _ ((D.glueIdeal W).overPiece i)) ≫
          D.ambIn W)
        (D.isOpenImmersion_sumIn W i) (D.isOpenImmersion_ofRestrict_comp_ambIn W i)
        (D.range_toFun_sumIn_eq W i)))

end LocalEmbeddingData

end Hironaka.Manifold

end
