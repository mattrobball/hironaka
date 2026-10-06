/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.OverPart
public import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrictHom
public import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientEmb
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceTransition
import Hironaka.AnalyticSpace.HomOfSections
public import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.SigmaLemmas
public import Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The lift of the glued space into the last transform and the ambient blow-up factorization

Kollár's resolution of the disjoint union `Y₀ = ⊔ᵢ X|Uᵢ ⊆ ⊔ᵢ Uᵢ` has, over each piece, the
resolution of the piece [Kol07, Proposition 37, proof]. At a gluing datum `Γ` of the local
resolutions and a relatively compact family `W ≤ Γ.W` of opens of the pieces' ambients: the
restriction `Ỹ(W') → Ỹ(W)` of a piece's local resolution to a smaller open
(`LocalResolutionRestrictHom.lean`), the part of the glued space over `pieceDom i Wᵢ` identified
with `Ỹ(Wᵢ)` (the gluing's `partIso`), sent into the functor's resolution of the disjoint-union
triple over `U_Σ` (`localResolutionHomOn` at the summand inclusion, `resIn`) and then into the
transported last transform `Sp(Y_r)` (`AmbientEmb.lean`) — the lift `glueLift i`, an isomorphism
onto the part of `Sp(Y_r)` over the `i`-th part of `Y₀`, compatible with `Π_r|_{Y_r}` and `emb i`
(`glueMap_restrictSet_comp_glueLift`); finally the ambient blow-up factorization
`ambientBlowUpFactorizationOfGluing` for any open covered by the pieces `pieceDom i Wᵢ`, and
clause (4) of `exists_functorial_resolution` at `U` for the glued space's map, with the independence
of the local resolution as the hypothesis `hind`. Not in the sources beyond Kollár's proof;
bookkeeping.
-/

@[expose] public section


noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

namespace LocalEmbeddingData

open _root_.Manifold

variable {X : AnalyticSpace.{u} 𝕜} {U : Set X}

/-- The part of the glued space over `pieceDom i Wᵢ` is open. Internal. -/
theorem isOpen_preimage_pieceDom (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (i : D.ι) :
    IsOpen (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹' (D.pieceDom i (W i) : Set X)) :=
  (D.pieceDom i (W i)).isOpen.preimage (Hom.continuous_toFun _)

/-- The two spellings of the part of the glued space over `pieceDom i Wᵢ` — `restrictSet` and the
glue's `Opens.comap` — are the same open. Internal. -/
theorem coe_openOf_preimage_pieceDom (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (i : D.ι) :
    ((openOf Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹' (D.pieceDom i (W i) : Set X)) :
      Opens Γ.glue.gluedOver.toKLocallyRingedSpace) : Set Γ.glue.gluedOver.toKLocallyRingedSpace) =
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun Γ.glue.descMap, Hom.continuous_toFun _⟩
        (D.pieceDom i (W i)) : Set Γ.glue.gluedOver.toKLocallyRingedSpace) := by
  rw [openOf_of_isOpen _ (D.isOpen_preimage_pieceDom bed Γ W i)]
  rfl

/-- **The part of the glued space over `pieceDom i Wᵢ` into the `i`-th piece**
([Wlo09, §4, (3)⇒(4)]: the gluing of the `Ṽᵢ`) — the gluing's `partIso` at
`P := pieceDom i Wᵢ ≤ dom i`, then the inclusion of the part of the piece. -/
def partIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G)) (hle : ∀ i, W i ≤ Γ.W i)
    (i : D.ι) :
    (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
      ((D.embedding i).localResolution bed (Γ.W i)
        (Γ.isCompact_closure_W i)).toKLocallyRingedSpace :=
  (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i)).hom ≫
    (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).inv ≫
    ofRestrict _ _

theorem isOpenImmersion_partIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hle : ∀ i, W i ≤ Γ.W i) (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.partIn bed Γ W hle i).1 := by
  have h1 : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i)).hom.1 := by
    have := KIso.isIso_hom_val (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i))
    infer_instance
  have h2 : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).inv.1 := by
    have : IsIso
        (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).inv.1 :=
      KIso.isIso_hom_val
        (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).symm
    infer_instance
  unfold partIn
  exact @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ h1 _
    (@AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ h2 _ inferInstance)

/-- Its range: the part of the piece over `Wᵢ` (in the spelling of `LocalResolutionOn.lean`). -/
theorem range_toFun_partIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hle : ∀ i, W i ≤ Γ.W i) (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun (D.partIn bed Γ W hle i)) =
      {y | ((bed.seqOn (D.embedding i).ambientTriple (D.embedding i).domBEDan_ambientTriple (Γ.W i)
          (Γ.isCompact_closure_W i)).toSuccession.stageMap (Fin.last _)
          ((bed.lastIdealOn (D.embedding i).ambientTriple (D.embedding i).domBEDan_ambientTriple
              (Γ.W i) (Γ.isCompact_closure_W i)).toAnalyticSpaceι y)).1 ∈ W i} := by
  ext r
  constructor
  · rintro ⟨y, rfl⟩
    exact ((D.embedding i).pieceOverIncl_mem_domOpens_iff (Γ.W i) (W i) _).mp
      (KLocallyRingedSpace.Hom.toFun
        (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).inv
        (KLocallyRingedSpace.Hom.toFun
          (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i)).hom y)).2
  · intro hr
    have hr' : KLocallyRingedSpace.Hom.toFun
        (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)) r ∈ D.pieceDom i (W i) :=
      ((D.embedding i).pieceOverIncl_mem_domOpens_iff (Γ.W i) (W i) _).mpr hr
    refine ⟨KLocallyRingedSpace.Hom.toFun
      (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i)).inv
      (KLocallyRingedSpace.Hom.toFun
        (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).hom
          ⟨r, hr'⟩), ?_⟩
    exact (congrArg (fun q => KLocallyRingedSpace.Hom.toFun
        (ofRestrict ((D.embedding i).localResolution bed (Γ.W i)
          (Γ.isCompact_closure_W i)).toKLocallyRingedSpace
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
            (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)), Hom.continuous_toFun _⟩
            (D.pieceDom i (W i))))
        (KLocallyRingedSpace.Hom.toFun
          (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))).inv q))
      (KIso.toFun_hom_toFun_inv (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i))
        _)).trans
      (congrArg (fun q => KLocallyRingedSpace.Hom.toFun
        (ofRestrict ((D.embedding i).localResolution bed (Γ.W i)
          (Γ.isCompact_closure_W i)).toKLocallyRingedSpace
          (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun
            (D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i)), Hom.continuous_toFun _⟩
            (D.pieceDom i (W i)))) q)
        (KIso.toFun_inv_toFun_hom
          (Γ.glue.partIso i (D.pieceDom i (W i)) ((D.embedding i).domOpens_mono (hle i))) ⟨r, hr'⟩))

/-- It lies over `des` (`partIso_inv_comp_over`). -/
theorem partIn_comp_pieceToSpace (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hle : ∀ i, W i ≤ Γ.W i) (i : D.ι) :
    D.partIn bed Γ W hle i ≫ D.pieceToSpace bed i (Γ.W i) (Γ.isCompact_closure_W i) =
      ofRestrict Γ.glue.gluedOver.toKLocallyRingedSpace
        (openOf _
          (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹' (D.pieceDom i (W i) : Set X))) ≫
      Γ.glue.descMap := by
  unfold partIn
  exact (Category.assoc _ _ _).trans
    ((congrArg
      (fun k => (restrictOpenIsoOfSetEq (D.coe_openOf_preimage_pieceDom bed Γ W i)).hom ≫ k)
      ((Category.assoc _ _ _).trans
        (Γ.glue.partIso_inv_comp_over i (D.pieceDom i (W i))
          ((D.embedding i).domOpens_mono (hle i))))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ Γ.glue.descMap)
          (restrictOpenIsoOfSetEq_hom_comp (D.coe_openOf_preimage_pieceDom bed Γ W i)))))


/-- **The local resolution over `Wᵢ` into the functor's on `T_Σ|U_Σ`** (the lift of
[Kol07, Definition 30.1]): `localResolutionHomOn` at `g := sigmaMk i`. -/
def resIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
      (bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW)).toKLocallyRingedSpace :=
  bed.localResolutionHomOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.embedding i).ambientTriple
    (D.embedding i).domBEDan_ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    (isAnalyticOpenEmbedding_sigmaMk _ i) (D.isPullbackOf_ambientTriple_sigmaTriple i) (W i) (hW i)
    (D.image_subset_ambImage W i) hbed

theorem isOpenImmersion_resIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.resIn bed W hW hbed i).1 :=
  bed.isOpenImmersion_localResolutionHomOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.embedding i).ambientTriple
    (D.embedding i).domBEDan_ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    (isAnalyticOpenEmbedding_sigmaMk _ i) (D.isPullbackOf_ambientTriple_sigmaTriple i) (W i) (hW i)
    (D.image_subset_ambImage W i) hbed

theorem range_toFun_resIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun (D.resIn bed W hW hbed i)) =
      {y | ((bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
          (D.isCompact_closure_ambImage W hW)).toSuccession.stageMap (Fin.last _)
          ((bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
              (D.isCompact_closure_ambImage W hW)).toAnalyticSpaceι y)).1 ∈
        ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
          (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))} :=
  bed.range_toFun_localResolutionHomOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.embedding i).ambientTriple
    (D.embedding i).domBEDan_ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    (isAnalyticOpenEmbedding_sigmaMk _ i) (D.isPullbackOf_ambientTriple_sigmaTriple i) (W i) (hW i)
    (D.image_subset_ambImage W i) hbed

/-- It lies over the summand inclusion of the restricted closed subspaces
(`localResolutionHomOn_comp_map`). -/
theorem resIn_comp_localResolutionMapOn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    D.resIn bed W hW hbed i ≫
        (bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
          (D.isCompact_closure_ambImage W hW) :
          (bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
            (D.isCompact_closure_ambImage W hW)).toKLocallyRingedSpace ⟶
          (BEDanFamStar.restrictedIdealOn D.sigmaTriple
            (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace) =
      ((D.embedding i).localResolutionMap bed (W i) (hW i) :
          ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
            ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace) ≫
        (IdealSheaf.homOfPullbackEq _ _
          (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple (D.ambImage W)
            (D.embedding i).ambientTriple
            (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (W i)
            (D.image_subset_ambImage W i) (D.isPullbackOf_ambientTriple_sigmaTriple i)) :
          ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
            (BEDanFamStar.restrictedIdealOn D.sigmaTriple
              (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace) :=
  bed.localResolutionHomOn_comp_map D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.embedding i).ambientTriple
    (D.embedding i).domBEDan_ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    (isAnalyticOpenEmbedding_sigmaMk _ i) (D.isPullbackOf_ambientTriple_sigmaTriple i) (W i) (hW i)
    (D.image_subset_ambImage W i) hbed

/-- **The part of the glued space over `pieceDom i Wᵢ` IS the local resolution over `Wᵢ`**
(`isoOfRangeEq` of `partIn` and of the restriction `Ỹ(Wᵢ) → Ỹ(Γ.Wᵢ)`). -/
def resIso (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ≅
      ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace :=
  @isoOfRangeEq _ _ _ _ _ (D.partIn bed Γ W hle i)
    ((D.embedding i).localResolutionRestrictHom bed (Γ.W i) (Γ.isCompact_closure_W i) (W i) (hW i)
      (hle i) hbed :
      ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
        ((D.embedding i).localResolution bed (Γ.W i)
          (Γ.isCompact_closure_W i)).toKLocallyRingedSpace)
    (D.isOpenImmersion_partIn bed Γ W hle i)
    ((D.embedding i).isOpenImmersion_localResolutionRestrictHom bed (Γ.W i)
      (Γ.isCompact_closure_W i) (W i) (hW i) (hle i) hbed)
    ((D.range_toFun_partIn bed Γ W hle i).trans
      ((D.embedding i).range_toFun_localResolutionRestrictHom bed (Γ.W i) (Γ.isCompact_closure_W i)
        (W i) (hW i) (hle i) hbed).symm)

theorem resIso_hom_comp_localResolutionRestrictHom (D : LocalEmbeddingData 𝕜 X U)
    (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    (D.resIso bed Γ W hW hle hbed i).hom ≫
        ((D.embedding i).localResolutionRestrictHom bed (Γ.W i) (Γ.isCompact_closure_W i) (W i)
          (hW i) (hle i) hbed :
          ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
            ((D.embedding i).localResolution bed (Γ.W i)
              (Γ.isCompact_closure_W i)).toKLocallyRingedSpace) =
      D.partIn bed Γ W hle i := by
  unfold resIso
  exact @isoOfRangeEq_hom_comp _ _ _ _ _ _ _ (D.isOpenImmersion_partIn bed Γ W hle i)
    ((D.embedding i).isOpenImmersion_localResolutionRestrictHom bed (Γ.W i)
      (Γ.isCompact_closure_W i) (W i) (hW i) (hle i) hbed) _

/-- The identification `Sp(Y_r) ≅ Ỹ_Σ(U_Σ)` of `AmbientEmb.lean` as an isomorphism of `K`-spaces.
Internal. -/
def ambLastIsoK (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) :
    (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace ≅
      (bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW)).toKLocallyRingedSpace :=
  haveI : IsIso (BEDanFamStar.ambLastIso bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW) (D.ambTheta W)) :=
    BEDanFamStar.isIso_ambLastIso bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW) (D.ambTheta W)
  @asIso _ _ _ _ (BEDanFamStar.ambLastIso bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW) (D.ambTheta W) :
      (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace ⟶
        (bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
          (D.isCompact_closure_ambImage W hW)).toKLocallyRingedSpace)
    (isIso_toKLocallyRingedSpace_of_isIso _)

/-- **`Y|des⁻¹(pieceDom i Wᵢ) → Sp(Y_r)`**: `resIso`, `resIn`, then the identification
`ambLastIso⁻¹` (`AmbientEmb.lean`). -/
def liftIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
      (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace :=
  (D.resIso bed Γ W hW hle hbed i).hom ≫ D.resIn bed W hW hbed i ≫ (D.ambLastIsoK bed W hW).inv

theorem isOpenImmersion_liftIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.liftIn bed Γ W hW hle hbed i).1 := by
  have h1 : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (D.resIso bed Γ W hW hle hbed i).hom.1 := by
    have := KIso.isIso_hom_val (D.resIso bed Γ W hW hle hbed i)
    infer_instance
  have h3 : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (D.ambLastIsoK bed W hW).inv.1 := by
    have : IsIso (D.ambLastIsoK bed W hW).inv.1 :=
      KIso.isIso_hom_val (D.ambLastIsoK bed W hW).symm
    infer_instance
  unfold liftIn
  exact @AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ h1 _
    (@AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _
      (D.isOpenImmersion_resIn bed W hW hbed i) _ h3)

/-- The ambient image of the last stage of a point of `Sp(Y_r)`, read through `ambLastIso`, is `Θ₀`
of the ambient image of its `Π_r`-image (the point form of the transport square of
`AmbientEmb.lean`). Internal. -/
theorem stageMap_ambLastIso_eq (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (p : (D.glueLast W bed hW).toAnalyticSpace) :
    ((bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW)).toSuccession.stageMap (Fin.last _)
        ((bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
            (D.isCompact_closure_ambImage W hW)).toAnalyticSpaceι
          ((BEDanFamStar.ambLastIso bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
              (D.isCompact_closure_ambImage W hW) (D.ambTheta W)) p))).1 =
      D.ambTheta₀ W
        ((D.glueIdeal W).toAnalyticSpaceι
          (D.glueMap W bed hW p)) :=
  congrArg (fun z =>
      ((BEDanFamStar.restrictedIdealOn D.sigmaTriple (D.ambImage W)).toAnalyticSpaceι z).1)
    (congrArg (fun k => AnalyticSpace.Hom.toFun k p)
      (BEDanFamStar.ambMapOn_square bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW) (D.ambTheta W)))

/-- Its range: the points of `Y_r` over the `i`-th piece's part of `Y₀`. -/
theorem range_toFun_liftIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun (D.liftIn bed Γ W hW hle hbed i)) =
      {p | (D.glueMap W bed hW) p ∈
        (D.glueIdeal W).overPiece i} := by
  ext p
  -- `p` is in the range iff `ambLastIso p` is in the range of `resIn`
  have key : p ∈ Set.range (KLocallyRingedSpace.Hom.toFun (D.liftIn bed Γ W hW hle hbed i)) ↔
      KLocallyRingedSpace.Hom.toFun (D.ambLastIsoK bed W hW).hom p ∈
        Set.range (KLocallyRingedSpace.Hom.toFun (D.resIn bed W hW hbed i)) := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨KLocallyRingedSpace.Hom.toFun (D.resIso bed Γ W hW hle hbed i).hom y,
        (KIso.toFun_hom_toFun_inv (D.ambLastIsoK bed W hW) _).symm⟩
    · rintro ⟨z, hz⟩
      refine ⟨KLocallyRingedSpace.Hom.toFun (D.resIso bed Γ W hW hle hbed i).inv z, ?_⟩
      change KLocallyRingedSpace.Hom.toFun (D.ambLastIsoK bed W hW).inv
        (KLocallyRingedSpace.Hom.toFun (D.resIn bed W hW hbed i)
          (KLocallyRingedSpace.Hom.toFun (D.resIso bed Γ W hW hle hbed i).hom
            (KLocallyRingedSpace.Hom.toFun (D.resIso bed Γ W hW hle hbed i).inv z))) = p
      rw [KIso.toFun_hom_toFun_inv, hz]
      exact KIso.toFun_inv_toFun_hom (D.ambLastIsoK bed W hW) p
  refine key.trans ((Set.ext_iff.mp (D.range_toFun_resIn bed W hW hbed i) _).trans ?_)
  change ((bed.seqOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW)).toSuccession.stageMap (Fin.last _)
      ((bed.lastIdealOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
          (D.isCompact_closure_ambImage W hW)).toAnalyticSpaceι
        ((BEDanFamStar.ambLastIso bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
            (D.isCompact_closure_ambImage W hW) (D.ambTheta W)) p))).1 ∈
      ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
        (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)) ↔
    ((D.glueIdeal W).toAnalyticSpaceι
      (D.glueMap W bed hW p)).1 = i
  exact (Iff.of_eq (congrArg
      (fun z => z ∈ ⇑(sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) ''
        (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))
      (D.stageMap_ambLastIso_eq bed W hW p))).trans
    (D.ambTheta₀_mem_image_iff W i _)

end LocalEmbeddingData

namespace LocalEmbeddingData

open _root_.Manifold

variable {X : AnalyticSpace.{u} 𝕜} {U : Set X}

/-- The two maps `Sp(Wᵢ)/𝓘ᵢ|Wᵢ → Sp(⊔ⱼ Gⱼ)/𝓘_Σ` agree: `homOfPullbackEq` along the restricted
summand inclusion followed by the restriction open immersion over `U_Σ`, and the
restriction-of-a-quotient map followed by the summand inclusion (both lie over
`Sp(Wᵢ ↪ ⊔ⱼ Gⱼ)`). Internal. -/
theorem homOfPullbackEq_restrictMap_comp_restrictOpensHom (D : LocalEmbeddingData 𝕜 X U)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G)) (i : D.ι) :
    (IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple (D.ambImage W)
          (D.embedding i).ambientTriple
          (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (W i)
          (D.image_subset_ambImage W i) (D.isPullbackOf_ambientTriple_sigmaTriple i)) :
        ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
          (BEDanFamStar.restrictedIdealOn D.sigmaTriple
            (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace) ≫
      (IdealSheaf.restrictOpensHom D.sigmaTriple.I (D.ambImage W) :
        (BEDanFamStar.restrictedIdealOn D.sigmaTriple
            (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace ⟶
          D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace) =
    D.sumIn W i := by
  obtain ⟨H, hH⟩ : ∃ H :
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (BEDanFamStar.restrictedIdealOn D.sigmaTriple
        (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace,
      H = IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple (D.ambImage W)
          (D.embedding i).ambientTriple
          (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (W i)
          (D.image_subset_ambImage W i) (D.isPullbackOf_ambientTriple_sigmaTriple i)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : (BEDanFamStar.restrictedIdealOn D.sigmaTriple
        (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace ⟶
      D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace,
      Q = IdealSheaf.restrictOpensHom D.sigmaTriple.I (D.ambImage W) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R :
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (D.embedding i).ideal.toAnalyticSpace.toKLocallyRingedSpace,
      R = (D.embedding i).restrictedIdealHom (W i) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : (D.embedding i).ideal.toAnalyticSpace.toKLocallyRingedSpace ⟶
      D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace,
      S = D.sigmaSummandHom i := ⟨_, rfl⟩
  have e1 : Q ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        D.sigmaAmbient).toKLocallyRingedSpace D.sigmaTriple.I =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (D.sigmaAmbient.restrict (D.ambImage W))).toKLocallyRingedSpace
        (BEDanFamStar.restrictedIdealOn D.sigmaTriple (D.ambImage W)) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (D.sigmaAmbient.inclusion (D.ambImage W)) := by
    rw [hQ]
    exact homOfPullbackEq_comp_toAnalyticSpaceι _ _ _
  have e2 : H ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (D.sigmaAmbient.restrict (D.ambImage W))).toKLocallyRingedSpace
        (BEDanFamStar.restrictedIdealOn D.sigmaTriple (D.ambImage W)) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        ((pieceAmbient.{u} 𝕜 (D.embedding i).G).restrict (W i))).toKLocallyRingedSpace
        ((D.embedding i).restrictedIdeal (W i)) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (AnalyticMap.restrictMap (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (W i)
          (D.ambImage W) (D.image_subset_ambImage W i)) := by
    rw [hH]
    exact homOfPullbackEq_comp_toAnalyticSpaceι _ _ _
  have e3 : S ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        D.sigmaAmbient).toKLocallyRingedSpace D.sigmaTriple.I =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (pieceAmbient.{u} 𝕜 (D.embedding i).G)).toKLocallyRingedSpace (D.embedding i).ideal ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) := by
    rw [hS]
    exact D.sigmaSummandHom_comp_toAnalyticSpaceι i
  have e4 : R ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        (pieceAmbient.{u} 𝕜 (D.embedding i).G)).toKLocallyRingedSpace (D.embedding i).ideal =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        ((pieceAmbient.{u} 𝕜 (D.embedding i).G).restrict (W i))).toKLocallyRingedSpace
        ((D.embedding i).restrictedIdeal (W i)) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
        ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (W i)) := by
    rw [hR]
    exact (D.embedding i).toAnalyticSpaceι_comp_restrictedIdealHom (W i)
  have e5 := toSpaceHom_comp_eq
    (AnalyticMap.restrictMap (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (W i)
      (D.ambImage W) (D.image_subset_ambImage W i))
    (D.sigmaAmbient.inclusion (D.ambImage W))
    ((sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).comp
      ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (W i))) fun _ => rfl
  have e6 := toSpaceHom_comp_eq ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (W i))
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
    ((sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i).comp
      ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (W i))) fun _ => rfl
  have hK : H ≫ Q = R ≫ S := by
    refine Hom.ext_of_comp_quotientι _ ?_
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => H ≫ k) e1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ toSpaceHom
          (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜)) (D.sigmaAmbient.inclusion (D.ambImage W)))
          e2).trans
        ((Category.assoc _ _ _).trans ((congrArg (fun k => quotientι (toSpace
            (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
            ((pieceAmbient.{u} 𝕜 (D.embedding i).G).restrict (W i))).toKLocallyRingedSpace
            ((D.embedding i).restrictedIdeal (W i)) ≫ k) (e5.trans e6.symm)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ toSpaceHom
              (ContinuousLinearEquiv.refl 𝕜 (Fin D.n → 𝕜))
              (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)) e4.symm).trans
            ((Category.assoc _ _ _).trans ((congrArg (fun k => R ≫ k) e3.symm).trans
              (Category.assoc _ _ _).symm)))))))))
  subst hH hQ hR hS
  exact hK

/-- `resIso` followed by the local resolution map over `Wᵢ` is `des` restricted over
`pieceDom i Wᵢ` followed by `pieceIso` (both lie over `X`: the open immersion of the piece over
`Wᵢ` is a monomorphism). Internal. -/
theorem resIso_hom_comp_localResolutionMap (D : LocalEmbeddingData 𝕜 X U)
    (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    (D.resIso bed Γ W hW hle hbed i).hom ≫
        ((D.embedding i).localResolutionMap bed (W i) (hW i) :
          ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
            ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace) =
      (Hom.restrictSet Γ.glue.descMap (D.pieceDom i (W i) : Set X) :
          (restrictSet Γ.glue.gluedOver
            (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
              (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
          (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace) ≫
        (D.pieceIso W i).hom := by
  have hP := (D.embedding i).isOpenImmersion_pieceOverHom (W i)
  refine Hom.ext_of_comp_of_isOpenImmersion ((D.embedding i).pieceOverHom (W i)) ?_
  obtain ⟨σ, hσ⟩ : ∃ σ : (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
      ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace,
      σ = (D.resIso bed Γ W hW hle hbed i).hom := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace,
      A = (D.embedding i).localResolutionMap bed (W i) (hW i) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
      ((D.embedding i).localResolution bed (Γ.W i) (Γ.isCompact_closure_W i)).toKLocallyRingedSpace,
      ρ = (D.embedding i).localResolutionRestrictHom bed (Γ.W i) (Γ.isCompact_closure_W i) (W i)
        (hW i) (hle i) hbed := ⟨_, rfl⟩
  obtain ⟨dr, hdr⟩ : ∃ dr : (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
      (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace,
      dr = Hom.restrictSet Γ.glue.descMap
        (D.pieceDom i (W i) : Set X) := ⟨_, rfl⟩
  have hTP : A ≫ (D.embedding i).pieceOverHom (W i) =
      (D.embedding i).toSpaceMap bed (W i) (hW i) := by
    rw [hA]
    exact ((D.embedding i).toSpaceMap_eq_comp_pieceOverHom bed (W i) (hW i)).symm
  have hK4 : ρ ≫ (D.embedding i).toSpaceMap bed (Γ.W i) (Γ.isCompact_closure_W i) =
      (D.embedding i).toSpaceMap bed (W i) (hW i) := by
    rw [hρ]
    exact (D.embedding i).localResolutionRestrictHom_comp_toSpaceMap bed (Γ.W i)
      (Γ.isCompact_closure_W i) (W i) (hW i) (hle i) hbed
  have hσρ : σ ≫ ρ = D.partIn bed Γ W hle i := by
    rw [hσ, hρ]
    exact D.resIso_hom_comp_localResolutionRestrictHom bed Γ W hW hle hbed i
  have hπ : D.partIn bed Γ W hle i ≫ (D.embedding i).toSpaceMap bed (Γ.W i)
      (Γ.isCompact_closure_W i) =
      ofRestrict Γ.glue.gluedOver.toKLocallyRingedSpace
        (openOf _
          (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹' (D.pieceDom i (W i) : Set X))) ≫
      Γ.glue.descMap :=
    D.partIn_comp_pieceToSpace bed Γ W hle i
  have hιP : (D.pieceIso W i).hom ≫ (D.embedding i).pieceOverHom (W i) =
      ofRestrict X.toKLocallyRingedSpace
        (openOf X (D.pieceDom i (W i) : Set X)) :=
    D.pieceIso_hom_comp_pieceOverHom W i
  have hdrn : dr ≫ ofRestrict X.toKLocallyRingedSpace
        (openOf X (D.pieceDom i (W i) : Set X)) =
      ofRestrict Γ.glue.gluedOver.toKLocallyRingedSpace
        (openOf _
          (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹' (D.pieceDom i (W i) : Set X))) ≫
      Γ.glue.descMap := by
    rw [hdr]
    exact Hom.restrictTo_comp_ofRestrict Γ.glue.descMap _ _
      (Hom.mapsTo_openOf Γ.glue.descMap _)
  have hK : (σ ≫ A) ≫ (D.embedding i).pieceOverHom (W i) =
      (dr ≫ (D.pieceIso W i).hom) ≫ (D.embedding i).pieceOverHom (W i) :=
    (Category.assoc _ _ _).trans ((congrArg (fun k => σ ≫ k) hTP).trans
      ((congrArg (fun k => σ ≫ k) hK4.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (D.embedding i).toSpaceMap bed (Γ.W i)
          (Γ.isCompact_closure_W i)) hσρ).trans (hπ.trans (hdrn.symm.trans
          ((congrArg (fun k => dr ≫ k) hιP.symm).trans (Category.assoc _ _ _).symm)))))))
  subst hσ hA hdr
  exact hK

/-- The compatibility with `map` and `emb` under `ambIn` (`glueMap_restrictSet_comp_glueLift` before
the restriction to the parts). -/
theorem liftIn_comp_glueMap_ambIn (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    D.liftIn bed Γ W hW hle hbed i ≫
        (D.glueMap W bed hW : (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace ⟶
          (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace) ≫ D.ambIn W =
      (D.resIso bed Γ W hW hle hbed i).hom ≫
        ((D.embedding i).localResolutionMap bed (W i) (hW i) :
          ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
            ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace) ≫
        D.sumIn W i := by
  obtain ⟨M, hM⟩ : ∃ M : (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace, M = D.glueMap W bed hW := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (BEDanFamStar.restrictedIdealOn D.sigmaTriple
        (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace,
      J = BEDanFamStar.ambIdealIso D.sigmaTriple (D.ambImage W) (D.ambTheta W) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : (BEDanFamStar.restrictedIdealOn D.sigmaTriple
        (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace ⟶
      D.sigmaTriple.I.toAnalyticSpace.toKLocallyRingedSpace,
      Q = IdealSheaf.restrictOpensHom D.sigmaTriple.I (D.ambImage W) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (bed.localResolutionOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW)).toKLocallyRingedSpace ⟶
      (BEDanFamStar.restrictedIdealOn D.sigmaTriple
        (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace,
      P = bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
        (D.isCompact_closure_ambImage W hW) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace,
      A = (D.embedding i).localResolutionMap bed (W i) (hW i) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H :
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (BEDanFamStar.restrictedIdealOn D.sigmaTriple
        (D.ambImage W)).toAnalyticSpace.toKLocallyRingedSpace,
      H = IdealSheaf.homOfPullbackEq _ _
        (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple (D.ambImage W)
          (D.embedding i).ambientTriple
          (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (W i)
          (D.image_subset_ambImage W i) (D.isPullbackOf_ambientTriple_sigmaTriple i)) := ⟨_, rfl⟩
  -- the transport square, inverted: `ambLastIso⁻¹ ≫ Π_r ≫ ambIdealIso = localResolutionMapOn`
  have sq : (D.ambLastIsoK bed W hW).hom ≫ P = M ≫ J := by
    rw [hP, hM, hJ]
    exact BEDanFamStar.ambMapOn_square bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
      (D.isCompact_closure_ambImage W hW) (D.ambTheta W)
  have sq' : (D.ambLastIsoK bed W hW).inv ≫ M ≫ J = P :=
    (congrArg (fun k => (D.ambLastIsoK bed W hW).inv ≫ k) sq.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ P) (D.ambLastIsoK bed W hW).inv_hom_id).trans
          (Category.id_comp P)))
  have sq2 : D.resIn bed W hW hbed i ≫ P = A ≫ H := by
    rw [hP, hA, hH]
    exact D.resIn_comp_localResolutionMapOn bed W hW hbed i
  have sq3 : H ≫ Q = D.sumIn W i := by
    rw [hH, hQ]
    exact D.homOfPullbackEq_restrictMap_comp_restrictOpensHom W i
  have hamb : D.ambIn W = J ≫ Q := by subst hJ hQ; rfl
  have hK : ((D.resIso bed Γ W hW hle hbed i).hom ≫ D.resIn bed W hW hbed i ≫
        (D.ambLastIsoK bed W hW).inv) ≫ M ≫ J ≫ Q =
      (D.resIso bed Γ W hW hle hbed i).hom ≫ A ≫ D.sumIn W i :=
    (Category.assoc _ _ _).trans (congrArg (fun k => (D.resIso bed Γ W hW hle hbed i).hom ≫ k)
      ((Category.assoc _ _ _).trans ((congrArg (fun k => D.resIn bed W hW hbed i ≫ k)
          ((congrArg (fun k => (D.ambLastIsoK bed W hW).inv ≫ k) (Category.assoc _ _ _).symm).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ Q) sq')))).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ Q) sq2).trans
          ((Category.assoc _ _ _).trans (congrArg (fun k => A ≫ k) sq3)))))))
  have hfin : D.liftIn bed Γ W hW hle hbed i ≫ M ≫ D.ambIn W =
      (D.resIso bed Γ W hW hle hbed i).hom ≫ A ≫ D.sumIn W i := by
    unfold liftIn
    exact (congrArg (fun k => ((D.resIso bed Γ W hW hle hbed i).hom ≫ D.resIn bed W hW hbed i ≫
      (D.ambLastIsoK bed W hW).inv) ≫ M ≫ k) hamb).trans hK
  subst hM hA
  exact hfin

/-- The part `Π_r⁻¹(overPiece i)` of `Sp(Y_r)` is open. Internal. -/
theorem isOpen_preimage_overPiece (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) (i : D.ι) :
    IsOpen (⇑(D.glueMap W bed hW) ⁻¹'
      (D.glueIdeal W).overPiece i) :=
  (IdealSheaf.isOpen_overPiece _ i).preimage (Hom.continuous_toFun _)

/-- The inclusion of the part `Π_r⁻¹(overPiece i)` is an open immersion (the KSpace instance,
named so that it can be passed explicitly). Internal. -/
theorem isOpenImmersion_ofRestrict_preimage_overPiece (D : LocalEmbeddingData 𝕜 X U)
    (bed : BEDanFamStar.{u} 𝕜) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)))) (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace
        (openOf _
          (⇑(D.glueMap W bed hW) ⁻¹'
            (D.glueIdeal W).overPiece i))).1 :=
  inferInstance

/-- The isomorphism behind `glueLift i`: `liftIn` against the inclusion of the part
`Π_r⁻¹(overPiece i)` (`isoOfRangeEq`). Internal. -/
def glueLiftIso (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ≅
      ((D.glueLast W bed hW).toAnalyticSpace.restrictSet
        (⇑(D.glueMap W bed hW) ⁻¹'
          (D.glueIdeal W).overPiece i)).toKLocallyRingedSpace :=
  @isoOfRangeEq _ _ _ _ _ (D.liftIn bed Γ W hW hle hbed i)
    (ofRestrict (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace
      (openOf _
        (⇑(D.glueMap W bed hW) ⁻¹'
          (D.glueIdeal W).overPiece i)))
    (D.isOpenImmersion_liftIn bed Γ W hW hle hbed i)
    (D.isOpenImmersion_ofRestrict_preimage_overPiece bed W hW i)
    ((D.range_toFun_liftIn bed Γ W hW hle hbed i).trans
      ((range_toFun_ofRestrict _ _).trans
        (congrArg SetLike.coe (openOf_of_isOpen _
          (D.isOpen_preimage_overPiece bed W hW i)))).symm)

/-- **`Y|des⁻¹(pieceDom i Wᵢ) ≅ Sp(Y_r)|_{Π_r⁻¹(overPiece i)}`** — the lift of the glued space into
the last transform ([Kol07, Proposition 37, proof]). -/
def glueLift (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (Γ : D.ResolutionGluing bed)
    (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
        (D.pieceDom i (W i) : Set
        X)) ⟶ (D.glueLast W bed hW).toAnalyticSpace.restrictSet
        (⇑(D.glueMap W bed hW) ⁻¹' (D.glueIdeal W).overPiece i)) :=
  (D.glueLiftIso bed Γ W hW hle hbed i).hom

theorem isIso_glueLift (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    IsIso (D.glueLift bed Γ W hW hle hbed i) :=
  isIso_of_isIso_toKLocallyRingedSpace _
    (D.glueLiftIso bed Γ W hW hle hbed i).isIso_hom

/-- `Π_r|_{Y_r}` restricted over the `i`-th part, after `glueLift i`, is `emb i` after `des`
restricted over `pieceDom i Wᵢ`. -/
theorem glueMap_restrictSet_comp_glueLift (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (i : D.ι) :
    D.glueLift bed Γ W hW hle hbed i ≫
        (D.glueMap W bed hW).restrictSet ((D.glueIdeal W).overPiece i) =
      AnalyticSpace.Hom.restrictSet (Γ.glue.descMap : Γ.glue.gluedOver ⟶ X)
          (D.pieceDom i (W i) : Set X) ≫ D.glueEmb W i := by
  -- names
  obtain ⟨L, hL⟩ : ∃ L : (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
      ((D.glueLast W bed hW).toAnalyticSpace.restrictSet
        (⇑(D.glueMap W bed hW) ⁻¹'
          (D.glueIdeal W).overPiece i)).toKLocallyRingedSpace,
      L = D.glueLift bed Γ W hW hle hbed i := ⟨_, rfl⟩
  obtain ⟨Mr, hMr⟩ : ∃ Mr : ((D.glueLast W bed hW).toAnalyticSpace.restrictSet
        (⇑(D.glueMap W bed hW) ⁻¹'
          (D.glueIdeal W).overPiece i)).toKLocallyRingedSpace ⟶
      ((D.glueIdeal W).toAnalyticSpace.restrictSet
        ((D.glueIdeal W).overPiece i)).toKLocallyRingedSpace,
      Mr = (D.glueMap W bed hW).restrictSet ((D.glueIdeal W).overPiece i) := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace ⟶
      ((D.glueIdeal W).toAnalyticSpace.restrictSet
        ((D.glueIdeal W).overPiece i)).toKLocallyRingedSpace,
      Em = D.glueEmb W i := ⟨_, rfl⟩
  obtain ⟨dr, hdr⟩ : ∃ dr : (restrictSet Γ.glue.gluedOver
        (KLocallyRingedSpace.Hom.toFun Γ.glue.descMap ⁻¹'
          (D.pieceDom i (W i) : Set X))).toKLocallyRingedSpace ⟶
      (X.restrictSet (D.pieceDom i (W i))).toKLocallyRingedSpace,
      dr = Hom.restrictSet Γ.glue.descMap
        (D.pieceDom i (W i) : Set X) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace, M = D.glueMap W bed hW := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ((D.embedding i).localResolution bed (W i) (hW i)).toKLocallyRingedSpace ⟶
      ((D.embedding i).restrictedIdeal (W i)).toAnalyticSpace.toKLocallyRingedSpace,
      A = (D.embedding i).localResolutionMap bed (W i) (hW i) := ⟨_, rfl⟩
  -- the facts
  have h1 : L ≫ ofRestrict (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace
      (openOf _
        (⇑(D.glueMap W bed hW) ⁻¹'
          (D.glueIdeal W).overPiece i)) =
      D.liftIn bed Γ W hW hle hbed i := by
    rw [hL]
    exact @isoOfRangeEq_hom_comp _ _ _ _ _ _ _ (D.isOpenImmersion_liftIn bed Γ W hW hle hbed i)
      (D.isOpenImmersion_ofRestrict_preimage_overPiece bed W hW i) _
  have h2 : Mr ≫ ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
      (openOf _ ((D.glueIdeal W).overPiece i)) =
      ofRestrict (D.glueLast W bed hW).toAnalyticSpace.toKLocallyRingedSpace
        (openOf _
          (⇑(D.glueMap W bed hW) ⁻¹'
            (D.glueIdeal W).overPiece i)) ≫
      M := by
    rw [hMr, hM]
    exact Hom.restrictTo_comp_ofRestrict (D.glueMap W bed hW) _ _
      (Hom.mapsTo_openOf (D.glueMap W bed hW) _)
  have h3 : Em ≫ ofRestrict (D.glueIdeal W).toAnalyticSpace.toKLocallyRingedSpace
        (openOf _ ((D.glueIdeal W).overPiece i)) ≫ D.ambIn W =
      (D.pieceIso W i).hom ≫ D.sumIn W i := by
    rw [hEm]
    exact D.glueEmb_comp_ambIn W i
  have h4 : D.liftIn bed Γ W hW hle hbed i ≫ M ≫ D.ambIn W =
      (D.resIso bed Γ W hW hle hbed i).hom ≫ A ≫ D.sumIn W i := by
    rw [hM, hA]
    exact D.liftIn_comp_glueMap_ambIn bed Γ W hW hle hbed i
  have h5 : (D.resIso bed Γ W hW hle hbed i).hom ≫ A = dr ≫ (D.pieceIso W i).hom := by
    rw [hA, hdr]
    exact D.resIso_hom_comp_localResolutionMap bed Γ W hW hle hbed i
  have hK : L ≫ Mr = dr ≫ Em := by
    refine Hom.ext_of_comp_ofRestrict ?_
    have := D.isOpenImmersion_ambIn W
    refine Hom.ext_of_comp_of_isOpenImmersion (D.ambIn W) ?_
    exact (congrArg (fun k => k ≫ D.ambIn W) (Category.assoc _ _ _)).trans
      ((congrArg (fun k => (L ≫ k) ≫ D.ambIn W) h2).trans
        ((congrArg (fun k => k ≫ D.ambIn W) (Category.assoc _ _ _).symm).trans
          ((congrArg (fun k => (k ≫ M) ≫ D.ambIn W) h1).trans
            ((Category.assoc _ _ _).trans (h4.trans ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun k => k ≫ D.sumIn W i) h5).trans
                ((Category.assoc _ _ _).trans ((congrArg (fun k => dr ≫ k) h3.symm).trans
                  ((congrArg (fun k => dr ≫ k) (Category.assoc _ _ _).symm).trans
                    ((Category.assoc _ _ _).symm.trans
                      (congrArg (fun k => k ≫ D.ambIn W) (Category.assoc _ _ _).symm))))))))))))
  subst hL hMr hEm hdr
  exact hK

/-- **The ambient blow-up factorization of the glued space's map** over any open `V` covered by the
pieces `pieceDom i Wᵢ`, `W ≤ Γ.W` relatively compact ([Kol07, Proposition 37, proof];
[Kol07, Theorem 45(4)]). -/
def ambientBlowUpFactorizationOfGluing (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (Γ : D.ResolutionGluing bed) (W : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 (D.embedding i).G))
    (hW : ∀ i, IsCompact (closure (W i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G))))
    (hle : ∀ i, W i ≤ Γ.W i) (hbed : bed.IsEmbeddedDesing) (V : Set X)
    (hcov : V ⊆ ⋃ i, (D.pieceDom i (W i) : Set X)) :
    AnalyticSpace.Hom.AmbientBlowUpFactorization (Γ.glue.descMap : Γ.glue.gluedOver ⟶ X) V where
  n := D.n
  ι := D.ι
  finite := inferInstance
  piece i := D.pieceDom i (W i)
  isOpen_piece i := (D.pieceDom i (W i)).isOpen
  subset_iUnion_piece := hcov
  G := D.ambOpens W
  ideal := D.glueIdeal W
  emb i := D.glueEmb W i
  emb_isIso i := D.isIso_glueEmb W i
  seq := (D.glueSeq W bed hW).toSuccession
  transform k := BEDanFamStar.ambTransformOn bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.ambTheta W) k
  transform_zero := rfl
  transform_succ _ := rfl
  hasLocalGenerators_saturation _ := saturationStalk_hasLocalGenerators _ _ _
  isNonsingular_last := BEDanFamStar.isNonsingular_ambLastOn bed D.sigmaTriple
    D.domBEDan_sigmaTriple (D.ambImage W) (D.isCompact_closure_ambImage W hW) (D.ambTheta W) hbed
  map := D.glueMap W bed hW
  map_comp := BEDanFamStar.ambMapOn_comp bed D.sigmaTriple D.domBEDan_sigmaTriple (D.ambImage W)
    (D.isCompact_closure_ambImage W hW) (D.ambTheta W)
  lift i := D.glueLift bed Γ W hW hle hbed i
  lift_isIso i := D.isIso_glueLift bed Γ W hW hle hbed i
  map_lift i := D.glueMap_restrictSet_comp_glueLift bed Γ W hW hle hbed i

/-- **Clause (4) of `exists_functorial_resolution` at `U` for the glued space's map to `X`**
([Kol07, Theorem 45(4)]), with the independence of the local resolution as `hind`: the
factorization at the gluing datum `Classical.choice` picks, `W := Γ.W`, `V := U`, transported along
`resolutionOnFullPair_eq_of_glues`. -/
theorem nonempty_ambientBlowUpFactorization_resolutionOnFullMap_of_independent
    (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) :
    Nonempty ((D.resolutionOnFullMap bed).AmbientBlowUpFactorization U) := by
  have h : D.ResolutionGluesOn bed :=
    D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  have hcov : U ⊆ ⋃ i, (D.pieceDom i (h.some.W i) : Set X) := fun x hx => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (D.subset_iUnion_inner hx)
    exact Set.mem_iUnion.mpr ⟨i, h.some.closure_inner_subset_pieceDom i (subset_closure hi)⟩
  have F := D.ambientBlowUpFactorizationOfGluing bed h.some h.some.W h.some.isCompact_closure_W
    (fun _ => le_rfl) hbed U hcov
  change Nonempty (((D.resolutionOnFullPair bed).2).AmbientBlowUpFactorization U)
  rw [D.resolutionOnFullPair_eq_of_glues bed h]
  exact ⟨F⟩

end LocalEmbeddingData

end Hironaka.Manifold

end
