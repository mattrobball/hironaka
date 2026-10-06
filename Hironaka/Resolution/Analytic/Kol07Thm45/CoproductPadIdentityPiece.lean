/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.CoproductPadIdentity
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Resolution.Analytic.Kol07Thm45.HomOfPullbackEqCalculus
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.QuotientHomSquares
import Hironaka.Resolution.Analytic.Kol07Thm45.RestrictSetIncl
import Hironaka.Resolution.Analytic.Kol07Thm45.ShearOverX
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The padding identity at the coproduct — the piece clause

The third conjunct of `PadIdentityOn` (`CoproductPadIdentity.lean`): Kollár's commutation of the
functor with closed embeddings [Kol07, 34.4] at the coproduct slice, summand by summand. The core
names the isomorphism `ψ := padIdentityIso` of the coproduct local resolutions and proves that it
carries the members and lies over the ambients. Here, on every piece `i`, the summand inclusions
`resIn⁺ i : Ỹ⁺ᵢ → Y⁺` and `resIn i : Ỹᵢ → Y` (open immersions, `AmbientLift.lean`) are matched
through `ψ`:

* `range_toFun_resIn_padAlong_comp_padIdentityIso`: `resIn⁺ i ≫ ψ` and `resIn i` have the same
  range — the summand `i` of the padded reading opens is carried by `ψ` to the summand `i` of the
  datum's (the point form of `ψ` over the ambients, `range_toFun_resIn`, the slice
  diffeomorphism's summand compatibility, the disjointness of the summands);
* `piecePadIdentityIso`, `piecePadIdentityHom`: the induced isomorphism `ψᵢ : Ỹ⁺ᵢ ≅ Ỹᵢ` of open
  immersions with equal ranges (`isoOfRangeEq`), with `resIn⁺ i ≫ ψ = ψᵢ ≫ resIn i`
  (`resIn_padAlong_comp_padIdentityIso`, by construction);
* `localResolutionMap_comp_piecePadIdentityHom`: `ψᵢ` lies over the restricted ideals along the
  zero extension `padExtOn`, as the morphism `padExtOnHom` (the morphism form of `ψ` over the
  ambients, the two summand squares
  `resIn_comp_localResolutionMapOn`, the composite identity
  `homOfPullbackEq_sigmaMk_comp_padRestrictMap` of the quotient homs, the cancellation of the
  open immersion `H⁺ᵢ`);
* `localResolutionToPiece_comp_piecePadIdentityHom`: hence `ψᵢ` lies over the piece
  (`localResolutionToPiece = embInv ∘ restrictedIdealHom ∘ localResolutionMap`, `embInv_padAlong`,
  `padSliceHom_comp_restrictedIdealHom_comp_padExtOnHom`: the slice morphism undoes the padding);
* `exists_piece_padIdentityIso`: the piece clause of `PadIdentityOn` against the NAMED `ψ`, and
  `padIdentityOn`: the padding identity of every datum (`padIdentityOn_of_forall_piece`).

The identification is by ranges and the calculus of the quotient homs, never by a uniqueness
principle, so no independence hypothesis enters. Not in the sources beyond Kollár's commutation;
bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

/-- Composition in the category of `𝕜`-locally ringed spaces with the category instance fixed
(the device of `HomOfPullbackEqCalculus.lean`: one spelling along a chain keeps the elaborator
from unifying two spellings of `≫` under pending metavariables). -/
local infixr:80 " ≫ₖ " => @CategoryStruct.comp (KLocallyRingedSpace 𝕜) _ _ _ _

/-- Associativity in the `𝕜`-locally-ringed-space category, with the composition's instance fixed.
-/
private theorem assocₖ {W X Y Z : KLocallyRingedSpace.{u} 𝕜} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ₖ g) ≫ₖ h = f ≫ₖ (g ≫ₖ h) :=
  Category.assoc f g h

/-- The left identity in the `𝕜`-locally-ringed-space category, with the composition's instance
fixed. -/
private theorem id_compₖ {X Y : KLocallyRingedSpace.{u} 𝕜} (f : X ⟶ Y) : 𝟙 X ≫ₖ f = f :=
  Category.id_comp f

section Piece

variable {U : Set X} (D : LocalEmbeddingData 𝕜 X U) {n' : ℕ} (σ : Fin D.n ↪ Fin n')
  (Wp : ∀ i : D.ι, Opens (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))
  (hWp : ∀ i, IsCompact (closure (Wp i : Set (pieceAmbient.{u} 𝕜
    ((D.padAlongData σ).embedding i).G))))

/-! ### The zero extension on the reading opens -/

/-- The zero extension `padExt σ Gᵢ` maps the datum's reading open
`padPreimageOpens i = padExt⁻¹(Wp i)` into the padded reading open `Wp i`. -/
theorem image_padExt_padPreimageOpens_subset (i : D.ι) :
    (padExt σ (D.embedding i).G : pieceAmbient.{u} 𝕜 (D.embedding i).G →
        pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) ''
      (D.padPreimageOpens σ Wp i : Set (pieceAmbient.{u} 𝕜 (D.embedding i).G)) ⊆
      (Wp i : Set (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)) :=
  image_subset_iff.2 fun _ hx => hx

/-- The zero extension restricted to the reading opens, `padPreimageOpens i → Wp i` (across the
models `Fin n → 𝕜` and `Fin n' → 𝕜`, so a raw map with its analyticity `contMDiff_padExtOn`, as
`padRestrictMap`). -/
def padExtOn (i : D.ι) :
    (pieceAmbient.{u} 𝕜 (D.embedding i).G).restrict (D.padPreimageOpens σ Wp i) →
      (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G).restrict (Wp i) :=
  fun x => ⟨padExt σ (D.embedding i).G x.1, x.2⟩

/-- It lies over the zero extension (definitional). -/
theorem inclusion_padExtOn (i : D.ι)
    (x : (pieceAmbient.{u} 𝕜 (D.embedding i).G).restrict (D.padPreimageOpens σ Wp i)) :
    (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G).inclusion (Wp i)
        (D.padExtOn σ Wp i x) =
      padExt σ (D.embedding i).G
        ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (D.padPreimageOpens σ Wp i) x) :=
  rfl

/-- The restricted zero extension is analytic (`ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff`,
as `contMDiff_padRestrictMap`). -/
theorem contMDiff_padExtOn (i : D.ι) :
    ContMDiff 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω (D.padExtOn σ Wp i) := fun p => by
  have hval : ContMDiffAt 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω
      ((Subtype.val : (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G).restrict (Wp i) →
        pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) ∘ D.padExtOn σ Wp i) p :=
    ((contMDiff_padExt σ (D.embedding i).G).comp contMDiff_subtype_val).contMDiffAt
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω) _ univ p).mp hval

/-- The datum's restricted ideal is the pull-back of the padded datum's along the restricted zero
extension (compare [Wlo09, §7.1]; `pullback_padExt_padIdeal` on the reading opens,
`pullback_pullback`). -/
theorem restrictedIdeal_eq_pullback_padExtOnMap (i : D.ι) :
    (D.embedding i).restrictedIdeal (D.padPreimageOpens σ Wp i) =
      (((D.padAlongData σ).embedding i).restrictedIdeal (Wp i)).pullback
        (D.padExtOn σ Wp i) (D.contMDiff_padExtOn σ Wp i) := by
  have h1 : (D.embedding i).restrictedIdeal (D.padPreimageOpens σ Wp i) =
      ((padIdeal σ (D.embedding i).ideal).pullback (padExt σ (D.embedding i).G)
        (contMDiff_padExt σ (D.embedding i).G)).pullback
        ⇑((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (D.padPreimageOpens σ Wp i))
        ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (D.padPreimageOpens σ Wp i)).contMDiff :=
    congrArg (fun K : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 (D.embedding i).G) =>
      K.pullback ⇑((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (D.padPreimageOpens σ Wp i))
        ((pieceAmbient.{u} 𝕜 (D.embedding i).G).inclusion (D.padPreimageOpens σ Wp i)).contMDiff)
      (pullback_padExt_padIdeal σ (D.embedding i).G (D.embedding i).ideal).symm
  have h2 : ((D.padAlongData σ).embedding i).restrictedIdeal (Wp i) =
      ((D.padAlongData σ).embedding i).ideal.pullback
        ⇑((pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G).inclusion (Wp i))
        ((pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G).inclusion (Wp i)).contMDiff :=
    rfl
  rw [h1, h2, IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr _ _ _ (funext fun _ => rfl)

/-- The morphism of the restricted closed subspaces over the restricted zero extension,
`Sp(I|padPreimageOpens i) → Sp(I⁺|Wp i)` (`homOfPullbackEq`). -/
def padExtOnHom (i : D.ι) :
    ((D.embedding i).restrictedIdeal (D.padPreimageOpens σ Wp i)).toAnalyticSpace ⟶
        (((D.padAlongData σ).embedding i).restrictedIdeal (Wp i)).toAnalyticSpace :=
  IdealSheaf.homOfPullbackEq (D.padExtOn σ Wp i) (D.contMDiff_padExtOn σ Wp i)
    (D.restrictedIdeal_eq_pullback_padExtOnMap σ Wp i)

variable (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)

/-! ### The summand identification -/

include hbed in
/-- **`resIn⁺ i ≫ ψ` and `resIn i` have the same range** ([Kol07, 34.4] summand by summand) — the
padded summand `i` is carried by `ψ` onto the datum's summand `i` (the point form
`localResolutionMapOn_inv_padIdentityIso_apply`, `range_toFun_resIn` for both data,
`inclusionMap_sigmaPadSliceDiffeomorph`, `coe_sigmaCoordImage`, `Sigma.mk.inj_iff`). -/
theorem range_toFun_resIn_padAlong_comp_padIdentityIso (i : D.ι) :
    Set.range (KLocallyRingedSpace.Hom.toFun
        ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ D.padIdentityIso σ Wp hWp bed hbed)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (D.resIn bed (D.padPreimageOpens σ Wp)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i)) := by
  let Ψ := D.padIdentityIso σ Wp hWp bed hbed
  let Ψi := @inv (AnalyticSpace.{u} 𝕜) _ _ _ Ψ
      (D.padIdentityIso_isIso σ Wp hWp bed hbed)
  let PiYP := bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
    (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
    ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp)
  let PiY := bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
    (D.ambImage (D.padPreimageOpens σ Wp))
    (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp))
  let incl := (D.isClosedSubmanifold_sigmaPadSlice σ).inclusionMap
  let Φ := D.sigmaPadSliceDiffeomorph σ
  let NP := fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G
  let N := fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G
  have hinv : ∀ z, Ψ (Ψi z) = z :=
    fun z => congrArg (fun k => k z)
      (@IsIso.inv_hom_id (AnalyticSpace.{u} 𝕜) _ _ _ Ψ
        (D.padIdentityIso_isIso σ Wp hWp bed hbed))
  have hinv' : ∀ y, Ψi (Ψ y) = y :=
    fun y => congrArg (fun k => k y)
      (@IsIso.hom_inv_id (AnalyticSpace.{u} 𝕜) _ _ _ Ψ
        (D.padIdentityIso_isIso σ Wp hWp bed hbed))
  have hb : ∀ z, (PiYP (Ψi z)).1.1 = incl (Φ ((PiY z).1.1)) :=
    D.localResolutionMapOn_inv_padIdentityIso_apply σ Wp hWp bed hbed
  have hamb : ((D.ambImage (D.padPreimageOpens σ Wp) : Opens D.sigmaAmbient) : Set D.sigmaAmbient) =
      ⋃ j, ⇑(sigmaMk N j) '' (D.padPreimageOpens σ Wp j : Set (pieceAmbient.{u} 𝕜
          (D.embedding j).G)) :=
    coe_sigmaCoordImage _ _
  refine (Set.range_comp Ψ
      (KLocallyRingedSpace.Hom.toFun ((D.padAlongData σ).resIn bed Wp hWp hbed i))).trans
    ((congrArg (fun S => Ψ '' S)
      ((D.padAlongData σ).range_toFun_resIn bed Wp hWp hbed i)).trans
      (Eq.trans ?_ (D.range_toFun_resIn bed (D.padPreimageOpens σ Wp)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i).symm))
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (PiYP y).1.1 ∈
        ⇑(sigmaMk NP i) '' (Wp i : Set (pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))
            := hy
    have hb' : (PiYP y).1.1 = incl (Φ ((PiY (Ψ y)).1.1)) := by
      have := hb (Ψ y)
      rwa [hinv'] at this
    have hmem : (PiY (Ψ y)).1.1 ∈
        ((D.ambImage (D.padPreimageOpens σ Wp) : Opens D.sigmaAmbient) : Set D.sigmaAmbient) :=
      (PiY (Ψ y)).1.2
    rw [hamb] at hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨x, hx, hxeq⟩ := hj
    rw [hb', ← hxeq, D.inclusionMap_sigmaPadSliceDiffeomorph σ j x] at hy'
    obtain ⟨w, hw, hweq⟩ := hy'
    have hweq' : (⟨i, w⟩ : Σ k, (NP k : Type u)) = ⟨j, padExt σ (D.embedding j).G x⟩ := hweq
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp hweq'
    exact ⟨x, hx, hxeq⟩
  · rintro ⟨x, hx, hxeq⟩
    refine ⟨Ψi z, ?_, hinv z⟩
    have hb'' : (PiYP (Ψi z)).1.1 = sigmaMk NP i (padExt σ (D.embedding i).G x) :=
      ((hb z).trans (congrArg (fun q => incl (Φ q)) hxeq.symm)).trans
        (D.inclusionMap_sigmaPadSliceDiffeomorph σ i x)
    exact ⟨padExt σ (D.embedding i).G x, hx, hb''.symm⟩

include hbed in
/-- `resIn⁺ i ≫ ψ` is an open immersion — the composite of the open
immersion `resIn⁺ i` (`isOpenImmersion_resIn`) with the isomorphism `ψ` (`padIdentityIso_isIso`;
`LocallyRingedSpace.IsOpenImmersion.of_isIso`, `.comp`). -/
theorem isOpenImmersion_resIn_padAlong_comp_padIdentityIso (i : D.ι) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ D.padIdentityIso σ Wp hWp bed hbed).1 := by
  have h₁ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      ((D.padAlongData σ).resIn bed Wp hWp hbed i).1 :=
    (D.padAlongData σ).isOpenImmersion_resIn bed Wp hWp hbed i
  have hA : @IsIso (AnalyticSpace.{u} 𝕜) _ _ _
      (D.padIdentityIso σ Wp hWp bed hbed) :=
    D.padIdentityIso_isIso σ Wp hWp bed hbed
  have hV : IsIso (D.padIdentityIso σ Wp hWp bed hbed).1 :=
    ⟨⟨(inv (D.padIdentityIso σ Wp hWp bed hbed)).1,
      congrArg (fun k => k.1) (IsIso.hom_inv_id (D.padIdentityIso σ Wp hWp bed hbed)),
      congrArg (fun k => k.1) (IsIso.inv_hom_id (D.padIdentityIso σ Wp hWp bed hbed))⟩⟩
  have h₂ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (D.padIdentityIso σ Wp hWp bed hbed).1 :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso _
  change AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
    (((D.padAlongData σ).resIn bed Wp hWp hbed i).1 ≫ (D.padIdentityIso σ Wp hWp bed hbed).1)
  exact AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp (H := h₁) _ _

include hbed in
/-- The isomorphism `ψᵢ : Ỹ⁺ᵢ ≅ Ỹᵢ` of the two open immersions into `Y` with the same range
(`isoOfRangeEq`). -/
def piecePadIdentityIso (i : D.ι) :
    (((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i)).toKLocallyRingedSpace ≅
      ((D.embedding i).localResolution bed (D.padPreimageOpens σ Wp i)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp i)).toKLocallyRingedSpace :=
  have _h₃ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      ((D.padAlongData σ).resIn bed Wp hWp hbed i ≫ D.padIdentityIso σ Wp hWp bed hbed).1 :=
    D.isOpenImmersion_resIn_padAlong_comp_padIdentityIso σ Wp hWp bed hbed i
  have _h₄ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.resIn bed
      (D.padPreimageOpens σ Wp) (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i).1 :=
    D.isOpenImmersion_resIn bed _ _ hbed i
  isoOfRangeEq _ _ (D.range_toFun_resIn_padAlong_comp_padIdentityIso σ Wp hWp bed hbed i)

include hbed in
/-- The piece isomorphism as a morphism of analytic spaces. -/
def piecePadIdentityHom (i : D.ι) :
    ((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i) ⟶
        (D.embedding i).localResolution bed (D.padPreimageOpens σ Wp i)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp i) :=
  (D.piecePadIdentityIso σ Wp hWp bed hbed i).hom

/-- `ψᵢ` is an isomorphism (the `hom` of an `Iso`). -/
theorem piecePadIdentityHom_isIso (i : D.ι) :
    IsIso (D.piecePadIdentityHom σ Wp hWp bed hbed i) :=
  (Hom.isIso_iff_isIso_toKLocallyRingedSpace _).2
    (show IsIso (D.piecePadIdentityIso σ Wp hWp bed hbed i).hom from inferInstance)

/-- **`resIn⁺ i ≫ ψ = ψᵢ ≫ resIn i`** (`isoOfRangeEq_hom_comp`). -/
theorem resIn_padAlong_comp_padIdentityIso (i : D.ι) :
    (D.padAlongData σ).resIn bed Wp hWp hbed i ≫ D.padIdentityIso σ Wp hWp bed hbed =
      D.piecePadIdentityHom σ Wp hWp bed hbed i ≫
        D.resIn bed (D.padPreimageOpens σ Wp) (D.isCompact_closure_padPreimageOpens σ Wp hWp)
          hbed i := by
  have _h₃ := D.isOpenImmersion_resIn_padAlong_comp_padIdentityIso σ Wp hWp bed hbed i
  have _h₄ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (D.resIn bed
      (D.padPreimageOpens σ Wp) (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i).1 :=
    D.isOpenImmersion_resIn bed _ _ hbed i
  exact (isoOfRangeEq_hom_comp _ _
    (D.range_toFun_resIn_padAlong_comp_padIdentityIso σ Wp hWp bed hbed i)).symm

/-! ### Over the restricted ideals, then over the piece -/

/-- **The two quotient homs into the padded coproduct's closed subspace agree** — along
`padRestrictMap ∘ sigmaMk i = sigmaMk⁺ i ∘ padExt` on the reading opens
(`homOfPullbackEq_comp_fun` twice and `homOfPullbackEq_congr_fun`, with
`inclusionMap_sigmaPadSliceDiffeomorph`). -/
theorem homOfPullbackEq_sigmaMk_comp_padRestrictMap (i : D.ι) :
    IdealSheaf.homOfPullbackEq _ _ (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap
        D.sigmaTriple (D.ambImage (D.padPreimageOpens σ Wp)) (D.embedding i).ambientTriple (sigmaMk
        (fun i => pieceAmbient.{u} 𝕜
        (D.embedding
        i).G) i) (D.padPreimageOpens σ Wp i) (D.image_subset_ambImage (D.padPreimageOpens σ Wp) i)
        (D.isPullbackOf_ambientTriple_sigmaTriple
        i)) ≫ IdealSheaf.homOfPullbackEq (D.padRestrictMap σ Wp) (D.contMDiff_padRestrictMap σ Wp)
        (D.restrictOpens_eq_pullback_padRestrictMap σ Wp) =
      D.padExtOnHom σ Wp i ≫ IdealSheaf.homOfPullbackEq _ _
          (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (D.padAlongData σ).sigmaTriple
          ((D.padAlongData σ).ambImage Wp) ((D.padAlongData σ).embedding i).ambientTriple (sigmaMk
          (fun i => pieceAmbient.{u} 𝕜
          ((D.padAlongData σ).embedding
          i).G) i) (Wp i) ((D.padAlongData σ).image_subset_ambImage Wp i)
          ((D.padAlongData σ).isPullbackOf_ambientTriple_sigmaTriple i)) := by
  have e₁ := BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple
    (D.ambImage (D.padPreimageOpens σ Wp)) (D.embedding i).ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (D.padPreimageOpens σ Wp i)
    (D.image_subset_ambImage (D.padPreimageOpens σ Wp) i)
    (D.isPullbackOf_ambientTriple_sigmaTriple i)
  have e₂ := D.restrictOpens_eq_pullback_padRestrictMap σ Wp
  have e₁₂ := e₁.trans ((congrArg (fun K : AnalyticManifold.IdealSheaf
      (D.sigmaAmbient.restrict (D.ambImage (D.padPreimageOpens σ Wp))) =>
        K.pullback
          ⇑(AnalyticMap.restrictMap (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
            (D.padPreimageOpens σ Wp i) (D.ambImage (D.padPreimageOpens σ Wp))
            (D.image_subset_ambImage (D.padPreimageOpens σ Wp) i))
        (AnalyticMap.restrictMap (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i)
          (D.padPreimageOpens σ Wp i) (D.ambImage (D.padPreimageOpens σ Wp))
          (D.image_subset_ambImage (D.padPreimageOpens σ Wp) i)).contMDiff) e₂).trans
    (IdealSheaf.pullback_pullback _ _ _ _ _))
  have e₁' := D.restrictedIdeal_eq_pullback_padExtOnMap σ Wp i
  have e₂' := BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (D.padAlongData σ).sigmaTriple
    ((D.padAlongData σ).ambImage Wp) ((D.padAlongData σ).embedding i).ambientTriple
    (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i) (Wp i)
    ((D.padAlongData σ).image_subset_ambImage Wp i)
    ((D.padAlongData σ).isPullbackOf_ambientTriple_sigmaTriple i)
  have e₁₂' := e₁'.trans ((congrArg (fun K : AnalyticManifold.IdealSheaf
      ((pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G).restrict (Wp i)) =>
        K.pullback (D.padExtOn σ Wp i) (D.contMDiff_padExtOn σ Wp i)) e₂').trans
    (IdealSheaf.pullback_pullback _ _ _ _ _))
  refine (IdealSheaf.homOfPullbackEq_comp_fun _ _ _ _ e₁ e₂ e₁₂).trans ?_
  refine Eq.trans ?_ (IdealSheaf.homOfPullbackEq_comp_fun _ _ _ _ e₁' e₂' e₁₂').symm
  exact IdealSheaf.homOfPullbackEq_congr_fun
    (funext fun x : (pieceAmbient.{u} 𝕜 (D.embedding i).G).restrict (D.padPreimageOpens σ Wp i) =>
      Subtype.ext (D.inclusionMap_sigmaPadSliceDiffeomorph σ i x.1)) _ _ _ _

include hbed in
/-- **`ψᵢ` lies over the restricted ideals along the zero extension** —
`padExtOnHom ∘ Πᵢ ∘ ψᵢ = Π⁺ᵢ` (the two summand squares `resIn_comp_localResolutionMapOn`, the
morphism form `localResolutionMapOn_comp_inv_padIdentityIso`,
`homOfPullbackEq_sigmaMk_comp_padRestrictMap`, and the cancellation of the open immersion
`homOfPullbackEq` along `sigmaMk⁺ i` — `isOpenImmersion_homOfPullbackEq_of_injective`). -/
theorem localResolutionMap_comp_piecePadIdentityHom (i : D.ι) :
    (D.piecePadIdentityHom σ Wp hWp bed hbed i ≫ (D.embedding i).localResolutionMap bed
        (D.padPreimageOpens σ Wp i) (D.isCompact_closure_padPreimageOpens σ Wp hWp
        i)) ≫ D.padExtOnHom σ Wp i =
      ((D.padAlongData σ).embedding i).localResolutionMap bed (Wp i) (hWp i) := by
  let Ψ := D.padIdentityIso σ Wp hWp bed hbed
  let Ψi := @inv (AnalyticSpace.{u} 𝕜) _ _ _ Ψ
      (D.padIdentityIso_isIso σ Wp hWp bed hbed)
  let rP := (D.padAlongData σ).resIn bed Wp hWp hbed i
  let r := D.resIn bed (D.padPreimageOpens σ Wp)
      (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i
  let PiYP := bed.localResolutionMapOn (D.padAlongData σ).sigmaTriple
    (D.padAlongData σ).domBEDan_sigmaTriple ((D.padAlongData σ).ambImage Wp)
    ((D.padAlongData σ).isCompact_closure_ambImage Wp hWp)
  let PiY := bed.localResolutionMapOn D.sigmaTriple D.domBEDan_sigmaTriple
    (D.ambImage (D.padPreimageOpens σ Wp))
    (D.isCompact_closure_ambImage _ (D.isCompact_closure_padPreimageOpens σ Wp hWp))
  let H := IdealSheaf.homOfPullbackEq (D.padRestrictMap σ Wp) (D.contMDiff_padRestrictMap σ Wp)
    (D.restrictOpens_eq_pullback_padRestrictMap σ Wp)
  let Hi := IdealSheaf.homOfPullbackEq _ _
    (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap D.sigmaTriple
      (D.ambImage (D.padPreimageOpens σ Wp)) (D.embedding i).ambientTriple
      (sigmaMk (fun i => pieceAmbient.{u} 𝕜 (D.embedding i).G) i) (D.padPreimageOpens σ Wp i)
      (D.image_subset_ambImage (D.padPreimageOpens σ Wp) i)
      (D.isPullbackOf_ambientTriple_sigmaTriple i))
  let Hp := IdealSheaf.homOfPullbackEq _ _
    (BEDanFamStar.restrictedIdealOn_eq_pullback_restrictMap (D.padAlongData σ).sigmaTriple
      ((D.padAlongData σ).ambImage Wp) ((D.padAlongData σ).embedding i).ambientTriple
      (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i) (Wp i)
      ((D.padAlongData σ).image_subset_ambImage Wp i)
      ((D.padAlongData σ).isPullbackOf_ambientTriple_sigmaTriple i))
  let ψ := D.piecePadIdentityHom σ Wp hWp bed hbed i
  let πi := (D.embedding i).localResolutionMap bed (D.padPreimageOpens σ Wp i)
    (D.isCompact_closure_padPreimageOpens σ Wp hWp i)
  let πP := ((D.padAlongData σ).embedding i).localResolutionMap bed (Wp i) (hWp i)
  let hi := D.padExtOnHom σ Wp i
  have sqP : rP ≫ₖ PiYP = πP
      ≫ₖ Hp := (D.padAlongData σ).resIn_comp_localResolutionMapOn bed Wp hWp hbed i
  have sq : r ≫ₖ PiY = πi ≫ₖ Hi :=
    D.resIn_comp_localResolutionMapOn bed (D.padPreimageOpens σ Wp)
      (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i
  have hb : Ψi ≫ₖ PiYP = PiY
      ≫ₖ H := D.localResolutionMapOn_comp_inv_padIdentityIso σ Wp hWp bed hbed
  have hsq : rP ≫ₖ Ψ = ψ ≫ₖ r := D.resIn_padAlong_comp_padIdentityIso σ Wp hWp bed hbed i
  have hc : Hi ≫ₖ H = hi ≫ₖ Hp := D.homOfPullbackEq_sigmaMk_comp_padRestrictMap σ Wp i
  have hii : Ψ ≫ₖ Ψi = 𝟙 _ :=
    @IsIso.hom_inv_id (AnalyticSpace.{u} 𝕜) _ _ _ Ψ
      (D.padIdentityIso_isIso σ Wp hWp bed hbed)
  -- the chain: Π⁺ᵢ ≫ H⁺ᵢ = ((ψᵢ ≫ Πᵢ) ≫ hᵢ) ≫ H⁺ᵢ
  have key : πP ≫ₖ Hp = ((ψ ≫ₖ πi) ≫ₖ hi) ≫ₖ Hp :=
    sqP.symm.trans ((congrArg (fun k => rP ≫ₖ k)
        ((id_compₖ PiYP).symm.trans (congrArg (fun k => k ≫ₖ PiYP) hii.symm))).trans
      (((congrArg (fun k => rP ≫ₖ k) (assocₖ Ψ Ψi PiYP)).trans (assocₖ rP Ψ (Ψi
          ≫ₖ PiYP)).symm).trans
        ((congrArg₂ (fun a b => a ≫ₖ b) hsq hb).trans
          (((assocₖ ψ r (PiY ≫ₖ H)).trans (congrArg (fun k => ψ ≫ₖ k) (assocₖ r PiY H).symm)).trans
            ((congrArg (fun k => ψ ≫ₖ (k ≫ₖ H)) sq).trans
              ((congrArg (fun k => ψ ≫ₖ k)
                  ((assocₖ πi Hi H).trans (congrArg (fun k => πi ≫ₖ k) hc))).trans
                (((congrArg (fun k => ψ ≫ₖ k) (assocₖ πi hi Hp).symm).trans
                    (assocₖ ψ (πi ≫ₖ hi) Hp).symm).trans
                  (congrArg (fun k => k ≫ₖ Hp) (assocₖ ψ πi hi).symm))))))))
  have hoi : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion Hp.1 :=
    isOpenImmersion_homOfPullbackEq_of_injective
      (AnalyticMap.restrictMap
        (sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i) (Wp i)
        ((D.padAlongData σ).ambImage Wp) ((D.padAlongData σ).image_subset_ambImage Wp i))
      (AnalyticMap.isLocalDiffeomorph_restrictMap
        (isLocalDiffeomorph_sigmaMk (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)
          i) (Wp i) ((D.padAlongData σ).ambImage Wp)
              ((D.padAlongData σ).image_subset_ambImage Wp i))
      (fun x y hxy => Subtype.ext
        ((isAnalyticOpenEmbedding_sigmaMk
          (fun i => pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G) i).2
          (congrArg Subtype.val hxy))) _
  have hmono : Mono Hp.1 := AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono _
  have key' : πP.1 ≫ Hp.1 = ((ψ ≫ₖ πi) ≫ₖ hi).1 ≫ Hp.1 := congrArg (fun k => k.1) key
  exact (Hom.ext ((@cancel_mono _ _ _ _ _ _ hmono _ _).mp key')).symm

/-- **The slice morphism undoes the padding on the restricted closed subspaces** —
`padSliceHom ∘ restrictedIdealHom⁺ ∘ padExtOnHom =
restrictedIdealHom` (`padCoordProj ∘ padExt = id`; quotient homs along a composite of functions,
`Hom.ext_of_comp_quotientι`). -/
theorem padSliceHom_comp_restrictedIdealHom_comp_padExtOnHom (i : D.ι) :
    (D.padExtOnHom σ Wp i ≫ ((D.padAlongData σ).embedding i).restrictedIdealHom
        (Wp i)) ≫ padSliceHom σ (D.embedding i).ideal =
      (D.embedding i).restrictedIdealHom (D.padPreimageOpens σ Wp i) := by
  refine Hom.ext_of_comp_quotientι _ ?_
  let A := D.padExtOnHom σ Wp i
  let B := ((D.padAlongData σ).embedding i).restrictedIdealHom (Wp i)
  let C := padSliceHom σ (D.embedding i).ideal
  let ι := (D.embedding i).ideal.toAnalyticSpaceι
  let ιP := ((D.padAlongData σ).embedding i).ideal.toAnalyticSpaceι
  let ιW := (((D.padAlongData σ).embedding i).restrictedIdeal (Wp i)).toAnalyticSpaceι
  let ι₀ := ((D.embedding i).restrictedIdeal (D.padPreimageOpens σ Wp i)).toAnalyticSpaceι
  let P := ofManifoldHom (padCoordProj σ (D.embedding i).G) (contMDiff_padCoordProj σ
      (D.embedding i).G)
  let V := ofManifoldHom (Subtype.val : (Wp i) →
    pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)
    (contMDiff_subtype_val : ContMDiff 𝓘(𝕜, Fin n' → 𝕜) 𝓘(𝕜, Fin n' → 𝕜) ω (Subtype.val : (Wp i) →
      pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G))
  let X := ofManifoldHom (D.padExtOn σ Wp i) (D.contMDiff_padExtOn σ Wp i)
  let V₀ := ofManifoldHom (Subtype.val : (D.padPreimageOpens σ Wp i) →
    pieceAmbient.{u} 𝕜 (D.embedding i).G)
    (contMDiff_subtype_val : ContMDiff 𝓘(𝕜, Fin D.n → 𝕜) 𝓘(𝕜, Fin D.n → 𝕜) ω
      (Subtype.val : (D.padPreimageOpens σ Wp i) → pieceAmbient.{u} 𝕜 (D.embedding i).G))
  let rIH := (D.embedding i).restrictedIdealHom (D.padPreimageOpens σ Wp i)
  change ((A ≫ₖ B) ≫ₖ C) ≫ₖ ι = rIH ≫ₖ ι
  have e₀ : rIH ≫ₖ ι = ι₀ ≫ₖ V₀ := quotientMap_comp_quotientι _ _ _ _
  have e₁ : A ≫ₖ ιW = ι₀ ≫ₖ X := homOfPullbackEq_comp_toAnalyticSpaceι _ _ _
  have e₂ : B ≫ₖ ιP = ιW ≫ₖ V := quotientMap_comp_quotientι _ _ _ _
  have e₃ : C ≫ₖ ι = ιP ≫ₖ P := quotientMap_comp_quotientι _ _ _ _
  have hfun : (padCoordProj σ (D.embedding i).G ∘ (Subtype.val : (Wp i) →
      pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)) ∘ D.padExtOn σ Wp i =
      (Subtype.val : (D.padPreimageOpens σ Wp i) → pieceAmbient.{u} 𝕜 (D.embedding i).G) :=
    funext fun x => padCoordProj_padExt σ (D.embedding i).G x.1
  have t8 : X ≫ₖ (V
      ≫ₖ P) = ofManifoldHom ((padCoordProj σ (D.embedding i).G ∘ (Subtype.val : (Wp i) →
      pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)) ∘ D.padExtOn σ Wp i)
      (((contMDiff_padCoordProj σ (D.embedding i).G).comp contMDiff_subtype_val).comp
        (D.contMDiff_padExtOn σ Wp i)) :=
    (congrArg (fun k => X ≫ₖ k) (ofManifoldHom_comp _ _ _ _).symm).trans
      (ofManifoldHom_comp _ _ _ _).symm
  have t9 : ofManifoldHom ((padCoordProj σ (D.embedding i).G ∘ (Subtype.val : (Wp i) →
      pieceAmbient.{u} 𝕜 ((D.padAlongData σ).embedding i).G)) ∘ D.padExtOn σ Wp i)
      (((contMDiff_padCoordProj σ (D.embedding i).G).comp contMDiff_subtype_val).comp
        (D.contMDiff_padExtOn σ Wp i)) = V₀ :=
    ofManifoldHom_congr hfun _
  exact ((assocₖ (A ≫ₖ B) C ι).trans (assocₖ A B (C ≫ₖ ι))).trans
    ((congrArg (fun k => A ≫ₖ (B ≫ₖ k)) e₃).trans
      ((congrArg (fun k => A ≫ₖ k) (assocₖ B ιP P).symm).trans
        ((congrArg (fun k => A ≫ₖ (k ≫ₖ P)) e₂).trans
          (((congrArg (fun k => A ≫ₖ k) (assocₖ ιW V P)).trans (assocₖ A ιW (V ≫ₖ P)).symm).trans
            ((congrArg (fun k => k ≫ₖ (V ≫ₖ P)) e₁).trans
              ((assocₖ ι₀ X (V ≫ₖ P)).trans
                ((congrArg (fun k => ι₀ ≫ₖ k) (t8.trans t9)).trans e₀.symm)))))))

include hbed in
/-- **`ψᵢ` lies over the piece** — `Πᵢ ∘ ψᵢ = Π⁺ᵢ`
for the maps to the piece `X|V` (`localResolutionToPiece = embInv ∘ restrictedIdealHom ∘
localResolutionMap`, `embInv_padAlong`, the two identities above). -/
theorem localResolutionToPiece_comp_piecePadIdentityHom (i : D.ι) :
    D.piecePadIdentityHom σ Wp hWp bed hbed i ≫
        (D.embedding i).localResolutionToPiece bed (D.padPreimageOpens σ Wp i)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp i) =
      ((D.padAlongData σ).embedding i).localResolutionToPiece bed (Wp i) (hWp i) := by
  let ψ := D.piecePadIdentityHom σ Wp hWp bed hbed i
  let πi := (D.embedding i).localResolutionMap bed (D.padPreimageOpens σ Wp i)
    (D.isCompact_closure_padPreimageOpens σ Wp hWp i)
  let πP := ((D.padAlongData σ).embedding i).localResolutionMap bed (Wp i) (hWp i)
  let hi := D.padExtOnHom σ Wp i
  let rIH := (D.embedding i).restrictedIdealHom (D.padPreimageOpens σ Wp i)
  let rIHP := ((D.padAlongData σ).embedding i).restrictedIdealHom (Wp i)
  let C := padSliceHom σ (D.embedding i).ideal
  let e := @inv (AnalyticSpace.{u} 𝕜) _ _ _ (D.embedding i).emb
      (D.embedding i).emb_isIso
  let eP := @inv (AnalyticSpace.{u} 𝕜) _ _ _ ((D.padAlongData σ).embedding i).emb
    ((D.padAlongData σ).embedding i).emb_isIso
  have h7 : (ψ ≫ₖ πi)
      ≫ₖ hi = πP := D.localResolutionMap_comp_piecePadIdentityHom σ Wp hWp bed hbed i
  have h8 : (hi ≫ₖ rIHP) ≫ₖ C = rIH := D.padSliceHom_comp_restrictedIdealHom_comp_padExtOnHom σ Wp i
  have hinv : eP = C ≫ₖ e := (D.embedding i).embInv_padAlong σ
  change ψ ≫ₖ ((πi ≫ₖ rIH) ≫ₖ e) = (πP ≫ₖ rIHP) ≫ₖ eP
  exact (((congrArg (fun k => ψ ≫ₖ k) (assocₖ πi rIH e)).trans (assocₖ ψ πi (rIH ≫ₖ e)).symm).trans
    ((congrArg (fun k => (ψ ≫ₖ πi) ≫ₖ (k ≫ₖ e)) h8.symm).trans
      (((congrArg (fun k => (ψ ≫ₖ πi) ≫ₖ k)
          ((assocₖ (hi ≫ₖ rIHP) C e).trans (assocₖ hi rIHP (C ≫ₖ e)))).trans
        (assocₖ (ψ ≫ₖ πi) hi (rIHP ≫ₖ (C ≫ₖ e))).symm).trans
        ((congrArg₂ (fun a b => a ≫ₖ (rIHP ≫ₖ b)) h7 hinv.symm).trans
          (assocₖ πP rIHP eP).symm))))

/-! ### The clause and the padding identity -/

include hbed in
/-- **The piece clause of `PadIdentityOn`** against the NAMED `ψ = padIdentityIso` — the hypothesis
`hc` of `padIdentityOn_of_forall_piece`: on every piece an isomorphism `ψᵢ` of the piece's local
resolutions over the piece with `resIn⁺ i ≫ ψ = ψᵢ ≫ resIn i`. -/
theorem exists_piece_padIdentityIso (i : D.ι) :
    ∃ ψᵢ : ((D.padAlongData σ).embedding i).localResolution bed (Wp i) (hWp i) ⟶
        (D.embedding i).localResolution bed (D.padPreimageOpens σ Wp i)
        (D.isCompact_closure_padPreimageOpens σ Wp hWp i),
      IsIso ψᵢ ∧
      ψᵢ ≫ (D.embedding i).localResolutionToPiece bed (D.padPreimageOpens σ Wp i)
          (D.isCompact_closure_padPreimageOpens σ Wp hWp i) =
        ((D.padAlongData σ).embedding i).localResolutionToPiece bed (Wp i) (hWp i) ∧
      (D.padAlongData σ).resIn bed Wp hWp hbed i ≫ D.padIdentityIso σ Wp hWp bed hbed =
        ψᵢ ≫ D.resIn bed (D.padPreimageOpens σ Wp)
          (D.isCompact_closure_padPreimageOpens σ Wp hWp) hbed i :=
  ⟨D.piecePadIdentityHom σ Wp hWp bed hbed i, D.piecePadIdentityHom_isIso σ Wp hWp bed hbed i,
    D.localResolutionToPiece_comp_piecePadIdentityHom σ Wp hWp bed hbed i,
    D.resIn_padAlong_comp_padIdentityIso σ Wp hWp bed hbed i⟩

include hbed in
/-- **The padding identity holds for every datum** ([Kol07, 34.4] at the coproduct slice) —
`padIdentityOn_of_forall_piece` at the piece clause. -/
theorem padIdentityOn : D.PadIdentityOn σ Wp hWp bed hbed :=
  D.padIdentityOn_of_forall_piece σ Wp hWp bed hbed
    (D.exists_piece_padIdentityIso σ Wp hWp bed hbed)

end Piece

end Hironaka.Manifold.LocalEmbeddingData

end
