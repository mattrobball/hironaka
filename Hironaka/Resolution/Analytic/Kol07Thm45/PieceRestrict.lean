/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceAmbientIncl
public import Hironaka.AnalyticSpace.Manifold.Chart
public import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The restriction of a piece embedding to an open sub-piece

Włodarczyk: if `Y_Z ⊂ Y_{Z'}` is an open embedding of germs then it extends to an open embedding
`U_Z ⊂ U_{Z'}` of the ambient manifolds [Wlo09, §4, (3)⇒(4)]; Kollár builds the resolution of a
variety from local embeddings into affine spaces, the local resolutions being compared through the
uniqueness up to automorphisms [Kol07, Theorem 36, proof]. For a piece embedding
`E : PieceEmbedding 𝕜 n X V` (an ambient `G ⊆ 𝕜ⁿ`, a reduced nowhere-zero ideal sheaf `𝓘` on
`Sp(G)` and the model isomorphism `emb : X|V ≅ Sp(G)/𝓘`) and an open `V' ⊆ V` of `X`, this
module builds the **restricted piece embedding** `E|V' : PieceEmbedding 𝕜 n X V'` — the embedding
to which the independence of the local resolution from the embedding
(`LocalResolutionIndependentOn`, `PieceGlueProof.lean`) is applied over the overlaps of
the pieces in the gluing of the local resolutions:

* `PieceEmbedding.restrictAmbient E hV'` — the shrunk ambient `G' := G ∖ amb(V ∖ V')`: the
  ambient image of the (closed) part of the piece outside `V'` is closed in `G`
  (`isClosedEmbedding_ambientPoint`: the closed-subspace inclusion is a closed embedding,
  `emb` a homeomorphism), so `G'` is open, with `Y ∩ G' = amb(V')`
  (`pieceCoord_ambientPoint_mem_restrictAmbient_iff`);
* `PieceEmbedding.restrictPiece E hV' hsub` — the embedding of `X|V'` with ambient `G'`, the
  SAME ideal pulled back along the inclusion `Sp(G') → Sp(G)` (`pieceAmbientIncl`, a local
  analytic isomorphism onto the open `coordPreimage G' G`), its stalk conditions transported along
  the open embedding (`germMap`, bijective at a local isomorphism), and the model isomorphism
  `X|V' ≅ Sp(G')/𝓘|G'` assembled as `X|V' ≅ (X|V)|_W ≅ (Sp(G)/𝓘)|_W ≅
  (Sp(G)|_{G'})/(𝓘|_{G'}) ≅ Sp(G')/𝓘'` (`restrictOpenIso`, `restrictOpen_quotient_iso`,
  `quotient_kIso` along `ofManifold_restrictOpen_iso` and the diffeomorphism
  `pieceAmbientInclDiffeo` — the pattern of `modelPieceEmbIso`, `PieceModel.lean`), the ideal
  identity by `comap_ofManifoldHom_eq_pullback`;
* the point bookkeeping: `pieceAmbientIncl_ambientPoint_restrictPiece` (the ambient point of a
  point of the sub-piece, read in `Sp(G)`, is its ambient point in the piece),
  `pieceCoord_ambientPoint_restrictPiece` (the same in `𝕜ⁿ`), `embPreimage_restrictPiece` (the
  points of the sub-piece over `W'` are the points of the piece over the image of `W'`).

Not in the sources beyond the remarks cited; bookkeeping. The support of a closed subspace is
Hironaka's [Hir64, Ch. 0, §1, p. 119].
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace Manifold
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K}

/-- A subset of `U` lies in the open `openOf X U` of the restriction — `U` itself when `U` is open,
everything otherwise (the convention of `openOf`). -/
theorem mem_openOf_of_subset {U U' : Set X} (hsub : U' ⊆ U) {x : X} (hx : x ∈ U') :
    x ∈ openOf X U := by
  by_cases hU : IsOpen U
  · rw [openOf_of_isOpen X hU]; exact hsub hx
  · rw [openOf_of_not_isOpen X hU]; trivial

/-- A point of the open `openOf X U` of an OPEN `U` lies in `U`. -/
theorem mem_of_mem_openOf {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ openOf X U) : x ∈ U := by
  rwa [openOf_of_isOpen X hU] at hx

end AnalyticSpace

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The identity is compatible (`Compat`) with two EQUAL ideal sheaves. -/
theorem compat_id_of_eq {X : KLocallyRingedSpace.{u} K}
    {J₁ J₂ : IdealSheaf X.toLocallyRingedSpace.𝒪} (h : J₁ = J₂) :
    QuotientSpace.Compat (𝟙 X : X ⟶ X).1 J₁ J₂ := by
  subst h
  intro z
  refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
  have hid : ((𝟙 X : X ⟶ X).1.stalkMap z).hom x =
      (𝟙 (X.toLocallyRingedSpace.presheaf.stalk z) : _ ⟶ _).hom x :=
    congrArg (fun φ => φ.hom x) (LocallyRingedSpace.stalkMap_id X.toLocallyRingedSpace z)
  rw [Ideal.mem_comap, hid]
  exact hx

/-- **Transport of a quotient along an equality of its ideal sheaves**, the `K`-isomorphism induced
by the identity of the ambient space (`quotientMap`) — deliberately NOT `eqToIso`: Lean's kernel
would try to normalise the equality's proof when comparing `eqToHom` terms. -/
def quotientIsoOfEq {X : KLocallyRingedSpace.{u} K}
    {J₁ J₂ : IdealSheaf X.toLocallyRingedSpace.𝒪} (h : J₁ = J₂) :
    X.quotient J₁ ≅ X.quotient J₂ where
  hom := quotientMap (𝟙 X) J₁ J₂ (compat_id_of_eq h)
  inv := quotientMap (𝟙 X) J₂ J₁ (compat_id_of_eq h.symm)
  hom_inv_id := Hom.ext_of_comp_quotientι J₁ (by
    rw [Category.assoc, quotientMap_comp_quotientι, Category.comp_id,
      quotientMap_comp_quotientι, Category.comp_id, Category.id_comp])
  inv_hom_id := Hom.ext_of_comp_quotientι J₂ (by
    rw [Category.assoc, quotientMap_comp_quotientι, Category.comp_id,
      quotientMap_comp_quotientι, Category.comp_id, Category.id_comp])

/-- The transport isomorphism lies over the identity — its `hom` followed by the canonical
morphism is the canonical morphism. -/
theorem quotientIsoOfEq_hom_comp_quotientι {X : KLocallyRingedSpace.{u} K}
    {J₁ J₂ : IdealSheaf X.toLocallyRingedSpace.𝒪} (h : J₁ = J₂) :
    (quotientIsoOfEq h).hom ≫ quotientι X J₂ = quotientι X J₁ :=
  (quotientMap_comp_quotientι _ _ _ _).trans (Category.comp_id _)

/-- The inverse of the transport isomorphism `quotient_kIso`, followed by the quotient map of the
`K`-isomorphism, is the identity. -/
theorem quotient_kIso_inv_comp_quotientMap {X' X : KLocallyRingedSpace.{u} K} (e : KIso X' X)
    (J : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    (quotient_kIso e J).inv ≫
        quotientMap e.hom (transportIdeal e J) J (QuotientSpace.compat_comap _ _) = 𝟙 _ := by
  rw [Iso.inv_comp_eq, Category.comp_id]
  have : LocallyRingedSpace.IsOpenImmersion
      (𝟙 (X.quotient J) : Hom (X.quotient J) (X.quotient J)).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (X.quotient J).toLocallyRingedSpace))
  exact ((Category.comp_id _).symm.trans (isoOfRangeEq_hom_comp
    (quotientMap e.hom (transportIdeal e J) J (QuotientSpace.compat_comap _ _))
    (𝟙 (X.quotient J)) (range_quotientMap_kIso e J))).symm

/-- The inverse of the restriction-quotient isomorphism `restrictOpen_quotient_iso`, followed by
the quotient map of the open immersion, is the open immersion of the quotient. -/
theorem restrictOpen_quotient_iso_inv_comp_quotientMap (X : KLocallyRingedSpace.{u} K)
    (J : IdealSheaf X.toLocallyRingedSpace.𝒪) (U : Opens X) :
    (restrictOpen_quotient_iso X J U).inv ≫
        quotientMap (X.ofRestrict U) (restrictIdeal X J U) J (QuotientSpace.compat_comap _ _) =
      ofRestrict (X.quotient J) (quotientOpens X J U) := by
  rw [Iso.inv_comp_eq]
  exact (isoOfRangeEq_hom_comp _ _ (range_quotientMap_ofRestrict X J U)).symm

/-- The restricted `K`-isomorphism `restrictOpenIso e V` lies over `e` — composed with the open
immersion of `Y | V` it is the open immersion of the source followed by `e`. -/
theorem restrictOpenIso_hom_comp_ofRestrict {X Y : KLocallyRingedSpace.{u} K} (e : X ≅ Y)
    (V : Opens Y) :
    (restrictOpenIso e V).hom ≫ ofRestrict Y V =
      ofRestrict X ((Opens.map e.hom.1.base).obj V) ≫ e.hom := by
  have : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict X ((Opens.map e.hom.1.base).obj V) ≫ e.hom).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict X ((Opens.map e.hom.1.base).obj V)).1 ≫ e.hom.1))
  exact isoOfRangeEq_hom_comp _ _ _

/-- The restriction-of-a-restriction isomorphism (`restrictOpen_restrictOpen_iso`) is over `X` on
points — its inverse followed by the two open immersions is the open immersion of the image
open. -/
theorem val_toFun_restrictOpen_restrictOpen_iso_inv {X : KLocallyRingedSpace.{u} K} (U : Opens X)
    (V : Opens (X.restrictOpen U)) (z : X.restrictOpen (imageOpens U V)) :
    (Hom.toFun (ofRestrict (X.restrictOpen U) V)
      (Hom.toFun (restrictOpen_restrictOpen_iso U V).inv z)).1 = Subtype.val z := by
  have hc : (restrictOpen_restrictOpen_iso U V).hom ≫ ofRestrict X (imageOpens U V) =
      ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U :=
    isoOfRangeEq_hom_comp _ _ _
  have hinv : (restrictOpen_restrictOpen_iso U V).inv ≫
      (ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U) = ofRestrict X (imageOpens U V) :=
    (Iso.inv_comp_eq _).mpr hc.symm
  exact congrArg (fun g => Hom.toFun g z) hinv

/-- Transporting an open subspace along an equality of the opens is the identity on points. -/
theorem val_toFun_eqToHom_restrictOpen {X : KLocallyRingedSpace.{u} K} {U U' : Opens X}
    (h : U = U') (y : X.restrictOpen U) :
    (Hom.toFun (eqToHom (congrArg X.restrictOpen h)) y).1 = Subtype.val y := by
  subst h
  rfl

end AnalyticSpace.KLocallyRingedSpace

namespace Hironaka.Manifold

open _root_.Manifold

section PieceCoord

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (G : Opens (Fin n → 𝕜))

/-- The coordinate map `pieceCoord` of a one-piece ambient is an open map (it is the chart at
every point, `map_nhds_pieceCoord`). -/
theorem isOpenMap_pieceCoord : IsOpenMap (pieceCoord.{u} G) :=
  IsOpenMap.of_nhds_le fun w => (map_nhds_pieceCoord (G := G) w).ge

/-- The coordinate map of a one-piece ambient has range `G`. -/
theorem range_pieceCoord : Set.range (pieceCoord.{u} G) = (G : Set (Fin n → 𝕜)) :=
  Set.ext fun v =>
    ⟨fun ⟨w, hw⟩ => hw ▸ pieceCoord_mem G w, fun hv => ⟨⟨PUnit.unit, ⟨v, hv⟩⟩, rfl⟩⟩

end PieceCoord

section ComapPieceAmbientIncl

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G)
  (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- The inverse image of a nowhere-zero ideal sheaf along the inclusion `Sp(G') → Sp(G)` of a
smaller one-piece ambient is nowhere zero — the germ map at a local analytic isomorphism is
injective (`germMap_bijective_of_isLocalDiffeomorphAt`). -/
theorem isNonzeroEverywhere_comap_pieceAmbientIncl (hJ : J.IsNonzeroEverywhere) :
    (J.pullback _ (pieceAmbientIncl h).contMDiff).IsNonzeroEverywhere := by
  intro b
  rw [IdealSheaf.stalkIdeal_pullback]
  exact fun hb => hJ (pieceAmbientIncl h b)
    ((Ideal.map_eq_bot_iff_of_injective (germMap_bijective_of_isLocalDiffeomorphAt _ _
      (isLocalDiffeomorph_pieceAmbientIncl h b)).1).mp hb)

/-- The inverse image of a reduced ideal sheaf along the inclusion `Sp(G') → Sp(G)` of a smaller
one-piece ambient is reduced — the germ map at a local analytic isomorphism is a ring isomorphism,
and a radical ideal maps to a radical ideal (`Ideal.map_radical_of_surjective`; the argument of
`IdealSheaf.isReduced_pullback_diffeomorph`). -/
theorem isReduced_comap_pieceAmbientIncl (hJ : J.IsReduced) :
    AnalyticManifold.IdealSheaf.IsReduced (J.pullback _ (pieceAmbientIncl h).contMDiff) := by
  intro b
  rw [IdealSheaf.stalkIdeal_pullback]
  obtain ⟨hinj, hsurj⟩ := germMap_bijective_of_isLocalDiffeomorphAt _ _
    (isLocalDiffeomorph_pieceAmbientIncl h b)
  have hker : RingHom.ker (germMap (⇑(pieceAmbientIncl h)) (pieceAmbientIncl h).contMDiff b) ≤
      J.stalkIdeal (pieceAmbientIncl h b) := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  rw [← Ideal.radical_eq_iff, ← Ideal.map_radical_of_surjective hsurj hker,
    Ideal.radical_eq_iff.mpr (hJ (pieceAmbientIncl h b))]

end ComapPieceAmbientIncl

/-- The canonical morphism `Sp(A)/J → Sp(A)` of a closed subspace is a closed embedding of the
underlying spaces — the inclusion of the closed cosupport (`range_toFun_closedSubspaceι`; the
support of a closed subspace, [Hir64, Ch. 0, §1, p. 119]), read into the manifold `A`. -/
theorem isClosedEmbedding_toFun_toAnalyticSpaceι {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
        (J : AnalyticManifold.IdealSheaf A) :
    IsClosedEmbedding (X := J.toAnalyticSpace) (Y := A)
      fun z => J.toAnalyticSpaceι z :=
  (IdealSheaf.isClosed_support J).isClosedEmbedding_subtypeVal

namespace PieceEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-! ### The embedding as a homeomorphism and as a `K`-isomorphism; the ambient point is a closed
embedding -/

/-- The model isomorphism `emb : X|V ≅ Sp(G)/𝓘` as a `K`-isomorphism of the underlying
`K`-local-ringed spaces, with the source in its `restrictOpen` spelling. -/
def embKIso :
    KIso (X.toKLocallyRingedSpace.restrictOpen (openOf X V))
      E.ideal.toAnalyticSpace.toKLocallyRingedSpace :=
  haveI : IsIso E.emb := E.emb_isIso
  { hom := (asIso E.emb).hom
    inv := (asIso E.emb).inv
    hom_inv_id := (asIso E.emb).hom_inv_id
    inv_hom_id := (asIso E.emb).inv_hom_id }

/-- The `hom` of `embKIso` is the embedding `emb`. -/
theorem embKIso_hom : E.embKIso.hom = E.emb := rfl

/-- The model isomorphism as a homeomorphism of the underlying spaces. -/
def embHomeomorph : (X.restrictSet V) ≃ₜ E.ideal.toAnalyticSpace :=
  haveI : IsIso E.emb := E.emb_isIso
  { toFun := E.emb
    invFun := (asIso E.emb).inv
    left_inv := fun y =>
      congrArg (fun g => g y) (asIso E.emb).hom_inv_id
    right_inv := fun z =>
      congrArg (fun g => g z) (asIso E.emb).inv_hom_id
    continuous_toFun := Hom.continuous_toFun E.emb
    continuous_invFun := Hom.continuous_toFun (asIso E.emb).inv }

/-- `embHomeomorph` evaluates as `emb` on points. -/
theorem embHomeomorph_apply (y : X.restrictSet V) :
    E.embHomeomorph y = E.emb y := rfl

/-- **The ambient point map of a piece is a closed embedding** `X|V → Sp(G)` — the
closed-subspace inclusion after the homeomorphism `emb`. -/
theorem isClosedEmbedding_ambientPoint : IsClosedEmbedding E.ambientPoint :=
  (isClosedEmbedding_toFun_toAnalyticSpaceι E.ideal).comp E.embHomeomorph.isClosedEmbedding

/-- The ambient image of a closed subset of the piece is closed in `Sp(G)`. -/
theorem isClosed_image_ambientPoint_of_isClosed {S : Set (X.restrictSet V)} (hS : IsClosed S) :
    IsClosed (E.ambientPoint '' S) :=
  E.isClosedEmbedding_ambientPoint.isClosedMap S hS

/-! ### The shrunk ambient `G' = G ∖ amb(V ∖ V')` -/

section RestrictAmbient

variable {V' : Set X}

/-- **The shrunk ambient is open** — `G` minus the coordinate image of the ambient points of the
piece outside the open `V'`, a closed set (`V ∖ V'` is closed in the piece, `ambientPoint` a
closed embedding, `pieceCoord` an injective open map with range `G`). -/
theorem isOpen_restrictAmbient (hV' : IsOpen V') :
    IsOpen ((E.G : Set (Fin n → 𝕜)) \
      ((fun y => pieceCoord E.G (E.ambientPoint y)) ''
        {y : X.restrictSet V | Subtype.val y ∉ V'})) := by
  have hT : IsClosed (E.ambientPoint '' {y : X.restrictSet V | Subtype.val y ∉ V'}) :=
    E.isClosed_image_ambientPoint_of_isClosed
      (hV'.isClosed_compl.preimage continuous_subtype_val)
  have heq : (E.G : Set (Fin n → 𝕜)) \
      ((fun y => pieceCoord E.G (E.ambientPoint y)) '' {y : X.restrictSet V | Subtype.val y ∉ V'}) =
        pieceCoord E.G '' (E.ambientPoint '' {y : X.restrictSet V | Subtype.val y ∉ V'})ᶜ := by
    rw [Set.compl_eq_univ_sdiff, Set.image_sdiff (pieceCoord_injective (G := E.G)),
      Set.image_univ, range_pieceCoord, Set.image_image]
  rw [heq]
  exact isOpenMap_pieceCoord E.G _ hT.isOpen_compl

/-- **The ambient open of the restricted embedding** (Włodarczyk's extension of an open embedding
of germs to an open embedding `U_Z ⊂ U_{Z'}` of the ambient manifolds, [Wlo09, §4, (3)⇒(4)]) —
`G` minus the ambient image of the part of the piece outside `V'`, so that `Y ∩ G' = amb(V')`
(`pieceCoord_ambientPoint_mem_restrictAmbient_iff`). -/
def restrictAmbient (hV' : IsOpen V') : Opens (Fin n → 𝕜) :=
  ⟨(E.G : Set (Fin n → 𝕜)) \
    ((fun y => pieceCoord E.G (E.ambientPoint y)) '' {y : X.restrictSet V | Subtype.val y ∉ V'}),
    E.isOpen_restrictAmbient hV'⟩

/-- The shrunk ambient lies in the ambient. -/
theorem restrictAmbient_le (hV' : IsOpen V') : E.restrictAmbient hV' ≤ E.G := fun _ hz => hz.1

/-- Membership in the shrunk ambient — a point of `G` whose only preimages in the piece (under the
ambient point map) lie in `V'`. -/
theorem mem_restrictAmbient (hV' : IsOpen V') {v : Fin n → 𝕜} :
    v ∈ E.restrictAmbient hV' ↔
      v ∈ E.G ∧ ∀ y : X.restrictSet V, pieceCoord E.G (E.ambientPoint y) = v → Subtype.val y ∈ V'
          := by
  change v ∈ (E.G : Set (Fin n → 𝕜)) \ _ ↔ _
  constructor
  · rintro ⟨hG, hnot⟩
    exact ⟨hG, fun y hy => by_contra fun hyV => hnot ⟨y, hyV, hy⟩⟩
  · rintro ⟨hG, h⟩
    exact ⟨hG, fun ⟨y, hyV, hy⟩ => hyV (h y hy)⟩

/-- **The ambient point of a point of the piece lies in the shrunk ambient iff the point lies in
`V'`** (Włodarczyk's `Y ∩ U_Z = Y_Z`, [Wlo09, §4, (3)⇒(4)]) — the ambient point map is
injective. -/
theorem pieceCoord_ambientPoint_mem_restrictAmbient_iff (hV' : IsOpen V') (y : X.restrictSet V) :
    pieceCoord E.G (E.ambientPoint y) ∈ E.restrictAmbient hV' ↔ Subtype.val y ∈ V' := by
  rw [E.mem_restrictAmbient]
  refine ⟨fun h => h.2 y rfl, fun hy => ⟨pieceCoord_mem E.G _, fun y' hy' => ?_⟩⟩
  rwa [E.isClosedEmbedding_ambientPoint.injective (pieceCoord_injective (G := E.G) hy')]

end RestrictAmbient

/-! ### The restricted embedding: its model isomorphism, assembled -/

section RestrictPiece

variable {V' : Set X}

/-- The ambient `K`-space `Sp(G)` of the piece. -/
abbrev ambientSpace : KLocallyRingedSpace.{u} 𝕜 :=
  (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (pieceAmbient 𝕜 E.G)).toKLocallyRingedSpace

/-- The shrunk ambient `K`-space `Sp(G')`. -/
abbrev restrictAmbientSpace (hV' : IsOpen V') : KLocallyRingedSpace.{u} 𝕜 :=
  (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (pieceAmbient 𝕜 (E.restrictAmbient hV'))).toKLocallyRingedSpace

/-- The open of the closed subspace `Sp(G)/𝓘` lying over the shrunk ambient `G'` (`quotientOpens`
at `coordPreimage G' G`). -/
def subPieceOpens (hV' : IsOpen V') : Opens E.ideal.toAnalyticSpace :=
  quotientOpens E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)

/-- The open of the piece `X|V` over the shrunk ambient — the preimage of `subPieceOpens` under
`emb`; its points are those of `embPreimage` at `coordPreimage G' G`. -/
def subPieceOpens₁ (hV' : IsOpen V') :
    Opens (X.toKLocallyRingedSpace.restrictOpen (openOf X V)) :=
  (Opens.map E.emb.1.base).obj (E.subPieceOpens hV')

/-- A point of the piece lies in `subPieceOpens₁` iff its ambient coordinate lies in the shrunk
ambient. -/
theorem mem_subPieceOpens₁ (hV' : IsOpen V')
    (y : X.toKLocallyRingedSpace.restrictOpen (openOf X V)) :
    y ∈ E.subPieceOpens₁ hV' ↔ pieceCoord E.G (E.ambientPoint y) ∈ E.restrictAmbient hV' :=
  Iff.rfl

/-- The two open immersions into `X` — of `X|V'` and of the open of `X|V` over the shrunk
ambient — have the same range, `V'` (`pieceCoord_ambientPoint_mem_restrictAmbient_iff`). -/
theorem range_ofRestrict_eq_range_subPieceOpens₁ (hV' : IsOpen V') (hsub : V' ⊆ V) :
    Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict X.toKLocallyRingedSpace
        (openOf X V'))) =
      Set.range (KLocallyRingedSpace.Hom.toFun
        (ofRestrict (X.toKLocallyRingedSpace.restrictOpen
            (openOf X V)) (E.subPieceOpens₁ hV') ≫
          ofRestrict X.toKLocallyRingedSpace (openOf X V))) := by
  rw [range_toFun_ofRestrict, Hom.toFun_comp, Set.range_comp, range_toFun_ofRestrict,
    openOf_of_isOpen X hV']
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, mem_openOf_of_subset hsub hx⟩,
      (E.mem_subPieceOpens₁ hV' _).mpr
        ((E.pieceCoord_ambientPoint_mem_restrictAmbient_iff hV' _).mpr hx), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (E.pieceCoord_ambientPoint_mem_restrictAmbient_iff hV' y).mp
      ((E.mem_subPieceOpens₁ hV' y).mp hy)

/-- The image in `X` of the open of the piece over the shrunk ambient is `V'` (`imageOpens`: the
range of the composite open immersion). -/
theorem imageOpens_subPieceOpens₁ (hV' : IsOpen V') (hsub : V' ⊆ V) :
    imageOpens (openOf X V) (E.subPieceOpens₁ hV') =
      openOf X V' :=
  Opens.ext ((E.range_ofRestrict_eq_range_subPieceOpens₁ hV' hsub).symm.trans
    (range_toFun_ofRestrict _ _))

/-- `X|V' ≅ (X|V)|_W`, `W` the open of the piece over the shrunk ambient — the restriction of a
restriction is the restriction to the image open (`restrictOpen_restrictOpen_iso`), the image
being `V'`. -/
def subPieceIso₁ (hV' : IsOpen V') (hsub : V' ⊆ V) :
    (X.restrictSet V').toKLocallyRingedSpace ≅
      (X.toKLocallyRingedSpace.restrictOpen
        (openOf X V)).restrictOpen (E.subPieceOpens₁ hV') :=
  eqToIso (congrArg X.toKLocallyRingedSpace.restrictOpen
      (E.imageOpens_subPieceOpens₁ hV' hsub).symm) ≪≫
    (restrictOpen_restrictOpen_iso (openOf X V)
      (E.subPieceOpens₁ hV')).symm

/-- The isomorphism `X|V' ≅ (X|V)|_W` is over `X` on points. -/
theorem val_toFun_subPieceIso₁ (hV' : IsOpen V') (hsub : V' ⊆ V) (y : X.restrictSet V') :
    (KLocallyRingedSpace.Hom.toFun (ofRestrict (X.toKLocallyRingedSpace.restrictOpen
        (openOf X V)) (E.subPieceOpens₁ hV'))
      (KLocallyRingedSpace.Hom.toFun (E.subPieceIso₁ hV' hsub).hom y)).1 = Subtype.val y :=
  (val_toFun_restrictOpen_restrictOpen_iso_inv (openOf X V)
    (E.subPieceOpens₁ hV')
    (KLocallyRingedSpace.Hom.toFun (eqToHom (congrArg X.toKLocallyRingedSpace.restrictOpen
      (E.imageOpens_subPieceOpens₁ hV' hsub).symm)) y)).trans
    (val_toFun_eqToHom_restrictOpen (E.imageOpens_subPieceOpens₁ hV' hsub).symm y)

/-- The `K`-isomorphism `Sp(G') ≅ Sp(G) | coordPreimage G' G` — `Sp` of the diffeomorphism
`pieceAmbientInclDiffeo`, then `Sp(U) ≅ Sp(G)|U` (`ofManifold_restrictOpen_iso`). -/
def restrictAmbientKIso (hV' : IsOpen V') :
    KIso (E.restrictAmbientSpace hV')
      (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G)) :=
  ofManifoldIso (⇑(pieceAmbientInclDiffeo (E.restrictAmbient_le hV')))
    (⇑(pieceAmbientInclDiffeo (E.restrictAmbient_le hV')).symm)
    (pieceAmbientInclDiffeo (E.restrictAmbient_le hV')).contMDiff
    (pieceAmbientInclDiffeo (E.restrictAmbient_le hV')).symm.contMDiff
    (pieceAmbientInclDiffeo (E.restrictAmbient_le hV')).symm_apply_apply
    (pieceAmbientInclDiffeo (E.restrictAmbient_le hV')).apply_symm_apply ≪≫
  (ofManifold_restrictOpen_iso (coordPreimage (E.restrictAmbient hV') E.G)).symm

/-- The `K`-isomorphism `Sp(G') ≅ Sp(G)|U` followed by the open immersion `Sp(G)|U → Sp(G)` is
`Sp` of the inclusion `pieceAmbientIncl`. -/
theorem restrictAmbientKIso_hom_comp_ofRestrict (hV' : IsOpen V') :
    (E.restrictAmbientKIso hV').hom ≫
        ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G) =
      ofManifoldHom (⇑(pieceAmbientIncl (E.restrictAmbient_le hV')))
        (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff := by
  have haux : (ofManifold_restrictOpen_iso (K := 𝕜) (E := Fin n → 𝕜)
        (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫
      ofRestrict (ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient 𝕜 E.G))
        (coordPreimage (E.restrictAmbient hV') E.G) =
      ofManifoldHom
        (Subtype.val : coordPreimage (E.restrictAmbient hV') E.G → pieceAmbient 𝕜 E.G)
        contMDiff_subtype_val := by
    rw [← ofManifold_restrictOpen_iso_hom_comp, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => ofManifoldHom (⇑(pieceAmbientInclDiffeo (E.restrictAmbient_le hV')))
        (pieceAmbientInclDiffeo (E.restrictAmbient_le hV')).contMDiff ≫ g) haux).trans
      ((ofManifoldHom_comp _ _ _ _).symm.trans
        (ofManifoldHom_congr (funext fun w => pieceAmbientInclDiffeo_apply _ w) _)))

/-- The restricted ideal `𝓘|_U`, transported along `Sp(G') ≅ Sp(G)|U`, is the pullback of `𝓘`
along the inclusion `Sp(G') → Sp(G)` (`comap_ofManifoldHom_eq_pullback`). -/
theorem transportIdeal_restrictAmbientKIso (hV' : IsOpen V') :
    transportIdeal (E.restrictAmbientKIso hV')
        (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G)) =
      E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff :=
  (QuotientSpace.comap_comp
      (φ := (ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G)).1)
      (J := E.ideal) (E.restrictAmbientKIso hV').hom.1).symm.trans
    ((congrArg (fun φ : (E.restrictAmbientSpace hV').toLocallyRingedSpace ⟶
          E.ambientSpace.toLocallyRingedSpace => QuotientSpace.comap φ E.ideal)
      (Hom.comp_val (E.restrictAmbientKIso hV').hom
        (ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G)))).symm.trans
      ((congrArg (fun g : E.restrictAmbientSpace hV' ⟶ E.ambientSpace =>
          QuotientSpace.comap g.1 E.ideal) (E.restrictAmbientKIso_hom_comp_ofRestrict hV')).trans
        (comap_ofManifoldHom_eq_pullback _ _ E.ideal)))

/-- **The model isomorphism of the restricted embedding**, `X|V' ≅ Sp(G')/𝓘'` — assembled as
`X|V' ≅ (X|V)|_W ≅ (Sp(G)/𝓘)|_W ≅ (Sp(G)|_U)/(𝓘|_U) ≅ Sp(G')/𝓘'` (the pattern of
`modelPieceEmbIso`, `PieceModel.lean`). -/
def restrictPieceEmbIso (hV' : IsOpen V') (hsub : V' ⊆ V) :
    (X.restrictSet V').toKLocallyRingedSpace ≅
      (AnalyticManifold.IdealSheaf.toAnalyticSpace (E.ideal.pullback _ (pieceAmbientIncl
          (E.restrictAmbient_le
          hV')).contMDiff)).toKLocallyRingedSpace :=
  E.subPieceIso₁ hV' hsub ≪≫ restrictOpenIso E.embKIso (E.subPieceOpens hV') ≪≫
    (restrictOpen_quotient_iso E.ambientSpace E.ideal
      (coordPreimage (E.restrictAmbient hV') E.G)).symm ≪≫
    (quotient_kIso (E.restrictAmbientKIso hV') _).symm ≪≫
    quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')

/-- **The restricted piece embedding** `E|V'` of an open `V' ⊆ V` (Włodarczyk's extension of an
open embedding `Y_Z ⊂ Y_{Z'}` of germs to an open embedding `U_Z ⊂ U_{Z'}` of the ambient
manifolds, [Wlo09, §4, (3)⇒(4)]) — the ambient shrunk to `restrictAmbient`, the SAME ideal pulled
back along the inclusion `Sp(G') → Sp(G)`, its stalk conditions transported along the open
embedding, the model isomorphism restricted (`restrictPieceEmbIso`). The embedding to which the
independence of the local resolution from the embedding (`LocalResolutionIndependentOn`) is applied
over an overlap of two pieces. -/
def restrictPiece (hV' : IsOpen V') (hsub : V' ⊆ V) : PieceEmbedding 𝕜 n X V' where
  G := E.restrictAmbient hV'
  ideal :=
      E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff
  isNonzeroEverywhere := isNonzeroEverywhere_comap_pieceAmbientIncl _ _ E.isNonzeroEverywhere
  isReduced := isReduced_comap_pieceAmbientIncl _ _ E.isReduced
  emb := (E.restrictPieceEmbIso hV' hsub).hom
  emb_isIso := by
    exact ⟨⟨(E.restrictPieceEmbIso hV' hsub).inv, (E.restrictPieceEmbIso hV' hsub).hom_inv_id,
      (E.restrictPieceEmbIso hV' hsub).inv_hom_id⟩⟩

/-- The ambient of the restricted embedding is the shrunk ambient (by `rfl`). -/
theorem restrictPiece_G (hV' : IsOpen V') (hsub : V' ⊆ V) :
    (E.restrictPiece hV' hsub).G = E.restrictAmbient hV' := rfl

/-- The ideal of the restricted embedding is the pullback of `𝓘` along the inclusion (by `rfl`);
the commutation of the functor with local analytic isomorphisms (`IsEmbeddedDesing`,
[Wlo09, Theorem 2.0.2(4)]) is read on it. -/
theorem restrictPiece_ideal (hV' : IsOpen V') (hsub : V' ⊆ V) :
    (E.restrictPiece hV' hsub).ideal =
      E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff :=
  rfl

/-- A point of the sub-piece `X|V'` as a point of the piece `X|V`. -/
theorem val_mem_openOf (hV' : IsOpen V') (hsub : V' ⊆ V) (y : X.restrictSet V') :
    Subtype.val y ∈ openOf X V :=
  mem_openOf_of_subset hsub
    (mem_of_mem_openOf hV' y.2)

/-- **The ambient point of a point of the sub-piece, read in `Sp(G)`, is its ambient point in the
piece** — the model isomorphism of the restricted embedding lies over the inclusion of the
ambients, factor by factor. -/
theorem pieceAmbientIncl_ambientPoint_restrictPiece (hV' : IsOpen V') (hsub : V' ⊆ V)
    (y : X.restrictSet V') :
    pieceAmbientIncl (E.restrictAmbient_le hV') ((E.restrictPiece hV' hsub).ambientPoint y) =
      E.ambientPoint ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩ := by
  -- the five factors of the model isomorphism, as functions: each lies over the next stage
  have s₅ : KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
        (E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff)) ∘
        KLocallyRingedSpace.Hom.toFun ((quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso
            hV')).hom) =
      KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
        (transportIdeal (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
          (coordPreimage (E.restrictAmbient hV') E.G)))) :=
    (Hom.toFun_comp _ _).symm.trans (congrArg KLocallyRingedSpace.Hom.toFun
      (quotientIsoOfEq_hom_comp_quotientι (E.transportIdeal_restrictAmbientKIso hV')))
  have s₄ : KLocallyRingedSpace.Hom.toFun (ofRestrict E.ambientSpace (coordPreimage
      (E.restrictAmbient hV') E.G)) ∘
        KLocallyRingedSpace.Hom.toFun (E.restrictAmbientKIso hV').hom =
      ⇑(pieceAmbientIncl (E.restrictAmbient_le hV')) :=
    (Hom.toFun_comp _ _).symm.trans ((congrArg KLocallyRingedSpace.Hom.toFun
      (E.restrictAmbientKIso_hom_comp_ofRestrict hV')).trans (toFun_ofManifoldHom _ _))
  have s₃ : KLocallyRingedSpace.Hom.toFun (E.restrictAmbientKIso hV').hom ∘
        KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
          (transportIdeal (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
            (coordPreimage (E.restrictAmbient hV') E.G)))) =
      KLocallyRingedSpace.Hom.toFun (quotientι
          (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) ∘
        KLocallyRingedSpace.Hom.toFun (quotientMap (E.restrictAmbientKIso hV').hom
          (transportIdeal (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
            (coordPreimage (E.restrictAmbient hV') E.G)))
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))
          (QuotientSpace.compat_comap _ _)) :=
    ((Hom.toFun_comp _ _).symm.trans ((congrArg KLocallyRingedSpace.Hom.toFun
      (quotientMap_comp_quotientι _ _ _ _)).trans (Hom.toFun_comp _ _))).symm
  have s₂ : KLocallyRingedSpace.Hom.toFun (quotientMap (E.restrictAmbientKIso hV').hom
        (transportIdeal (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
          (coordPreimage (E.restrictAmbient hV') E.G)))
        (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))
        (QuotientSpace.compat_comap _ _)) ∘
        KLocallyRingedSpace.Hom.toFun (quotient_kIso (E.restrictAmbientKIso hV')
            (restrictIdeal E.ambientSpace E.ideal
          (coordPreimage (E.restrictAmbient hV') E.G))).inv = id :=
    (Hom.toFun_comp _ _).symm.trans ((congrArg KLocallyRingedSpace.Hom.toFun
      (quotient_kIso_inv_comp_quotientMap _ _)).trans (Hom.toFun_id _))
  have s₁ : KLocallyRingedSpace.Hom.toFun (ofRestrict E.ambientSpace (coordPreimage
      (E.restrictAmbient hV') E.G)) ∘
        KLocallyRingedSpace.Hom.toFun (quotientι
          (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))) =
      KLocallyRingedSpace.Hom.toFun (quotientι E.ambientSpace E.ideal) ∘
        KLocallyRingedSpace.Hom.toFun (quotientMap
          (ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G))
          (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))
          E.ideal (QuotientSpace.compat_comap _ _)) :=
    ((Hom.toFun_comp _ _).symm.trans ((congrArg KLocallyRingedSpace.Hom.toFun
      (quotientMap_comp_quotientι _ _ _ _)).trans (Hom.toFun_comp _ _))).symm
  have s₀ : KLocallyRingedSpace.Hom.toFun (quotientMap
        (ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G))
        (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))
        E.ideal (QuotientSpace.compat_comap _ _)) ∘
        KLocallyRingedSpace.Hom.toFun (restrictOpen_quotient_iso E.ambientSpace E.ideal
          (coordPreimage (E.restrictAmbient hV') E.G)).inv =
      KLocallyRingedSpace.Hom.toFun (ofRestrict (E.ambientSpace.quotient E.ideal)
          (E.subPieceOpens hV')) :=
    (Hom.toFun_comp _ _).symm.trans (congrArg KLocallyRingedSpace.Hom.toFun
      (restrictOpen_quotient_iso_inv_comp_quotientMap _ _ _))
  have r₂ : KLocallyRingedSpace.Hom.toFun (ofRestrict (E.ambientSpace.quotient E.ideal)
      (E.subPieceOpens hV')) ∘
        KLocallyRingedSpace.Hom.toFun (restrictOpenIso E.embKIso (E.subPieceOpens hV')).hom =
      KLocallyRingedSpace.Hom.toFun E.emb ∘ KLocallyRingedSpace.Hom.toFun (ofRestrict
          (X.toKLocallyRingedSpace.restrictOpen
        (openOf X V)) (E.subPieceOpens₁ hV')) :=
    (Hom.toFun_comp _ _).symm.trans ((congrArg KLocallyRingedSpace.Hom.toFun
      (restrictOpenIso_hom_comp_ofRestrict _ _)).trans (Hom.toFun_comp _ _))
  -- the points along the chain
  obtain ⟨z₁, hz₁⟩ : ∃ z, z = KLocallyRingedSpace.Hom.toFun (E.subPieceIso₁ hV' hsub).hom y := ⟨_,
      rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z, z = KLocallyRingedSpace.Hom.toFun (restrictOpenIso E.embKIso
      (E.subPieceOpens hV')).hom z₁ :=
    ⟨_, rfl⟩
  obtain ⟨z₃, hz₃⟩ : ∃ z, z = KLocallyRingedSpace.Hom.toFun (restrictOpen_quotient_iso
      E.ambientSpace E.ideal
      (coordPreimage (E.restrictAmbient hV') E.G)).inv z₂ := ⟨_, rfl⟩
  obtain ⟨z₄, hz₄⟩ : ∃ z, z = KLocallyRingedSpace.Hom.toFun (quotient_kIso
      (E.restrictAmbientKIso hV')
      (restrictIdeal E.ambientSpace E.ideal (coordPreimage (E.restrictAmbient hV') E.G))).inv z₃ :=
    ⟨_, rfl⟩
  have r₁ : KLocallyRingedSpace.Hom.toFun (ofRestrict (X.toKLocallyRingedSpace.restrictOpen
        (openOf X V)) (E.subPieceOpens₁ hV')) z₁ =
      ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩ :=
    Subtype.ext ((congrArg (fun w => (KLocallyRingedSpace.Hom.toFun (ofRestrict
        (X.toKLocallyRingedSpace.restrictOpen
      (openOf X V)) (E.subPieceOpens₁ hV')) w).1) hz₁).trans
      (E.val_toFun_subPieceIso₁ hV' hsub y))
  have key : pieceAmbientIncl (E.restrictAmbient_le hV')
      (KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
        (E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff))
        (KLocallyRingedSpace.Hom.toFun ((quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso
            hV')).hom) z₄)) =
      KLocallyRingedSpace.Hom.toFun (quotientι E.ambientSpace E.ideal)
        (KLocallyRingedSpace.Hom.toFun E.emb ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩) :=
    (congrArg ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
        (Function.comp_apply.symm.trans (congrFun s₅ z₄))).trans
      (((congrFun s₄ (KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
            (transportIdeal (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G)))) z₄)).symm.trans
          Function.comp_apply).trans
        ((congrArg (KLocallyRingedSpace.Hom.toFun (ofRestrict E.ambientSpace
            (coordPreimage (E.restrictAmbient hV') E.G)))
            (Function.comp_apply.symm.trans ((congrFun s₃ z₄).trans Function.comp_apply))).trans
          ((congrArg (fun w => KLocallyRingedSpace.Hom.toFun (ofRestrict E.ambientSpace
              (coordPreimage (E.restrictAmbient hV') E.G)) (KLocallyRingedSpace.Hom.toFun (quotientι
                (E.ambientSpace.restrictOpen (coordPreimage (E.restrictAmbient hV') E.G))
                (restrictIdeal E.ambientSpace E.ideal
                  (coordPreimage (E.restrictAmbient hV') E.G))) w))
              ((congrArg (KLocallyRingedSpace.Hom.toFun (quotientMap (E.restrictAmbientKIso hV').hom
                (transportIdeal (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
                  (coordPreimage (E.restrictAmbient hV') E.G)))
                (restrictIdeal E.ambientSpace E.ideal
                  (coordPreimage (E.restrictAmbient hV') E.G))
                (QuotientSpace.compat_comap _ _))) hz₄).trans
                (Function.comp_apply.symm.trans ((congrFun s₂ z₃).trans (id_eq z₃))))).trans
            ((Function.comp_apply.symm.trans ((congrFun s₁ z₃).trans Function.comp_apply)).trans
              ((congrArg (KLocallyRingedSpace.Hom.toFun (quotientι E.ambientSpace E.ideal))
                  ((congrArg (KLocallyRingedSpace.Hom.toFun (quotientMap
                    (ofRestrict E.ambientSpace (coordPreimage (E.restrictAmbient hV') E.G))
                    (restrictIdeal E.ambientSpace E.ideal
                      (coordPreimage (E.restrictAmbient hV') E.G))
                    E.ideal (QuotientSpace.compat_comap _ _))) hz₃).trans
                    (Function.comp_apply.symm.trans (congrFun s₀ z₂)))).trans
                ((congrArg (KLocallyRingedSpace.Hom.toFun (quotientι E.ambientSpace E.ideal))
                    ((congrArg (KLocallyRingedSpace.Hom.toFun (ofRestrict
                        (E.ambientSpace.quotient E.ideal)
                      (E.subPieceOpens hV'))) hz₂).trans
                      (Function.comp_apply.symm.trans
                        ((congrFun r₂ z₁).trans Function.comp_apply)))).trans
                  (congrArg (fun w => KLocallyRingedSpace.Hom.toFun
                      (quotientι E.ambientSpace E.ideal)
                    (KLocallyRingedSpace.Hom.toFun E.emb w)) r₁)))))))
  -- the composite `hom`, factor by factor
  have e₀ : (E.restrictPieceEmbIso hV' hsub).hom =
      (E.subPieceIso₁ hV' hsub).hom ≫
        ((restrictOpenIso E.embKIso (E.subPieceOpens hV')).hom ≫
          ((restrictOpen_quotient_iso E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫
            ((quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
                (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫
              (quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom))) := rfl
  have hchain : KLocallyRingedSpace.Hom.toFun (E.restrictPieceEmbIso hV' hsub).hom y =
      KLocallyRingedSpace.Hom.toFun ((quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso
          hV')).hom) z₄ := by
    subst hz₄ hz₃ hz₂ hz₁
    exact (congrArg (fun g => KLocallyRingedSpace.Hom.toFun g y) e₀).trans
      (((congrFun (Hom.toFun_comp (E.subPieceIso₁ hV' hsub).hom
        ((restrictOpenIso E.embKIso (E.subPieceOpens hV')).hom ≫
          ((restrictOpen_quotient_iso E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫
            ((quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
                (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫
              (quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom)))) y).trans
          Function.comp_apply).trans
      (((congrFun (Hom.toFun_comp (restrictOpenIso E.embKIso (E.subPieceOpens hV')).hom
          ((restrictOpen_quotient_iso E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G)).inv ≫
            ((quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
                (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫
              (quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom)))
          (KLocallyRingedSpace.Hom.toFun (E.subPieceIso₁ hV' hsub).hom y)).trans
              Function.comp_apply).trans
      (((congrFun (Hom.toFun_comp (restrictOpen_quotient_iso E.ambientSpace E.ideal
            (coordPreimage (E.restrictAmbient hV') E.G)).inv
          ((quotient_kIso (E.restrictAmbientKIso hV') (restrictIdeal E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G))).inv ≫
            (quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom))
          (KLocallyRingedSpace.Hom.toFun (restrictOpenIso E.embKIso (E.subPieceOpens hV')).hom
            (KLocallyRingedSpace.Hom.toFun (E.subPieceIso₁ hV' hsub).hom y))).trans
                Function.comp_apply).trans
      ((congrFun (Hom.toFun_comp (quotient_kIso (E.restrictAmbientKIso hV')
            (restrictIdeal E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G))).inv
          ((quotientIsoOfEq (E.transportIdeal_restrictAmbientKIso hV')).hom))
          (KLocallyRingedSpace.Hom.toFun (restrictOpen_quotient_iso E.ambientSpace E.ideal
              (coordPreimage (E.restrictAmbient hV') E.G)).inv
            (KLocallyRingedSpace.Hom.toFun (restrictOpenIso E.embKIso (E.subPieceOpens hV')).hom
              (KLocallyRingedSpace.Hom.toFun (E.subPieceIso₁ hV' hsub).hom y)))).trans
          Function.comp_apply))))
  -- the two ambient points, read through the closed-subspace inclusions (definitional)
  have e₁ : (E.restrictPiece hV' hsub).ambientPoint y =
      KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
        (E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff))
        (KLocallyRingedSpace.Hom.toFun (E.restrictPieceEmbIso hV' hsub).hom y) := rfl
  have e₂ : E.ambientPoint ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩ =
      KLocallyRingedSpace.Hom.toFun (quotientι E.ambientSpace E.ideal)
        (KLocallyRingedSpace.Hom.toFun E.emb ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩) := rfl
  exact (congrArg (fun w => pieceAmbientIncl (E.restrictAmbient_le hV') w) e₁).trans
    ((congrArg (fun w => pieceAmbientIncl (E.restrictAmbient_le hV')
      (KLocallyRingedSpace.Hom.toFun (quotientι (E.restrictAmbientSpace hV')
        (E.ideal.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff)) w))
      hchain).trans (key.trans e₂.symm))

/-- The ambient point of a point of the sub-piece is its ambient point in the piece, read in
`𝕜ⁿ`. -/
theorem pieceCoord_ambientPoint_restrictPiece (hV' : IsOpen V') (hsub : V' ⊆ V)
    (y : X.restrictSet V') :
    pieceCoord _ ((E.restrictPiece hV' hsub).ambientPoint y) =
      pieceCoord E.G (E.ambientPoint ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩) :=
  (pieceCoord_pieceAmbientIncl (E.restrictAmbient_le hV')
    ((E.restrictPiece hV' hsub).ambientPoint y)).symm.trans
    (congrArg (pieceCoord E.G) (E.pieceAmbientIncl_ambientPoint_restrictPiece hV' hsub y))

/-- **The points of the sub-piece over an open `W'` of the shrunk ambient are the points of the
piece over the image of `W'`** (in `V'`). -/
theorem embPreimage_restrictPiece (hV' : IsOpen V') (hsub : V' ⊆ V)
    (W' : Opens (pieceAmbient 𝕜 (E.restrictAmbient hV'))) (y : X.restrictSet V') :
    y ∈ (E.restrictPiece hV' hsub).embPreimage W' ↔
      E.ambientPoint ⟨Subtype.val y, val_mem_openOf hV' hsub y⟩ ∈
        pieceAmbientImageOpens (E.restrictAmbient_le hV') W' :=
  (show (E.restrictPiece hV' hsub).ambientPoint y ∈ W' ↔
      pieceAmbientIncl (E.restrictAmbient_le hV') ((E.restrictPiece hV' hsub).ambientPoint y) ∈
        pieceAmbientImageOpens (E.restrictAmbient_le hV') W' from
    ⟨fun hy => ⟨_, hy, rfl⟩, fun ⟨_, hw, hwe⟩ => pieceAmbientIncl_injective _ hwe ▸ hw⟩).trans
    (iff_of_eq (congrArg (· ∈ pieceAmbientImageOpens (E.restrictAmbient_le hV') W')
      (E.pieceAmbientIncl_ambientPoint_restrictPiece hV' hsub y)))

end RestrictPiece

end PieceEmbedding

end Hironaka.Manifold

end
