/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The closed subspace along an analytic map, and the restriction of an isomorphism

The independence of the local resolution of a piece from its embedding
[Kol07, Theorem 36, proof] compares two local resolutions as analytic `𝕜`-spaces: each is the
closed subspace of the last stage of a blow-up sequence cut out by the final ideal-theoretic
strict transform (`IdealSheaf.toAnalyticSpace`, the closed subspace of `Sp` of a manifold), and
the comparison is a chain of isomorphisms of closed subspaces, each induced by an identity of ideal
sheaves along a manifold map — the functoriality of the germ quotient (`quotientMap`) along
`Sp(f)`. This module provides that layer:

* `IdealSheaf.homOfPullbackEq` (`PieceIndependence.lean`, with the compatibility
  `compat_ofManifoldHom_of_eq`): **the morphism of closed subspaces over `Sp(f)`** when
  `J' = f^* J`, for ANY analytic map `f` between standard-model manifolds (two models allowed) —
  the generalisation of `padSliceHom` (`PadIdeal.lean`), with `restrictedIdealHom` its instance at
  an open inclusion; on points it is `f` (`toFun_homOfPullbackEq_val`), it lies over
  `Sp(f)` (`homOfPullbackEq_comp_toAnalyticSpaceι`), and along a DIFFEOMORPHISM it is an
  isomorphism (`isIso_homOfPullbackEq_of_diffeomorph`: the base map is a homeomorphism of
  cosupports and the fibre maps are bijective, the mechanism of `isIso_padSliceHom` — Mathlib's
  `LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` and `to_iso`).
* `isIso_homOfPullbackEq_inclusionMap`: the weak commutation with closed embeddings,
  `j^* B(X, I_X) = B(Y, I_Y)` [Kol07, 34.4], read on the closed subspaces — along a closed embedding
  `S ↪ M` with `𝓘_S ≤ J`, the closed subspace of `S` cut out by `J|_S` IS the closed subspace of
  `M` cut out by `J`: the cosupport of `J` lies in `S`, and the stalk maps are onto with kernel
  `𝓘_{S,p} ≤ J_p` (`bijective_fiberMap_homOfPullbackEq_inclusionMap`). Used at the last stage of
  the push-forward chain of a padded embedding.
* `PieceEmbedding.embInv`: the inverse `Sp(G)/𝓘_Y ≅ X|V` of a piece embedding, named
  (`localResolutionToPiece` inlines it, `localResolutionToPiece_eq`).
* `QuotientSpace.compat_comp`, `KLocallyRingedSpace.quotientMap_comp`: the functoriality of the
  germ quotient is functorial (`Hom.ext_of_comp_quotientι`, `quotientMap_comp_quotientι`).
* `AnalyticSpace.exists_restrictSet_isIso_of_comp_eq`: an isomorphism over `Z` restricts, for every
  `N ⊆ Z`, to an isomorphism of the restrictions (`restrictSet`, `Hom.restrictSet`) over `N`,
  compatible with the restricted projections: `isoOfRangeEq` of the two open immersions
  into `B` (the ranges agree because an isomorphism is a homeomorphism, in both branches of the
  `openOf` convention), and the composite by the uniqueness of lifts through the open immersion
  `Z|N → Z` (`Hom.ext_of_comp_ofRestrict`). The conclusion is the shape in which the independence
  of the local resolution is stated (`localResolution_independent_local`).

Closed subspaces and restrictions of analytic spaces are those of [Hir64, Ch. 0, §1, pp. 119–120].
Not in the sources; bookkeeping on `quotientMap`, `ofManifoldHom` and `restrictSet`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set CategoryTheory
open scoped Manifold ContDiff Topology

universe u

/-! ### Functoriality of the germ-family quotient -/

namespace AnalyticSpace

namespace QuotientSpace

variable {X'' X' X : AlgebraicGeometry.LocallyRingedSpace.{u}} (φ' : X'' ⟶ X') (φ : X' ⟶ X)
  (J'' : Manifold.IdealSheaf X''.𝒪) (J' : Manifold.IdealSheaf X'.𝒪)
  (J : Manifold.IdealSheaf X.𝒪)

/-- Compatibility composes: if `φ'` carries `𝒥'` into `𝒥''` and `φ` carries `𝒥` into `𝒥'`, the
composite carries `𝒥` into `𝒥''` (the stalk map of a composite is the composite of the stalk
maps). -/
theorem compat_comp (h' : Compat φ' J'' J') (h : Compat φ J' J) : Compat (φ' ≫ φ) J'' J := by
  intro z
  rw [← stalkIdeal_comap (φ' ≫ φ) J z, comap_comp, stalkIdeal_comap]
  exact (Ideal.map_mono ((stalkIdeal_comap φ J (φ'.base z)).le.trans (h (φ'.base z)))).trans
    (h' z)

end QuotientSpace

end AnalyticSpace

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {X'' X' X : KLocallyRingedSpace.{u} K} (ψ' : X'' ⟶ X') (ψ : X' ⟶ X)
  (J'' : Manifold.IdealSheaf X''.toLocallyRingedSpace.𝒪)
  (J' : Manifold.IdealSheaf X'.toLocallyRingedSpace.𝒪)
  (J : Manifold.IdealSheaf X.toLocallyRingedSpace.𝒪)

/-- The functoriality of the closed subspace is functorial: the induced morphisms compose
(`Hom.ext_of_comp_quotientι` and `quotientMap_comp_quotientι`). -/
theorem quotientMap_comp (h' : QuotientSpace.Compat ψ'.1 J'' J') (h : QuotientSpace.Compat ψ.1 J' J)
    (h'' : QuotientSpace.Compat (ψ' ≫ ψ).1 J'' J) :
    quotientMap ψ' J'' J' h' ≫ quotientMap ψ J' J h = quotientMap (ψ' ≫ ψ) J'' J h'' := by
  apply Hom.ext_of_comp_quotientι
  rw [Category.assoc, quotientMap_comp_quotientι ψ J' J h, ← Category.assoc,
    quotientMap_comp_quotientι ψ' J'' J' h', Category.assoc,
    quotientMap_comp_quotientι (ψ' ≫ ψ) J'' J h'']

end AnalyticSpace.KLocallyRingedSpace

namespace Hironaka.Manifold

open _root_.Manifold

open AnalyticSpace KLocallyRingedSpace

/-! ### The closed subspace along an analytic map with `J' = f^* J` -/

section HomOfPullback

variable {𝕜 : Type} [RCLike 𝕜]

variable {k n : ℕ} {A : AnalyticManifold.{u} 𝕜 (Fin k → 𝕜)}
  {A' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (f : A' → A)
  (hf : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω f)
  {J' : AnalyticManifold.IdealSheaf A'} {J : AnalyticManifold.IdealSheaf A}

/-- On points the morphism of closed subspaces is `f`. -/
theorem toFun_homOfPullbackEq_val (h : J' = J.pullback f hf) (z : J'.toAnalyticSpace) :
    (IdealSheaf.homOfPullbackEq f hf h z).1 = f z.1 :=
  rfl

/-- The morphism of closed subspaces lies over `Sp(f)`: `ι_J ∘ homOfPullbackEq = Sp(f) ∘ ι_{J'}`
(`quotientMap_comp_quotientι`). -/
theorem homOfPullbackEq_comp_toAnalyticSpaceι (h : J' = J.pullback f hf) :
    IdealSheaf.homOfPullbackEq f hf h ≫ J.toAnalyticSpaceι =
      J'.toAnalyticSpaceι ≫ (show
          (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A' ⟶ toSpace
          (ContinuousLinearEquiv.refl 𝕜 (Fin k → 𝕜)) A) from ofManifoldHom f hf) :=
  quotientMap_comp_quotientι (ofManifoldHom f hf) J' J (compat_ofManifoldHom_of_eq f hf h)

/-- The stalk map of `Sp(f)` is the germ map (`stalkMap_ofManifoldHom_eq_germMap`, bundled). -/
theorem stalkMap_ofManifoldHom_hom (x : A') :
    ((ofManifoldHom f hf).1.stalkMap x).hom = germMap f hf x :=
  RingHom.ext (stalkMap_ofManifoldHom_eq_germMap f hf x)

/-- The cosupport of a pull-back along a map whose germ maps are bijective is the preimage of the
cosupport (`Ideal.comap_map_of_bijective`). -/
theorem cosupport_pullback_of_bijective (hbij : ∀ z, Function.Bijective (germMap f hf z)) :
    (J.pullback f hf).support = f ⁻¹' J.support := by
  ext z
  change (J.pullback f hf).stalkIdeal z ≠ ⊤ ↔ J.stalkIdeal (f z) ≠ ⊤
  rw [IdealSheaf.stalkIdeal_pullback]
  refine not_congr ⟨fun ht => ?_, fun ht => by rw [ht, Ideal.map_top]⟩
  have e := Ideal.comap_map_of_bijective _ (hbij z) (I := J.stalkIdeal (f z))
  rw [ht, Ideal.comap_top] at e
  exact e.symm

/-- Along a diffeomorphism (any two standard models) the morphism of closed subspaces is an
isomorphism: the base map is the homeomorphism of cosupports induced by `g`, the fibre maps are
bijective because the germ maps of `g` are ring isomorphisms (`germMap_bijective_of_diffeomorph`),
so it is an open immersion onto the whole target (the mechanism of `isIso_padSliceHom`). -/
theorem isIso_homOfPullbackEq_of_diffeomorph
    (g : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin k → 𝕜) A' A ω)
    (h : J' = J.pullback ⇑g g.contMDiff) :
    IsIso (IdealSheaf.homOfPullbackEq ⇑g g.contMDiff h) := by
  subst h
  have hsurj : Function.Surjective ⇑g := fun y => ⟨g.symm y, g.apply_symm_apply y⟩
  have hval : IsIso (IdealSheaf.homOfPullbackEq (J := J) (J' := J.pullback ⇑g g.contMDiff) ⇑g
      g.contMDiff rfl).1 := by
    change IsIso (QuotientSpace.map (ofManifoldHom ⇑g g.contMDiff).1 (J.pullback ⇑g g.contMDiff) J
      (compat_ofManifoldHom_of_eq ⇑g g.contMDiff rfl))
    set F := QuotientSpace.map (ofManifoldHom ⇑g g.contMDiff).1 (J.pullback ⇑g g.contMDiff) J
      (compat_ofManifoldHom_of_eq ⇑g g.contMDiff rfl) with hF
    -- the base map is the homeomorphism of cosupports induced by `g`
    let e : (J.pullback ⇑g g.contMDiff).support ≃ₜ J.support :=
      (g.toHomeomorph.image _).trans (Homeomorph.setCongr (by
        rw [Diffeomorph.coe_toHomeomorph,
          cosupport_pullback_of_bijective _ _ (fun z => germMap_bijective_of_diffeomorph g z),
          Set.image_preimage_eq _ hsurj]))
    have hbase : (F.base : (J.pullback ⇑g g.contMDiff).support → J.support) = e :=
      funext fun _ => Subtype.ext rfl
    have hemb : Topology.IsOpenEmbedding (F.base : (J.pullback ⇑g g.contMDiff).support →
        J.support) := hbase ▸ e.isOpenEmbedding
    have : ∀ z, IsIso (F.stalkMap z) := fun z => by
      refine QuotientSpace.isIso_map_stalkMap_of_bijective _ _ _ _ z ?_
      obtain ⟨hinj, hsurj'⟩ := germMap_bijective_of_diffeomorph g z.1
      refine ⟨Ideal.quotientMap_injective' ?_, Ideal.quotientMap_surjective ?_⟩
      · change (IdealSheaf.stalkIdeal _ z.1).comap ((ofManifoldHom ⇑g g.contMDiff).1.stalkMap
          z.1).hom ≤ _
        rw [stalkMap_ofManifoldHom_hom, IdealSheaf.stalkIdeal_pullback]
        exact (Ideal.comap_map_of_bijective _ ⟨hinj, hsurj'⟩).le
      · rw [stalkMap_ofManifoldHom_hom]
        exact hsurj'
    have : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion F :=
      AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso F hemb
    have : Epi F.base := (TopCat.epi_iff_surjective F.base).mpr (hbase ▸ e.surjective)
    exact AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso F
  exact AnalyticSpace.isIso_of_isIso_toKLocallyRingedSpace _ (isIso_of_isIso_val _)

end HomOfPullback

/-! ### The closed subspace along a closed embedding -/

section ClosedEmbedding

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S s)

/-- The kernel of the germ map of the inclusion of a closed submanifold at `p` is the stalk of
`𝓘_S` at `p` (`restrictStalk`, `stalkIdeal_idealSheaf_of_mem`). -/
theorem ker_germMap_inclusionMap (p : hS.toAnalyticManifold) :
    RingHom.ker (germMap ⇑hS.inclusionMap hS.inclusionMap.contMDiff p) =
      hS.idealSheaf.stalkIdeal (hS.inclusionMap p) := by
  rw [hS.stalkIdeal_idealSheaf_of_mem (a := hS.inclusionMap p) (p : S).2]
  exact congrArg RingHom.ker (RingHom.ext (hS.germMap_inclusionMap_eq_restrictStalk p))

/-- With `𝓘_S ≤ J`, the cosupport of `J` lies in `S` (off `S` the stalk of `𝓘_S` is the unit
ideal). -/
theorem cosupport_subset_of_idealSheaf_le {J : AnalyticManifold.IdealSheaf M}
    (hle : hS.idealSheaf ≤ J) :
    J.support ⊆ S := fun x hx => by
  by_contra hxS
  exact hx (top_le_iff.mp ((hS.stalkIdeal_idealSheaf_of_notMem hxS).symm.le.trans
    (IdealSheaf.le_def.mp hle x)))

/-- With `𝓘_S ≤ J`, the cosupport of `J|_S` is the preimage of the cosupport of `J` (the germ maps
of the inclusion are onto with kernel `𝓘_{S,p} ≤ J_p`). -/
theorem cosupport_pullback_inclusionMap {J : AnalyticManifold.IdealSheaf M}
    (hle : hS.idealSheaf ≤ J) :
    (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).support =
      ⇑hS.inclusionMap ⁻¹' J.support := by
  ext p
  change (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).stalkIdeal p ≠ ⊤ ↔
    J.stalkIdeal (hS.inclusionMap p) ≠ ⊤
  rw [IdealSheaf.stalkIdeal_pullback]
  refine not_congr ⟨fun ht => ?_, fun ht => by rw [ht, Ideal.map_top]⟩
  have h1 := Ideal.comap_map_of_surjective _ (hS.germMap_inclusionMap_surjective p)
    (J.stalkIdeal (hS.inclusionMap p))
  rw [ht, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, ker_germMap_inclusionMap,
    sup_eq_left.mpr (IdealSheaf.le_def.mp hle _)] at h1
  exact h1.symm

/-- With `𝓘_S ≤ J`, the fibre maps of the closed-subspace morphism along the inclusion are
bijective: the germ maps of the inclusion are onto with kernel `𝓘_{S,p} ≤ J_p`. -/
theorem bijective_fiberMap_homOfPullbackEq_inclusionMap {J : AnalyticManifold.IdealSheaf M}
    (hle : hS.idealSheaf ≤ J)
    (z : QuotientSpace.support
      (ofManifold 𝕜 (Fin (n - s) → 𝕜) hS.toAnalyticManifold).toLocallyRingedSpace
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)) :
    Function.Bijective (QuotientSpace.fiberMap (ofManifoldHom ⇑hS.inclusionMap
      hS.inclusionMap.contMDiff).1 (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) J
      (compat_ofManifoldHom_of_eq ⇑hS.inclusionMap hS.inclusionMap.contMDiff rfl) z) := by
  have hsurj := hS.germMap_inclusionMap_surjective z.1
  refine ⟨Ideal.quotientMap_injective' ?_, Ideal.quotientMap_surjective ?_⟩
  · change (IdealSheaf.stalkIdeal _ z.1).comap ((ofManifoldHom ⇑hS.inclusionMap
      hS.inclusionMap.contMDiff).1.stalkMap z.1).hom ≤ _
    rw [stalkMap_ofManifoldHom_hom, IdealSheaf.stalkIdeal_pullback]
    refine le_trans (Ideal.comap_map_of_surjective _ hsurj _).le ?_
    rw [← RingHom.ker_eq_comap_bot, ker_germMap_inclusionMap]
    exact sup_le le_rfl (IdealSheaf.le_def.mp hle _)
  · rw [stalkMap_ofManifoldHom_hom]
    exact hsurj

/-- **Along a closed embedding `S ↪ M` with `𝓘_S ≤ J`, the closed subspace of `S` cut out by
`J|_S` is the closed subspace of `M` cut out by `J`**: the morphism of closed subspaces over
`Sp(S ↪ M)` is an isomorphism (the cosupport of `J` lies in `S`, the fibre maps are bijective). The
weak commutation with closed embeddings `j^* B(X, I_X) = B(Y, I_Y)` [Kol07, 34.4], read on the
subspaces; used at the last stage of the push-forward chain of a padded embedding
(`idealSheaf_range_pushforwardIncl_le_strictTransformSubspaceSeq`). -/
theorem isIso_homOfPullbackEq_inclusionMap {J : AnalyticManifold.IdealSheaf M}
    (hle : hS.idealSheaf ≤ J)
    {J_S : AnalyticManifold.IdealSheaf hS.toAnalyticManifold}
    (h : J_S = J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) :
    IsIso (IdealSheaf.homOfPullbackEq ⇑hS.inclusionMap hS.inclusionMap.contMDiff h) := by
  subst h
  have hcos := cosupport_pullback_inclusionMap hS hle
  have hJS := cosupport_subset_of_idealSheaf_le hS hle
  have hval : IsIso (IdealSheaf.homOfPullbackEq (J := J)
      (J' := J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) ⇑hS.inclusionMap
      hS.inclusionMap.contMDiff rfl).1 := by
    change IsIso (QuotientSpace.map (ofManifoldHom ⇑hS.inclusionMap hS.inclusionMap.contMDiff).1
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) J
      (compat_ofManifoldHom_of_eq ⇑hS.inclusionMap hS.inclusionMap.contMDiff rfl))
    set F := QuotientSpace.map (ofManifoldHom ⇑hS.inclusionMap hS.inclusionMap.contMDiff).1
      (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) J
      (compat_ofManifoldHom_of_eq ⇑hS.inclusionMap hS.inclusionMap.contMDiff rfl) with hF
    -- the base map is a homeomorphism: the cosupport of `J` lies in `S`
    let e : (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).support ≃ₜ J.support :=
      { toFun := fun z => ⟨hS.inclusionMap z.1, (Set.ext_iff.mp hcos z.1).mp z.2⟩
        invFun := fun x => ⟨⟨x.1, hJS x.2⟩, (Set.ext_iff.mp hcos _).mpr x.2⟩
        left_inv := fun z => Subtype.ext (Subtype.ext rfl)
        right_inv := fun x => Subtype.ext rfl
        continuous_toFun :=
          (hS.inclusionMap.contMDiff.continuous.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
    have hbase : (F.base : (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).support →
        J.support) = e := funext fun _ => Subtype.ext rfl
    have hemb : Topology.IsOpenEmbedding (F.base :
        (J.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).support → J.support) :=
      hbase ▸ e.isOpenEmbedding
    have : ∀ z, IsIso (F.stalkMap z) := fun z =>
      QuotientSpace.isIso_map_stalkMap_of_bijective _ _ _ _ z
        (bijective_fiberMap_homOfPullbackEq_inclusionMap hS hle z)
    have : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion F :=
      AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso F hemb
    have : Epi F.base := (TopCat.epi_iff_surjective F.base).mpr (hbase ▸ e.surjective)
    exact AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso F
  exact AnalyticSpace.isIso_of_isIso_toKLocallyRingedSpace _ (isIso_of_isIso_val _)

end ClosedEmbedding

/-! ### The inverse of a piece embedding, named -/

section EmbInv

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- The inverse `Sp(G)/𝓘_Y ≅ X|V` of the piece embedding, named (`localResolutionToPiece` inlines
it as `inv E.emb`). -/
def PieceEmbedding.embInv :
    E.ideal.toAnalyticSpace ⟶ X.restrictSet V :=
  have : IsIso E.emb := E.emb_isIso
  inv E.emb

/-- `embInv ∘ emb = id`. -/
theorem PieceEmbedding.embInv_comp_emb : E.emb ≫ E.embInv = 𝟙 _ := by
  have : IsIso E.emb := E.emb_isIso
  exact IsIso.hom_inv_id E.emb

/-- `emb ∘ embInv = id`. -/
theorem PieceEmbedding.emb_comp_embInv : E.embInv ≫ E.emb = 𝟙 _ := by
  have : IsIso E.emb := E.emb_isIso
  exact IsIso.inv_hom_id E.emb

/-- The local resolution map over the piece, through `embInv` (definitional). -/
theorem PieceEmbedding.localResolutionToPiece_eq (bed : BEDanFamStar.{u} 𝕜)
    (W : Opens (pieceAmbient.{u} 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) :
    E.localResolutionToPiece bed W hW =
      (E.localResolutionMap bed W hW ≫ E.restrictedIdealHom W) ≫ E.embInv :=
  rfl

end EmbInv

end Hironaka.Manifold

/-! ### Restriction of an isomorphism over a map to the preimages of a set -/

namespace AnalyticSpace

open KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The restriction of a morphism lies over it (`Hom.restrictSet` is the lift through the open
immersion, `IsOpenImmersion.lift_fac`). -/
theorem Hom.restrictSet_comp_ofRestrict {X Y : AnalyticSpace.{u} K} (f : X ⟶ Y) (V : Set Y) :
    Hom.restrictSet f V ≫ KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y V) =
      KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace
        (openOf X (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) ≫ f := by
  have h₁ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (KLocallyRingedSpace.ofRestrict Y.toKLocallyRingedSpace (openOf Y V)).1 := inferInstance
  exact KLocallyRingedSpace.Hom.ext
    (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁) _ _
      (range_toFun_ofRestrict_comp_subset f V))

namespace KLocallyRingedSpace

/-- An isomorphism `ψ : A ≅ B` over `Z` restricts to an isomorphism of the open restrictions of
the convention `openOf`, compatible with the restricted projections (the `K`-level form):
`isoOfRangeEq` of the two open immersions into `B`, whose ranges agree because `ψ` is a
homeomorphism (so `Π_A⁻¹N` is open iff `Π_B⁻¹N` is, and the `openOf` branches agree), and the
uniqueness of lifts through `Z|N → Z`. -/
theorem exists_restrictSet_isIso_of_comp_eq {A B Z : AnalyticSpace.{u} K}
    (ψ : A.toKLocallyRingedSpace ⟶ B.toKLocallyRingedSpace) [IsIso ψ]
    (pA : A.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace)
    (pB : B.toKLocallyRingedSpace ⟶ Z.toKLocallyRingedSpace) (h : ψ ≫ pB = pA) (N : Set Z) :
    ∃ ψ' : A.toKLocallyRingedSpace.restrictOpen
          (openOf A (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N)) ⟶
        B.toKLocallyRingedSpace.restrictOpen (openOf B (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N)),
      IsIso ψ' ∧ ψ' ≫ Hom.restrictSet pB N = Hom.restrictSet pA N := by
  have hψ1 : IsIso ψ.1 := (isIso_iff_isIso_val ψ).mp inferInstance
  -- the preimages of `N` correspond under `ψ`
  have hpre : KLocallyRingedSpace.Hom.toFun pA ⁻¹' N =
      KLocallyRingedSpace.Hom.toFun ψ ⁻¹' (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N) := by
    rw [← h]; rfl
  have hsurj : Function.Surjective (KLocallyRingedSpace.Hom.toFun ψ) :=
    (KIso.homeomorph (asIso ψ)).surjective
  have hopen : IsOpen (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N) ↔
      IsOpen (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N) := by
    rw [hpre]
    exact (KIso.homeomorph (asIso ψ)).isOpen_preimage
  -- the two opens of the convention correspond as sets
  set UA : Opens A.toKLocallyRingedSpace := openOf A (KLocallyRingedSpace.Hom.toFun pA ⁻¹' N)
    with hUA
  set UB : Opens B.toKLocallyRingedSpace := openOf B (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N)
    with hUB
  have hsets : SetLike.coe UA = KLocallyRingedSpace.Hom.toFun ψ ⁻¹' SetLike.coe UB := by
    rw [hUA, hUB]
    by_cases hN : IsOpen (KLocallyRingedSpace.Hom.toFun pB ⁻¹' N)
    · rw [openOf_of_isOpen _ hN, openOf_of_isOpen _ (hopen.mpr hN)]
      exact hpre
    · rw [openOf_of_not_isOpen _ hN, openOf_of_not_isOpen _ (mt hopen.mp hN)]
      simp
  -- the two open immersions into `B` with the same range
  have ha : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict A.toKLocallyRingedSpace UA ≫ ψ).1 := by
    rw [KLocallyRingedSpace.Hom.comp_val]
    infer_instance
  have hb : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict B.toKLocallyRingedSpace UB).1 := inferInstance
  have hrange : Set.range (KLocallyRingedSpace.Hom.toFun
        (ofRestrict A.toKLocallyRingedSpace UA ≫ ψ)) =
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict B.toKLocallyRingedSpace UB)) := by
    rw [KLocallyRingedSpace.Hom.range_toFun_comp, range_toFun_ofRestrict, range_toFun_ofRestrict,
      hsets, Set.image_preimage_eq _ hsurj]
  refine ⟨(isoOfRangeEq _ _ hrange).hom, inferInstance, ?_⟩
  -- the compatibility: both sides are the lift of `A|_{Π_A⁻¹N} → A → Z` through `Z|_N → Z`
  have hZ : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1 := inferInstance
  apply KLocallyRingedSpace.Hom.ext
  refine AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq (H := hZ)
    (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1
    (ofRestrict A.toKLocallyRingedSpace UA ≫ pA).1
    (range_toFun_ofRestrict_comp_subset pA N) _ ?_
  have hB : (Hom.restrictSet pB N).1 ≫ (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1 =
      (ofRestrict B.toKLocallyRingedSpace UB ≫ pB).1 :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac (H := hZ) _ _
      (range_toFun_ofRestrict_comp_subset pB N)
  have hE : (isoOfRangeEq _ _ hrange).hom.1 ≫ (ofRestrict B.toKLocallyRingedSpace UB).1 =
      (ofRestrict A.toKLocallyRingedSpace UA ≫ ψ).1 :=
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (le_of_eq hrange)
  calc ((isoOfRangeEq _ _ hrange).hom ≫ Hom.restrictSet pB N).1 ≫
        (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1
      = (isoOfRangeEq _ _ hrange).hom.1 ≫ ((Hom.restrictSet pB N).1 ≫
          (ofRestrict Z.toKLocallyRingedSpace (openOf Z N)).1) := Category.assoc _ _ _
    _ = (isoOfRangeEq _ _ hrange).hom.1 ≫ (ofRestrict B.toKLocallyRingedSpace UB ≫ pB).1 :=
          congrArg _ hB
    _ = ((isoOfRangeEq _ _ hrange).hom.1 ≫ (ofRestrict B.toKLocallyRingedSpace UB).1) ≫ pB.1 :=
          (Category.assoc _ _ _).symm
    _ = (ofRestrict A.toKLocallyRingedSpace UA ≫ ψ).1 ≫ pB.1 := congrArg (· ≫ pB.1) hE
    _ = (ofRestrict A.toKLocallyRingedSpace UA).1 ≫ (ψ ≫ pB).1 := Category.assoc _ _ _
    _ = (ofRestrict A.toKLocallyRingedSpace UA ≫ pA).1 := by
          rw [h, KLocallyRingedSpace.Hom.comp_val]

end KLocallyRingedSpace

/-- An isomorphism `ψ : A ≅ B` over `Z` (`Π_B ∘ ψ = Π_A`) restricts, for every `N ⊆ Z`, to an
isomorphism of the restrictions (`restrictSet`, `Hom.restrictSet`) over `N`, compatible with the
restricted projections — the shape in which the independence of the local resolution is stated
(`localResolution_independent_local`); the `K`-level content is
`KLocallyRingedSpace.exists_restrictSet_isIso_of_comp_eq`. -/
theorem exists_restrictSet_isIso_of_comp_eq {A B Z : AnalyticSpace.{u} K} (ψ : A ⟶ B)
    (hψ : IsIso ψ) (pA : A ⟶ Z) (pB : B ⟶ Z) (h : ψ ≫ pB = pA) (N : Set Z) :
    ∃ ψ' : A.restrictSet (pA ⁻¹' N) ⟶ B.restrictSet (pB ⁻¹' N),
      IsIso ψ' ∧ ψ' ≫ pB.restrictSet N = pA.restrictSet N := by
  have hψA : @IsIso (AnalyticSpace.{u} K) _ A B ψ := hψ
  have hψK : @IsIso (AnalyticSpace.KLocallyRingedSpace.{u} K) _
      (AnalyticSpace.toKLocallyRingedSpace A)
      (AnalyticSpace.toKLocallyRingedSpace B) ψ :=
    ⟨⟨(inv ψ : B ⟶ A), IsIso.hom_inv_id ψ, IsIso.inv_hom_id ψ⟩⟩
  obtain ⟨ψ', hiso, hc⟩ :=
    KLocallyRingedSpace.exists_restrictSet_isIso_of_comp_eq ψ pA pB h N
  exact ⟨ψ', AnalyticSpace.isIso_of_isIso_toKLocallyRingedSpace _ hiso, hc⟩

end AnalyticSpace

end
