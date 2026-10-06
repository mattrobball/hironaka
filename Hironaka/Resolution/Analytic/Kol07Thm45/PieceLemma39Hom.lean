/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Shear
public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
public import Hironaka.Resolution.Analytic.Kol07Thm45.PadSliceDiffeomorph
import Hironaka.AnalyticSpace.ChartLift
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.AnalyticSpace.MonoidalUnique
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lemma 39 at the morphism level: the padded embeddings are equivalent as closed subspaces

Kollár's Lemma 39 says that two closed embeddings `i₁ : Y → G₁ ⊆ 𝕜ⁿ`, `i₂ : Y → G₂ ⊆ 𝕜ᵐ` of one
piece `Y = X|V` become "equivalent under a (nonlinear) automorphism" after padding to `𝕜^{n+m}`
[Kol07, Lemma 39]. `PieceLemma39Shear.lean` proves this on POINTS and IDEALS: the shear `Ψ` of the
two local lifts carries the left-padded embedded points to the right-padded ones and pulls the
right-padded ideal back to the left-padded one. The comparison of the local resolutions of a piece
for two embeddings [Kol07, Theorem 36, proof] needs the statement as an identity of MORPHISMS: the
isomorphism of closed subspaces `Sp(W₁)/𝓘₁|W₁ ≅ Sp(W₂)/𝓘₂|W₂` induced by the shear (the
functoriality of the closed subspace along `Sp(Ψ)`, `ClosedSubspaceHom.lean`'s `homOfPullbackEq`),
read down to `X|V` through the two paddings, is the identity of the piece. The point clause alone
does not determine the stalk maps: over `ℝ`, the ideal `(x² + y²)` on `𝕜²` admits the automorphism
`y ↦ −y` of the padded ambient fixing the embedded points. This module proves that identity,
`exists_padded_equivalence_hom`.

The mathematics is that of the shear module: the padded stalk maps of the two embeddings agree
through the shear (`padStalkMap_eq_comp_germMapOn_shear`), and a morphism into `Sp(M)` is
determined by its action on coordinate germs (`hom_ext_of_coord_chart`,
`Hironaka/AnalyticSpace/MonoidalUnique.lean`). The argument:

* **the padding links** — `padSliceIso_inv_eq_homOfPullbackEq` (the inverse of the slice
  isomorphism `padSliceIso` of `PadIdeal.lean` is the closed-subspace morphism over the zero
  extension `s`, a right inverse of `padSliceHom` because `p ∘ s = id`),
  `PieceEmbedding.toAnalyticSpaceι_comp_padAlong_emb` (the padded ambient embedding lies over `s`),
  `toAnalyticSpaceι_comp_restrictedIdealHom` (the restriction-of-a-quotient map
  `restrictedIdealHom` of `PieceIndependence.lean`, the closed-subspace morphism over the open
  inclusion, lies over it);
* **the points** — `PieceEmbedding.exists_ambientPoint_eq_of_stalkIdeal_ne_top` (the cosupport of
  the ideal is the set of embedded points), `toFun_embInv_restrictedIdealHom` (the read-down map
  `emb⁻¹ ∘ restrictedIdealHom W` on points), `ambient_comp_embInv_restrictedIdealHom` (the read-down
  map followed by the ambient embedding is the inclusion of the closed subspace);
* **the core** — `padded_equivalence_hom_aux` and `padded_equivalence_hom_of_stalkMap`: for ANY
  local isomorphism `Ψ` of the padded ambients restricting to a diffeomorphism `W₁ ≃ W₂` that
  carries the embedded points and interchanges the padded stalk maps, the morphism identity; the
  proof cancels the isomorphism `emb₂` and the closed-subspace inclusion `toAnalyticSpaceι`
  (`Hom.ext_of_comp_quotientι`), then compares two morphisms `Sp(W₁)/𝓘₁|W₁ ⟶ Sp(padOpens₂)` on
  coordinate germs: at a point over
  the embedded point `s₁(i₁ y)` the germs pull back equally by the stalk identity, the two composite
  stalk maps being identified as MORPHISM identities (`stalkMap_germ_congr` transporting the germ
  of the section `u_j ∘ Ψ`, no dependent rewrite);
* **the assembly** — `padded_equivalence_hom_of_shear` (the core at the shear of the two lifts) and
  `exists_padded_equivalence_hom`: the witnesses of `embeddings_equivalent_under_automorphism_pad`,
  the ideal identity `pullback_padIdeal_inclusion_eq_of_shear` (the shear module's extracted fourth
  clause) and the morphism identity.

Not in the sources beyond Lemma 39; bookkeeping over the shear module. The theorem itself has no
user in the library: `exists_padded_equivalence_hom_point` (`LocalResolutionShear.lean`) repeats
its construction with the point clause of `embeddings_equivalent_under_automorphism_pad` added, on
the same witnesses, and that form is what `LocalResolutionShear.lean` and
`CoproductMixedTransition.lean` use; the core `padded_equivalence_hom_of_shear` is shared by both.
-/

public section

noncomputable section

open TopologicalSpace Set CategoryTheory AlgebraicGeometry Opposite Filter
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

open AnalyticSpace KLocallyRingedSpace

variable {𝕜 : Type} [RCLike 𝕜]

/-! ### The padding links -/

local notation:80 g:81 " ⊚ " f:80 => CategoryTheory.CategoryStruct.comp (obj := AnalyticSpace _) f g

section PaddingLinks

variable {n n' : ℕ} (σ : Fin n ↪ Fin n') {G : Opens (Fin n → 𝕜)}
  (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- **The inverse of the slice isomorphism `padSliceIso` is the closed-subspace morphism over the
zero extension** `s = padExt` (`homOfPullbackEq` at `s`, with `s^*(p^*J + 𝓘_S) = J`,
`pullback_padExt_padIdeal`): it is a right inverse of `padSliceHom` because `p ∘ s = id`
(`padCoordProj_padExt`, `ofManifoldHom_comp`, `Hom.ext_of_comp_quotientι`), and a right inverse of
an isomorphism is its inverse (`IsIso.eq_inv_of_inv_hom_id`). -/
theorem padSliceIso_inv_eq_homOfPullbackEq :
    (padSliceIso σ J).inv =
      IdealSheaf.homOfPullbackEq (J' := J) (J := padIdeal σ J) (padExt σ G) (contMDiff_padExt σ G)
        (pullback_padExt_padIdeal σ G J).symm := by
  have hiso : IsIso (padSliceHom σ J) := isIso_padSliceHom σ J
  change @inv (AnalyticSpace.{u} 𝕜) _ _ _ (padSliceHom σ J) hiso = _
  symm
  refine @IsIso.eq_inv_of_inv_hom_id (AnalyticSpace.{u} 𝕜) _ _ _
    (padSliceHom σ J) hiso _ ?_
  -- the composite `homOfPullbackEq padExt ≫ padSliceHom` is the identity of `Sp(G)/J`
  let Sp_p : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
      (pieceAmbient.{u} 𝕜 (padOpens σ G)) ⟶ toSpace (ContinuousLinearEquiv.refl 𝕜
      (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 G)) :=
    ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G)
  let Sp_s : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 G) ⟶ toSpace
      (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) (pieceAmbient.{u} 𝕜 (padOpens σ G))) :=
    ofManifoldHom (padExt σ G) (contMDiff_padExt σ G)
  let h := IdealSheaf.homOfPullbackEq (J' := J) (J := padIdeal σ J) (padExt σ G)
    (contMDiff_padExt σ G) (pullback_padExt_padIdeal σ G J).symm
  have s1 : J.toAnalyticSpaceι ⊚ padSliceHom σ J = Sp_p ⊚ (padIdeal σ J).toAnalyticSpaceι :=
    quotientMap_comp_quotientι _ _ _ _
  have s2 : (padIdeal σ J).toAnalyticSpaceι ⊚ h = Sp_s ⊚ J.toAnalyticSpaceι :=
    homOfPullbackEq_comp_toAnalyticSpaceι (J' := J) (J := padIdeal σ J) (padExt σ G)
      (contMDiff_padExt σ G) (pullback_padExt_padIdeal σ G J).symm
  have hid : padCoordProj σ G ∘ padExt σ G = id := funext (padCoordProj_padExt σ G)
  have key : ∀ (f : pieceAmbient.{u} 𝕜 G → pieceAmbient.{u} 𝕜 G)
      (hf : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f), f = id →
      ofManifoldHom f hf = 𝟙 (ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G)) := by
    rintro f hf rfl
    rfl
  have s3 : Sp_p ⊚ Sp_s = 𝟙 _ :=
    (ofManifoldHom_comp _ _ _ _).symm.trans (key _ _ hid)
  refine Hom.ext_of_comp_quotientι (X := ofManifold 𝕜 (Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G)) J ?_
  change J.toAnalyticSpaceι ⊚ (padSliceHom σ J ⊚ h) =
    J.toAnalyticSpaceι ⊚ 𝟙 _
  calc J.toAnalyticSpaceι ⊚ (padSliceHom σ J ⊚ h)
      = (J.toAnalyticSpaceι ⊚ padSliceHom σ J) ⊚ h := Category.assoc _ _ _
    _ = (Sp_p ⊚ (padIdeal σ J).toAnalyticSpaceι) ⊚ h := congrArg (fun k => k ⊚ h) s1
    _ = Sp_p ⊚ ((padIdeal σ J).toAnalyticSpaceι ⊚ h) := (Category.assoc _ _ _).symm
    _ = Sp_p ⊚ (Sp_s ⊚ J.toAnalyticSpaceι) := congrArg (fun k => Sp_p ⊚ k) s2
    _ = (Sp_p ⊚ Sp_s) ⊚ J.toAnalyticSpaceι := Category.assoc _ _ _
    _ = 𝟙 _ ⊚ J.toAnalyticSpaceι :=
        congrArg (fun k => k ⊚ J.toAnalyticSpaceι) s3
    _ = J.toAnalyticSpaceι := Category.comp_id _
    _ = J.toAnalyticSpaceι ⊚ 𝟙 _ :=
        (Category.id_comp _).symm

end PaddingLinks

namespace PieceEmbedding

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- **The padded ambient embedding lies over the zero extension** (the padding `𝕜ⁿ ⊂ 𝕜ⁿ⁺ᵐ` of
[Kol07, Theorem 36, proof]; compare [Wlo09, §7.1]): `ι' ∘ emb' = Sp(s) ∘ ι ∘ emb` for the padding
`E.padAlong σ` — its `emb` is `(padSliceIso σ 𝓘)⁻¹ ∘ emb`, so `padSliceIso_inv_eq_homOfPullbackEq`
and `homOfPullbackEq_comp_toAnalyticSpaceι`. -/
theorem toAnalyticSpaceι_comp_padAlong_emb {n' : ℕ} (σ : Fin n ↪ Fin n') :
    (E.padAlong σ).ideal.toAnalyticSpaceι ⊚ (E.padAlong σ).emb =
      (show toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 E.G) ⟶
          (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜))
          (pieceAmbient.{u} 𝕜 (padOpens σ E.G))) from
        ofManifoldHom (padExt σ E.G) (contMDiff_padExt σ E.G)) ⊚
      (E.ideal.toAnalyticSpaceι ⊚ E.emb) := by
  let Sp_s : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 E.G) ⟶ toSpace
      (ContinuousLinearEquiv.refl 𝕜 (Fin n' → 𝕜)) (pieceAmbient.{u} 𝕜 (padOpens σ E.G))) :=
    ofManifoldHom (padExt σ E.G) (contMDiff_padExt σ E.G)
  let h := IdealSheaf.homOfPullbackEq (J' := E.ideal) (J := padIdeal σ E.ideal) (padExt σ E.G)
    (contMDiff_padExt σ E.G) (pullback_padExt_padIdeal σ E.G E.ideal).symm
  have h1 : (padIdeal σ E.ideal).toAnalyticSpaceι ⊚ h = Sp_s ⊚ E.ideal.toAnalyticSpaceι :=
    homOfPullbackEq_comp_toAnalyticSpaceι (J' := E.ideal) (J := padIdeal σ E.ideal)
      (padExt σ E.G) (contMDiff_padExt σ E.G) (pullback_padExt_padIdeal σ E.G E.ideal).symm
  have h2 : (padSliceIso σ E.ideal).inv = h := padSliceIso_inv_eq_homOfPullbackEq σ E.ideal
  have s0 : (E.padAlong σ).ideal.toAnalyticSpaceι ⊚ (E.padAlong σ).emb =
      (padIdeal σ E.ideal).toAnalyticSpaceι ⊚ ((padSliceIso σ E.ideal).inv ⊚ E.emb) := rfl
  have s1 : (padIdeal σ E.ideal).toAnalyticSpaceι ⊚ ((padSliceIso σ E.ideal).inv ⊚ E.emb) =
      ((padIdeal σ E.ideal).toAnalyticSpaceι ⊚ (padSliceIso σ E.ideal).inv) ⊚ E.emb :=
    Category.assoc _ _ _
  have s2 : ((padIdeal σ E.ideal).toAnalyticSpaceι ⊚ (padSliceIso σ E.ideal).inv) ⊚ E.emb =
      ((padIdeal σ E.ideal).toAnalyticSpaceι ⊚ h) ⊚ E.emb :=
    congrArg (fun k : E.ideal.toAnalyticSpace ⟶ (padIdeal σ E.ideal).toAnalyticSpace =>
        ((padIdeal σ E.ideal).toAnalyticSpaceι ⊚ k) ⊚ E.emb) h2
  have s3 : ((padIdeal σ E.ideal).toAnalyticSpaceι ⊚ h) ⊚ E.emb =
      (Sp_s ⊚ E.ideal.toAnalyticSpaceι) ⊚ E.emb :=
    congrArg (fun k => k ⊚ E.emb) h1
  have s4 : (Sp_s ⊚ E.ideal.toAnalyticSpaceι) ⊚ E.emb = Sp_s ⊚ (E.ideal.toAnalyticSpaceι ⊚ E.emb) :=
    (Category.assoc _ _ _).symm
  exact s0.trans (s1.trans (s2.trans (s3.trans s4)))

/-- **The restriction-of-a-quotient map lies over the open inclusion**, as morphisms
`Sp(W)/𝓘|W ⟶ Sp(G)`: the morphism form of `toFun_toAnalyticSpaceι_restrictedIdealHom`
(`homOfPullbackEq_comp_toAnalyticSpaceι` at the open inclusion). -/
theorem toAnalyticSpaceι_comp_restrictedIdealHom (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    E.ideal.toAnalyticSpaceι ⊚ E.restrictedIdealHom W =
      (show (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          ((pieceAmbient.{u} 𝕜 E.G).restrict W)) ⟶ toSpace (ContinuousLinearEquiv.refl 𝕜
          (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ W)
          (AnalyticManifold.inclusion _ W).contMDiff) ⊚
      (E.restrictedIdeal W).toAnalyticSpaceι :=
  homOfPullbackEq_comp_toAnalyticSpaceι (J' := E.restrictedIdeal W) (J := E.ideal) _ _ rfl

/-- **The embedded points are the cosupport of the ideal**: a point of `G` with a proper stalk of
`𝓘_Y` is an ambient point `i(y)` — the contrapositive of `stalkIdeal_eq_top_of_forall_ne`. -/
theorem exists_ambientPoint_eq_of_stalkIdeal_ne_top (z : pieceAmbient.{u} 𝕜 E.G)
    (hz : E.ideal.stalkIdeal z ≠ ⊤) : ∃ y, E.ambientPoint y = z := by
  by_contra h
  exact hz (PieceEmbedding.stalkIdeal_eq_top_of_forall_ne E z fun y hy => h ⟨y, hy⟩)

/-- **The read-down map on points**: a point `z` of `Sp(W)/𝓘|W` lying over the ambient point
`i(y)` is carried by `emb⁻¹ ∘ restrictedIdealHom W` to `y` (`Subtype.ext` on `Sp(G)/𝓘`, then
`embInv_comp_emb`). -/
theorem toFun_embInv_restrictedIdealHom (W : Opens (pieceAmbient.{u} 𝕜 E.G))
    (z : (E.restrictedIdeal W).toAnalyticSpace) {y : X.restrictSet V}
    (hy : E.ambientPoint y =
      (((E.restrictedIdeal W).toAnalyticSpaceι z).1 :
        pieceAmbient.{u} 𝕜 E.G)) :
    (E.embInv ⊚ E.restrictedIdealHom W) z = y := by
  have h1 : (E.restrictedIdealHom W) z =
      E.emb y := by
    apply Subtype.ext
    exact (toFun_toAnalyticSpaceι_restrictedIdealHom E W z).trans hy.symm
  change E.embInv
    (E.restrictedIdealHom W z) = y
  rw [h1]
  exact congrArg (fun k : X.restrictSet V ⟶ X.restrictSet V =>
    k y) E.embInv_comp_emb

/-- **The read-down map, followed by the ambient embedding, is the inclusion of the closed
subspace**: `(ι ∘ emb) ∘ (emb⁻¹ ∘ restrictedIdealHom W) = Sp(W ↪ G) ∘ ι_W` (`emb_comp_embInv`,
`toAnalyticSpaceι_comp_restrictedIdealHom`). -/
theorem ambient_comp_embInv_restrictedIdealHom (W : Opens (pieceAmbient.{u} 𝕜 E.G)) :
    (E.ideal.toAnalyticSpaceι ⊚ E.emb) ⊚ (E.embInv ⊚ E.restrictedIdealHom W) =
      (show (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          ((pieceAmbient.{u} 𝕜 E.G).restrict W)) ⟶ toSpace (ContinuousLinearEquiv.refl 𝕜
          (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 E.G) from
        ofManifoldHom (AnalyticManifold.inclusion _ W)
          (AnalyticManifold.inclusion _ W).contMDiff) ⊚
      (E.restrictedIdeal W).toAnalyticSpaceι :=
  calc (E.ideal.toAnalyticSpaceι ⊚ E.emb) ⊚ (E.embInv ⊚ E.restrictedIdealHom W)
      = E.ideal.toAnalyticSpaceι ⊚ (E.emb ⊚ (E.embInv ⊚ E.restrictedIdealHom W)) :=
        (Category.assoc _ _ _).symm
    _ = E.ideal.toAnalyticSpaceι ⊚ ((E.emb ⊚ E.embInv) ⊚ E.restrictedIdealHom W) :=
        congrArg (fun k => E.ideal.toAnalyticSpaceι ⊚ k) (Category.assoc _ _ _)
    _ =
        E.ideal.toAnalyticSpaceι ⊚
            (𝟙 _ ⊚ E.restrictedIdealHom W) :=
        congrArg (fun k => E.ideal.toAnalyticSpaceι ⊚ (k ⊚ E.restrictedIdealHom W))
          E.emb_comp_embInv
    _ = E.ideal.toAnalyticSpaceι ⊚ E.restrictedIdealHom W :=
        congrArg (fun k => E.ideal.toAnalyticSpaceι ⊚ k) (Category.comp_id _)
    _ = _ ⊚ (E.restrictedIdeal W).toAnalyticSpaceι := toAnalyticSpaceι_comp_restrictedIdealHom E W

end PieceEmbedding

/-! ### The core identity from the stalk identity -/

section Core

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)))
  (W₂ : Opens (pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)))
  (Gd : Diffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜)
    ((pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)).restrict W₁)
    ((pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)).restrict W₂) ω)
  (Ψ : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G) →
    pieceAmbient.{u} 𝕜 (padOpens (Fin.natAddEmb n) E₂.G))
  (hΨ : ContMDiffOn 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω Ψ W₁)

/-- The two padded ambients on the model `𝕜^{n+m}`, abbreviated for this section. -/
local notation "𝔸₁" => pieceAmbient 𝕜 (padOpens (Fin.castAddEmb m) E₁.G)
local notation "𝔸₂" => pieceAmbient 𝕜 (padOpens (Fin.natAddEmb n) E₂.G)
local notation "𝕊" => toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))

/-- The coordinate-germ step of the core: the two morphisms `Sp(W₁)/𝓘₁|W₁ ⟶ Sp(padOpens₂)` — the
inclusion after `g`, and the right-padded ambient embedding after the read-down map — are equal:
`hom_ext_of_coord_chart` at every point, the coordinate germs pulled back equally by the stalk
identity `hδ`. -/
theorem padded_equivalence_hom_aux (hg : ∀ z, (Gd z).1 = Ψ z.1)
    (hpt : ∀ y, padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁ →
      Ψ (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
        padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y))
    (hδ : ∀ (y : X.restrictSet V) (hb : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁)
      (hc : Ψ (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
        padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y)),
      padStalkMap E₂ (Fin.natAddEmb n) y =
        (padStalkMap E₁ (Fin.castAddEmb m) y).comp (germMapOn Ψ (V := W₁) hΨ hb hc)) :
    ((show 𝕊 ((𝔸₂).restrict W₂) ⟶ 𝕊 (𝔸₂) from
      ofManifoldHom (AnalyticManifold.inclusion _ W₂)
        (AnalyticManifold.inclusion _ W₂).contMDiff) ⊚
      (show 𝕊 ((𝔸₁).restrict W₁) ⟶ 𝕊 ((𝔸₂).restrict W₂) from
      ofManifoldHom Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff)) ⊚
      ((E₁.padLeft m).restrictedIdeal W₁).toAnalyticSpaceι =
    ((show toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin m → 𝕜)) (pieceAmbient.{u} 𝕜 E₂.G) ⟶
        𝕊 (𝔸₂) from
      ofManifoldHom (padExt (Fin.natAddEmb n) E₂.G) (contMDiff_padExt _ _)) ⊚
      (E₂.ideal.toAnalyticSpaceι ⊚ E₂.emb)) ⊚
      ((E₁.padLeft m).embInv ⊚ (E₁.padLeft m).restrictedIdealHom W₁) := by
  let P₁ := E₁.padLeft m
  let ι₁ : (P₁.restrictedIdeal W₁).toAnalyticSpace ⟶ P₁.ideal.toAnalyticSpace :=
    P₁.restrictedIdealHom W₁
  let q₁ : (P₁.restrictedIdeal W₁).toAnalyticSpace ⟶ 𝕊 ((𝔸₁).restrict W₁) :=
    (P₁.restrictedIdeal W₁).toAnalyticSpaceι
  let qP₁ : P₁.ideal.toAnalyticSpace ⟶ 𝕊 (𝔸₁) :=
    P₁.ideal.toAnalyticSpaceι
  let i₁ := E₁.ideal.toAnalyticSpaceι ⊚ E₁.emb
  let i₂ := E₂.ideal.toAnalyticSpaceι ⊚ E₂.emb
  let ρ := P₁.embInv ⊚ ι₁
  let Sp₁ : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 E₁.G) ⟶ 𝕊
      (𝔸₁)) :=
    ofManifoldHom (padExt (Fin.castAddEmb m) E₁.G) (contMDiff_padExt _ _)
  let Sp₂ : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin m → 𝕜)) (pieceAmbient.{u} 𝕜 E₂.G) ⟶ 𝕊
      (𝔸₂)) :=
    ofManifoldHom (padExt (Fin.natAddEmb n) E₂.G) (contMDiff_padExt _ _)
  let SpG : 𝕊 ((𝔸₁).restrict W₁) ⟶ 𝕊 ((𝔸₂).restrict W₂) :=
    ofManifoldHom Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff
  let Spι₁ : 𝕊 ((𝔸₁).restrict W₁) ⟶ 𝕊 (𝔸₁) :=
    ofManifoldHom (AnalyticManifold.inclusion _ W₁)
      (AnalyticManifold.inclusion _ W₁).contMDiff
  let Spι₂ : 𝕊 ((𝔸₂).restrict W₂) ⟶ 𝕊 (𝔸₂) :=
    ofManifoldHom (AnalyticManifold.inclusion _ W₂)
      (AnalyticManifold.inclusion _ W₂).contMDiff
  have e5 : qP₁ ⊚ P₁.emb = Sp₁ ⊚ i₁ := E₁.toAnalyticSpaceι_comp_padAlong_emb (Fin.castAddEmb m)
  have e6 : (qP₁ ⊚ P₁.emb) ⊚ ρ = Spι₁ ⊚ q₁ := P₁.ambient_comp_embInv_restrictedIdealHom W₁
  have hμν : (Sp₁ ⊚ i₁) ⊚ ρ = Spι₁ ⊚ q₁ := (congrArg (fun k => k ⊚ ρ) e5.symm).trans e6
  change (Spι₂ ⊚ SpG) ⊚ q₁ = (Sp₂ ⊚ i₂) ⊚ ρ
  refine hom_ext_of_coord_chart (ψ := ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜))
    (Z := (P₁.restrictedIdeal W₁).toAnalyticSpace)
    (M' := (𝔸₂ : Type u)) _ _ ?_
  intro z
  -- the point of `W₁` under `z`
  let zp : (𝔸₁).restrict W₁ := z.1
  have hne : P₁.ideal.stalkIdeal (AnalyticManifold.inclusion _ W₁ zp) ≠ ⊤ :=
    fun htop => z.2 (by
      have hs :=
          IdealSheaf.stalkIdeal_pullback (AnalyticManifold.inclusion _ W₁)
        (AnalyticManifold.inclusion _ W₁).contMDiff P₁.ideal zp
      change (P₁.restrictedIdeal W₁).stalkIdeal zp = ⊤
      exact hs.trans ((congrArg (Ideal.map _) htop).trans (Ideal.map_top _)))
  obtain ⟨y, hy⟩ := P₁.exists_ambientPoint_eq_of_stalkIdeal_ne_top _ hne
  have hρz : ρ z = y :=
    P₁.toFun_embInv_restrictedIdealHom W₁ z hy
  subst hρz
  have hy' : padExt (Fin.castAddEmb m) E₁.G
      (E₁.ambientPoint (ρ z)) = (zp.1 : 𝔸₁) :=
    (ambientPoint_padLeft E₁ _).symm.trans hy
  have hb : padExt (Fin.castAddEmb m) E₁.G
      (E₁.ambientPoint (ρ z)) ∈ W₁ := by
    rw [hy']; exact zp.2
  have hc := hpt _ hb
  have hδy := hδ _ hb hc
  -- the chart at the common image point and the two membership facts
  have hg₁ : (padExt (Fin.natAddEmb n) E₂.G
      (E₂.ambientPoint (ρ z)) : 𝔸₂) =
      ((Spι₂ ⊚ SpG) ⊚ q₁).1.base z := by
    change _ = (Gd zp).1
    rw [hg zp, ← hy', hc]
  refine ⟨chartAt (Fin (n + m) → 𝕜) (padExt (Fin.natAddEmb n) E₂.G
      (E₂.ambientPoint (ρ z))),
    IsManifold.chart_mem_maximalAtlas _,
    Set.mem_of_eq_of_mem hg₁.symm (show (padExt (Fin.natAddEmb n) E₂.G
      (E₂.ambientPoint (ρ z)) : 𝔸₂) ∈ _ from
        mem_chart_source _ _),
    (show (padExt (Fin.natAddEmb n) E₂.G
      (E₂.ambientPoint (ρ z)) : 𝔸₂) ∈ _ from
        mem_chart_source _ _), fun j => ?_⟩
  -- the coordinate germ `u_j` at the image point and the section `u_j ∘ Ψ` on `U`
  let Φ := chartAt (Fin (n + m) → 𝕜) (padExt (Fin.natAddEmb n) E₂.G
    (E₂.ambientPoint (ρ z)))
  have hΦ : Φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, Fin (n + m) → 𝕜) ω _ :=
    IsManifold.chart_mem_maximalAtlas _
  let U : Opens (𝔸₁) :=
    ⟨W₁ ∩ Ψ ⁻¹' Φ.source, hΨ.continuousOn.isOpen_inter_preimage W₁.2 Φ.open_source⟩
  have hU : padExt (Fin.castAddEmb m) E₁.G
      (E₁.ambientPoint (ρ z)) ∈ U :=
    ⟨hb, by change Ψ _ ∈ Φ.source; rw [hc]; exact mem_chart_source _ _⟩
  have hU' : (zp.1 : 𝔸₁) ∈ U := by rw [← hy']; exact hU
  have hΨU : ContMDiffOn 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜) ω
      (extendSection 𝕜 (Fin (n + m) → 𝕜)
        (chartSection (Fin (n + m) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) Φ hΦ j) ∘
          Ψ) U := by
    have hproj : ContMDiff 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜) ω
        (fun v : Fin (n + m) → 𝕜 => (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) v j) :=
      (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (n + m) => 𝕜) j).contMDiff.comp
        ((ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜) :
          (Fin (n + m) → 𝕜) →L[𝕜] (Fin (n + m) → 𝕜)).contMDiff)
    have hcoord : ContMDiffOn 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜) ω
        (fun w => (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) (Φ (Ψ w)) j) U :=
      hproj.comp_contMDiffOn ((contMDiffOn_of_mem_maximalAtlas (n := ω) hΦ).comp
        (hΨ.mono Set.inter_subset_left) fun _ hw => hw.2)
    refine hcoord.congr fun w hw => ?_
    change extendSection 𝕜 (Fin (n + m) → 𝕜) _ (Ψ w) = _
    rw [extendSection_of_mem 𝕜 (Fin (n + m) → 𝕜) _ hw.2]
    rfl
  -- the coordinate germ, as a term
  let c₂ := coord (Fin (n + m) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) Φ hΦ
    (mem_chart_source (Fin (n + m) → 𝕜) (padExt (Fin.natAddEmb n) E₂.G
      (E₂.ambientPoint (ρ z)))) j
  let c₁ := coord (Fin (n + m) → 𝕜) (ContinuousLinearEquiv.refl 𝕜 (Fin (n + m) → 𝕜)) Φ hΦ
    (Set.mem_of_eq_of_mem hg₁.symm (show (padExt (Fin.natAddEmb n) E₂.G
      (E₂.ambientPoint (ρ z)) : 𝔸₂) ∈ _ from
        mem_chart_source _ _)) j
  -- the four stalk-map computations
  have L1 : (((Sp₂ ⊚ i₂) ⊚ ρ).1.stalkMap z).hom c₂ =
      (ρ.1.stalkMap z).hom (padStalkMap E₂ (Fin.natAddEmb n)
        (ρ z) c₂) := by
    refine (stalkMap_comp_apply ρ (Sp₂ ⊚ i₂) z _).trans ?_
    refine congrArg (ρ.1.stalkMap z).hom ?_
    refine (stalkMap_comp_apply i₂ Sp₂ _ _).trans ?_
    exact congrArg (E₂.pieceStalkMap _) (stalkMap_ofManifoldHom_eq_germMap _ _ _ _)
  have L2 : padStalkMap E₂ (Fin.natAddEmb n) (ρ z) c₂ =
      padStalkMap E₁ (Fin.castAddEmb m) (ρ z)
        (germMapOn Ψ (V := W₁) hΨ hb hc c₂) :=
    congrArg (fun φ => φ c₂) hδy
  have L3 : ∀ d, (ρ.1.stalkMap z).hom (padStalkMap E₁ (Fin.castAddEmb m)
      (ρ z) d) =
      (((Sp₁ ⊚ i₁) ⊚ ρ).1.stalkMap z).hom d := fun d => by
    refine ((stalkMap_comp_apply ρ (Sp₁ ⊚ i₁) z d).trans ?_).symm
    refine congrArg (ρ.1.stalkMap z).hom ?_
    refine (stalkMap_comp_apply i₁ Sp₁ _ _).trans ?_
    exact congrArg (E₁.pieceStalkMap _) (stalkMap_ofManifoldHom_eq_germMap _ _ _ _)
  have hθ : germMapOn Ψ (V := W₁) hΨ hb hc c₂ =
      (structureSheaf 𝕜 (Fin (n + m) → 𝕜) (𝔸₁)).presheaf.germ U _ hU
        (sectionOfContMDiffOn _ U hΨU) :=
    germMapOn_germ Ψ hΨ hb hc (mem_chart_source _ _) _ hU hΨU
  have L4 := stalkMap_germ_congr hμν z hU hU' (sectionOfContMDiffOn _ U hΨU)
  have R2 : ((Spι₁ ⊚ q₁).1.stalkMap z).hom
      ((structureSheaf 𝕜 (Fin (n + m) → 𝕜) (𝔸₁)).presheaf.germ U _ hU'
        (sectionOfContMDiffOn _ U hΨU)) =
      (q₁.1.stalkMap z).hom (germMap (AnalyticManifold.inclusion _ W₁)
        (AnalyticManifold.inclusion _ W₁).contMDiff zp
        ((structureSheaf 𝕜 (Fin (n + m) → 𝕜) (𝔸₁)).presheaf.germ U _ hU'
          (sectionOfContMDiffOn _ U hΨU))) := by
    refine (stalkMap_comp_apply q₁ Spι₁ z _).trans ?_
    exact congrArg (q₁.1.stalkMap z).hom (stalkMap_ofManifoldHom_eq_germMap _ _ _ _)
  have R1 : (((Spι₂ ⊚ SpG) ⊚ q₁).1.stalkMap z).hom c₁ =
      (q₁.1.stalkMap z).hom (germMap Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff zp
        (germMap (AnalyticManifold.inclusion _ W₂)
          (AnalyticManifold.inclusion _ W₂).contMDiff (Gd zp) c₁)) := by
    refine (stalkMap_comp_apply q₁ (Spι₂ ⊚ SpG) z _).trans ?_
    refine congrArg (q₁.1.stalkMap z).hom ?_
    refine (stalkMap_comp_apply SpG Spι₂ _ _).trans ?_
    refine (stalkMap_ofManifoldHom_eq_germMap _ _ _ _).trans ?_
    exact congrArg _ (stalkMap_ofManifoldHom_eq_germMap _ _ _ _)
  -- the germs on `W₁` agree: both are the germ of `u_j ∘ Ψ`
  have hΨ' : ContMDiffOn 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω
      (Ψ ∘ (Subtype.val : (𝔸₁).restrict W₁ → 𝔸₁)) ⊤ :=
    (hΨ.comp_contMDiff contMDiff_subtype_val fun w => w.2).contMDiffOn
  have hcomp : ∀ s, germMap Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff zp
      (germMap (AnalyticManifold.inclusion _ W₂)
        (AnalyticManifold.inclusion _ W₂).contMDiff (Gd zp) s) =
      germMap (AnalyticManifold.inclusion _ W₁)
        (AnalyticManifold.inclusion _ W₁).contMDiff zp
        (germMapOn Ψ (V := W₁) hΨ zp.2 (hg zp).symm s) := fun s => by
    refine (germMapOn_germMapOn
      (AnalyticManifold.inclusion _ W₂).contMDiff.contMDiffOn
      Gd.toContMDiffMap.contMDiff.contMDiffOn (Opens.mem_top zp) rfl (Opens.mem_top _) rfl
      ((AnalyticManifold.inclusion _ W₂).contMDiff.comp
        Gd.toContMDiffMap.contMDiff).contMDiffOn (Opens.mem_top zp) rfl s).trans ?_
    refine (germMapOn_congr _ hΨ' (Opens.mem_top zp) rfl (hg zp).symm (fun w _ => hg w) s).trans ?_
    exact (germMapOn_germMapOn hΨ (contMDiff_subtype_val (U := W₁)).contMDiffOn (Opens.mem_top zp)
      rfl zp.2 (hg zp).symm hΨ' (Opens.mem_top zp) (hg zp).symm s).symm
  have hθ' : germMapOn Ψ (V := W₁) hΨ zp.2 (hg zp).symm c₁ =
      (structureSheaf 𝕜 (Fin (n + m) → 𝕜) (𝔸₁)).presheaf.germ U _ hU'
        (sectionOfContMDiffOn _ U hΨU) :=
    germMapOn_germ Ψ hΨ zp.2 (hg zp).symm _ _ hU' hΨU
  have G : germMap (AnalyticManifold.inclusion _ W₁)
      (AnalyticManifold.inclusion _ W₁).contMDiff zp
      ((structureSheaf 𝕜 (Fin (n + m) → 𝕜) (𝔸₁)).presheaf.germ U _ hU'
        (sectionOfContMDiffOn _ U hΨU)) =
      germMap Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff zp
        (germMap (AnalyticManifold.inclusion _ W₂)
          (AnalyticManifold.inclusion _ W₂).contMDiff (Gd zp) c₁) :=
    (congrArg _ hθ'.symm).trans (hcomp c₁).symm
  calc (((Sp₂ ⊚ i₂) ⊚ ρ).1.stalkMap z).hom c₂
      = (ρ.1.stalkMap z).hom (padStalkMap E₂ (Fin.natAddEmb n) _ c₂) := L1
    _ = (ρ.1.stalkMap z).hom (padStalkMap E₁ (Fin.castAddEmb m) _ _) := congrArg _ L2
    _ = (((Sp₁ ⊚ i₁) ⊚ ρ).1.stalkMap z).hom _ := L3 _
    _ = (((Sp₁ ⊚ i₁) ⊚ ρ).1.stalkMap z).hom _ := congrArg _ hθ
    _ = ((Spι₁ ⊚ q₁).1.stalkMap z).hom _ := L4
    _ = (q₁.1.stalkMap z).hom _ := R2
    _ = (q₁.1.stalkMap z).hom _ := congrArg _ G
    _ = (((Spι₂ ⊚ SpG) ⊚ q₁).1.stalkMap z).hom c₁ := R1.symm

/-- The core in general form: the morphism identity from the stalk identity, for any local
isomorphism `Ψ` of the padded ambients restricting to a diffeomorphism `Gd : W₁ ≃ W₂`, carrying the
left-padded embedded points to the right-padded ones and interchanging the padded stalk maps. -/
theorem padded_equivalence_hom_of_stalkMap (hg : ∀ z, (Gd z).1 = Ψ z.1)
    (hpt : ∀ y, padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁ →
      Ψ (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
        padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y))
    (hδ : ∀ (y : X.restrictSet V) (hb : padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y) ∈ W₁)
      (hc : Ψ (padExt (Fin.castAddEmb m) E₁.G (E₁.ambientPoint y)) =
        padExt (Fin.natAddEmb n) E₂.G (E₂.ambientPoint y)),
      padStalkMap E₂ (Fin.natAddEmb n) y =
        (padStalkMap E₁ (Fin.castAddEmb m) y).comp (germMapOn Ψ (V := W₁) hΨ hb hc))
    (hI : (E₁.padLeft m).restrictedIdeal W₁ =
      ((E₂.padRight n).restrictedIdeal W₂).pullback Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff) :
    (E₂.padRight n).embInv ⊚ ((E₂.padRight n).restrictedIdealHom W₂ ⊚
        IdealSheaf.homOfPullbackEq Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff hI) =
      (E₁.padLeft m).embInv ⊚ (E₁.padLeft m).restrictedIdealHom W₁ := by
  let P₁ := E₁.padLeft m
  let P₂ := E₂.padRight n
  let ι₁ : (P₁.restrictedIdeal W₁).toAnalyticSpace ⟶ P₁.ideal.toAnalyticSpace :=
    P₁.restrictedIdealHom W₁
  let ι₂ : (P₂.restrictedIdeal W₂).toAnalyticSpace ⟶ P₂.ideal.toAnalyticSpace :=
    P₂.restrictedIdealHom W₂
  let hg' : (P₁.restrictedIdeal W₁).toAnalyticSpace ⟶ (P₂.restrictedIdeal W₂).toAnalyticSpace :=
    IdealSheaf.homOfPullbackEq Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff hI
  let q₁ : (P₁.restrictedIdeal W₁).toAnalyticSpace ⟶ 𝕊 ((𝔸₁).restrict W₁) :=
    (P₁.restrictedIdeal W₁).toAnalyticSpaceι
  let q₂ : (P₂.restrictedIdeal W₂).toAnalyticSpace ⟶ 𝕊 ((𝔸₂).restrict W₂) :=
    (P₂.restrictedIdeal W₂).toAnalyticSpaceι
  let qP₁ : P₁.ideal.toAnalyticSpace ⟶ 𝕊 (𝔸₁) :=
    P₁.ideal.toAnalyticSpaceι
  let qP₂ : P₂.ideal.toAnalyticSpace ⟶ 𝕊 (𝔸₂) :=
    P₂.ideal.toAnalyticSpaceι
  let i₁ := E₁.ideal.toAnalyticSpaceι ⊚ E₁.emb
  let i₂ := E₂.ideal.toAnalyticSpaceι ⊚ E₂.emb
  let ρ := P₁.embInv ⊚ ι₁
  let Sp₁ : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (pieceAmbient.{u} 𝕜 E₁.G) ⟶ 𝕊
      (𝔸₁)) :=
    ofManifoldHom (padExt (Fin.castAddEmb m) E₁.G) (contMDiff_padExt _ _)
  let Sp₂ : (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin m → 𝕜)) (pieceAmbient.{u} 𝕜 E₂.G) ⟶ 𝕊
      (𝔸₂)) :=
    ofManifoldHom (padExt (Fin.natAddEmb n) E₂.G) (contMDiff_padExt _ _)
  let SpG : 𝕊 ((𝔸₁).restrict W₁) ⟶ 𝕊 ((𝔸₂).restrict W₂) :=
    ofManifoldHom Gd.toContMDiffMap Gd.toContMDiffMap.contMDiff
  let Spι₁ : 𝕊 ((𝔸₁).restrict W₁) ⟶ 𝕊 (𝔸₁) :=
    ofManifoldHom (AnalyticManifold.inclusion _ W₁)
      (AnalyticManifold.inclusion _ W₁).contMDiff
  let Spι₂ : 𝕊 ((𝔸₂).restrict W₂) ⟶ 𝕊 (𝔸₂) :=
    ofManifoldHom (AnalyticManifold.inclusion _ W₂)
      (AnalyticManifold.inclusion _ W₂).contMDiff
  -- the identities of the layer
  have e1 : P₂.embInv ⊚ P₂.emb = 𝟙 _ := P₂.embInv_comp_emb
  have e1' : P₂.emb ⊚ P₂.embInv = 𝟙 _ := P₂.emb_comp_embInv
  have e2 : qP₂ ⊚ ι₂ = Spι₂ ⊚ q₂ := P₂.toAnalyticSpaceι_comp_restrictedIdealHom W₂
  have e3 : q₂ ⊚ hg' = SpG ⊚ q₁ := homOfPullbackEq_comp_toAnalyticSpaceι _ _ hI
  have e4 : qP₂ ⊚ P₂.emb = Sp₂ ⊚ i₂ := E₂.toAnalyticSpaceι_comp_padAlong_emb (Fin.natAddEmb n)
  have e5 : qP₁ ⊚ P₁.emb = Sp₁ ⊚ i₁ := E₁.toAnalyticSpaceι_comp_padAlong_emb (Fin.castAddEmb m)
  have e6 : (qP₁ ⊚ P₁.emb) ⊚ ρ = Spι₁ ⊚ q₁ := P₁.ambient_comp_embInv_restrictedIdealHom W₁
  have hμν : (Sp₁ ⊚ i₁) ⊚ ρ = Spι₁ ⊚ q₁ := (congrArg (fun k => k ⊚ ρ) e5.symm).trans e6
  -- third: the two morphisms into `Sp(padOpens₂)` agree on coordinate germs
  have main : (Spι₂ ⊚ SpG) ⊚ q₁ = (Sp₂ ⊚ i₂) ⊚ ρ :=
    padded_equivalence_hom_aux E₁ E₂ W₁ W₂ Gd Ψ hΨ hg hpt hδ
  -- second: reduce to `main`
  have key : qP₂ ⊚ (P₂.emb ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg'))) = qP₂ ⊚ (P₂.emb ⊚ ρ) :=
    calc qP₂ ⊚ (P₂.emb ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg')))
        = qP₂ ⊚ ((P₂.emb ⊚ P₂.embInv) ⊚ (ι₂ ⊚ hg')) :=
          congrArg (fun k => qP₂ ⊚ k) (Category.assoc _ _ _)
      _ = qP₂ ⊚ (𝟙 _ ⊚ (ι₂ ⊚ hg')) :=
          congrArg (fun k => qP₂ ⊚ (k ⊚ (ι₂ ⊚ hg'))) e1'
      _ = qP₂ ⊚ (ι₂ ⊚ hg') := congrArg (fun k => qP₂ ⊚ k) (Category.comp_id _)
      _ = (qP₂ ⊚ ι₂) ⊚ hg' := Category.assoc _ _ _
      _ = (Spι₂ ⊚ q₂) ⊚ hg' := congrArg (fun k => k ⊚ hg') e2
      _ = Spι₂ ⊚ (q₂ ⊚ hg') := (Category.assoc _ _ _).symm
      _ = Spι₂ ⊚ (SpG ⊚ q₁) := congrArg (fun k => Spι₂ ⊚ k) e3
      _ = (Spι₂ ⊚ SpG) ⊚ q₁ := Category.assoc _ _ _
      _ = (Sp₂ ⊚ i₂) ⊚ ρ := main
      _ = (qP₂ ⊚ P₂.emb) ⊚ ρ := congrArg (fun k => k ⊚ ρ) e4.symm
      _ = qP₂ ⊚ (P₂.emb ⊚ ρ) := (Category.assoc _ _ _).symm
  have key' : P₂.emb ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg')) = P₂.emb ⊚ ρ :=
    Hom.ext_of_comp_quotientι (X := ofManifold 𝕜 (Fin (n + m) → 𝕜)
      (𝔸₂)) P₂.ideal key
  -- first: cancel the isomorphism `P₂.emb`
  calc P₂.embInv ⊚ (ι₂ ⊚ hg')
      = 𝟙 _ ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg')) :=
          (Category.comp_id _).symm
    _ = (P₂.embInv ⊚ P₂.emb) ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg')) :=
        congrArg (fun k => k ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg'))) e1.symm
    _ = P₂.embInv ⊚ (P₂.emb ⊚ (P₂.embInv ⊚ (ι₂ ⊚ hg'))) := (Category.assoc _ _ _).symm
    _ = P₂.embInv ⊚ (P₂.emb ⊚ ρ) := congrArg (fun k => P₂.embInv ⊚ k) key'
    _ = (P₂.embInv ⊚ P₂.emb) ⊚ ρ := Category.assoc _ _ _
    _ = 𝟙 _ ⊚ ρ := congrArg (fun k => k ⊚ ρ) e1
    _ = ρ := Category.comp_id _

end Core

/-! ### The core identity at the shear of the two lifts, and the assembly -/

section Assembly

variable {n m : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E₁ : PieceEmbedding 𝕜 n X V) (E₂ : PieceEmbedding 𝕜 m X V) (x : X.restrictSet V)
  (O₁ : Opens (Fin n → 𝕜)) (j₂ : (Fin n → 𝕜) → (Fin m → 𝕜)) (hj₂ : ContDiffOn 𝕜 ω j₂ O₁)
  (O₂ : Opens (Fin m → 𝕜)) (j₁ : (Fin m → 𝕜) → (Fin n → 𝕜)) (hj₁ : ContDiffOn 𝕜 ω j₁ O₂)

/-- **The morphism identity for the explicit shear** `Ψ = shearAmbient` of the two lifts
([Kol07, Lemma 39, proof]): with `W₁ := Ψ.source`, `W₂ := Ψ.target`, `g := Ψ` restricted and `hI`
the ideal identity (`pullback_padIdeal_inclusion_eq_of_shear`), the closed-subspace morphism
`homOfPullbackEq` over `g`, read down to `X|V` through the right padding, is the left padding's
reading — the general core `padded_equivalence_hom_of_stalkMap` at the shear: the embedded points
are carried by `shearAmbient_padExt`, the padded stalk maps interchanged by
`padStalkMap_eq_comp_germMapOn_shear`. -/
theorem padded_equivalence_hom_of_shear
    (v₂ : ∀ y, E₁.modelPoint y ∈ O₁ → j₂ (E₁.modelPoint y) = E₂.modelPoint y)
    (v₁ : ∀ y, E₂.modelPoint y ∈ O₂ → j₁ (E₂.modelPoint y) = E₁.modelPoint y)
    (H₂ : ∀ (y : X.restrictSet V) (hy : E₁.modelPoint y ∈ O₁) (k : Fin m),
      E₂.modelStalkMap y (modelCoordGerm (E₂.modelPoint y) k) =
        E₁.modelStalkMap y (modelGerm (fun v => j₂ v k) (contDiffOn_pi.mp hj₂ k) hy))
    (H₁ : ∀ (y : X.restrictSet V) (hy : E₂.modelPoint y ∈ O₂) (k : Fin n),
      E₁.modelStalkMap y (modelCoordGerm (E₁.modelPoint y) k) =
        E₂.modelStalkMap y (modelGerm (fun v => j₁ v k) (contDiffOn_pi.mp hj₁ k) hy))
    (hI : (E₁.padLeft m).restrictedIdeal
        ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩ =
      ((E₂.padRight n).restrictedIdeal
        ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).target,
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_target⟩).pullback
        (partialDiffeomorphToDiffeomorph (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)).toContMDiffMap
        (partialDiffeomorphToDiffeomorph
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁)).toContMDiffMap.contMDiff) :
    (IdealSheaf.homOfPullbackEq
        (partialDiffeomorphToDiffeomorph
        (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁
        hj₁)).toContMDiffMap
        (partialDiffeomorphToDiffeomorph
        (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁
        hj₁)).toContMDiffMap.contMDiff hI ≫ (E₂.padRight n).restrictedIdealHom
        ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).target,
        (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_target⟩) ≫ (E₂.padRight n).embInv =
      (E₁.padLeft m).restrictedIdealHom ⟨(shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).source,
          (shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁).open_source⟩ ≫ (E₁.padLeft m).embInv := by
  let Ψₐ := shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁
  refine padded_equivalence_hom_of_stalkMap E₁ E₂ ⟨Ψₐ.source, Ψₐ.open_source⟩
    ⟨Ψₐ.target, Ψₐ.open_target⟩ (partialDiffeomorphToDiffeomorph Ψₐ) Ψₐ Ψₐ.contMDiffOn_toFun
    (partialDiffeomorphToDiffeomorph_apply_coe Ψₐ) ?_ ?_ hI
  · intro y hb
    obtain ⟨hy₁, hj⟩ := modelPoint_mem_of_padExt_mem_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hb
    have h₂ := v₂ y hy₁
    exact shearAmbient_padExt E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y h₂ (v₁ y (h₂ ▸ hj))
  · intro y hb hc
    obtain ⟨hy₁, hj⟩ := modelPoint_mem_of_padExt_mem_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hb
    have h₂ := v₂ y hy₁
    have hy₂ : E₂.modelPoint y ∈ O₂ := h₂ ▸ hj
    exact padStalkMap_eq_comp_germMapOn_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ y hy₁ hy₂ h₂ (H₂ y hy₁)
      (H₁ y hy₂) hb hc

/-- **Lemma 39 at the MORPHISM level** ([Kol07, Lemma 39]: the two padded embeddings are
"equivalent under a (nonlinear) automorphism", built in the proof from an extension `j₂` of `i₂`):
near the padded ambient point of every `x`, a bijective local analytic isomorphism `g` of opens of
the padded ambients pulling the right-padded restricted ideal back to the left-padded one, such
that **the morphism of closed subspaces `Sp(W₁)/𝓘₁|W₁ → Sp(W₂)/𝓘₂|W₂` over `g`
(`homOfPullbackEq`), followed by the right padding's identification with `X|V`, is the left
padding's identification** — the closed-subspace isomorphism induced by the shear IS the identity
of the piece. Proved from the local lifts (`exists_modelLift`, `PieceLemma39Model.lean`) and the
shear `shearAmbient` of the two lifts: the witnesses of
`embeddings_equivalent_under_automorphism_pad`, the ideal identity
`pullback_padIdeal_inclusion_eq_of_shear`, the morphism identity `padded_equivalence_hom_of_shear`.
The point clause of `embeddings_equivalent_under_automorphism` is its shadow on base points. -/
theorem exists_padded_equivalence_hom :
    ∃ (W₁ : Opens (pieceAmbient.{u} 𝕜 (E₁.padLeft m).G))
      (W₂ : Opens (pieceAmbient.{u} 𝕜 (E₂.padRight n).G))
      (g : AnalyticMap ((pieceAmbient.{u} 𝕜 (E₁.padLeft m).G).restrict W₁)
        ((pieceAmbient.{u} 𝕜 (E₂.padRight n).G).restrict W₂)),
      (E₁.padLeft m).ambientPoint x ∈ W₁ ∧
      IsLocalDiffeomorph 𝓘(𝕜, Fin (n + m) → 𝕜) 𝓘(𝕜, Fin (n + m) → 𝕜) ω g ∧
      Function.Bijective g ∧
      ∃ hI : (E₁.padLeft m).restrictedIdeal W₁ =
          ((E₂.padRight n).restrictedIdeal W₂).pullback ⇑g g.contMDiff,
        (IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI ≫ (E₂.padRight n).restrictedIdealHom
            W₂) ≫ (E₂.padRight n).embInv =
          (E₁.padLeft m).restrictedIdealHom W₁ ≫ (E₁.padLeft m).embInv := by
  obtain ⟨O₁, hx₁, j₂, hj₂, H₂⟩ := E₁.exists_modelLift E₂ x
  obtain ⟨O₂, hx₂, j₁, hj₁, H₁⟩ := E₂.exists_modelLift E₁ x
  have v₂ : ∀ y, E₁.modelPoint y ∈ O₁ → j₂ (E₁.modelPoint y) = E₂.modelPoint y := fun y hy =>
    funext fun k => (E₁.modelPoint_eq_of_coord_eq E₂ y _ hy k (H₂ y hy k)).symm
  have v₁ : ∀ y, E₂.modelPoint y ∈ O₂ → j₁ (E₂.modelPoint y) = E₁.modelPoint y := fun y hy =>
    funext fun k => (E₂.modelPoint_eq_of_coord_eq E₁ y _ hy k (H₁ y hy k)).symm
  let Ψₐ := shearAmbient E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁
  have hI := pullback_padIdeal_inclusion_eq_of_shear E₁ E₂ Ψₐ (partialDiffeomorphToDiffeomorph Ψₐ)
    (partialDiffeomorphToDiffeomorph_apply_coe Ψₐ)
    (stalkIdeal_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ v₂ v₁ H₂ H₁)
  refine ⟨⟨Ψₐ.source, Ψₐ.open_source⟩, ⟨Ψₐ.target, Ψₐ.open_target⟩,
    (partialDiffeomorphToDiffeomorph Ψₐ).toContMDiffMap, ?_,
    (partialDiffeomorphToDiffeomorph Ψₐ).isLocalDiffeomorph,
    (partialDiffeomorphToDiffeomorph Ψₐ).toEquiv.bijective, hI, ?_⟩
  · exact (congrArg (fun p : pieceAmbient.{u} 𝕜 (padOpens (Fin.castAddEmb m) E₁.G) =>
      p ∈ Ψₐ.source) (ambientPoint_padLeft E₁ x)).mpr
      (padExt_mem_shearAmbient_source E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ x hx₁ hx₂ (v₂ x hx₁) (v₁ x hx₂))
  · exact padded_equivalence_hom_of_shear E₁ E₂ x O₁ j₂ hj₂ O₂ j₁ hj₁ v₂ v₁ H₂ H₁ hI

end Assembly

end Hironaka.Manifold

end
