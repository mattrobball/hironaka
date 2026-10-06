/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PadRestrict
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrictResolution
public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionPad
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The inverse piece embeddings under padding and restriction

Four squares of morphisms of closed subspaces, closed by `Hom.ext_of_comp_quotientι` (a map into
a quotient is determined by its composite with the quotient's inclusion) except the third, which
follows from the retraction identities of the embeddings (`emb_comp_embInv_padAlong`,
`embInv_comp_emb`); the final composite square is assembled from the other three:

* `homOfPullbackEq` along a composite of local analytic isomorphisms is the composite of the
  `homOfPullbackEq`s (functoriality of the induced morphism of closed subspaces);
* the padded-slice morphism `padSliceHom` commutes with the inclusions of ambients (the coordinate
  square `padCoordProj_comp_pieceAmbientIncl` of `PadRestrict.lean`);
* the inverse embedding of the padded piece is the slice morphism followed by the inverse
  embedding of the piece (`emb_comp_embInv_padAlong`);
* the inverse embedding of the restricted piece lies over the inclusion of the pieces
  (`restrictPiece_emb_comp_quotientι_comp_ambientInclHom`), and so, composing, the inverse
  embedding of the PADDED RESTRICTED piece is carried by `homOfPullbackEq` along the padded
  inclusion of ambients to the inverse embedding of the padded piece, over the inclusion of the
  pieces.

The last identity is what the transition between a padded piece and a piece of the other
embedding needs (`ShearOverX.lean`): the two read-down maps from the common closed subspace
`Sp(𝓘₀|W₁')` to `X` are the shear's two maps (`hmor`) conjugated by these squares. Not in the
sources; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace
open KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜]

section Functoriality

variable {n : ℕ} {A₁ A₂ A₃ : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (f₁ : AnalyticMap A₁ A₂) (f₂ : AnalyticMap A₂ A₃)
  {J₁ : AnalyticManifold.IdealSheaf A₁} {J₂ : AnalyticManifold.IdealSheaf A₂}
      {J₃ : AnalyticManifold.IdealSheaf A₃}

/-- `homOfPullbackEq` along a composite is the composite of the `homOfPullbackEq`s — both lie
over `Sp(f₂ ∘ f₁)`
(`Hom.ext_of_comp_quotientι`, `homOfPullbackEq_comp_toAnalyticSpaceι`, `ofManifoldHom_comp`). -/
theorem _root_.Manifold.IdealSheaf.homOfPullbackEq_comp (h₁ : J₁ = J₂.pullback ⇑f₁ f₁.contMDiff)
    (h₂ : J₂ = J₃.pullback ⇑f₂ f₂.contMDiff)
    (h₁₂ : J₁ = J₃.pullback (⇑f₂ ∘ ⇑f₁) (f₂.contMDiff.comp f₁.contMDiff)) :
    IdealSheaf.homOfPullbackEq ⇑f₁ f₁.contMDiff h₁ ≫ IdealSheaf.homOfPullbackEq ⇑f₂ f₂.contMDiff h₂
        =
      IdealSheaf.homOfPullbackEq (⇑f₂ ∘ ⇑f₁) (f₂.contMDiff.comp f₁.contMDiff) h₁₂ := by
  refine Hom.ext_of_comp_quotientι _ ?_
  have e₂ : IdealSheaf.homOfPullbackEq ⇑f₂ f₂.contMDiff h₂ ≫ J₃.toAnalyticSpaceι =
      J₂.toAnalyticSpaceι ≫ ofManifoldHom ⇑f₂ f₂.contMDiff :=
    homOfPullbackEq_comp_toAnalyticSpaceι ⇑f₂ f₂.contMDiff h₂
  have e₁ : IdealSheaf.homOfPullbackEq ⇑f₁ f₁.contMDiff h₁ ≫ J₂.toAnalyticSpaceι =
      J₁.toAnalyticSpaceι ≫ ofManifoldHom ⇑f₁ f₁.contMDiff :=
    homOfPullbackEq_comp_toAnalyticSpaceι ⇑f₁ f₁.contMDiff h₁
  have e₁₂ : IdealSheaf.homOfPullbackEq (⇑f₂ ∘ ⇑f₁) (f₂.contMDiff.comp f₁.contMDiff) h₁₂ ≫
        J₃.toAnalyticSpaceι =
      J₁.toAnalyticSpaceι ≫ ofManifoldHom (⇑f₂ ∘ ⇑f₁) (f₂.contMDiff.comp f₁.contMDiff) :=
    homOfPullbackEq_comp_toAnalyticSpaceι (⇑f₂ ∘ ⇑f₁) (f₂.contMDiff.comp f₁.contMDiff) h₁₂
  have key : (IdealSheaf.homOfPullbackEq ⇑f₁ f₁.contMDiff h₁ ≫
        IdealSheaf.homOfPullbackEq ⇑f₂ f₂.contMDiff h₂) ≫ J₃.toAnalyticSpaceι =
      IdealSheaf.homOfPullbackEq (⇑f₂ ∘ ⇑f₁) (f₂.contMDiff.comp f₁.contMDiff) h₁₂ ≫
        J₃.toAnalyticSpaceι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => IdealSheaf.homOfPullbackEq ⇑f₁ f₁.contMDiff h₁ ≫ k) e₂).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ ofManifoldHom ⇑f₂ f₂.contMDiff) e₁).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => J₁.toAnalyticSpaceι ≫ k)
                (ofManifoldHom_comp ⇑f₁ f₁.contMDiff ⇑f₂ f₂.contMDiff).symm).trans e₁₂.symm)))))
  exact key

end Functoriality

section PadSquare

variable {n n' : ℕ} (σ : Fin n ↪ Fin n') {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G)
  (J : AnalyticManifold.IdealSheaf (pieceAmbient.{u} 𝕜 G))

/-- Composition in the category of `𝕜`-locally ringed spaces, pinned: the analytic-space `≫`
unfolds to it, and pinning every step of the chain to one spelling keeps the elaborator from
unifying the two spellings under pending metavariables (a `whnf` timeout otherwise). -/
local infixr:80 " ≫ₖ " => @CategoryStruct.comp (KLocallyRingedSpace 𝕜) _ _ _ _

/-- **The padded-slice morphism commutes with the inclusions of ambients** — `padSliceHom` for
`J` after `homOfPullbackEq` along the padded
inclusion is `homOfPullbackEq` along the inclusion after `padSliceHom` for the restricted ideal;
both lie over the coordinate square `padCoordProj ∘ ι⁺ = ι ∘ padCoordProj'`. -/
theorem padSliceHom_comp_homOfPullbackEq_pieceAmbientIncl :
    (IdealSheaf.homOfPullbackEq ⇑(pieceAmbientIncl (padOpens_mono σ h))
        (pieceAmbientIncl (padOpens_mono σ h)).contMDiff (padIdeal_comap σ h J)) ≫ padSliceHom σ J =
      padSliceHom σ (J.pullback _ (pieceAmbientIncl h).contMDiff) ≫ (IdealSheaf.homOfPullbackEq (J'
          := J.pullback _ (pieceAmbientIncl
          h).contMDiff) (J := J) ⇑(pieceAmbientIncl h) (pieceAmbientIncl h).contMDiff rfl) := by
  refine Hom.ext_of_comp_quotientι _ ?_
  -- the two slice morphisms lie over the coordinate projections
  have s₁ : padSliceHom σ J ≫ₖ J.toAnalyticSpaceι =
      (padIdeal σ J).toAnalyticSpaceι ≫ₖ
        ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G) :=
    quotientMap_comp_quotientι _ _ _ _
  have s₂ : padSliceHom σ (J.pullback _ (pieceAmbientIncl h).contMDiff) ≫ₖ
        AnalyticManifold.IdealSheaf.toAnalyticSpaceι (J.pullback _ (pieceAmbientIncl h).contMDiff) =
      AnalyticManifold.IdealSheaf.toAnalyticSpaceι (padIdeal σ (J.pullback _ (pieceAmbientIncl
          h).contMDiff))
          ≫ₖ
        ofManifoldHom (padCoordProj σ G') (contMDiff_padCoordProj σ G') :=
    quotientMap_comp_quotientι _ _ _ _
  -- the two `homOfPullbackEq`s lie over the inclusions of ambients
  have e₁ : IdealSheaf.homOfPullbackEq ⇑(pieceAmbientIncl (padOpens_mono σ h))
        (pieceAmbientIncl (padOpens_mono σ h)).contMDiff (padIdeal_comap σ h J) ≫ₖ
        (padIdeal σ J).toAnalyticSpaceι =
      AnalyticManifold.IdealSheaf.toAnalyticSpaceι (padIdeal σ (J.pullback _ (pieceAmbientIncl
          h).contMDiff))
          ≫ₖ
        ofManifoldHom ⇑(pieceAmbientIncl (padOpens_mono σ h))
          (pieceAmbientIncl (padOpens_mono σ h)).contMDiff :=
    homOfPullbackEq_comp_toAnalyticSpaceι ⇑(pieceAmbientIncl (padOpens_mono σ h))
      (pieceAmbientIncl (padOpens_mono σ h)).contMDiff (padIdeal_comap σ h J)
  have e₂ :
      IdealSheaf.homOfPullbackEq
          (J' := J.pullback _ (pieceAmbientIncl h).contMDiff)
        (J := J) ⇑(pieceAmbientIncl h) (pieceAmbientIncl h).contMDiff rfl ≫ₖ J.toAnalyticSpaceι =
      AnalyticManifold.IdealSheaf.toAnalyticSpaceι (J.pullback _ (pieceAmbientIncl h).contMDiff) ≫ₖ
        ofManifoldHom ⇑(pieceAmbientIncl h) (pieceAmbientIncl h).contMDiff :=
    homOfPullbackEq_comp_toAnalyticSpaceι ⇑(pieceAmbientIncl h) (pieceAmbientIncl h).contMDiff rfl
  -- the coordinate square `padCoordProj_comp_pieceAmbientIncl` as a square of morphisms of spaces
  have hsq₀ : ∀ (k : pieceAmbient.{u} 𝕜 (padOpens σ G') → pieceAmbient.{u} 𝕜 G)
      (hk : ContMDiff 𝓘(𝕜, Fin n' → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω k)
      (_ : padCoordProj σ G ∘ pieceAmbientIncl (padOpens_mono σ h) = k),
      ofManifoldHom (padCoordProj σ G ∘ pieceAmbientIncl (padOpens_mono σ h))
          ((contMDiff_padCoordProj σ G).comp (pieceAmbientIncl (padOpens_mono σ h)).contMDiff) =
        ofManifoldHom k hk := by
    intro k hk e
    subst e
    rfl
  have hsq : ofManifoldHom ⇑(pieceAmbientIncl (padOpens_mono σ h))
        (pieceAmbientIncl (padOpens_mono σ h)).contMDiff ≫ₖ
        ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G) =
      ofManifoldHom (padCoordProj σ G') (contMDiff_padCoordProj σ G') ≫ₖ
        ofManifoldHom ⇑(pieceAmbientIncl h) (pieceAmbientIncl h).contMDiff :=
    (ofManifoldHom_comp _ _ _ _).symm.trans
      ((hsq₀ _ _ (padCoordProj_comp_pieceAmbientIncl σ h)).trans (ofManifoldHom_comp _ _ _ _))
  -- the chain, every step in the pinned spelling
  have key : (IdealSheaf.homOfPullbackEq ⇑(pieceAmbientIncl (padOpens_mono σ h))
        (pieceAmbientIncl (padOpens_mono σ h)).contMDiff (padIdeal_comap σ h J) ≫ₖ
        padSliceHom σ J) ≫ₖ J.toAnalyticSpaceι =
      (padSliceHom σ (J.pullback _ (pieceAmbientIncl h).contMDiff) ≫ₖ
        IdealSheaf.homOfPullbackEq
            (J' := J.pullback _ (pieceAmbientIncl h).contMDiff)
          (J := J) ⇑(pieceAmbientIncl h) (pieceAmbientIncl h).contMDiff rfl) ≫ₖ
        J.toAnalyticSpaceι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => IdealSheaf.homOfPullbackEq ⇑(pieceAmbientIncl (padOpens_mono σ h))
          (pieceAmbientIncl (padOpens_mono σ h)).contMDiff (padIdeal_comap σ h J) ≫ₖ k) s₁).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ₖ ofManifoldHom (padCoordProj σ G) (contMDiff_padCoordProj σ G))
            e₁).trans
            ((Category.assoc _ _ _).trans
              ((congrArg
                  (fun k => AnalyticManifold.IdealSheaf.toAnalyticSpaceι (padIdeal σ
                      (Manifold.IdealSheaf.pullback _ (pieceAmbientIncl
                      h).contMDiff
                  J)) ≫ₖ k) hsq).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun k => k ≫ₖ ofManifoldHom ⇑(pieceAmbientIncl h)
                    (pieceAmbientIncl h).contMDiff) s₂.symm).trans
                    ((Category.assoc _ _ _).trans
                      ((congrArg (fun k => padSliceHom σ (J.pullback _ (pieceAmbientIncl
                          h).contMDiff) ≫ₖ k) e₂.symm).trans
                        (Category.assoc _ _ _).symm)))))))))
  exact key

end PadSquare

section PieceSquares

variable {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V V' : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- **The inverse embedding of the padded piece is the slice morphism followed by the piece's
inverse embedding** — `emb_comp_embInv_padAlong` read backwards through `embInv_comp_emb`. -/
theorem PieceEmbedding.embInv_padAlong {n' : ℕ} (σ : Fin n ↪ Fin n') :
    (E.padAlong σ).embInv =
      padSliceHom σ E.ideal ≫ E.embInv := by
  have h₁ : (E.padAlong σ).embInv ≫ E.emb = padSliceHom σ E.ideal :=
    E.emb_comp_embInv_padAlong σ
  have h₂ : E.emb ≫ E.embInv = 𝟙 _ := E.embInv_comp_emb
  exact (Category.comp_id _).symm.trans
    ((congrArg (fun k => (E.padAlong σ).embInv ≫ k) h₂.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ E.embInv) h₁)))

variable (hV' : IsOpen V') (hsub : V' ⊆ V)

/-- **The inverse embedding of the restricted piece lies over the inclusion of the pieces** —
`homOfPullbackEq` along the inclusion of
the shrunk ambient followed by the piece's inverse embedding is the restricted piece's inverse
embedding followed by `X|V' → X|V` (`restrictPiece_emb_comp_quotientι_comp_ambientInclHom`,
`Hom.ext_of_comp_quotientι`). -/
theorem PieceEmbedding.embInv_comp_homOfPullbackEq_restrictPiece :
    (IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal) (J := E.ideal)
          ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
          (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl) ≫ E.embInv =
      (E.restrictPiece hV' hsub).embInv ≫
          (show X.restrictSet V' ⟶ X.restrictSet V from KLocallyRingedSpace.restrictIncl
            X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub)) := by
  -- the embeddings lie over the inclusion
  have hemb : (E.restrictPiece hV' hsub).emb ≫
      IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal) (J := E.ideal)
        ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
        (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl =
      KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) ≫
        E.emb := by
    refine Hom.ext_of_comp_quotientι _ ?_
    have e : IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal) (J := E.ideal)
          ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
          (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl ≫ E.ideal.toAnalyticSpaceι =
        (E.restrictPiece hV' hsub).ideal.toAnalyticSpaceι ≫ E.ambientInclHom hV' :=
      homOfPullbackEq_comp_toAnalyticSpaceι _ _ rfl
    have key : ((E.restrictPiece hV' hsub).emb ≫
          IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal) (J := E.ideal)
            ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
            (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl) ≫
          E.ideal.toAnalyticSpaceι =
        (KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) ≫
          E.emb) ≫ E.ideal.toAnalyticSpaceι :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun k => (E.restrictPiece hV' hsub).emb ≫ k) e).trans
          ((E.restrictPiece_emb_comp_quotientι_comp_ambientInclHom hV' hsub).trans
            (Category.assoc _ _ _).symm))
    exact key
  have h₁ : (E.restrictPiece hV' hsub).embInv ≫ (E.restrictPiece hV' hsub).emb = 𝟙 _ :=
    (E.restrictPiece hV' hsub).emb_comp_embInv
  have h₂ : E.emb ≫ E.embInv = 𝟙 _ := E.embInv_comp_emb
  have inner : (E.restrictPiece hV' hsub).emb ≫
      (IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal) (J := E.ideal)
        ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
        (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl ≫ E.embInv) =
      KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ E.embInv) hemb).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
            (openOf_le_openOf hV' hsub) ≫ k) h₂).trans (Category.comp_id _))))
  exact (Category.id_comp _).symm.trans
    ((congrArg (fun k => k ≫ (IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal)
        (J := E.ideal) ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
        (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl ≫ E.embInv)) h₁.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (E.restrictPiece hV' hsub).embInv ≫ k) inner)))

/-- **The inverse embedding of the padded restricted piece is carried to the inverse embedding of
the padded piece** by `homOfPullbackEq` along the padded inclusion of ambients
(`isPullbackOf_ambientTriple_padAlong_restrictPiece`, `PadRestrict.lean`), over the inclusion of
the pieces `X|V' → X|V` — the pad square, the restrict square and `embInv_padAlong` twice. -/
theorem PieceEmbedding.embInv_comp_homOfPullbackEq_padAlong_restrictPiece {n' : ℕ}
    (σ : Fin n ↪ Fin n') :
    (IdealSheaf.homOfPullbackEq (J' := ((E.restrictPiece hV' hsub).padAlong σ).ideal)
        (J := (E.padAlong σ).ideal) ⇑(pieceAmbientIncl
        (padOpens_mono σ (E.restrictAmbient_le hV'))) (pieceAmbientIncl (padOpens_mono σ
        (E.restrictAmbient_le
        hV'))).contMDiff (padIdeal_comap σ (E.restrictAmbient_le hV') E.ideal)) ≫
        (E.padAlong σ).embInv =
      ((E.restrictPiece hV' hsub).padAlong σ).embInv ≫ (show
          (X.restrictSet V' ⟶ X.restrictSet
          V) from KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
          (openOf_le_openOf hV' hsub)) := by
  have hpad : IdealSheaf.homOfPullbackEq _ _ (padIdeal_comap σ (E.restrictAmbient_le hV') E.ideal) ≫
        padSliceHom σ E.ideal =
      padSliceHom σ
          (Manifold.IdealSheaf.pullback _ (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff
          E.ideal) ≫
        IdealSheaf.homOfPullbackEq (J' := E.ideal.pullback _ (pieceAmbientIncl
            (E.restrictAmbient_le hV')).contMDiff) (J := E.ideal)
          ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
          (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl :=
    padSliceHom_comp_homOfPullbackEq_pieceAmbientIncl σ (E.restrictAmbient_le hV') E.ideal
  have hres : IdealSheaf.homOfPullbackEq (J' := (E.restrictPiece hV' hsub).ideal) (J := E.ideal)
        ⇑(pieceAmbientIncl (E.restrictAmbient_le hV'))
        (pieceAmbientIncl (E.restrictAmbient_le hV')).contMDiff rfl ≫ E.embInv =
      (E.restrictPiece hV' hsub).embInv ≫
        KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace (openOf_le_openOf hV' hsub) :=
    E.embInv_comp_homOfPullbackEq_restrictPiece hV' hsub
  have e₁ : (E.padAlong σ).embInv = padSliceHom σ E.ideal ≫ E.embInv := E.embInv_padAlong σ
  have e₂ : ((E.restrictPiece hV' hsub).padAlong σ).embInv =
      padSliceHom σ (E.restrictPiece hV' hsub).ideal ≫ (E.restrictPiece hV' hsub).embInv :=
    (E.restrictPiece hV' hsub).embInv_padAlong σ
  exact (congrArg (fun k => IdealSheaf.homOfPullbackEq _ _
      (padIdeal_comap σ (E.restrictAmbient_le hV') E.ideal) ≫ k) e₁).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ E.embInv) hpad).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => padSliceHom σ (E.restrictPiece hV' hsub).ideal ≫ k) hres).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun k => k ≫ KLocallyRingedSpace.restrictIncl X.toKLocallyRingedSpace
                (openOf_le_openOf hV' hsub)) e₂.symm))))))

end PieceSquares

end Hironaka.Manifold

end
