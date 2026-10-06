/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PadRestrict
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlue
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.Kol07Thm45.ShearPoints
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The base opens of the padded restricted pieces

Two identities of base opens in `X` for the transition between a padded piece and a piece of the
other embedding (`CoproductMixedTransition.lean`):

* **padding and restriction commute on the base opens**: the base open of the padded piece
  `E.padAlong σ` over the image (in its ambient) of an open `Q` of the padded SHRUNK ambient of
  `E|V'` is the base open of the padded restricted piece `(E|V').padAlong σ` over `Q` — the
  ambient points correspond through `pieceAmbientIncl_padExt` (`PadRestrict.lean`) and
  `ambientPoint_padAlong`, and a point of the piece whose ambient point lies in the shrunk
  ambient's image lies in `V'` (`pieceCoord_ambientPoint_mem_restrictAmbient_iff`);
* **the shear identifies the base opens**: for two embeddings `F₁`, `F₂` of one piece with the
  shear `g : W₁ → W₂` of `exists_padded_equivalence_hom_point` (`LocalResolutionShear.lean`;
  bijective local isomorphism, the ideal identity `hI`, the morphism identity `hmor`, the point
  clause `hpt`), the base open of `F₁` over the image in its ambient of an open `Q ⊆ W₁` is the
  base open of `F₂` over the image of `g(Q)` —
  `hpt` one way, `ambientPoint_mem_of_shear` (the shear's opens see the same points) and the
  injectivity of `g` the other.

Together: the padded first piece of `sumPadData D₁ D₂` (`CoproductSumData.lean`) over the shear's
shrunken open `W₁'` and the padded second piece over `g(W₁')` lie over ONE open `P` of `X` — the
base open of that transition. Not in the sources; bookkeeping.
-/

public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff CategoryTheory

universe u

namespace Hironaka.Manifold.PieceEmbedding

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜}

section PadRestrict

variable {n : ℕ} {V V' : Set X} (E : PieceEmbedding 𝕜 n X V) (hV' : IsOpen V') (hsub : V' ⊆ V)
  {n' : ℕ} (σ : Fin n ↪ Fin n')

/-- **Padding and restriction commute on the base opens** — the base open of the padded piece
over the image of an open `Q` of the padded shrunk ambient is the base open of the padded
restricted piece over `Q`. -/
theorem domOpens_padAlong_pieceAmbientImageOpens
    (Q : Opens (pieceAmbient.{u} 𝕜 ((E.restrictPiece hV' hsub).padAlong σ).G)) :
    (E.padAlong σ).domOpens
        (pieceAmbientImageOpens (padOpens_mono σ (E.restrictAmbient_le hV')) Q) =
      ((E.restrictPiece hV' hsub).padAlong σ).domOpens Q := by
  -- the ambient point of the padded restricted piece, carried into the padded piece's ambient
  have key : ∀ y' : X.restrictSet V',
      pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV'))
          (((E.restrictPiece hV' hsub).padAlong σ).ambientPoint y') =
        (E.padAlong σ).ambientPoint ⟨Subtype.val y', val_mem_openOf hV' hsub y'⟩ := by
    intro y'
    refine (congrArg (pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV')))
      ((E.restrictPiece hV' hsub).ambientPoint_padAlong σ y')).trans ?_
    refine (pieceAmbientIncl_padExt σ (E.restrictAmbient_le hV') _).trans ?_
    refine (congrArg (padExt σ E.G)
      (E.pieceAmbientIncl_ambientPoint_restrictPiece hV' hsub y')).trans ?_
    exact (E.ambientPoint_padAlong σ _).symm
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (E.padAlong σ).mem_domOpens.mp hx
    obtain ⟨w, hw, hwy⟩ := (mem_pieceAmbientImageOpens _).mp
      (hy : (E.padAlong σ).ambientPoint y ∈ _)
    have hwy' : pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV')) w =
        padExt σ E.G (E.ambientPoint y) :=
      hwy.trans (E.ambientPoint_padAlong σ y)
    have hcoord : E.ambientPoint y =
        pieceAmbientIncl (E.restrictAmbient_le hV') (padCoordProj σ (E.restrictAmbient hV') w) := by
      have h := congrArg (padCoordProj σ E.G) hwy'
      rw [padCoordProj_pieceAmbientIncl, padCoordProj_padExt] at h
      exact h.symm
    have hyV' : Subtype.val y ∈ V' := by
      refine (E.pieceCoord_ambientPoint_mem_restrictAmbient_iff hV' y).mp ?_
      rw [hcoord, pieceCoord_pieceAmbientIncl]
      exact pieceCoord_mem _ _
    set y' : X.restrictSet V' :=
      ⟨Subtype.val y, AnalyticSpace.mem_openOf_of_subset Set.Subset.rfl hyV'⟩
    refine ((E.restrictPiece hV' hsub).padAlong σ).mem_domOpens.mpr ⟨y', ?_, rfl⟩
    have hyy : (⟨Subtype.val y', val_mem_openOf hV' hsub y'⟩ : X.restrictSet V) = y :=
      Subtype.ext rfl
    have hamb : pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV'))
        (((E.restrictPiece hV' hsub).padAlong σ).ambientPoint y') =
        pieceAmbientIncl (padOpens_mono σ (E.restrictAmbient_le hV')) w :=
      (key y').trans ((congrArg (E.padAlong σ).ambientPoint hyy).trans hwy.symm)
    change ((E.restrictPiece hV' hsub).padAlong σ).ambientPoint y' ∈ Q
    rw [pieceAmbientIncl_injective _ hamb]
    exact hw
  · intro hx
    obtain ⟨y', hy', rfl⟩ := ((E.restrictPiece hV' hsub).padAlong σ).mem_domOpens.mp hx
    refine (E.padAlong σ).mem_domOpens.mpr ⟨⟨Subtype.val y', val_mem_openOf hV' hsub y'⟩, ?_, rfl⟩
    exact (mem_pieceAmbientImageOpens _).mpr ⟨_, hy', key y'⟩

end PadRestrict

section Shear

variable {k : ℕ} {V : Set X} (F₁ F₂ : PieceEmbedding 𝕜 k X V)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 F₁.G)) (W₂ : Opens (pieceAmbient.{u} 𝕜 F₂.G))
  (g : AnalyticMap ((pieceAmbient.{u} 𝕜 F₁.G).restrict W₁)
    ((pieceAmbient.{u} 𝕜 F₂.G).restrict W₂))

/-- **The shear identifies the base opens** ([Kol07, Lemma 39] read on the shear) — the base open
of `F₁` over the image of an open `Q ⊆ W₁` is the base open of `F₂` over the image of `g(Q)`: the
point clause `hpt` one way, the shear's opens seeing the same points (`ambientPoint_mem_of_shear`)
and the injectivity of `g` the other. -/
theorem domOpens_imageOpens_eq_of_shear (hbij : Function.Bijective g)
    (hloc : IsLocalDiffeomorph 𝓘(𝕜, Fin k → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω g)
    (hI : F₁.restrictedIdeal W₁ = (F₂.restrictedIdeal W₂).pullback ⇑g g.contMDiff)
    (hmor : ((IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI) ≫ (F₂.restrictedIdealHom W₂)) ≫
        F₂.embInv =
      F₁.restrictedIdealHom W₁ ≫ F₁.embInv)
    (hpt : ∀ (y : X.restrictSet V) (hy : F₁.ambientPoint y ∈ W₁),
      (g ⟨F₁.ambientPoint y, hy⟩).1 = F₂.ambientPoint y)
    (Q : Opens ((pieceAmbient.{u} 𝕜 F₁.G).restrict W₁)) :
    F₁.domOpens (AnalyticMap.imageOpens ((pieceAmbient.{u} 𝕜 F₁.G).inclusion W₁)
        (isLocalDiffeomorph_inclusion _ W₁) Q) =
      F₂.domOpens (AnalyticMap.imageOpens (((pieceAmbient.{u} 𝕜 F₂.G).inclusion W₂).comp g)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
            (isLocalDiffeomorph_inclusion _ W₂) hloc) Q) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := F₁.mem_domOpens.mp hx
    have hy' : F₁.ambientPoint y ∈ AnalyticMap.imageOpens ((pieceAmbient.{u} 𝕜 F₁.G).inclusion W₁)
        (isLocalDiffeomorph_inclusion _ W₁) Q := hy
    obtain ⟨w, hw, hwy⟩ := hy'
    have hyW₁ : F₁.ambientPoint y ∈ W₁ := by
      rw [← hwy]
      exact w.2
    have hw' : w = ⟨F₁.ambientPoint y, hyW₁⟩ := Subtype.ext hwy
    refine F₂.mem_domOpens.mpr ⟨y, ⟨w, hw, ?_⟩, rfl⟩
    rw [hw']
    exact hpt y hyW₁
  · intro hx
    obtain ⟨y, hy, rfl⟩ := F₂.mem_domOpens.mp hx
    have hy' : F₂.ambientPoint y ∈ AnalyticMap.imageOpens
        (((pieceAmbient.{u} 𝕜 F₂.G).inclusion W₂).comp g)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
            (isLocalDiffeomorph_inclusion _ W₂) hloc) Q := hy
    obtain ⟨w, hw, hwy⟩ := hy'
    have hyW₂ : F₂.ambientPoint y ∈ W₂ := by
      rw [← hwy]
      exact (g w).2
    have hyW₁ : F₁.ambientPoint y ∈ W₁ :=
      F₁.ambientPoint_mem_of_shear F₂ W₁ W₂ g hbij.2 hloc hI hmor y hyW₂
    have hgw : g ⟨F₁.ambientPoint y, hyW₁⟩ = g w := Subtype.ext ((hpt y hyW₁).trans hwy.symm)
    have hw' : (⟨F₁.ambientPoint y, hyW₁⟩ : (pieceAmbient.{u} 𝕜 F₁.G).restrict W₁) = w :=
      hbij.1 hgw
    exact F₁.mem_domOpens.mpr ⟨y, ⟨w, hw, (congrArg Subtype.val hw').symm⟩, rfl⟩

end Shear

end Hironaka.Manifold.PieceEmbedding

end
