/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Hom
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The shear's opens see the same points of the piece

Kollár's Lemma 39 [Kol07, Lemma 39] read on the shear of `exists_padded_equivalence_hom`
(`PieceLemma39Hom.lean`): two embeddings `F₁`, `F₂` of one piece `X|V` (of one dimension), opens
`W₁`, `W₂` of their ambients, a SURJECTIVE analytic map `g : W₁ → W₂` carrying the restricted ideal
of `F₂` to that of `F₁` (`hI`) with the morphism identity `hmor` — "`g` induces the identity of the
piece over `W₁`, read through the two embeddings" — see the same points: a point of the piece whose
`F₂`-ambient point lies in `W₂` has its `F₁`-ambient point in `W₁`. (The converse is the shear's
point clause `hpt`.) The argument: the point of `Sp(𝓘₂|W₂)` over the `F₂`-ambient point exists
(`restrictedIdealHom` is `homOfPullbackEq` along the inclusion, `range_toFun_homOfPullbackEq`), it
is the image under `homOfPullbackEq g` of a point of `Sp(𝓘₁|W₁)` (`g` a surjective local
isomorphism), `hmor` reads that point down to the SAME point of the piece, and
`ambient_comp_embInv_restrictedIdealHom` says its `F₁`-ambient point is the point's coordinate in
`W₁`.

Used by `ShearBaseOpens.lean`: the base open of the padded first piece over the shear's shrunken
open EQUALS the base open of the padded second piece over its image. Not in the sources;
bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.PieceEmbedding

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {k : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (F₁ F₂ : PieceEmbedding 𝕜 k X V)
  (W₁ : Opens (pieceAmbient.{u} 𝕜 F₁.G)) (W₂ : Opens (pieceAmbient.{u} 𝕜 F₂.G))
  (g : AnalyticMap ((pieceAmbient.{u} 𝕜 F₁.G).restrict W₁)
    ((pieceAmbient.{u} 𝕜 F₂.G).restrict W₂))

/-- **The shear's opens see the same points of the piece** ([Kol07, Lemma 39] read on the shear)
— for a surjective `g : W₁ → W₂` with the ideal identity `hI` and the morphism identity `hmor` (the
two read-down maps of `Sp(𝓘₁|W₁)` to the piece agree), a point of the piece whose `F₂`-ambient
point lies in `W₂` has its `F₁`-ambient point in `W₁`. -/
theorem ambientPoint_mem_of_shear (hg : Function.Surjective g)
    (hloc : IsLocalDiffeomorph 𝓘(𝕜, Fin k → 𝕜) 𝓘(𝕜, Fin k → 𝕜) ω g)
    (hI : F₁.restrictedIdeal W₁ = (F₂.restrictedIdeal W₂).pullback ⇑g g.contMDiff)
    (hmor : ((IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI) ≫ (F₂.restrictedIdealHom W₂)) ≫
        F₂.embInv =
      F₁.restrictedIdealHom W₁ ≫ F₁.embInv)
    (y : X.restrictSet V) (hy : F₂.ambientPoint y ∈ W₂) : F₁.ambientPoint y ∈ W₁ := by
  -- the point of `Sp(𝓘₂|W₂)` over the `F₂`-ambient point of `y`
  have hz₂ : F₂.emb y ∈
      Set.range ⇑(F₂.restrictedIdealHom W₂) := by
    rw [restrictedIdealHom,
      range_toFun_homOfPullbackEq _ (isLocalDiffeomorph_inclusion (pieceAmbient.{u} 𝕜 F₂.G) W₂)]
    exact ⟨⟨F₂.ambientPoint y, hy⟩, rfl⟩
  obtain ⟨z₂, hz₂⟩ := hz₂
  -- it is the image of a point of `Sp(𝓘₁|W₁)` under `homOfPullbackEq g` (`g` surjective)
  have hz₁ : z₂ ∈ Set.range ⇑(IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI) := by
    rw [range_toFun_homOfPullbackEq _ hloc]
    exact hg _
  obtain ⟨z₁, hz₁⟩ := hz₁
  -- `hmor` reads `z₁` down to `y`
  have h1 :
      ((IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI ≫ F₂.restrictedIdealHom
          W₂) ≫ F₂.embInv) z₁ = y := by
    change F₂.embInv
      ((F₂.restrictedIdealHom W₂)
        ((IdealSheaf.homOfPullbackEq ⇑g g.contMDiff hI) z₁)) = y
    rw [hz₁, hz₂]
    exact congrArg (fun k => k y) F₂.embInv_comp_emb
  rw [hmor] at h1
  -- the `F₁`-ambient point of the read-down of `z₁` is `z₁`'s coordinate, a point of `W₁`
  have h2 := congrArg (fun k => k z₁)
    (F₁.ambient_comp_embInv_restrictedIdealHom W₁)
  change F₁.ambientPoint ((F₁.restrictedIdealHom W₁ ≫ F₁.embInv) z₁) =
    ((F₁.restrictedIdeal W₁).toAnalyticSpaceι
        z₁).1 at h2
  rw [h1] at h2
  rw [h2]
  exact ((F₁.restrictedIdeal W₁).toAnalyticSpaceι z₁).2

end Hironaka.Manifold.PieceEmbedding

end
