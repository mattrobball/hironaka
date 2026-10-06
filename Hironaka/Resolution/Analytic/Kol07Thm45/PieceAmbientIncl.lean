/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceLemma39Model
import Hironaka.AnalyticSpace.Manifold.Sigma
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceModel
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The one-piece ambient: the inclusion of a smaller open

An open embedding of germs `Y_Z ⊂ Y_{Z'}` extends to an open embedding `U_Z ⊂ U_{Z'}` of the
ambient opens [Wlo09, §4, (3)⇒(4)]: the ambient of a restricted piece embedding is a smaller open
`G' ≤ G`, and the one-piece ambients `Sp(G') → Sp(G)` (`pieceAmbient`) include accordingly. This
module builds that inclusion as an analytic map, an open embedding and a local analytic
isomorphism (a diffeomorphism onto the coordinate preimage of `G'`), and the image of an open
under it.

* `coordPreimage G' G`: the points of `Sp(G)` with coordinates in `G'`;
* `pieceAmbientIncl h : AnalyticMap (pieceAmbient 𝕜 G') (pieceAmbient 𝕜 G)`, with
  `pieceCoord_pieceAmbientIncl` (the identity on coordinates), `pieceAmbientIncl_injective`;
* `pieceAmbientInclDiffeo h`: the same map as a diffeomorphism onto `(pieceAmbient 𝕜 G).restrict
  (coordPreimage G' G)`; hence `isLocalDiffeomorph_pieceAmbientIncl` (a diffeomorphism followed by
  the inclusion of an open, `isLocalDiffeomorph_inclusion`);
* `pieceAmbientImageOpens h W'`: the image of an open of `Sp(G')`, an open of `Sp(G)`
  (`AnalyticMap.imageOpens` of the inclusion), with
  `mem_pieceAmbientImageOpens`, `pieceAmbientImageOpens_le` and
  `isCompact_closure_pieceAmbientImageOpens` (relatively compact opens have relatively compact
  images).

Bookkeeping on the coordinate map `pieceCoord` (`PieceLemma39Model.lean`) and on
`isLocalDiffeomorph_inclusion`.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

section Incl

variable {G' G : Opens (Fin n → 𝕜)} (h : G' ≤ G)

variable (G' G) in
/-- The points of the one-piece ambient of `G` whose coordinates lie in `G'`. -/
def coordPreimage : Opens (pieceAmbient.{u} 𝕜 G) :=
  ⟨pieceCoord G ⁻¹' (G' : Set (Fin n → 𝕜)),
    G'.isOpen.preimage (contMDiff_pieceCoord G).continuous⟩

/-- Membership in `coordPreimage G' G`: the coordinate lies in `G'`. -/
theorem mem_coordPreimage {w : pieceAmbient.{u} 𝕜 G} :
    w ∈ coordPreimage G' G ↔ pieceCoord G w ∈ G' :=
  Iff.rfl

/-- The inclusion `Sp(G') → Sp(G)` on points: the same coordinates. -/
def pieceAmbientInclFun : pieceAmbient.{u} 𝕜 G' → pieceAmbient.{u} 𝕜 G :=
  fun w => ⟨PUnit.unit, ⟨pieceCoord G' w, h (pieceCoord_mem G' w)⟩⟩

/-- The inclusion of one-piece ambients preserves the coordinate. -/
theorem pieceCoord_pieceAmbientInclFun (w : pieceAmbient.{u} 𝕜 G') :
    pieceCoord G (pieceAmbientInclFun h w) = pieceCoord G' w := rfl

/-- The inclusion lands in the preimage open `coordPreimage G' G`. -/
theorem pieceAmbientInclFun_mem_coordPreimage (w : pieceAmbient.{u} 𝕜 G') :
    pieceAmbientInclFun h w ∈ coordPreimage G' G :=
  pieceCoord_mem G' w

/-- The inclusion of one-piece ambients is injective (its coordinate is). -/
theorem pieceAmbientInclFun_injective : Function.Injective (pieceAmbientInclFun.{u} h) := by
  intro w w' hw
  exact pieceCoord_injective G' (congrArg (pieceCoord G) hw)

/-- The inclusion is analytic (`ContMDiff.sigmaDesc`/`contMDiff_sigmaMk_comp_iff` on the one-point
`Σ`, the coordinate map `pieceCoord`). -/
theorem contMDiff_pieceAmbientInclFun :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbientInclFun.{u} h) := by
  have h0 : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (fun w : pieceAmbient.{u} 𝕜 G' => (⟨pieceCoord G' w, h (pieceCoord_mem G' w)⟩ : G)) :=
    (contMDiff_subtypeVal_comp_iff_of_opens (𝕜 := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜)
      (fun w : pieceAmbient.{u} 𝕜 G' => (⟨pieceCoord G' w, h (pieceCoord_mem G' w)⟩ : G))).mp
      (contMDiff_pieceCoord G')
  exact (contMDiff_sigmaMk_comp_iff (I := 𝓘(𝕜, Fin n → 𝕜)) (J := 𝓘(𝕜, Fin n → 𝕜)) (n := ω)
    (M := fun _ : PUnit.{u + 1} => (G : Type)) (P := pieceAmbient.{u} 𝕜 G') (i := PUnit.unit)
    (h := fun w : pieceAmbient.{u} 𝕜 G' => (⟨pieceCoord G' w, h (pieceCoord_mem G' w)⟩ : G))).mpr h0

/-- **The inclusion `Sp(G') → Sp(G)` of one-piece ambients** for `G' ≤ G` (the open embedding
`U_Z ⊂ U_{Z'}` of ambient opens in [Wlo09, §4, (3)⇒(4)]). -/
def pieceAmbientIncl :
    AnalyticMap (pieceAmbient.{u} 𝕜 G') (pieceAmbient.{u} 𝕜 G) :=
  ⟨pieceAmbientInclFun h, contMDiff_pieceAmbientInclFun h⟩

/-- The analytic inclusion `Sp(G') → Sp(G)` evaluates as `pieceAmbientInclFun`. -/
theorem pieceAmbientIncl_apply (w : pieceAmbient.{u} 𝕜 G') :
    pieceAmbientIncl h w = pieceAmbientInclFun h w := rfl

/-- The inclusion `Sp(G') → Sp(G)` preserves the coordinate. -/
theorem pieceCoord_pieceAmbientIncl (w : pieceAmbient.{u} 𝕜 G') :
    pieceCoord G (pieceAmbientIncl h w) = pieceCoord G' w := rfl

/-- The inclusion `Sp(G') → Sp(G)` is injective. -/
theorem pieceAmbientIncl_injective : Function.Injective (pieceAmbientIncl.{u} h) :=
  pieceAmbientInclFun_injective h

variable (G' G) in
/-- The inverse of the inclusion on its image: the same coordinates, read in `G'`. -/
def pieceAmbientInclInv : coordPreimage.{u} G' G → pieceAmbient.{u} 𝕜 G' :=
  fun v => ⟨PUnit.unit, ⟨pieceCoord G v.1, v.2⟩⟩

variable (G' G) in
/-- The inverse of the inclusion, on `coordPreimage G' G`, is analytic (a coordinate map). -/
theorem contMDiff_pieceAmbientInclInv :
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbientInclInv.{u} G' G) := by
  have h0 : ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (fun v : coordPreimage.{u} G' G => (⟨pieceCoord G v.1, v.2⟩ : G')) :=
    (contMDiff_subtypeVal_comp_iff_of_opens (𝕜 := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜)
      (fun v : coordPreimage.{u} G' G => (⟨pieceCoord G v.1, v.2⟩ : G'))).mp
      ((contMDiff_pieceCoord G).comp contMDiff_subtype_val)
  exact (contMDiff_sigmaMk_comp_iff (I := 𝓘(𝕜, Fin n → 𝕜)) (J := 𝓘(𝕜, Fin n → 𝕜)) (n := ω)
    (M := fun _ : PUnit.{u + 1} => (G' : Type)) (P := coordPreimage.{u} G' G) (i := PUnit.unit)
    (h := fun v : coordPreimage.{u} G' G => (⟨pieceCoord G v.1, v.2⟩ : G'))).mpr h0

/-- The inclusion as a diffeomorphism of `Sp(G')` onto the coordinate preimage of `G'` in
`Sp(G)`. -/
def pieceAmbientInclDiffeo :
    Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) (pieceAmbient.{u} 𝕜 G')
      ((pieceAmbient.{u} 𝕜 G).restrict (coordPreimage G' G)) ω where
  toFun w := ⟨pieceAmbientInclFun h w, pieceAmbientInclFun_mem_coordPreimage h w⟩
  invFun := pieceAmbientInclInv G' G
  left_inv := fun _ => Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (Subtype.ext rfl))
  right_inv := fun _ =>
    Subtype.ext (Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (Subtype.ext rfl)))
  contMDiff_toFun :=
    (contMDiff_subtypeVal_comp_iff_of_opens (𝕜 := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜)
      (fun w : pieceAmbient.{u} 𝕜 G' =>
        (⟨pieceAmbientInclFun h w, pieceAmbientInclFun_mem_coordPreimage h w⟩ :
          coordPreimage G' G))).mp (contMDiff_pieceAmbientInclFun h)
  contMDiff_invFun := contMDiff_pieceAmbientInclInv G' G

/-- The diffeomorphism onto `coordPreimage G' G` evaluates as the inclusion. -/
theorem pieceAmbientInclDiffeo_apply (w : pieceAmbient.{u} 𝕜 G') :
    (pieceAmbientInclDiffeo h w).1 = pieceAmbientIncl h w := rfl

/-- The inclusion is a local analytic isomorphism: the diffeomorphism onto the coordinate preimage
followed by the inclusion of that open. -/
theorem isLocalDiffeomorph_pieceAmbientIncl :
    IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (pieceAmbientIncl.{u} h) := by
  intro w
  have h1 := (pieceAmbientInclDiffeo h).isLocalDiffeomorph w
  have h2 := Manifold.isLocalDiffeomorph_inclusion (pieceAmbient.{u} 𝕜 G) (coordPreimage G' G)
    (pieceAmbientInclDiffeo h w)
  exact IsLocalDiffeomorphAt.comp (hf := h1) (hg := h2)

/-- The image of an open of `Sp(G')` in `Sp(G)` (`AnalyticMap.imageOpens` of the inclusion). -/
abbrev pieceAmbientImageOpens (W' : Opens (pieceAmbient.{u} 𝕜 G')) :
    Opens (pieceAmbient.{u} 𝕜 G) :=
  AnalyticMap.imageOpens (pieceAmbientIncl h) (isLocalDiffeomorph_pieceAmbientIncl h) W'

/-- Membership in the image open: the image of a point of `W'` under the inclusion. -/
theorem mem_pieceAmbientImageOpens {W' : Opens (pieceAmbient.{u} 𝕜 G')} {v : pieceAmbient.{u} 𝕜 G} :
    v ∈ pieceAmbientImageOpens h W' ↔ ∃ w ∈ W', pieceAmbientIncl h w = v :=
  Iff.rfl

/-- The image of the preimage of `W` lies in `W`. -/
theorem pieceAmbientImageOpens_le (W : Opens (pieceAmbient.{u} 𝕜 G))
    (W' : Opens (pieceAmbient.{u} 𝕜 G')) (hW' : ∀ w ∈ W', pieceAmbientIncl h w ∈ W) :
    pieceAmbientImageOpens h W' ≤ W := by
  rintro _ ⟨w, hw, rfl⟩
  exact hW' w hw

/-- A relatively compact open has a relatively compact image. -/
theorem isCompact_closure_pieceAmbientImageOpens (W' : Opens (pieceAmbient.{u} 𝕜 G'))
    (hW' : IsCompact (closure (W' : Set (pieceAmbient 𝕜 G')))) :
    IsCompact (closure (pieceAmbientImageOpens h W' : Set (pieceAmbient 𝕜 G))) :=
  AnalyticMap.isCompact_closure_image (pieceAmbientIncl h) hW'

end Incl

end Hironaka.Manifold

end
