/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Equality of morphisms of locally ringed spaces is local on the source

Two morphisms of locally ringed spaces that agree after restriction to every member of an open
cover of the source are equal: their base maps agree pointwise, and their stalk maps agree
because the stalk map of a composite is the composite of the stalk maps (`stalkMap_comp`) and the
stalk map of the open immersion `X | U → X` is an isomorphism, so Mathlib's
`SheafedSpace.hom_stalk_ext` applies. The `K`-morphism form follows since the `K`-condition is a
proposition (`Hom.ext`). This is the uniqueness half of the gluing of morphisms along an open
cover (`Hironaka/AnalyticSpace/HomGlue.lean` is the existence half), used for the uniqueness of the
lift in Hironaka's universal mapping property (**) of a monoidal transformation
[Hir64, Ch. 0, §2]: a lift is determined locally.

Stated for general locally ringed spaces and `K`-local-ringed spaces. Mathlib has
`LocallyRingedSpace.GlueData`, `IsOpenImmersion.lift` and `TopCat.Sheaf.existsUnique_gluing'` but
no locality lemma for morphisms out of a space covered by opens; `SheafedSpace.hom_stalk_ext` is
the ingredient.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AnalyticSpace

/-- Equality of morphisms of locally ringed spaces is local on the source: if `f` and `g` agree
after restriction to every member of an open cover, they are equal. -/
theorem LocallyRingedSpace.hom_ext_of_cover {X Y : LocallyRingedSpace.{u}} (f g : X ⟶ Y)
    {ι : Type*} (U : ι → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, X.ofRestrict (U i).isOpenEmbedding ≫ f = X.ofRestrict (U i).isOpenEmbedding ≫ g) :
    f = g := by
  have hb : f.base = g.base := by
    ext x
    obtain ⟨i, hi⟩ := hU x
    have := congrArg (fun φ : X.restrict (U i).isOpenEmbedding ⟶ Y => φ.base ⟨x, hi⟩) (h i)
    exact this
  obtain ⟨⟨fb, fc⟩, fp⟩ := f
  obtain ⟨⟨gb, gc⟩, gp⟩ := g
  obtain rfl : fb = gb := hb
  have key : ∀ x, (⟨⟨fb, fc⟩, fp⟩ : X ⟶ Y).stalkMap x = (⟨⟨fb, gc⟩, gp⟩ : X ⟶ Y).stalkMap x := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    have h1 : HEq ((X.ofRestrict (U i).isOpenEmbedding ≫ (⟨⟨fb, fc⟩, fp⟩ : X ⟶ Y)).stalkMap ⟨x, hi⟩)
        ((X.ofRestrict (U i).isOpenEmbedding ≫ (⟨⟨fb, gc⟩, gp⟩ : X ⟶ Y)).stalkMap ⟨x, hi⟩) := by
      rw [h i]
    have h2 := eq_of_heq h1
    have e₁ := LocallyRingedSpace.stalkMap_comp (X.ofRestrict (U i).isOpenEmbedding)
      (⟨⟨fb, fc⟩, fp⟩ : X ⟶ Y) ⟨x, hi⟩
    have e₂ := LocallyRingedSpace.stalkMap_comp (X.ofRestrict (U i).isOpenEmbedding)
      (⟨⟨fb, gc⟩, gp⟩ : X ⟶ Y) ⟨x, hi⟩
    have h3 := e₁.symm.trans (h2.trans e₂)
    have hoi : LocallyRingedSpace.IsOpenImmersion (X.ofRestrict (U i).isOpenEmbedding) :=
      LocallyRingedSpace.IsOpenImmersion.ofRestrict X (U i).isOpenEmbedding
    have : IsIso ((X.ofRestrict (U i).isOpenEmbedding).stalkMap ⟨x, hi⟩) :=
      LocallyRingedSpace.IsOpenImmersion.stalk_iso (X.ofRestrict (U i).isOpenEmbedding) ⟨x, hi⟩
    exact (cancel_mono ((X.ofRestrict (U i).isOpenEmbedding).stalkMap ⟨x, hi⟩)).mp h3
  have h3 : (⟨fb, fc⟩ : X.toSheafedSpace ⟶ Y.toSheafedSpace) = ⟨fb, gc⟩ :=
    SheafedSpace.hom_stalk_ext _ _ rfl fun x => by
      rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
      exact key x
  have hc : fc = gc := by
    have := congrArg (fun φ : X.toSheafedSpace ⟶ Y.toSheafedSpace => φ.hom) h3
    exact eq_of_heq (PresheafedSpace.Hom.mk.inj this).2
  subst hc
  rfl

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- Equality of `K`-morphisms is local on the source: `K`-morphisms that agree after restriction
to every member of an open cover are equal (`Hom.ext` and the locally-ringed-space statement). -/
theorem hom_ext_of_cover {X Y : KLocallyRingedSpace.{u} K} (f g : X ⟶ Y) {ι : Type*}
    (U : ι → Opens X) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, ofRestrict X (U i) ≫ f = ofRestrict X (U i) ≫ g) : f = g :=
  Hom.ext (LocallyRingedSpace.hom_ext_of_cover f.1 g.1 U hU fun i => congrArg Subtype.val (h i))

end KLocallyRingedSpace

end AnalyticSpace
