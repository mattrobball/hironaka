/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
import Hironaka.AnalyticSpace.Glue.Normalize
import Hironaka.AnalyticSpace.Glue.OverProper
import Hironaka.AnalyticSpace.Manifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The part of a glued space over a base open subset is the part of the piece

Over `V_i` the glued space `Ṽ` of [Wlo09, §4] is `Ṽ_i`: for a gluing datum `G : GlueOver X R π dom`
and an open subset `P ≤ dom i`, the open immersion `ιGlued i` carries the part of the `i`-th piece
over `P` onto the part of the glued space over `P` (`range_ofRestrict_comp_ιGlued`, from
`mem_range_toFun_ιGlued_iff` of `Hironaka.AnalyticSpace.Glue.OverProper`), hence
`partIso : (R i)|π_i⁻¹P ≅ Ṽ|des⁻¹P`, an isomorphism over `X` (`partIso_over`,
`partIso_inv_comp_over`). Through it, statements about a glued local resolution over a base open
subset are read on the piece (`Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep`,
`ResolutionOnMembers`, `LocalModel`, `AmbientLift`, `AmbientFactorization`).
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K} {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace}
  {dom : ι → Opens X} (G : GlueOver X R π dom) [Countable ι]

/-- **The part of the `i`-th piece over `P ≤ dom i` maps onto the part of the glued space over `P`**
under `ιGlued i`: a point of the glued space over `P ⊆ dom i` comes from the `i`-th piece
(`mem_range_toFun_ιGlued_iff`), from a point over `P`. -/
theorem range_ofRestrict_comp_ιGlued (i : ι) (P : Opens X) (hP : P ≤ dom i) :
    range (KLocallyRingedSpace.Hom.toFun (ofRestrict (R i).toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun
            (π i)⟩ P) ≫ G.ιGlued i)) =
      range (KLocallyRingedSpace.Hom.toFun (ofRestrict G.gluedOver.toKLocallyRingedSpace
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap,
            Hom.continuous_toFun G.descMap⟩ P))) := by
  rw [range_toFun_ofRestrict]
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    change KLocallyRingedSpace.Hom.toFun G.descMap (KLocallyRingedSpace.Hom.toFun
        (G.ιGlued i) y.1) ∈ P
    rw [G.toFun_descMap_ιGlued]
    exact y.2
  · intro hz
    obtain ⟨y, rfl⟩ := (G.mem_range_toFun_ιGlued_iff i z).mpr (hP hz)
    refine ⟨Subtype.mk y ?_, rfl⟩
    change KLocallyRingedSpace.Hom.toFun (π i) y ∈ P
    rw [← G.toFun_descMap_ιGlued]
    exact hz

/-- The open immersion of the part of the `i`-th piece over `P` into the glued space. -/
theorem isOpenImmersion_ofRestrict_comp_ιGlued (i : ι) (P : Opens X) :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion (ofRestrict (R i).toKLocallyRingedSpace
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun
          (π i)⟩ P) ≫ G.ιGlued i).1 :=
  inferInstanceAs (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
    ((ofRestrict (R i).toKLocallyRingedSpace
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P)).1 ≫
          (G.ιGlued i).1))

/-- **The part of the glued space over `P ≤ dom i` is the part of the `i`-th piece over `P`**
(`isoOfRangeEq` on `ofRestrict ≫ ιGlued i`; [Wlo09, §4]). -/
def partIso (i : ι) (P : Opens X) (hP : P ≤ dom i) :
    (R i).toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun (π i)⟩ P) ≅
      G.gluedOver.toKLocallyRingedSpace.restrictOpen
        (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap, Hom.continuous_toFun G.descMap⟩ P) :=
  have := G.isOpenImmersion_ofRestrict_comp_ιGlued i P
  isoOfRangeEq _ _ (G.range_ofRestrict_comp_ιGlued i P hP)

/-- The identification, followed by the open immersion of the part of the glued space, is the open
immersion of the part of the piece followed by `ιGlued i`. -/
theorem partIso_hom_comp_ofRestrict (i : ι) (P : Opens X) (hP : P ≤ dom i) :
    (G.partIso i P hP).hom ≫ ofRestrict _ _ = ofRestrict _ _ ≫ G.ιGlued i := by
  have := G.isOpenImmersion_ofRestrict_comp_ιGlued i P
  exact isoOfRangeEq_hom_comp (ofRestrict (R i).toKLocallyRingedSpace
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun
          (π i)⟩ P) ≫ G.ιGlued i)
    (ofRestrict G.gluedOver.toKLocallyRingedSpace
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap, Hom.continuous_toFun G.descMap⟩ P))
    (G.range_ofRestrict_comp_ιGlued i P hP)

/-- Its inverse, followed by `ofRestrict ≫ ιGlued i`, is the open immersion of the part of the
glued space. -/
theorem partIso_inv_comp_ofRestrict (i : ι) (P : Opens X) (hP : P ≤ dom i) :
    (G.partIso i P hP).inv ≫ ofRestrict _ _ ≫ G.ιGlued i = ofRestrict _ _ := by
  have := G.isOpenImmersion_ofRestrict_comp_ιGlued i P
  exact Glue.isoOfRangeEq_inv_comp (ofRestrict (R i).toKLocallyRingedSpace
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun (π i), Hom.continuous_toFun
          (π i)⟩ P) ≫ G.ιGlued i)
    (ofRestrict G.gluedOver.toKLocallyRingedSpace
      (Opens.comap ⟨KLocallyRingedSpace.Hom.toFun G.descMap, Hom.continuous_toFun G.descMap⟩ P))
    (G.range_ofRestrict_comp_ιGlued i P hP)

/-- The identification lies over `X`: `π i` on the part of the piece is `des` on the part of the
glued space. -/
theorem partIso_over (i : ι) (P : Opens X) (hP : P ≤ dom i) :
    ofRestrict _ _ ≫ π i = ((G.partIso i P hP).hom ≫ ofRestrict _ _) ≫ G.descMap := by
  rw [G.partIso_hom_comp_ofRestrict, Category.assoc, G.ιGlued_descMap]

/-- The inverse identification lies over `X`. -/
theorem partIso_inv_comp_over (i : ι) (P : Opens X) (hP : P ≤ dom i) :
    (G.partIso i P hP).inv ≫ ofRestrict _ _ ≫ π i = ofRestrict _ _ ≫ G.descMap :=
  calc (G.partIso i P hP).inv ≫ ofRestrict _ _ ≫ π i
      = (G.partIso i P hP).inv ≫ ofRestrict _ _ ≫ G.ιGlued i ≫ G.descMap := by
        rw [G.ιGlued_descMap]
    _ = ((G.partIso i P hP).inv ≫ ofRestrict _ _ ≫ G.ιGlued i) ≫ G.descMap := by
        simp only [Category.assoc]
    _ = ofRestrict _ _ ≫ G.descMap := by rw [G.partIso_inv_comp_ofRestrict]

end AnalyticSpace.GlueOver

end
