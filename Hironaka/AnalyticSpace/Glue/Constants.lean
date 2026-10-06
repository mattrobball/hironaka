/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Space
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Sections on the images of the pieces of a glued space

Building blocks for the `K`-structure of the glued space of `K`-gluing data
(`Hironaka.AnalyticSpace.Glue.Space`): the sheaf component `(ι i).c.app O` of the open immersion of
a piece is an isomorphism for every open subset `O` inside the image of the piece (Mathlib's `c_iso`
on the image of its preimage), hence injective on sections there (`c_app_injective_of_le`); and the
points of the glued space are described through the pieces: Mathlib describes the points of a
topological gluing (`TopCat.GlueData.ι_eq_iff_rel`), and the glued locally ringed space differs from
the topological gluing by the comparison isomorphisms of the three gluing layers, composed here into
one homeomorphism `topIso` and transported pointwise, so that two points of pieces with the same
image come from a point of the overlap piece (`exists_of_ι_base_eq`) and the preimage in the `i`-th
piece of the image of the `j`-th is `W i j` (`map_pieceOpens_eq`).

Conventions. `D.ι i`, `D.pieceOpens`, `D.constOn` are those of `Hironaka.AnalyticSpace.Glue.Space`;
`opensFunctor` is Mathlib's image functor of an open immersion. For `O = pieceOpens i` the sheaf
component is the isomorphism `c_iso ⊤`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue.KGlueData

universe u

variable {K : Type} [RCLike K] (D : KGlueData.{u} K)

/-- An open of the glued space inside the image of the `i`-th piece is the image of its preimage. -/
theorem pieceOpens_map_eq_of_le {i : D.J} (O : Opens D.glued) (hO : O ≤ D.pieceOpens i) :
    (LocallyRingedSpace.IsOpenImmersion.opensFunctor (D.ι i)).obj ((Opens.map (D.ι i).base).obj O)
      = O := by
  apply Opens.ext
  refine Set.image_preimage_eq_of_subset ?_
  intro z hz
  obtain ⟨y, hy⟩ := (D.mem_pieceOpens_iff i z).mp (hO hz)
  exact ⟨y, hy⟩

/-- The sheaf component of the open immersion of a piece is an isomorphism on the opens inside the
image of the piece. -/
theorem isIso_c_app_of_le {i : D.J} (O : Opens D.glued) (hO : O ≤ D.pieceOpens i) :
    IsIso ((D.ι i).c.app (op O)) := by
  rw [← D.pieceOpens_map_eq_of_le O hO]
  exact (inferInstance : PresheafedSpace.IsOpenImmersion (D.ι i).1).c_iso _

/-- The sheaf component of the open immersion of a piece is injective on the sections of an open
inside the image of the piece. -/
theorem c_app_injective_of_le {i : D.J} (O : Opens D.glued) (hO : O ≤ D.pieceOpens i) :
    Function.Injective ((D.ι i).c.app (op O)).hom := by
  have := D.isIso_c_app_of_le O hO
  exact ((ConcreteCategory.isIso_iff_bijective _).mp this).injective

/-! ### Points of the glued space: the overlaps come from the pieces `V (i, j)`

Mathlib describes the points of a topological gluing (`TopCat.GlueData.ι_eq_iff_rel`); the glued
locally ringed space differs from the topological gluing by the comparison isomorphisms of the
three gluing layers, composed here into one homeomorphism and transported pointwise. -/

instance (i j k : D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.J) :
    PreservesLimit
      (cospan (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f i j)
        (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f i k))
      (PresheafedSpace.forget CommRingCat) := by
  have := D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.f_open i j
  exact PresheafedSpace.IsOpenImmersion.forget_preservesLimitsOfLeft _ _

/-- The comparison between the topological gluing and the underlying space of the glued locally
ringed space: the composite of Mathlib's `gluedIso` (presheafed → topological), `isoPresheafedSpace`
and `isoSheafedSpace`. -/
noncomputable def topIso :
    D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.glued
      ≅ D.glued.toTopCat :=
  (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.gluedIso
      (PresheafedSpace.forget CommRingCat)).symm ≪≫
    (PresheafedSpace.forget CommRingCat).mapIso
      D.toLRSGlueData.toSheafedSpaceGlueData.isoPresheafedSpace.symm ≪≫
    (SheafedSpace.forget CommRingCat).mapIso D.toLRSGlueData.isoSheafedSpace.symm

/-- The base map of a piece's open immersion is the topological gluing's structure map followed by
the comparison. -/
theorem ι_base_eq_topIso (i : D.J) :
    (D.ι i).base =
      D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.ι i
        ≫ D.topIso.hom := by
  have h₁ : (D.ι i).base = (D.toLRSGlueData.toSheafedSpaceGlueData.toGlueData.ι i).hom.base ≫
      D.toLRSGlueData.isoSheafedSpace.inv.hom.base :=
    (congrArg (fun φ => φ.hom.base) (D.toLRSGlueData.ι_isoSheafedSpace_inv i)).symm
  have h₂ : (D.toLRSGlueData.toSheafedSpaceGlueData.toGlueData.ι i).hom.base =
      (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.ι i).base ≫
        D.toLRSGlueData.toSheafedSpaceGlueData.isoPresheafedSpace.inv.base :=
    (congrArg (fun φ => φ.base)
      (D.toLRSGlueData.toSheafedSpaceGlueData.ι_isoPresheafedSpace_inv i)).symm
  have h₃ : (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.ι i).base =
      D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.toGlueData.ι i
        ≫ (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.gluedIso
          (PresheafedSpace.forget CommRingCat)).inv :=
    (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.ι_gluedIso_inv
      (PresheafedSpace.forget CommRingCat) i).symm
  rw [h₁, h₂, h₃]
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

/-- Two points of pieces with the same image in the glued space come from a point of the overlap
piece `V (i, j)`: `x = f i j v` and `y = f j i (t i j v)`. -/
theorem exists_of_ι_base_eq {i j : D.J} {x : D.Y i} {y : D.Y j}
    (h : (D.ι i).base x = (D.ι j).base y) :
    ∃ v : (D.Y i).restrictOpen (D.W i j),
      (D.f i j).base v = x ∧ (D.f j i).base ((D.t i j).1.base v) = y := by
  have hx := congrArg (fun φ => φ x) (D.ι_base_eq_topIso i)
  have hy := congrArg (fun φ => φ y) (D.ι_base_eq_topIso j)
  have hinj : Function.Injective D.topIso.hom := (TopCat.homeoOfIso D.topIso).injective
  have h' := hinj (hx.symm.trans (h.trans hy))
  obtain ⟨v, hv₁, hv₂⟩ :=
    (D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData.ι_eq_iff_rel
      i j x y).mp h'
  exact ⟨v, hv₁, hv₂⟩

/-- The preimage in the `i`-th piece of the image of the `j`-th piece is the open `W i j`. -/
theorem map_pieceOpens_eq (i j : D.J) :
    (Opens.map (D.ι i).base).obj (D.pieceOpens j) = D.W i j := by
  apply Opens.ext
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (D.mem_pieceOpens_iff j _).mp hx
    obtain ⟨v, hv, -⟩ := D.exists_of_ι_base_eq hy.symm
    rw [← hv]
    exact v.2
  · intro hx
    refine (D.mem_pieceOpens_iff j _).mpr ⟨(D.f j i).base ((D.t i j).1.base ⟨x, hx⟩), ?_⟩
    have hg := congrArg (fun φ => φ.base ⟨x, hx⟩)
      (D.toLRSGlueData.toGlueData.glue_condition i j)
    exact hg

end AnalyticSpace.Glue.KGlueData
