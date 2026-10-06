/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Incl
public import Hironaka.AnalyticSpace.Glue.Desc
import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.AnalyticSpace.StalkMapLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A `K`-space is the gluing of any open cover of itself

For a `K`-space `Y` and a family of open subsets `U : J → Opens Y`, the `K`-gluing data
`coverData Y U` (`Hironaka.AnalyticSpace.Glue.Data`) has pieces `Y | U i`, open subsets
`W i j = (U i)⁻¹ (U j)` and the identity transitions (the two double restrictions
`(Y | U i) | W i j` and `(Y | U j) | W j i` are both the trace of `U i ⊓ U j`, so they are
canonically `K`-isomorphic over `Y`: `coverT`). Its glued `K`-space maps to `Y` (`gluedCoverDesc`,
the universal property of the multicoequalizer), and when the `U i` cover `Y` this map is an open
immersion with full range, hence a `K`-isomorphism (`coverIso`), with
`ιK i ≫ coverIso.hom = ofRestrict Y (U i)`. This is how the complexified space `X(ℂ)` is presented
as a glued space in the gluing of local complexifications (`Hironaka.AnalyticSpace.Glue.Morphism`),
so that a morphism out of it is assembled from morphisms on the pieces by the universal property.

Conventions. Every identity between the transitions is proved by cancelling the monomorphic
inclusions into `Y` (`hom_ext_of_comp_eq`): all the maps of `coverData` are the identity of `Y` on
points. The descent morphism is an open immersion by Mathlib's
`LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` (an open embedding of the base with isomorphic
stalk maps, both read off from `ι i ≫ gluedCoverDesc = ofRestrict`). One open subset `U = ⊤` gives
the glued space `Y | ⊤`, isomorphic to `Y` (`restrictOpenTopIso`); the empty family gives the empty
glued space, which covers `Y` only if `Y` is empty. Not in the sources.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K] (Y : KLocallyRingedSpace.{u} K) {J : Type u} (U : J → Opens Y)

/-- The open of the piece `Y | U i` glued to `Y | U j`: the trace of `U j`. -/
def coverW (i j : J) : Opens (Y.restrictOpen (U i)) :=
  (Opens.map (ofRestrict Y (U i)).1.base).obj (U j)

theorem mem_coverW {i j : J} {x : Y.restrictOpen (U i)} : x ∈ coverW Y U i j ↔ x.1 ∈ U j :=
  Iff.rfl

theorem range_toFun_incl₂_coverW (i j : J) :
    Set.range (KLocallyRingedSpace.Hom.toFun (incl₂ Y (U i) (coverW Y U i j))) =
        (U i : Set Y) ∩ U j := by
  ext y
  rw [mem_range_toFun_incl₂]
  constructor
  · rintro ⟨h, hW⟩
    exact ⟨h, hW⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, h'⟩

/-- The identity transition between the two traces of `U i ⊓ U j`. -/
noncomputable def coverT (i j : J) :
    (Y.restrictOpen (U i)).restrictOpen (coverW Y U i j) ⟶
      (Y.restrictOpen (U j)).restrictOpen (coverW Y U j i) :=
  liftAlong (incl₂ Y (U j) (coverW Y U j i)) (incl₂ Y (U i) (coverW Y U i j)) (by
    rw [range_toFun_incl₂_coverW, range_toFun_incl₂_coverW, Set.inter_comm])

theorem coverT_comp_incl₂ (i j : J) :
    coverT Y U i j ≫ incl₂ Y (U j) (coverW Y U j i) = incl₂ Y (U i) (coverW Y U i j) :=
  liftAlong_comp _ _ _

theorem toFun_coverT (i j : J) (x : (Y.restrictOpen (U i)).restrictOpen (coverW Y U i j)) :
    (KLocallyRingedSpace.Hom.toFun (coverT Y U i j) x).1.1 = x.1.1 :=
  toFun_liftAlong (incl₂ Y (U j) (coverW Y U j i)) (incl₂ Y (U i) (coverW Y U i j)) _ x

/-- The `K`-gluing core of an open cover: pieces `Y | U i`, identity transitions. -/
noncomputable abbrev coverCore : KGlueCore.{u} K where
  J := J
  Y i := Y.restrictOpen (U i)
  W i j := coverW Y U i j
  W_id i := by
    apply Opens.ext
    exact Set.eq_univ_of_forall fun x => x.2
  t i j := coverT Y U i j
  t_id i := by
    apply hom_ext_of_comp_eq (incl₂ Y (U i) (coverW Y U i i))
    rw [coverT_comp_incl₂, Category.id_comp]
  t_inter i j k x hx := by
    change (KLocallyRingedSpace.Hom.toFun (coverT Y U i j) x).1.1 ∈ U k
    rw [toFun_coverT]
    exact hx

theorem coverCore_t (i j : J) : (coverCore Y U).t i j = coverT Y U i j := rfl

/-- The restricted transitions of the cover core are the identity of `Y` on points: they commute
with the inclusions into `Y`. -/
theorem coverCore_tRes_comp_incl₂ (i j k : J) :
    (coverCore Y U).tRes i j k ≫ incl₂ Y (U j) (coverW Y U j k ⊓ coverW Y U j i) =
      incl₂ Y (U i) (coverW Y U i j ⊓ coverW Y U i k) := by
  have h₁ := congrArg (fun φ => φ ≫ ofRestrict Y (U j))
    ((coverCore Y U).tRes_comp_ofRestrict i j k)
  have h₂ : (restrictOpenIncl (Y.restrictOpen (U i)) (inf_le_left (b := coverW Y U i k)) ≫
      coverT Y U i j ≫ ofRestrict (Y.restrictOpen (U j)) (coverW Y U j i)) ≫ ofRestrict Y (U j) =
      incl₂ Y (U i) (coverW Y U i j ⊓ coverW Y U i k) := by
    rw [Category.assoc, Category.assoc]
    change restrictOpenIncl (Y.restrictOpen (U i)) _ ≫ coverT Y U i j ≫
      incl₂ Y (U j) (coverW Y U j i) = _
    rw [coverT_comp_incl₂]
    change restrictOpenIncl (Y.restrictOpen (U i)) _ ≫
      ofRestrict (Y.restrictOpen (U i)) (coverW Y U i j) ≫ ofRestrict Y (U i) =
      ofRestrict (Y.restrictOpen (U i)) (coverW Y U i j ⊓ coverW Y U i k) ≫ ofRestrict Y (U i)
    rw [← Category.assoc, restrictOpenIncl_comp_ofRestrict]
  exact (Category.assoc _ _ _).symm.trans (h₁.trans h₂)

/-- The `K`-gluing data of an open cover. -/
noncomputable abbrev coverData : KGlueData.{u} K where
  toKGlueCore := coverCore Y U
  cocycle i j k :=
    hom_ext_of_comp_eq (incl₂ Y (U i) (coverW Y U i j ⊓ coverW Y U i k)) (by
      have h₁ := congrArg (fun φ => (coverCore Y U).tRes i j k ≫ (coverCore Y U).tRes j k i ≫ φ)
        (coverCore_tRes_comp_incl₂ Y U k i j)
      have h₂ := congrArg (fun φ => (coverCore Y U).tRes i j k ≫ φ)
        (coverCore_tRes_comp_incl₂ Y U j k i)
      have h₃ := coverCore_tRes_comp_incl₂ Y U i j k
      have hassoc : ((coverCore Y U).tRes i j k ≫ (coverCore Y U).tRes j k i ≫
          (coverCore Y U).tRes k i j) ≫ incl₂ Y (U i) (coverW Y U i j ⊓ coverW Y U i k) =
          (coverCore Y U).tRes i j k ≫ (coverCore Y U).tRes j k i ≫
          ((coverCore Y U).tRes k i j ≫ incl₂ Y (U i) (coverW Y U i j ⊓ coverW Y U i k)) := by
        simp only [Category.assoc]
      exact hassoc.trans (h₁.trans (h₂.trans (h₃.trans (Category.id_comp _).symm))))

/-! ### The descent to `Y` -/

theorem coverData_compat (i j : J) :
    (coverData Y U).f i j ≫ (ofRestrict Y (U i)).1 =
      (((coverData Y U).t i j).1 ≫ (coverData Y U).f j i) ≫ (ofRestrict Y (U j)).1 :=
  ((Category.assoc _ _ _).trans (congrArg Subtype.val (coverT_comp_incl₂ Y U i j))).symm

/-- The descent of the inclusions `Y | U i ⟶ Y` to the glued `K`-space of the cover. -/
noncomputable def gluedCoverDesc : (coverData Y U).gluedK ⟶ Y :=
  (coverData Y U).descK (fun i => ofRestrict Y (U i)) (coverData_compat Y U)

theorem ιK_gluedCoverDesc (i : J) :
    (coverData Y U).ιK i ≫ gluedCoverDesc Y U = ofRestrict Y (U i) :=
  (coverData Y U).ιK_descK _ _ i

theorem toFun_gluedCoverDesc_ιK (i : J) (y : Y.restrictOpen (U i)) :
    KLocallyRingedSpace.Hom.toFun (gluedCoverDesc Y U) (KLocallyRingedSpace.Hom.toFun
        ((coverData Y U).ιK i) y) = y.1 :=
  (coverData Y U).toFun_descK_ιK _ _ i y

theorem gluedCoverDesc_injective : Function.Injective (KLocallyRingedSpace.Hom.toFun
    (gluedCoverDesc Y U)) := by
  intro z z' h
  obtain ⟨i, y, rfl⟩ := (coverData Y U).exists_ι_base_eq z
  obtain ⟨j, y', rfl⟩ := (coverData Y U).exists_ι_base_eq z'
  have hyy' : y.1 = y'.1 := by
    have h₁ := toFun_gluedCoverDesc_ιK Y U i y
    have h₂ := toFun_gluedCoverDesc_ιK Y U j y'
    exact h₁.symm.trans (h.trans h₂)
  have hy : y ∈ coverW Y U i j := by
    change y.1 ∈ U j
    rw [hyy']
    exact y'.2
  have hglue := congrArg (fun φ => φ.base (⟨y, hy⟩ : (Y.restrictOpen (U i)).restrictOpen
    (coverW Y U i j))) ((coverData Y U).toLRSGlueData.toGlueData.glue_condition i j)
  have hpt : ((coverData Y U).f j i).base (((coverData Y U).t i j).1.base ⟨y, hy⟩) = y' := by
    apply Subtype.ext
    exact (toFun_coverT Y U i j ⟨y, hy⟩).trans hyy'
  change ((coverData Y U).ι i).base y = ((coverData Y U).ι j).base y'
  rw [← hpt]
  exact hglue.symm

theorem gluedCoverDesc_surjective (hU : ∀ y : Y, ∃ i, y ∈ U i) :
    Function.Surjective (KLocallyRingedSpace.Hom.toFun (gluedCoverDesc Y U)) := by
  intro y
  obtain ⟨i, hi⟩ := hU y
  exact ⟨KLocallyRingedSpace.Hom.toFun ((coverData Y U).ιK i) ⟨y, hi⟩,
      toFun_gluedCoverDesc_ιK Y U i ⟨y, hi⟩⟩

theorem isOpenMap_gluedCoverDesc : IsOpenMap (KLocallyRingedSpace.Hom.toFun
    (gluedCoverDesc Y U)) := by
  intro O hO
  have himage : KLocallyRingedSpace.Hom.toFun (gluedCoverDesc Y U) '' O =
      ⋃ i, Subtype.val '' (((coverData Y U).ι i).base ⁻¹' O) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨i, w, rfl⟩ := (coverData Y U).exists_ι_base_eq z
      exact Set.mem_iUnion.mpr ⟨i, w, hz, (toFun_gluedCoverDesc_ιK Y U i w).symm⟩
    · intro hy
      obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨((coverData Y U).ι i).base w, hw, toFun_gluedCoverDesc_ιK Y U i w⟩
  rw [himage]
  exact isOpen_iUnion fun i => (U i).2.isOpenMap_subtype_val _
    (hO.preimage ((coverData Y U).ι i).base.hom.continuous)

theorem continuous_toFun_gluedCoverDesc : Continuous (KLocallyRingedSpace.Hom.toFun
    (gluedCoverDesc Y U)) :=
  (gluedCoverDesc Y U).1.base.hom.continuous

theorem isOpenEmbedding_gluedCoverDesc :
    Topology.IsOpenEmbedding (KLocallyRingedSpace.Hom.toFun (gluedCoverDesc Y U)) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_toFun_gluedCoverDesc Y U)
    (gluedCoverDesc_injective Y U) (isOpenMap_gluedCoverDesc Y U)

theorem isIso_stalkMap_gluedCoverDesc (z : (coverData Y U).glued) :
    IsIso ((gluedCoverDesc Y U).1.stalkMap z) := by
  obtain ⟨i, y, rfl⟩ := (coverData Y U).exists_ι_base_eq z
  have key : ∀ {φ ψ : (Y.restrictOpen (U i)).toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace},
      φ = ψ → IsIso (ψ.stalkMap y) → IsIso (φ.stalkMap y) := by
    rintro φ ψ rfl hψ
    exact hψ
  have h₁ : IsIso (((coverData Y U).ι i ≫ (gluedCoverDesc Y U).1).stalkMap y) :=
    key ((coverData Y U).ι_descLRS (fun i => ofRestrict Y (U i)) (coverData_compat Y U) i)
      ((ConcreteCategory.isIso_iff_bijective _).mpr (bijective_stalkMap_ofRestrict Y (U i) y))
  have h₂ := (congrArg (fun φ => IsIso φ)
    (LocallyRingedSpace.stalkMap_comp ((coverData Y U).ι i) (gluedCoverDesc Y U).1 y)).mp h₁
  have h₃ : IsIso (((coverData Y U).ι i).stalkMap y) := inferInstance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h₃ h₂

instance isOpenImmersion_gluedCoverDesc :
    LocallyRingedSpace.IsOpenImmersion (gluedCoverDesc Y U).1 :=
  have : ∀ z, IsIso ((gluedCoverDesc Y U).1.stalkMap z) := isIso_stalkMap_gluedCoverDesc Y U
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ (isOpenEmbedding_gluedCoverDesc Y U)

theorem range_toFun_gluedCoverDesc (hU : ∀ y : Y, ∃ i, y ∈ U i) :
    Set.range (KLocallyRingedSpace.Hom.toFun (gluedCoverDesc Y U)) = Set.range
        (KLocallyRingedSpace.Hom.toFun (𝟙 Y)) := by
  rw [(gluedCoverDesc_surjective Y U hU).range_eq]
  exact Set.range_id.symm

/-- A `K`-space is `K`-isomorphic to the glued `K`-space of any open cover of itself. -/
noncomputable def coverIso (hU : ∀ y : Y, ∃ i, y ∈ U i) : KIso (coverData Y U).gluedK Y :=
  haveI : LocallyRingedSpace.IsOpenImmersion (𝟙 Y : Y ⟶ Y).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 Y.toLocallyRingedSpace))
  isoOfRangeEq (gluedCoverDesc Y U) (𝟙 Y) (range_toFun_gluedCoverDesc Y U hU)

theorem coverIso_hom (hU : ∀ y : Y, ∃ i, y ∈ U i) : (coverIso Y U hU).hom = gluedCoverDesc Y U :=
  haveI : LocallyRingedSpace.IsOpenImmersion (𝟙 Y : Y ⟶ Y).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 Y.toLocallyRingedSpace))
  (Category.comp_id _).symm.trans (isoOfRangeEq_hom_comp (gluedCoverDesc Y U) (𝟙 Y) _)

theorem ιK_comp_coverIso_hom (hU : ∀ y : Y, ∃ i, y ∈ U i) (i : J) :
    (coverData Y U).ιK i ≫ (coverIso Y U hU).hom = ofRestrict Y (U i) := by
  rw [coverIso_hom, ιK_gluedCoverDesc]

end AnalyticSpace.Glue
