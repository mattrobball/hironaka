/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Gluing data for `K`-spaces along transition isomorphisms

A family of `K`-local-ringed spaces `Y i`, open subsets `W i j ⊆ Y i` with `W i i = ⊤`,
`K`-morphisms `t i j : Y i | W i j ⟶ Y j | W j i` with `t i i = 𝟙`, mapping the points of
`W i j ∩ W i k` into `W j k`, and satisfying the cocycle condition as morphisms on the triple
overlaps (`KGlueCore`, `KGlueData`), define gluing data for locally ringed spaces in Mathlib's sense
(`LocallyRingedSpace.GlueData`, `KGlueData.toLRSGlueData`): the pieces `V (i, j) = Y i | W i j`, the
open immersions `f i j = ofRestrict`, the transitions `t i j`, and the transitions `t' i j k` on the
pullbacks `V (i, j) ×_{U i} V (i, k)`, obtained by conjugating the restricted transition maps
`tRes i j k : Y i | (W i j ⊓ W i k) ⟶ Y j | (W j k ⊓ W j i)` through the canonical isomorphisms of
the pullbacks with the meets (`pbIso`). Mathlib has a pointwise constructor only for topological
gluing (`TopCat.GlueData.mk'`); this is its analogue for `K`-spaces, after the pattern of
`AlgebraicGeometry.Scheme.Cover.gluedCover`.

Conventions. The cocycle condition is required for the restricted maps `tRes`, which are defined
from the `t i j` by the universal property of the open immersions
(`LocallyRingedSpace.IsOpenImmersion.lift`); it is proved in practice by cancelling the monomorphism
`ofRestrict` and using the pointwise identities. The pullback `pullback (f i j) (f i k)` is
identified with `Y i | (W i j ⊓ W i k)` by `pbIso`, whose inverse is the pair of inclusions of the
meet into the two open subsets. A single piece has `W = ⊤`, `t = 𝟙`, and the glued space is the
piece; disjoint pieces (`W i j = ⊥` for `i ≠ j`) have empty transitions, and the glued space is the
disjoint union.

This is the categorical input of the gluing of local complexifications into a complexification (the
theorem of Bruhat and Whitney [BW59, Proposition 1], cited by Hironaka in [Hir64, Ch. 0, §1, p. 120,
footnote 7]; the cocycle on a neighbourhood follows the pattern of the proof of [Car57, §3,
Proposition 2]), and of the gluing of local resolutions over a base
(`Hironaka.AnalyticSpace.Glue.Over`). The glued `K`-space is built in
`Hironaka.AnalyticSpace.Glue.KSpace`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- The inclusion of opens composed with the open immersion of the larger open is the open
immersion of the smaller one. -/
@[reassoc (attr := simp)]
theorem restrictOpenIncl_comp_ofRestrict (A : KLocallyRingedSpace.{u} K) {U U' : Opens A}
    (h : U ≤ U') : restrictOpenIncl A h ≫ ofRestrict A U' = ofRestrict A U := by
  rw [restrictOpenIncl, Hom.restrictTo_comp_ofRestrict, Category.comp_id]

/-- Gluing data for `K`-spaces along transition morphisms of open subsets (isomorphisms once the
cocycle identity of `KGlueData` holds): the pieces, the open subsets, the transitions with their
compatibility on points. -/
structure KGlueCore (K : Type) [RCLike K] where
  /-- The index type. -/
  J : Type u
  /-- The pieces. -/
  Y : J → KLocallyRingedSpace.{u} K
  /-- The open subset `W i j ⊆ Y i` glued to `Y j`. -/
  W : ∀ i, J → Opens (Y i)
  W_id : ∀ i, W i i = ⊤
  /-- The transition `K`-morphisms. -/
  t : ∀ i j, (Y i).restrictOpen (W i j) ⟶ (Y j).restrictOpen (W j i)
  t_id : ∀ i, t i i = 𝟙 _
  /-- The transition from `i` to `j` maps the points of `W i k` into `W j k`. -/
  t_inter : ∀ i j k (x : (Y i).restrictOpen (W i j)), x.1 ∈ W i k → (KLocallyRingedSpace.Hom.toFun
      (t i j) x).1 ∈ W j k

namespace KGlueCore

variable (D : KGlueCore.{u} K)

/-- The transition `t i j` on the meet `W i j ⊓ W i k`, landing in `W j k ⊓ W j i`. -/
noncomputable def tRes (i j k : D.J) :
    (D.Y i).restrictOpen (D.W i j ⊓ D.W i k) ⟶ (D.Y j).restrictOpen (D.W j k ⊓ D.W j i) :=
  have h₁ : LocallyRingedSpace.IsOpenImmersion (ofRestrict (D.Y j) (D.W j k ⊓ D.W j i)).1 :=
    inferInstance
  have hr : Set.range (restrictOpenIncl (D.Y i) (inf_le_left (b := D.W i k)) ≫ D.t i j ≫
      ofRestrict (D.Y j) (D.W j i)).1.base ⊆
      Set.range (ofRestrict (D.Y j) (D.W j k ⊓ D.W j i)).1.base := by
    rintro _ ⟨x, rfl⟩
    have hx : (KLocallyRingedSpace.Hom.toFun (D.t i j) (KLocallyRingedSpace.Hom.toFun
        (restrictOpenIncl (D.Y i) inf_le_left) x)).1 ∈
        D.W j k := by
      apply D.t_inter i j k
      have : (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl (D.Y i) (inf_le_left (b :=
          D.W i k))) x).1 = x.1 :=
        Hom.toFun_restrictTo (𝟙 (D.Y i)) _ _ _ x
      rw [this]
      exact x.2.2
    refine ⟨⟨(KLocallyRingedSpace.Hom.toFun (D.t i j) (KLocallyRingedSpace.Hom.toFun
        (restrictOpenIncl (D.Y i) inf_le_left) x)).1,
      hx, (KLocallyRingedSpace.Hom.toFun (D.t i j) (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl
          (D.Y i) inf_le_left) x)).2⟩, rfl⟩
  Hom.ofFac (restrictOpenIncl (D.Y i) inf_le_left ≫ D.t i j ≫ ofRestrict (D.Y j) (D.W j i))
    (ofRestrict (D.Y j) (D.W j k ⊓ D.W j i))
    (LocallyRingedSpace.IsOpenImmersion.lift (H := h₁) (ofRestrict (D.Y j) (D.W j k ⊓ D.W j i)).1
      (restrictOpenIncl (D.Y i) inf_le_left ≫ D.t i j ≫ ofRestrict (D.Y j) (D.W j i)).1 hr)
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁) _ _ _)

theorem tRes_comp_ofRestrict (i j k : D.J) :
    D.tRes i j k ≫ ofRestrict (D.Y j) (D.W j k ⊓ D.W j i) =
      restrictOpenIncl (D.Y i) inf_le_left ≫ D.t i j ≫ ofRestrict (D.Y j) (D.W j i) :=
  Hom.ext (by
    rw [Hom.comp_val, tRes, Hom.ofFac_val]
    exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)

/-- The restricted transition followed by the inclusion of the meet into `W j i` is the inclusion
into `W i j` followed by the transition. -/
theorem tRes_comp_restrictOpenIncl (i j k : D.J) :
    D.tRes i j k ≫ restrictOpenIncl (D.Y j) (inf_le_right (a := D.W j k)) =
      restrictOpenIncl (D.Y i) (inf_le_left (b := D.W i k)) ≫ D.t i j := by
  apply Hom.ext
  have h : LocallyRingedSpace.IsOpenImmersion (ofRestrict (D.Y j) (D.W j i)).1 := inferInstance
  rw [← cancel_mono (ofRestrict (D.Y j) (D.W j i)).1]
  have e₁ := congrArg Subtype.val (D.tRes_comp_ofRestrict i j k)
  have e₂ := congrArg Subtype.val (restrictOpenIncl_comp_ofRestrict (D.Y j)
    (inf_le_right (a := D.W j k) (b := D.W j i)))
  simp only [Hom.comp_val] at e₁ e₂ ⊢
  rw [Category.assoc, e₂, e₁, Category.assoc]

/-- The open immersion of the piece `V (i, j) = Y i | W i j` into `Y i`, as a morphism of locally
ringed spaces. -/
noncomputable abbrev f (i j : D.J) :
    ((D.Y i).restrictOpen (D.W i j)).toLocallyRingedSpace ⟶ (D.Y i).toLocallyRingedSpace :=
  (ofRestrict (D.Y i) (D.W i j)).1

instance (i j : D.J) : LocallyRingedSpace.IsOpenImmersion (D.f i j) :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (ofRestrict (D.Y i) (D.W i j)).1)

/-- The points of the pullback of `V (i, j)` and `V (i, k)` land in the meet `W i j ⊓ W i k`. -/
theorem range_pullback_fst_subset (i j k : D.J) :
    Set.range (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j).base ⊆
      Set.range (ofRestrict (D.Y i) (D.W i j ⊓ D.W i k)).1.base := by
  rintro _ ⟨p, rfl⟩
  have hcond := congrArg (fun φ => φ.base p) (pullback.condition (f := D.f i j) (g := D.f i k))
  simp only [LocallyRingedSpace.comp_base] at hcond
  have h₁ : ((pullback.fst (D.f i j) (D.f i k)).base p).1 ∈ D.W i j :=
    ((pullback.fst (D.f i j) (D.f i k)).base p).2
  have h₂ : ((pullback.fst (D.f i j) (D.f i k)).base p).1 ∈ D.W i k := by
    have : ((pullback.fst (D.f i j) (D.f i k)).base p).1 =
        ((pullback.snd (D.f i j) (D.f i k)).base p).1 := hcond
    rw [this]
    exact ((pullback.snd (D.f i j) (D.f i k)).base p).2
  exact ⟨⟨_, h₁, h₂⟩, rfl⟩

/-- From the pullback of `V (i, j)` and `V (i, k)` over `Y i` to the meet
`Y i | (W i j ⊓ W i k)`. -/
noncomputable def pbToRes (i j k : D.J) :
    pullback (D.f i j) (D.f i k) ⟶
      ((D.Y i).restrictOpen (D.W i j ⊓ D.W i k)).toLocallyRingedSpace :=
  LocallyRingedSpace.IsOpenImmersion.lift (ofRestrict (D.Y i) (D.W i j ⊓ D.W i k)).1
    (pullback.fst (D.f i j) (D.f i k) ≫ D.f i j) (D.range_pullback_fst_subset i j k)

theorem pbToRes_comp_ofRestrict (i j k : D.J) :
    D.pbToRes i j k ≫ (ofRestrict (D.Y i) (D.W i j ⊓ D.W i k)).1 =
      pullback.fst (D.f i j) (D.f i k) ≫ D.f i j :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _

/-- From the meet to the pullback: the pair of inclusions. -/
noncomputable def resToPb (i j k : D.J) :
    ((D.Y i).restrictOpen (D.W i j ⊓ D.W i k)).toLocallyRingedSpace ⟶
      pullback (D.f i j) (D.f i k) :=
  pullback.lift (restrictOpenIncl (D.Y i) inf_le_left).1 (restrictOpenIncl (D.Y i) inf_le_right).1
    (by
      have e₁ := congrArg Subtype.val (restrictOpenIncl_comp_ofRestrict (D.Y i)
        (inf_le_left (a := D.W i j) (b := D.W i k)))
      have e₂ := congrArg Subtype.val (restrictOpenIncl_comp_ofRestrict (D.Y i)
        (inf_le_right (a := D.W i j) (b := D.W i k)))
      simp only [Hom.comp_val] at e₁ e₂
      exact e₁.trans e₂.symm)

@[simp]
theorem resToPb_fst (i j k : D.J) :
    D.resToPb i j k ≫ pullback.fst (D.f i j) (D.f i k) = (restrictOpenIncl (D.Y i) inf_le_left).1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem resToPb_snd (i j k : D.J) :
    D.resToPb i j k ≫ pullback.snd (D.f i j) (D.f i k) =
      (restrictOpenIncl (D.Y i) inf_le_right).1 :=
  pullback.lift_snd _ _ _

/-- The pullback of two pieces over `Y i` is the meet of their opens. -/
noncomputable def pbIso (i j k : D.J) :
    pullback (D.f i j) (D.f i k) ≅
      ((D.Y i).restrictOpen (D.W i j ⊓ D.W i k)).toLocallyRingedSpace where
  hom := D.pbToRes i j k
  inv := D.resToPb i j k
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, resToPb_fst, Category.id_comp]
      have h : LocallyRingedSpace.IsOpenImmersion (D.f i j) := inferInstance
      rw [← cancel_mono (D.f i j), Category.assoc]
      have e := congrArg Subtype.val (restrictOpenIncl_comp_ofRestrict (D.Y i)
        (inf_le_left (a := D.W i j) (b := D.W i k)))
      simp only [Hom.comp_val] at e
      rw [e]
      exact D.pbToRes_comp_ofRestrict i j k
    · rw [Category.assoc, resToPb_snd, Category.id_comp]
      have h : LocallyRingedSpace.IsOpenImmersion (D.f i k) := inferInstance
      rw [← cancel_mono (D.f i k), Category.assoc]
      have e := congrArg Subtype.val (restrictOpenIncl_comp_ofRestrict (D.Y i)
        (inf_le_right (a := D.W i j) (b := D.W i k)))
      simp only [Hom.comp_val] at e
      rw [e, ← pullback.condition]
      exact D.pbToRes_comp_ofRestrict i j k
  inv_hom_id := by
    have h : LocallyRingedSpace.IsOpenImmersion (ofRestrict (D.Y i) (D.W i j ⊓ D.W i k)).1 :=
      inferInstance
    rw [← cancel_mono (ofRestrict (D.Y i) (D.W i j ⊓ D.W i k)).1, Category.assoc,
      D.pbToRes_comp_ofRestrict, ← Category.assoc, resToPb_fst, Category.id_comp]
    have e := congrArg Subtype.val (restrictOpenIncl_comp_ofRestrict (D.Y i)
      (inf_le_left (a := D.W i j) (b := D.W i k)))
    simp only [Hom.comp_val] at e
    exact e

theorem pbIso_inv_fst (i j k : D.J) :
    (D.pbIso i j k).inv ≫ pullback.fst (D.f i j) (D.f i k) =
      (restrictOpenIncl (D.Y i) inf_le_left).1 :=
  D.resToPb_fst i j k

theorem pbIso_inv_snd (i j k : D.J) :
    (D.pbIso i j k).inv ≫ pullback.snd (D.f i j) (D.f i k) =
      (restrictOpenIncl (D.Y i) inf_le_right).1 :=
  D.resToPb_snd i j k

theorem pbIso_hom_incl (i j k : D.J) :
    (D.pbIso i j k).hom ≫ (restrictOpenIncl (D.Y i) (inf_le_left (b := D.W i k))).1 =
      pullback.fst (D.f i j) (D.f i k) := by
  rw [← D.pbIso_inv_fst i j k, Iso.hom_inv_id_assoc]

end KGlueCore

/-- Gluing data with the cocycle condition on the restricted transitions. -/
structure KGlueData (K : Type) [RCLike K] extends KGlueCore.{u} K where
  cocycle : ∀ i j k, toKGlueCore.tRes i j k ≫ toKGlueCore.tRes j k i ≫ toKGlueCore.tRes k i j = 𝟙 _

namespace KGlueData

variable (D : KGlueData.{u} K)

/-- The identity piece `Y i | ⊤ ⟶ Y i` is an isomorphism. -/
theorem isIso_f_id (i : D.J) : IsIso (D.f i i) := by
  have hW := D.W_id i
  have key : ∀ (W : Opens (D.Y i)), W = ⊤ → IsIso (ofRestrict (D.Y i) W).1 := by
    rintro W rfl
    have : LocallyRingedSpace.IsOpenImmersion (𝟙 (D.Y i) : D.Y i ⟶ D.Y i).1 :=
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (D.Y i).toLocallyRingedSpace))
    have e : (restrictOpenTopIso (D.Y i)).hom = ofRestrict (D.Y i) ⊤ := by
      have := isoOfRangeEq_hom_comp (ofRestrict (D.Y i) ⊤) (𝟙 (D.Y i))
        (by rw [range_toFun_ofRestrict, Hom.toFun_id, Set.range_id]; rfl)
      rw [Category.comp_id] at this
      exact this
    rw [← e]
    exact KIso.isIso_hom_val (restrictOpenTopIso (D.Y i))
  exact key _ hW

/-- The transition on the pullbacks: the restricted transition, conjugated by the identifications
of the pullbacks with the meets. -/
noncomputable def t' (i j k : D.J) :
    pullback (D.f i j) (D.f i k) ⟶ pullback (D.f j k) (D.f j i) :=
  (D.pbIso i j k).hom ≫ (D.tRes i j k).1 ≫ (D.pbIso j k i).inv

theorem t'_fac (i j k : D.J) :
    D.t' i j k ≫ pullback.snd (D.f j k) (D.f j i) =
      pullback.fst (D.f i j) (D.f i k) ≫ (D.t i j).1 := by
  rw [t', Category.assoc, Category.assoc, D.pbIso_inv_snd, ← D.pbIso_hom_incl i j k, Category.assoc]
  congr 1
  have e := congrArg Subtype.val (D.tRes_comp_restrictOpenIncl i j k)
  simp only [Hom.comp_val] at e
  exact e

theorem t'_cocycle (i j k : D.J) : D.t' i j k ≫ D.t' j k i ≫ D.t' k i j = 𝟙 _ := by
  simp only [t', Category.assoc, Iso.inv_hom_id_assoc]
  have e := congrArg Subtype.val (D.cocycle i j k)
  simp only [Hom.comp_val, Hom.id_val] at e
  have e' : (D.tRes i j k).1 ≫ (D.tRes j k i).1 ≫ (D.tRes k i j).1 = 𝟙 _ := e
  rw [reassoc_of% e']
  exact Iso.hom_inv_id _

/-- The gluing data in Mathlib's categorical form. -/
noncomputable def toGlueData : CategoryTheory.GlueData LocallyRingedSpace.{u} where
  J := D.J
  U i := (D.Y i).toLocallyRingedSpace
  V p := ((D.Y p.1).restrictOpen (D.W p.1 p.2)).toLocallyRingedSpace
  f i j := D.f i j
  f_mono i j := inferInstance
  f_hasPullback i j k := inferInstance
  f_id i := D.isIso_f_id i
  t i j := (D.t i j).1
  t_id i := by rw [D.t_id i]; rfl
  t' i j k := D.t' i j k
  t_fac i j k := D.t'_fac i j k
  cocycle i j k := D.t'_cocycle i j k

/-- The gluing data of locally ringed spaces. -/
noncomputable def toLRSGlueData : LocallyRingedSpace.GlueData where
  toGlueData := D.toGlueData
  f_open i j := inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (D.f i j))

end KGlueData

end AnalyticSpace.Glue
