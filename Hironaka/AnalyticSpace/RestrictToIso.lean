/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.OpenSubspaceLemmas
public import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.Glue.Normalize
import Hironaka.AnalyticSpace.LiftRestrictStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Local isomorphisms of `K`-local-ringed spaces on points and stalks

If the restriction `φ|U : X|U → Y|V` of a `K`-morphism `φ : X → Y` is a `K`-isomorphism, then `φ`
is injective on `U`, maps open subsets of `U` to open subsets of `Y`, and has bijective stalk maps
at the points of `U`. Also the hom equations of the double-restriction isomorphism
`(X|U)|V ≅ X|(imageOpens U V)` (`restrictOpen_restrictOpen_iso`). Routine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

theorem KIso.homeomorph_apply {A B : KLocallyRingedSpace.{u} K} (e : KIso A B) (a : A) :
    KIso.homeomorph e a = Hom.toFun e.hom a := rfl

section IsoOfRangeEq

variable {A B X : KLocallyRingedSpace.{u} K} (a : A ⟶ X) (b : B ⟶ X)
  [LocallyRingedSpace.IsOpenImmersion a.1] [LocallyRingedSpace.IsOpenImmersion b.1]
  (h : Set.range (Hom.toFun a) = Set.range (Hom.toFun b))

end IsoOfRangeEq

section DoubleRestrict

variable (X : KLocallyRingedSpace.{u} K) (U : Opens X) (V : Opens (X.restrictOpen U))

theorem imageOpens_le : imageOpens U V ≤ U := by
  rintro _ ⟨v, rfl⟩
  exact v.1.2

@[reassoc]
theorem restrictOpen_restrictOpen_iso_inv_comp :
    (restrictOpen_restrictOpen_iso U V).inv ≫ ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U =
      ofRestrict X (imageOpens U V) :=
  Glue.isoOfRangeEq_inv_comp _ _ _

end DoubleRestrict

section LocalIso

variable {A B : KLocallyRingedSpace.{u} K} (φ : A ⟶ B) (U : Opens A) (V : Opens B)
  (hUV : ∀ u ∈ U, Hom.toFun φ u ∈ V) [IsIso (Hom.restrictTo φ U V hUV)]

/-- The homeomorphism `U ≃ₜ V` underlying the local isomorphism. -/
def restrictToHomeomorph : A.restrictOpen U ≃ₜ B.restrictOpen V :=
  KIso.homeomorph (asIso (Hom.restrictTo φ U V hUV))

theorem restrictToHomeomorph_apply_val (u : A.restrictOpen U) :
    (restrictToHomeomorph φ U V hUV u).1 = Hom.toFun φ u.1 := by
  rw [restrictToHomeomorph, KIso.homeomorph_apply, asIso_hom]
  exact Hom.toFun_restrictTo φ U V hUV u

include V hUV in
/-- A local isomorphism is injective on `U`. -/
theorem injOn_toFun_of_isIso_restrictTo : Set.InjOn (Hom.toFun φ) U := by
  intro u₁ hu₁ u₂ hu₂ heq
  have h : restrictToHomeomorph φ U V hUV ⟨u₁, hu₁⟩ = restrictToHomeomorph φ U V hUV ⟨u₂, hu₂⟩ :=
    Subtype.ext ((restrictToHomeomorph_apply_val φ U V hUV ⟨u₁, hu₁⟩).trans
      (heq.trans (restrictToHomeomorph_apply_val φ U V hUV ⟨u₂, hu₂⟩).symm))
  exact congrArg Subtype.val ((restrictToHomeomorph φ U V hUV).injective h)

include V hUV in
/-- A local isomorphism maps open subsets of `U` to open subsets of `B`. -/
theorem isOpen_image_of_isIso_restrictTo {S : Set A} (hS : IsOpen S) :
    IsOpen (Hom.toFun φ '' (S ∩ U)) := by
  have hset : Hom.toFun φ '' (S ∩ U) =
      Subtype.val '' ((restrictToHomeomorph φ U V hUV) ''
        ((Subtype.val : A.restrictOpen U → A) ⁻¹' S)) := by
    ext b
    constructor
    · rintro ⟨u, ⟨huS, huU⟩, rfl⟩
      refine ⟨restrictToHomeomorph φ U V hUV ⟨u, huU⟩, ⟨⟨u, huU⟩, huS, rfl⟩, ?_⟩
      exact restrictToHomeomorph_apply_val φ U V hUV ⟨u, huU⟩
    · rintro ⟨v, ⟨u, huS, rfl⟩, rfl⟩
      refine ⟨u.1, ⟨huS, u.2⟩, ?_⟩
      exact (restrictToHomeomorph_apply_val φ U V hUV u).symm
  rw [hset]
  exact V.isOpen.isOpenMap_subtype_val _
    ((restrictToHomeomorph φ U V hUV).isOpenMap _ (hS.preimage continuous_subtype_val))

include V hUV in
/-- A local isomorphism has bijective stalk maps at the points of `U`. -/
theorem bijective_stalkMap_of_isIso_restrictTo (u : A) (hu : u ∈ U) :
    Function.Bijective (φ.1.stalkMap u).hom := by
  have h1 : Function.Bijective ((Hom.restrictTo φ U V hUV).1.stalkMap ⟨u, hu⟩).hom :=
    bijective_stalkMap_of_isIso _ _
  have h2 := (bijective_stalkMap_iff_of_comp_eq _ _ (Hom.restrictTo_comp_ofRestrict φ U V hUV)
    ⟨u, hu⟩).mp h1
  have h3 := LocallyRingedSpace.stalkMap_comp (ofRestrict A U).1 φ.1 ⟨u, hu⟩
  rw [Hom.comp_val, h3] at h2
  have ho : Function.Bijective ((ofRestrict A U).1.stalkMap ⟨u, hu⟩).hom :=
    have := KLocallyRingedSpace.isIso_ofRestrict_stalkMap A U ⟨u, hu⟩
    ConcreteCategory.bijective_of_isIso _
  exact (Function.Bijective.of_comp_iff' ho _).mp h2

end LocalIso

end AnalyticSpace.KLocallyRingedSpace
