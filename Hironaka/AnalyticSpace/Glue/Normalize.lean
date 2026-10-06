/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Restrict
public import Hironaka.AnalyticSpace.Glue.Incl
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.Glue.Data
import Hironaka.AnalyticSpace.Manifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The restricted complexification over its inclusions

The hypotheses of the gluing of complexifications are stated for the restricted complexifications
`C.restrictLe V` of `Hironaka.AnalyticSpace.Glue.Restrict`; this module restates them in one
uniform setting, morphisms out of the complexified open subspaces `(X | V)(ℂ)` into the spaces
`Y_i`, compared after the monomorphic inclusions.

* Bridge lemmas, chiefly `Complexification.restrictLeHom_comp_ofRestrict`: `f | V` followed by the
  inclusion of its target `Y | (Y ∖ f(U ∖ V)) ⟶ Y` is the complexified inclusion
  `(X | V)(ℂ) ⟶ (X | U)(ℂ)` followed by `f`.
* `pairLift`, the lift of `f ∘ incl_V` into an open subset `Ω ∋ f(V)`, and the normalized transition
  datum `PairIso Ci Cj V`: domains `Ωi`, `Ωj` containing the images of `V` and inside the loci where
  the real points lie over `V`, a `K`-isomorphism `e : Y_i | Ωi ≅ Y_j | Ωj`, and compatibility with
  `f_i`, `f_j`; with `symm`, `refl`, and the real-point lemmas (`toFun_e_hom_val`,
  `exists_eq_of_toFun_e_hom_eq`).
* `PairIso.ofHiso`, the datum extracted from the local isomorphisms of two complexifications near
  the real points (the hypothesis `hiso` of the gluing theorem).
* `exists_eq_near_of_huniq`, the uniqueness hypothesis `huniq` of the gluing theorem in the uniform
  setting: two morphisms out of an open subset of `Y_i` containing `f_i(V)`, both compatible with
  `f_i`, `f_k`, agree on an open subset containing `f_i(V)`.

Conventions. The complexification functor `complexifyHom` (`Hironaka.AnalyticSpace.Complexify`) is
applied to the inclusion `restrictOpenIncl`; `complexifyRestrictIso` has the identity as underlying
morphism, so `complexifyRestrictIso.hom ≫ ofRestrict = complexifyHom (ofRestrict)` is an equality of
sheaf components (`complexifyRestrictIso_hom_comp_ofRestrict`); the identification
`restrictRestrictIso` is over `X` (`restrictRestrictIso_inv_comp_ofRestrict`). For `V = U`,
`restrictLeHom` is `f` transported along `X | U ≅ (X | U) | ⊤`. Not in the sources.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- The inverse of the isomorphism of two open immersions with the same range is over the
target. -/
theorem isoOfRangeEq_inv_comp {A B X : KLocallyRingedSpace.{u} K} (a : A ⟶ X) (b : B ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion a.1] [LocallyRingedSpace.IsOpenImmersion b.1]
    (h : Set.range (KLocallyRingedSpace.Hom.toFun a) = Set.range
        (KLocallyRingedSpace.Hom.toFun b)) :
    (isoOfRangeEq a b h).inv ≫ a = b := by
  have h₁ : (isoOfRangeEq a b h).inv ≫ a =
      (isoOfRangeEq a b h).inv ≫ ((isoOfRangeEq a b h).hom ≫ b) :=
    congrArg (fun φ => (isoOfRangeEq a b h).inv ≫ φ) (isoOfRangeEq_hom_comp a b h).symm
  rw [h₁, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem toFun_restrictOpenIncl (A : KLocallyRingedSpace.{u} K) {U U' : Opens A} (h : U ≤ U')
    (u : A.restrictOpen U) : KLocallyRingedSpace.Hom.toFun (restrictOpenIncl A h) u = ⟨u.1,
        h u.2⟩ :=
  Subtype.ext (Hom.toFun_restrictTo (𝟙 A) U U' _ u)

/-- Transport along an equality of opens is over the space. -/
theorem eqToIso_restrictOpen_inv_comp_ofRestrict (X : KLocallyRingedSpace.{u} K) {A B : Opens X}
    (h : A = B) : (eqToIso (congrArg X.restrictOpen h)).inv ≫ ofRestrict X A = ofRestrict X B := by
  subst h
  simp

/-- Transport along an equality of opens is over the space (hom form). -/
theorem eqToIso_restrictOpen_hom_comp_ofRestrict (X : KLocallyRingedSpace.{u} K) {A B : Opens X}
    (h : A = B) : (eqToIso (congrArg X.restrictOpen h)).hom ≫ ofRestrict X B = ofRestrict X A := by
  subst h
  simp

/-- The identification `(X | U)(ℂ) ≅ X(ℂ) | U` followed by the inclusion is the complexified
inclusion. -/
theorem complexifyRestrictIso_hom_comp_ofRestrict (X : KLocallyRingedSpace.{u} ℝ)
    [HasRealResidueFields X] (U : Opens X) :
    (complexifyRestrictIso X U).hom ≫ ofRestrict (complexify X) U =
      complexifyHom (ofRestrict X U) := by
  apply Hom.ext
  change 𝟙 _ ≫ (ofRestrict (complexify X) U).1 = (complexifyHom (ofRestrict X U)).1
  rw [Category.id_comp]
  rfl

/-- The identification `(X | U) | V ≅ X | V` is over `X`. -/
theorem restrictRestrictIso_inv_comp_ofRestrict {X : AnalyticSpace.{u} ℝ} {U : Opens X}
    (V : Opens X) (hV : V ≤ U) :
    (Complexification.restrictRestrictIso (X := X) (U := U) V hV).inv ≫
        ofRestrict (X.toKLocallyRingedSpace.restrictOpen U)
          (Complexification.pullbackOpens (X := X) (U := U) V) =
      restrictOpenIncl X.toKLocallyRingedSpace hV := by
  apply hom_ext_of_comp_eq (ofRestrict X.toKLocallyRingedSpace U)
  rw [restrictOpenIncl_comp_ofRestrict]
  unfold Complexification.restrictRestrictIso
  rw [Iso.trans_inv, Category.assoc, Category.assoc]
  have h₀ := isoOfRangeEq_inv_comp
    (ofRestrict (X.toKLocallyRingedSpace.restrictOpen U)
      (Complexification.pullbackOpens (X := X) (U := U) V) ≫ ofRestrict X.toKLocallyRingedSpace U)
    (ofRestrict X.toKLocallyRingedSpace
      (imageOpens U (Complexification.pullbackOpens (X := X) (U := U) V)))
    (by rw [range_toFun_ofRestrict]; rfl)
  change _ ≫ (restrictOpen_restrictOpen_iso U
    (Complexification.pullbackOpens (X := X) (U := U) V)).inv ≫
    (ofRestrict _ _ ≫ ofRestrict _ U) = _
  rw [restrictOpen_restrictOpen_iso, h₀]
  exact eqToIso_restrictOpen_inv_comp_ofRestrict X.toKLocallyRingedSpace
    (imageOpens_map_eq X.toKLocallyRingedSpace hV)


/-- The identification `(X | U) | V ≅ X | imageOpens U V` is over `X` (hom form). -/
theorem restrictOpen_restrictOpen_iso_hom_comp (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (V : Opens (X.restrictOpen U)) :
    (restrictOpen_restrictOpen_iso U V).hom ≫ ofRestrict X (imageOpens U V) =
      ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U := by
  unfold restrictOpen_restrictOpen_iso
  exact isoOfRangeEq_hom_comp _ _ _

/-- The identification `(X | U) | V ≅ X | imageOpens U V` is over `X` (inverse form). -/
theorem restrictOpen_restrictOpen_iso_inv_comp (X : KLocallyRingedSpace.{u} K) (U : Opens X)
    (V : Opens (X.restrictOpen U)) :
    (restrictOpen_restrictOpen_iso U V).inv ≫ (ofRestrict (X.restrictOpen U) V ≫ ofRestrict X U) =
      ofRestrict X (imageOpens U V) := by
  unfold restrictOpen_restrictOpen_iso
  exact isoOfRangeEq_inv_comp _ _ _

/-- The inclusion of `A | ⊤` is an isomorphism (`restrictOpenTopIso`). -/
theorem isIso_ofRestrict_top (A : KLocallyRingedSpace.{u} K) : IsIso (ofRestrict A ⊤) := by
  have : LocallyRingedSpace.IsOpenImmersion (𝟙 A : A ⟶ A).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 A.toLocallyRingedSpace))
  have h : (isoOfRangeEq (ofRestrict A ⊤) (𝟙 A)
      (by rw [range_toFun_ofRestrict, Hom.toFun_id, Set.range_id]; rfl)).hom = ofRestrict A ⊤ :=
    (Category.comp_id _).symm.trans (isoOfRangeEq_hom_comp _ _ _)
  rw [← h]
  infer_instance

end AnalyticSpace.Glue

namespace AnalyticSpace.Complexification

open Glue

universe u

variable {X : AnalyticSpace.{u} ℝ} {U : Opens X} (C : Complexification (X.restrictOpen U))

/-- The morphism of the restricted complexification, followed by the inclusion of its target, is
the complexified inclusion `(X | V)(ℂ) ⟶ (X | U)(ℂ)` followed by `f`. -/
theorem restrictLeHom_comp_ofRestrict (V : Opens X) (hV : V ≤ U) :
    C.restrictLeHom V hV ≫ ofRestrict C.Y.toKLocallyRingedSpace (C.restrictLeOpens V) =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) ≫ C.f := by
  have h₂ := Hom.restrictTo_comp_ofRestrict C.fK (pullbackOpens (X := X) (U := U) V)
    (C.restrictLeOpens V) (fun u hu => C.toFun_mem_restrictLeOpens u hu)
  have h₃ := complexifyRestrictIso_hom_comp_ofRestrict (X.toKLocallyRingedSpace.restrictOpen U)
    (pullbackOpens (X := X) (U := U) V)
  have h₄ : complexifyHom (restrictRestrictIso (X := X) (U := U) V hV).inv ≫
      complexifyHom (ofRestrict (X.toKLocallyRingedSpace.restrictOpen U)
        (pullbackOpens (X := X) (U := U) V)) =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) := by
    rw [← complexifyHom_comp, restrictRestrictIso_inv_comp_ofRestrict]
  have e₁ : C.restrictLeHom V hV ≫ ofRestrict C.Y.toKLocallyRingedSpace (C.restrictLeOpens V) =
      (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
        ((complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
          (pullbackOpens (X := X) (U := U) V)).hom ≫
        (Hom.restrictTo C.fK (pullbackOpens (X := X) (U := U) V) (C.restrictLeOpens V)
          (fun u hu => C.toFun_mem_restrictLeOpens u hu) ≫
          ofRestrict C.Y.toKLocallyRingedSpace (C.restrictLeOpens V))) :=
    (Category.assoc _ _ _).trans (congrArg (fun φ => _ ≫ φ) (Category.assoc _ _ _))
  have e₂ : (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
        ((complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
          (pullbackOpens (X := X) (U := U) V)).hom ≫
        (Hom.restrictTo C.fK (pullbackOpens (X := X) (U := U) V) (C.restrictLeOpens V)
          (fun u hu => C.toFun_mem_restrictLeOpens u hu) ≫
          ofRestrict C.Y.toKLocallyRingedSpace (C.restrictLeOpens V))) =
      (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
        ((complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
          (pullbackOpens (X := X) (U := U) V)).hom ≫
        (ofRestrict (complexify (X.toKLocallyRingedSpace.restrictOpen U))
          (pullbackOpens (X := X) (U := U) V) ≫ C.fK)) :=
    congrArg (fun φ => (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
      ((complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
        (pullbackOpens (X := X) (U := U) V)).hom ≫ φ)) h₂
  have e₃ : (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
        ((complexifyRestrictIso (X.toKLocallyRingedSpace.restrictOpen U)
          (pullbackOpens (X := X) (U := U) V)).hom ≫
        (ofRestrict (complexify (X.toKLocallyRingedSpace.restrictOpen U))
          (pullbackOpens (X := X) (U := U) V) ≫ C.fK)) =
      (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
        (complexifyHom (ofRestrict (X.toKLocallyRingedSpace.restrictOpen U)
          (pullbackOpens (X := X) (U := U) V)) ≫ C.fK) :=
    congrArg (fun φ => (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫ φ)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ C.fK) h₃))
  have e₄ : (complexifyIso (restrictRestrictIso (X := X) (U := U) V hV)).inv ≫
        (complexifyHom (ofRestrict (X.toKLocallyRingedSpace.restrictOpen U)
          (pullbackOpens (X := X) (U := U) V)) ≫ C.fK) =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) ≫ C.f :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ C.fK) h₄)
  exact e₁.trans (e₂.trans (e₃.trans e₄))

end AnalyticSpace.Complexification

namespace AnalyticSpace.Glue

universe u

variable {X : AnalyticSpace.{u} ℝ}

/-- On points, the complexified inclusion followed by `f` is `f`. -/
theorem toFun_complexifyIncl_comp {U : Opens X} (C : Complexification (X.restrictOpen U))
    {V : Opens X} (hV : V ≤ U) (v : X.restrictOpen V) :
    KLocallyRingedSpace.Hom.toFun (complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) ≫
        C.f) v =
      KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩ :=
  congrArg (KLocallyRingedSpace.Hom.toFun C.f) (toFun_restrictOpenIncl X.toKLocallyRingedSpace hV v)

/-- On points, the morphism of the restricted complexification is `f`. -/
theorem toFun_restrictLeHom_val {U : Opens X} (C : Complexification (X.restrictOpen U))
    (V : Opens X) (hV : V ≤ U) (v : X.restrictOpen V) :
    (KLocallyRingedSpace.Hom.toFun (C.restrictLeHom V hV) v).1 = KLocallyRingedSpace.Hom.toFun C.f
        ⟨v.1, hV v.2⟩ :=
  (congrFun (congrArg KLocallyRingedSpace.Hom.toFun (C.restrictLeHom_comp_ofRestrict V hV)) v).trans
    (toFun_complexifyIncl_comp C hV v)

theorem range_complexifyIncl_comp_subset {U : Opens X} (C : Complexification (X.restrictOpen U))
    {V : Opens X} (hV : V ≤ U) (Ω : Opens C.Y)
    (h : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩ ∈ Ω) :
    Set.range (KLocallyRingedSpace.Hom.toFun (complexifyHom (restrictOpenIncl
        X.toKLocallyRingedSpace hV) ≫ C.f)) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict C.Y.toKLocallyRingedSpace Ω)) := by
  rintro _ ⟨v, rfl⟩
  rw [range_toFun_ofRestrict]
  exact Set.mem_of_eq_of_mem (toFun_complexifyIncl_comp C hV v) (h v)

/-- The lift of `f ∘ (inclusion of V)` into the open `Ω ⊆ Y` containing `f(V)`. -/
noncomputable def pairLift {U : Opens X} (C : Complexification (X.restrictOpen U)) {V : Opens X}
    (hV : V ≤ U) (Ω : Opens C.Y) (h : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun C.f
        ⟨v.1, hV v.2⟩ ∈ Ω) :
    complexify (X.restrictOpen V).toKLocallyRingedSpace ⟶
      C.Y.toKLocallyRingedSpace.restrictOpen Ω :=
  liftAlong (ofRestrict C.Y.toKLocallyRingedSpace Ω)
    (complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) ≫ C.f)
    (range_complexifyIncl_comp_subset C hV Ω h)

theorem pairLift_comp {U : Opens X} (C : Complexification (X.restrictOpen U)) {V : Opens X}
    (hV : V ≤ U) (Ω : Opens C.Y) (h : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun C.f
        ⟨v.1, hV v.2⟩ ∈ Ω) :
    pairLift C hV Ω h ≫ ofRestrict C.Y.toKLocallyRingedSpace Ω =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) ≫ C.f :=
  liftAlong_comp _ _ _

theorem toFun_pairLift_val {U : Opens X} (C : Complexification (X.restrictOpen U)) {V : Opens X}
    (hV : V ≤ U) (Ω : Opens C.Y) (h : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun C.f
        ⟨v.1, hV v.2⟩ ∈ Ω)
    (v : X.restrictOpen V) : (KLocallyRingedSpace.Hom.toFun (pairLift C hV Ω h) v).1 =
        KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩ :=
  (congrFun (congrArg KLocallyRingedSpace.Hom.toFun (pairLift_comp C hV Ω h)) v).trans
    (toFun_complexifyIncl_comp C hV v)

/-- A normalized transition datum between two local complexifications over the open `V`: opens
`Ωi ⊆ Y_i`, `Ωj ⊆ Y_j` containing the images of `V`, inside the loci where the real points lie over
`V`, and a `K`-isomorphism `Y_i | Ωi ≅ Y_j | Ωj` compatible with `f_i` and `f_j` on `V`. -/
structure PairIso {Ui Uj : Opens X} (Ci : Complexification (X.restrictOpen Ui))
    (Cj : Complexification (X.restrictOpen Uj)) (V : Opens X) (hVi : V ≤ Ui) (hVj : V ≤ Uj) where
  /-- The domain in `Y_i`. -/
  Ωi : Opens Ci.Y
  /-- The domain in `Y_j`. -/
  Ωj : Opens Cj.Y
  /-- The transition isomorphism. -/
  e : KIso (Ci.Y.toKLocallyRingedSpace.restrictOpen Ωi) (Cj.Y.toKLocallyRingedSpace.restrictOpen Ωj)
  mem_Ωi : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩ ∈ Ωi
  mem_Ωj : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun Cj.f ⟨v.1, hVj v.2⟩ ∈ Ωj
  Ωi_le : Ωi ≤ Ci.restrictLeOpens V
  Ωj_le : Ωj ≤ Cj.restrictLeOpens V
  compat : pairLift Ci hVi Ωi mem_Ωi ≫ e.hom ≫ ofRestrict Cj.Y.toKLocallyRingedSpace Ωj =
    complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hVj) ≫ Cj.f

namespace PairIso

variable {Ui Uj : Opens X} {Ci : Complexification (X.restrictOpen Ui)}
  {Cj : Complexification (X.restrictOpen Uj)} {V : Opens X} {hVi : V ≤ Ui} {hVj : V ≤ Uj}

theorem lift_comp_hom (P : PairIso Ci Cj V hVi hVj) :
    pairLift Ci hVi P.Ωi P.mem_Ωi ≫ P.e.hom = pairLift Cj hVj P.Ωj P.mem_Ωj :=
  liftAlong_unique _ _ _ _ ((Category.assoc _ _ _).trans P.compat)

/-- On the image of a point of `V`, the transition is `f_i x ↦ f_j x`. -/
theorem toFun_e_hom_val (P : PairIso Ci Cj V hVi hVj) (v : X.restrictOpen V) :
    (KLocallyRingedSpace.Hom.toFun P.e.hom ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩,
        P.mem_Ωi v⟩).1 =
      KLocallyRingedSpace.Hom.toFun Cj.f ⟨v.1, hVj v.2⟩ := by
  have h₁ : KLocallyRingedSpace.Hom.toFun (pairLift Ci hVi P.Ωi P.mem_Ωi) v =
      ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩, P.mem_Ωi v⟩ :=
    Subtype.ext (toFun_pairLift_val Ci hVi P.Ωi P.mem_Ωi v)
  have h₂ : KLocallyRingedSpace.Hom.toFun P.e.hom (KLocallyRingedSpace.Hom.toFun
      (pairLift Ci hVi P.Ωi P.mem_Ωi) v) =
      KLocallyRingedSpace.Hom.toFun (pairLift Cj hVj P.Ωj P.mem_Ωj) v :=
    congrFun (congrArg KLocallyRingedSpace.Hom.toFun P.lift_comp_hom) v
  rw [← h₁]
  exact (congrArg Subtype.val h₂).trans (toFun_pairLift_val Cj hVj P.Ωj P.mem_Ωj v)

/-- A point of the domain whose image under the transition is a real point of `Y_j` is a real point
of `Y_i` over `V` (transitions preserve non-real points): the real points of `Ωj` lie over `V`, and
on them the inverse of the transition is `f_j x ↦ f_i x`. -/
theorem exists_eq_of_toFun_e_hom_eq (P : PairIso Ci Cj V hVi hVj)
    (y : Ci.Y.toKLocallyRingedSpace.restrictOpen P.Ωi) (u : X.restrictOpen Uj)
    (hu : (KLocallyRingedSpace.Hom.toFun P.e.hom y).1 = KLocallyRingedSpace.Hom.toFun Cj.f u) :
    ∃ v : X.restrictOpen V, y.1 = KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩ := by
  have huV : u.1 ∈ V := Cj.mem_restrictLeOpens.mp (P.Ωj_le (KLocallyRingedSpace.Hom.toFun P.e.hom
      y).2) u hu.symm
  refine ⟨⟨u.1, huV⟩, ?_⟩
  have h₁ : KLocallyRingedSpace.Hom.toFun P.e.hom y =
      KLocallyRingedSpace.Hom.toFun P.e.hom ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨u.1, hVi huV⟩,
          P.mem_Ωi ⟨u.1, huV⟩⟩ := by
    apply Subtype.ext
    rw [P.toFun_e_hom_val ⟨u.1, huV⟩, hu]
    rfl
  have hinv : ∀ z, KLocallyRingedSpace.Hom.toFun P.e.inv (KLocallyRingedSpace.Hom.toFun P.e.hom z)
      = z := fun z =>
    congrFun (congrArg KLocallyRingedSpace.Hom.toFun P.e.hom_inv_id) z
  have h₂ := congrArg (KLocallyRingedSpace.Hom.toFun P.e.inv) h₁
  exact congrArg Subtype.val ((hinv y).symm.trans (h₂.trans (hinv _)))

/-- The transposed datum. -/
noncomputable def symm (P : PairIso Ci Cj V hVi hVj) : PairIso Cj Ci V hVj hVi where
  Ωi := P.Ωj
  Ωj := P.Ωi
  e := P.e.symm
  mem_Ωi := P.mem_Ωj
  mem_Ωj := P.mem_Ωi
  Ωi_le := P.Ωj_le
  Ωj_le := P.Ωi_le
  compat :=
    (congrArg (fun φ => φ ≫ P.e.inv ≫ ofRestrict Ci.Y.toKLocallyRingedSpace P.Ωi)
      P.lift_comp_hom.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun φ => pairLift Ci hVi P.Ωi P.mem_Ωi ≫ φ)
        (Iso.hom_inv_id_assoc P.e (ofRestrict Ci.Y.toKLocallyRingedSpace P.Ωi))).trans
      (pairLift_comp _ _ _ _)))

/-- The images of `V` lie in the image of an open `W ⊆ Y | (Y ∖ f(U ∖ V))` containing
`f | V (V)`. -/
theorem mem_imageOpens_of_mem_restrictLeHom {U : Opens X} (C : Complexification (X.restrictOpen U))
    {V : Opens X} (hV : V ≤ U)
    (W : Opens (C.Y.toKLocallyRingedSpace.restrictOpen (C.restrictLeOpens V)))
    (hW : ∀ x : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun (C.restrictLeHom V hV) x ∈ W)
    (v : X.restrictOpen V) :
    KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩ ∈ imageOpens (C.restrictLeOpens V) W := by
  refine mem_imageOpens.mpr ⟨C.toFun_mem_restrictLeOpens ⟨v.1, hV v.2⟩ v.2, ?_⟩
  have h := hW v
  have e' : KLocallyRingedSpace.Hom.toFun (C.restrictLeHom V hV) v =
      ⟨KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩, C.toFun_mem_restrictLeOpens ⟨v.1,
          hV v.2⟩ v.2⟩ :=
    Subtype.ext (toFun_restrictLeHom_val C V hV v)
  rw [e'] at h
  exact h

/-- The normalized datum extracted from the data of the hypothesis `hiso` of the gluing theorem (the
open subsets `W`, `W'` of the restricted complexifications and the `K`-isomorphism `e` between
them): the domains are the images of `W`, `W'` in `Y_i`, `Y_j`, the isomorphism is `e` transported
along the identifications of `Hironaka.AnalyticSpace.OpenSubspaceLemmas`, and the compatibility
follows from the given one after cancelling the isomorphism `(X | V)(ℂ) | ⊤ ≅ (X | V)(ℂ)` and the
monomorphic inclusions. -/
noncomputable def ofHiso
    (W : Opens (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)))
    (W' : Opens (Cj.Y.toKLocallyRingedSpace.restrictOpen (Cj.restrictLeOpens V)))
    (hW : ∀ x : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun (Ci.restrictLeHom V hVi) x ∈ W)
    (hW' : ∀ x : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun (Cj.restrictLeHom V hVj) x ∈ W')
    (e : KIso ((Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)).restrictOpen W)
      ((Cj.Y.toKLocallyRingedSpace.restrictOpen (Cj.restrictLeOpens V)).restrictOpen W'))
    (heq : Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫ e.hom =
      Hom.restrictTo (Cj.restrictLeHom V hVj) ⊤ W' (fun x _ => hW' x)) :
    PairIso Ci Cj V hVi hVj where
  Ωi := imageOpens (Ci.restrictLeOpens V) W
  Ωj := imageOpens (Cj.restrictLeOpens V) W'
  e := (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).symm ≪≫ e ≪≫
    restrictOpen_restrictOpen_iso (Cj.restrictLeOpens V) W'
  mem_Ωi := mem_imageOpens_of_mem_restrictLeHom Ci hVi W hW
  mem_Ωj := mem_imageOpens_of_mem_restrictLeHom Cj hVj W' hW'
  Ωi_le := fun _ hy => (mem_imageOpens.mp hy).fst
  Ωj_le := fun _ hy => (mem_imageOpens.mp hy).fst
  compat := by
    have hiso := isIso_ofRestrict_top (complexify (X.restrictOpen V).toKLocallyRingedSpace)
    apply (cancel_epi (ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤)).mp
    -- (1) the lift agrees with `hiso`'s restricted morphism, transported
    have h1 : ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫
        pairLift Ci hVi (imageOpens (Ci.restrictLeOpens V) W)
          (mem_imageOpens_of_mem_restrictLeHom Ci hVi W hW) =
        Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫
          (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).hom := by
      apply hom_ext_of_comp_eq (ofRestrict Ci.Y.toKLocallyRingedSpace
        (imageOpens (Ci.restrictLeOpens V) W))
      have l₁ := (Category.assoc _ _ _).trans (congrArg
        (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ)
        (pairLift_comp Ci hVi (imageOpens (Ci.restrictLeOpens V) W)
          (mem_imageOpens_of_mem_restrictLeHom Ci hVi W hW)))
      have r₁ := (Category.assoc _ _ _).trans (congrArg
        (fun φ => Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫ φ)
        (restrictOpen_restrictOpen_iso_hom_comp Ci.Y.toKLocallyRingedSpace
          (Ci.restrictLeOpens V) W))
      have r₂ := (Category.assoc _ _ _).symm.trans (congrArg
        (fun φ => φ ≫ ofRestrict Ci.Y.toKLocallyRingedSpace (Ci.restrictLeOpens V))
        (Hom.restrictTo_comp_ofRestrict (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x)))
      have r₃ := (Category.assoc _ _ _).trans (congrArg
        (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ)
        (Ci.restrictLeHom_comp_ofRestrict V hVi))
      exact l₁.trans (r₁.trans (r₂.trans r₃)).symm
    -- (2) `hiso`'s equation, followed by the inclusions into `Y_j`
    have h2 : Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫
        (e.hom ≫ (ofRestrict _ W' ≫ ofRestrict Cj.Y.toKLocallyRingedSpace (Cj.restrictLeOpens V))) =
        ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫
          (complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hVj) ≫ Cj.f) := by
      have s₁ := (Category.assoc _ _ _).symm.trans (congrArg
        (fun φ => φ ≫ (ofRestrict _ W' ≫ ofRestrict Cj.Y.toKLocallyRingedSpace
          (Cj.restrictLeOpens V))) heq)
      have s₂ := (Category.assoc _ _ _).symm.trans (congrArg
        (fun φ => φ ≫ ofRestrict Cj.Y.toKLocallyRingedSpace (Cj.restrictLeOpens V))
        (Hom.restrictTo_comp_ofRestrict (Cj.restrictLeHom V hVj) ⊤ W' (fun x _ => hW' x)))
      have s₃ := (Category.assoc _ _ _).trans (congrArg
        (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ)
        (Cj.restrictLeHom_comp_ofRestrict V hVj))
      exact s₁.trans (s₂.trans s₃)
    -- (3) assemble
    have m₁ := (Category.assoc _ _ _).symm.trans (congrArg
      (fun φ => φ ≫ (((restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).symm ≪≫ e ≪≫
        restrictOpen_restrictOpen_iso (Cj.restrictLeOpens V) W').hom ≫
        ofRestrict Cj.Y.toKLocallyRingedSpace (imageOpens (Cj.restrictLeOpens V) W'))) h1)
    have m₂ : ((restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).hom ≫
        (((restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).symm ≪≫ e ≪≫
          restrictOpen_restrictOpen_iso (Cj.restrictLeOpens V) W').hom ≫
          ofRestrict Cj.Y.toKLocallyRingedSpace (imageOpens (Cj.restrictLeOpens V) W'))) =
        e.hom ≫ (ofRestrict _ W' ≫ ofRestrict Cj.Y.toKLocallyRingedSpace (Cj.restrictLeOpens V)) :=
      (congrArg (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).hom ≫ φ)
        (Category.assoc _ _ _)).trans
        ((Iso.hom_inv_id_assoc (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W) _).trans
        ((Category.assoc _ _ _).trans (congrArg (fun φ => e.hom ≫ φ)
          (restrictOpen_restrictOpen_iso_hom_comp Cj.Y.toKLocallyRingedSpace
            (Cj.restrictLeOpens V) W'))))
    exact m₁.trans ((Category.assoc _ _ _).trans ((congrArg
      (fun φ => Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫ φ) m₂).trans h2))

end PairIso

/-- The diagonal datum: the identity of `Y_i` on `⊤`. -/
noncomputable def PairIso.refl {Ui : Opens X} (Ci : Complexification (X.restrictOpen Ui)) :
    PairIso Ci Ci Ui le_rfl le_rfl where
  Ωi := ⊤
  Ωj := ⊤
  e := Iso.refl _
  mem_Ωi := fun _ => Set.mem_univ _
  mem_Ωj := fun _ => Set.mem_univ _
  Ωi_le := fun _ _ => Ci.mem_restrictLeOpens.mpr fun u _ => u.2
  Ωj_le := fun _ _ => Ci.mem_restrictLeOpens.mpr fun u _ => u.2
  compat :=
    (congrArg (fun φ => pairLift Ci le_rfl ⊤ (fun _ => Set.mem_univ _) ≫ φ)
      (Category.id_comp (ofRestrict Ci.Y.toKLocallyRingedSpace ⊤))).trans (pairLift_comp _ _ _ _)


/-! ### The uniqueness hypothesis of the gluing theorem in the uniform setting -/

/-- The uniqueness hypothesis `huniq` of the gluing theorem, restated for two `K`-morphisms `g₁ g₂`
out of an open subset `D ⊆ Y_i` containing `f_i(V)` and inside `Y_i ∖ f_i(U_i ∖ V)`, both compatible
with `f_i`, `f_k` on `V` and with range inside `Y_k ∖ f_k(U_k ∖ V)`: they agree on an open subset
`N ⊆ D` containing `f_i(V)`. The proof applies `huniq` to the restricted complexifications
`C_i | V`, `C_k | V` and translates along the identifications and the bridge lemma
`restrictLeHom_comp_ofRestrict`. -/
theorem exists_eq_near_of_huniq
    (huniq : ∀ (V : Opens X) (C C' : Complexification (X.restrictOpen V)) (W : Opens C.Y)
      (hW : ∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W)
      (g₁ g₂ : C.Y.toKLocallyRingedSpace.restrictOpen W ⟶ C'.Y.toKLocallyRingedSpace),
      Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ g₁ = ofRestrict _ ⊤ ≫ C'.f →
      Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ g₂ = ofRestrict _ ⊤ ≫ C'.f →
      ∃ (W₀ : Opens C.Y) (hle : W₀ ≤ W), (∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W₀) ∧
        restrictOpenIncl C.Y.toKLocallyRingedSpace hle ≫ g₁ =
          restrictOpenIncl C.Y.toKLocallyRingedSpace hle ≫ g₂)
    {Ui Uk : Opens X} (Ci : Complexification (X.restrictOpen Ui))
    (Ck : Complexification (X.restrictOpen Uk)) (V : Opens X) (hVi : V ≤ Ui) (hVk : V ≤ Uk)
    (D : Opens Ci.Y) (hD : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1,
        hVi v.2⟩ ∈ D)
    (hDle : D ≤ Ci.restrictLeOpens V)
    (g₁ g₂ : Ci.Y.toKLocallyRingedSpace.restrictOpen D ⟶ Ck.Y.toKLocallyRingedSpace)
    (hg₁ : pairLift Ci hVi D hD ≫ g₁ =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hVk) ≫ Ck.f)
    (hg₂ : pairLift Ci hVi D hD ≫ g₂ =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hVk) ≫ Ck.f)
    (hr₁ : ∀ y : Ci.Y.toKLocallyRingedSpace.restrictOpen D,
      KLocallyRingedSpace.Hom.toFun g₁ y ∈ Ck.restrictLeOpens V)
    (hr₂ : ∀ y : Ci.Y.toKLocallyRingedSpace.restrictOpen D,
      KLocallyRingedSpace.Hom.toFun g₂ y ∈ Ck.restrictLeOpens V) :
    ∃ (N : Opens Ci.Y) (hle : N ≤ D),
      (∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩ ∈ N) ∧
      restrictOpenIncl Ci.Y.toKLocallyRingedSpace hle ≫ g₁ =
        restrictOpenIncl Ci.Y.toKLocallyRingedSpace hle ≫ g₂ := by
  -- the open `D` seen inside `Y_i | Θ_i`
  let W : Opens (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) :=
    (Opens.map (ofRestrict Ci.Y.toKLocallyRingedSpace (Ci.restrictLeOpens V)).1.base).obj D
  have hW : ∀ x : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun (Ci.restrictLeHom V hVi) x ∈ W :=
      fun x => by
    change (KLocallyRingedSpace.Hom.toFun (Ci.restrictLeHom V hVi) x).1 ∈ D
    rw [toFun_restrictLeHom_val]
    exact hD x
  -- `(Y_i | Θ_i) | W ≅ Y_i | D`
  let ρ : (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)).restrictOpen W ≅
      Ci.Y.toKLocallyRingedSpace.restrictOpen D :=
    restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W ≪≫
      eqToIso (congrArg Ci.Y.toKLocallyRingedSpace.restrictOpen
        (imageOpens_map_eq Ci.Y.toKLocallyRingedSpace hDle))
  have hρ : ρ.hom ≫ ofRestrict Ci.Y.toKLocallyRingedSpace D =
      ofRestrict _ W ≫ ofRestrict Ci.Y.toKLocallyRingedSpace (Ci.restrictLeOpens V) :=
    (Category.assoc _ _ _).trans ((congrArg
      (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W).hom ≫ φ)
      (eqToIso_restrictOpen_hom_comp_ofRestrict Ci.Y.toKLocallyRingedSpace
        (imageOpens_map_eq Ci.Y.toKLocallyRingedSpace hDle))).trans
      (restrictOpen_restrictOpen_iso_hom_comp Ci.Y.toKLocallyRingedSpace
        (Ci.restrictLeOpens V) W))
  -- the two morphisms into `Y_k | Θ_k`
  have hrange : ∀ g : Ci.Y.toKLocallyRingedSpace.restrictOpen D ⟶ Ck.Y.toKLocallyRingedSpace,
      (∀ y, KLocallyRingedSpace.Hom.toFun g y ∈ Ck.restrictLeOpens V) →
      Set.range (KLocallyRingedSpace.Hom.toFun (ρ.hom ≫ g)) ⊆
        Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict Ck.Y.toKLocallyRingedSpace
            (Ck.restrictLeOpens V))) := by
    intro g hr
    rintro _ ⟨y, rfl⟩
    rw [range_toFun_ofRestrict]
    exact hr _
  let g₁' := liftAlong (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V)) (ρ.hom ≫ g₁)
    (hrange g₁ hr₁)
  let g₂' := liftAlong (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V)) (ρ.hom ≫ g₂)
    (hrange g₂ hr₂)
  -- `hiso`'s restricted morphism, transported to `Y_i | D`, is the lift of `f_i` on `V`
  have hlift : Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫ ρ.hom =
      ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫
        pairLift Ci hVi D hD := by
    apply hom_ext_of_comp_eq (ofRestrict Ci.Y.toKLocallyRingedSpace D)
    have l₁ := (Category.assoc _ _ _).trans (congrArg
      (fun φ => Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫ φ) hρ)
    have l₂ := (Category.assoc _ _ _).symm.trans (congrArg
      (fun φ => φ ≫ ofRestrict Ci.Y.toKLocallyRingedSpace (Ci.restrictLeOpens V))
      (Hom.restrictTo_comp_ofRestrict (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x)))
    have l₃ := (Category.assoc _ _ _).trans (congrArg
      (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ)
      (Ci.restrictLeHom_comp_ofRestrict V hVi))
    have r₁ := (Category.assoc _ _ _).trans (congrArg
      (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ)
      (pairLift_comp Ci hVi D hD))
    exact (l₁.trans (l₂.trans l₃)).trans r₁.symm
  -- the hypotheses of `huniq`
  have hyp : ∀ (g : Ci.Y.toKLocallyRingedSpace.restrictOpen D ⟶ Ck.Y.toKLocallyRingedSpace)
      (hr : ∀ y, KLocallyRingedSpace.Hom.toFun g y ∈ Ck.restrictLeOpens V),
      pairLift Ci hVi D hD ≫ g =
        complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hVk) ≫ Ck.f →
      Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫
        liftAlong (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V)) (ρ.hom ≫ g)
          (hrange g hr) =
        ofRestrict _ ⊤ ≫ Ck.restrictLeHom V hVk := by
    intro g hr hg
    apply hom_ext_of_comp_eq (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V))
    have l₁ := (Category.assoc _ _ _).trans (congrArg
      (fun φ => Hom.restrictTo (Ci.restrictLeHom V hVi) ⊤ W (fun x _ => hW x) ≫ φ)
      (liftAlong_comp (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V))
        (ρ.hom ≫ g) (hrange g hr)))
    have l₂ := (Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ g) hlift)
    have l₃ := (Category.assoc _ _ _).trans (congrArg
      (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ) hg)
    have r₁ := (Category.assoc _ _ _).trans (congrArg
      (fun φ => ofRestrict (complexify (X.restrictOpen V).toKLocallyRingedSpace) ⊤ ≫ φ)
      (Ck.restrictLeHom_comp_ofRestrict V hVk))
    exact (l₁.trans (l₂.trans l₃)).trans r₁.symm
  obtain ⟨W₀, hle, hW₀, heq⟩ := huniq V (Ci.restrictLe V hVi) (Ck.restrictLe V hVk) W hW g₁' g₂'
    (hyp g₁ hr₁ hg₁) (hyp g₂ hr₂ hg₂)
  refine ⟨imageOpens (Ci.restrictLeOpens V) W₀, ?_,
    PairIso.mem_imageOpens_of_mem_restrictLeHom Ci hVi W₀ hW₀, ?_⟩
  · intro y hy
    obtain ⟨hyΘ, hyW₀⟩ := mem_imageOpens.mp hy
    exact hle hyW₀
  · -- the inclusion of `N` into `D` factors through the transported equality
    have hτ : restrictOpenIncl Ci.Y.toKLocallyRingedSpace
        (show imageOpens (Ci.restrictLeOpens V) W₀ ≤ D from fun y hy =>
          hle (mem_imageOpens.mp hy).snd) =
        (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫
          restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle ≫
            ρ.hom := by
      apply hom_ext_of_comp_eq (ofRestrict Ci.Y.toKLocallyRingedSpace D)
      have l := restrictOpenIncl_comp_ofRestrict Ci.Y.toKLocallyRingedSpace
        (show imageOpens (Ci.restrictLeOpens V) W₀ ≤ D from fun y hy =>
          hle (mem_imageOpens.mp hy).snd)
      have r₁ := (Category.assoc _ _ _).trans (congrArg
        (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫ φ)
        ((Category.assoc _ _ _).trans (congrArg (fun φ =>
          restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle ≫
            φ) hρ)))
      have r₂ := congrArg
        (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫ φ)
        ((Category.assoc _ _ _).symm.trans (congrArg
          (fun φ => φ ≫ ofRestrict Ci.Y.toKLocallyRingedSpace (Ci.restrictLeOpens V))
          (restrictOpenIncl_comp_ofRestrict
            (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle)))
      have r₃ := restrictOpen_restrictOpen_iso_inv_comp Ci.Y.toKLocallyRingedSpace
        (Ci.restrictLeOpens V) W₀
      exact l.trans (r₁.trans (r₂.trans r₃)).symm
    have key : ∀ (g : Ci.Y.toKLocallyRingedSpace.restrictOpen D ⟶ Ck.Y.toKLocallyRingedSpace)
        (hr : ∀ y, KLocallyRingedSpace.Hom.toFun g y ∈ Ck.restrictLeOpens V),
        ((restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫
          restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle ≫
            ρ.hom) ≫ g =
        (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫
          ((restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle ≫
            liftAlong (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V)) (ρ.hom ≫ g)
              (hrange g hr)) ≫
            ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V)) := by
      intro g hr
      have c₁ := Category.assoc (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv
        (restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle ≫
          ρ.hom) g
      have c₂ := congrArg
        (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫ φ)
        (Category.assoc (restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen
          (Ci.restrictLeOpens V)) hle) ρ.hom g)
      have c₃ := congrArg
        (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫
          (restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen (Ci.restrictLeOpens V)) hle ≫
            φ))
        (liftAlong_comp (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V))
          (ρ.hom ≫ g) (hrange g hr)).symm
      have c₄ := congrArg
        (fun φ => (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫ φ)
        (Category.assoc (restrictOpenIncl (Ci.Y.toKLocallyRingedSpace.restrictOpen
          (Ci.restrictLeOpens V)) hle)
          (liftAlong (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V)) (ρ.hom ≫ g)
            (hrange g hr))
          (ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V))).symm
      exact c₁.trans (c₂.trans (c₃.trans c₄))
    rw [hτ]
    exact (key g₁ hr₁).trans ((congrArg (fun φ =>
      (restrictOpen_restrictOpen_iso (Ci.restrictLeOpens V) W₀).inv ≫
        (φ ≫ ofRestrict Ck.Y.toKLocallyRingedSpace (Ck.restrictLeOpens V))) heq).trans
      (key g₂ hr₂).symm)

end AnalyticSpace.Glue
