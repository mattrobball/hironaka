/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.Manifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Morphisms over a base: uniqueness under conjugation; the part of a restriction

General facts behind the independence and the gluing of the local resolutions along an
exhaustion (`resolutionOn_indep`, `resolutionGlues_of_isEmbeddedDesing` of
`Hironaka/Resolution/Analytic/Kol07Thm45/GluingProperties.lean`; the gluing of local
desingularizations of [Wlo09, §4, §4.3]):

* `CategoryTheory.uniq_of_conj`: in any category, if the isomorphisms over a base `Z` between `A'`
  and `B'` are unique, so are those between `A` and `B` for any `A ≅ A'`, `B ≅ B'` over `Z` —
  conjugation by the two identifications is injective and preserves "over `Z`";
* `CategoryTheory.over_of_conj_inv_hom`: conjugating a morphism over `Z` by isomorphisms over `Z`
  gives a morphism over `Z`;
* `KLocallyRingedSpace.exists_iso_restrictOpen_restrictOpen_comap`: for a `K`-morphism `g : A ⟶ Z`
  and opens `U ⊆ A`, `U' ⊆ Z` with `g(U) ⊆ U'`, the part of the restriction `A|U` over an open `O`
  whose preimage lies in `U` (through `g|U ≫ ofRestrict Z U'`) is the part of `A` over `O`, over
  `Z` — the identification through which the gluing of the restricted resolutions along an
  exhaustion reads the isomorphisms of the full glued spaces (it needs only `g⁻¹O ⊆ U`, not
  `U = g⁻¹U'`).

The remaining lemmas — `conj_conj_inv` (conjugating back and forth is the identity), `over_comp₃`
(a composite of three morphisms over the base is over the base), `over_inv_of_over` (the inverse
of an isomorphism over the base) and `conj_over_eq` (the structure maps under conjugation) — are
the bookkeeping of conjugation and composition over the base.

Routine; used by `Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverIsoReg.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/PieceGlueIndep.lean`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology

universe u

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- **Uniqueness of the morphisms over a base transports along isomorphisms over the base**: with
`a : A ≅ A'`, `b : B ≅ B'` over `Z` (`a.hom ≫ πA' = πA`, `b.hom ≫ πB' = πB`), two isomorphisms
`s s' : A ⟶ B` over `Z` conjugate to isomorphisms `a.inv ≫ s ≫ b.hom` over `Z` from `A'` to `B'`,
which agree by hypothesis; cancelling the isomorphisms gives `s = s'`. -/
theorem uniq_of_conj {A A' B B' Z : C} (πA : A ⟶ Z) (πA' : A' ⟶ Z) (πB : B ⟶ Z) (πB' : B' ⟶ Z)
    (a : A ≅ A') (b : B ≅ B') (ha : a.hom ≫ πA' = πA) (hb : b.hom ≫ πB' = πB)
    (huniq : ∀ s s' : A' ⟶ B', IsIso s → IsIso s' → s ≫ πB' = πA' → s' ≫ πB' = πA' → s = s')
    (s s' : A ⟶ B) (hs : IsIso s) (hs' : IsIso s') (hc : s ≫ πB = πA) (hc' : s' ≫ πB = πA) :
    s = s' := by
  have key : ∀ t : A ⟶ B, t ≫ πB = πA → (a.inv ≫ t ≫ b.hom) ≫ πB' = πA' := by
    intro t ht
    rw [Category.assoc, Category.assoc, hb, ht, ← ha, Iso.inv_hom_id_assoc]
  have h := huniq (a.inv ≫ s ≫ b.hom) (a.inv ≫ s' ≫ b.hom)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv a)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hs (Iso.isIso_hom b)))
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_inv a)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ hs' (Iso.isIso_hom b)))
    (key s hc) (key s' hc')
  exact (Iso.cancel_iso_hom_right _ _ b).mp ((Iso.cancel_iso_inv_left a _ _).mp h)

/-- **Conjugating a morphism over a base by isomorphisms over the base gives a morphism over the
base**: `pA' = (a.inv ≫ s ≫ b.hom) ≫ pB'` from `pA = s ≫ pB`, `a.inv ≫ pA = pA'` and
`b.hom ≫ pB' = pB`. -/
theorem over_of_conj_inv_hom {A A' B B' Z : C} (a : A ≅ A') (b : B ≅ B') (pA : A ⟶ Z)
    (pA' : A' ⟶ Z) (pB : B ⟶ Z) (pB' : B' ⟶ Z) (ha : a.inv ≫ pA = pA') (hb : b.hom ≫ pB' = pB)
    (s : A ⟶ B) (hs : pA = s ≫ pB) : pA' = (a.inv ≫ s ≫ b.hom) ≫ pB' := by
  rw [Category.assoc, Category.assoc, hb, ← hs, ha]

/-- Conjugating back and forth is the identity: `a.hom ≫ (a.inv ≫ f ≫ b.hom) ≫ b.inv = f`. -/
theorem conj_conj_inv {A A' B B' : C} (a : A ≅ A') (b : B ≅ B') (f : A ⟶ B) :
    a.hom ≫ (a.inv ≫ f ≫ b.hom) ≫ b.inv = f := by
  simp

/-- A composite of three morphisms over a base, each over the base in the "restricted" form
`ofR ≫ p = (e ≫ ofR') ≫ p'`, is over the base. -/
theorem over_comp₃ {A B C' D YA YB YC YD Z : C} (e : A ⟶ B) (t : B ⟶ C') (f : C' ⟶ D)
    (ofA : A ⟶ YA) (ofB : B ⟶ YB) (ofC : C' ⟶ YC) (ofD : D ⟶ YD) (pA : YA ⟶ Z) (pB : YB ⟶ Z)
    (pC : YC ⟶ Z) (pD : YD ⟶ Z) (he : ofA ≫ pA = (e ≫ ofB) ≫ pB)
    (ht : ofB ≫ pB = (t ≫ ofC) ≫ pC) (hf : ofC ≫ pC = (f ≫ ofD) ≫ pD) :
    ofA ≫ pA = ((e ≫ t ≫ f) ≫ ofD) ≫ pD := by
  rw [he, Category.assoc, ht, Category.assoc, hf]
  simp only [Category.assoc]

/-- The inverse of an isomorphism over a base (restricted form) is over the base. -/
theorem over_inv_of_over {A A' Y Y' Z : C} (α : A ⟶ A') [IsIso α] (ofR : A ⟶ Y) (ofR' : A' ⟶ Y')
    (p : Y ⟶ Z) (p' : Y' ⟶ Z) (h : ofR ≫ p = (α ≫ ofR') ≫ p') :
    ofR' ≫ p' = (inv α ≫ ofR) ≫ p := by
  rw [Category.assoc, h, Category.assoc, IsIso.inv_hom_id_assoc]

/-- A morphism over a base, conjugated by two identifications over the base, followed by the
target's structure map, is the source's structure map: `(a ≫ s ≫ b) ≫ ofB ≫ p' = ofA ≫ p`. -/
theorem conj_over_eq {A A' B B' Y Y' Z : C} (a : A ⟶ A') (s : A' ⟶ B') (b : B' ⟶ B) (ofA : A ⟶ Y)
    (ofA' : A' ⟶ Y) (ofB : B ⟶ Y') (ofB' : B' ⟶ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z)
    (ha : a ≫ ofA' = ofA) (hb : b ≫ ofB = ofB') (hs : ofA' ≫ p = (s ≫ ofB') ≫ p') :
    (a ≫ s ≫ b) ≫ ofB ≫ p' = ofA ≫ p := by
  simp only [Category.assoc]
  rw [← Category.assoc b, hb, ← Category.assoc s, ← hs, ← Category.assoc, ha]

end CategoryTheory

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- **The part of the restriction `g|U : A|U ⟶ Z|U'` over an open `O` with `g⁻¹O ⊆ U` is the part of
`A` over `O`**, over `Z`: the two open immersions `(A|U)|_{(g|U)⁻¹O} ⟶ A|U ⟶ A` and `A|g⁻¹O ⟶ A`
have the same range (`isoOfRangeEq`). -/
theorem exists_iso_restrictOpen_restrictOpen_comap {A Z : KLocallyRingedSpace.{u} K} (g : A ⟶ Z)
    (U : Opens A) (U' : Opens Z) (h : ∀ a ∈ U, Hom.toFun g a ∈ U') (O : Opens Z)
    (hOU : ∀ a, Hom.toFun g a ∈ O → a ∈ U) :
    ∃ e : (A.restrictOpen U).restrictOpen
          (Opens.comap ⟨Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U'),
            Hom.continuous_toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U')⟩ O) ⟶
        A.restrictOpen (Opens.comap ⟨Hom.toFun g, Hom.continuous_toFun g⟩ O),
      IsIso e ∧ ofRestrict _ _ ≫ (Hom.restrictTo g U U' h ≫ ofRestrict Z U') =
        (e ≫ ofRestrict _ _) ≫ g := by
  have hπ : ∀ a : A.restrictOpen U,
      Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U') a = Hom.toFun g a.1 := fun a =>
    Hom.toFun_restrictTo g U U' h a
  have hinst : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (A.restrictOpen U)
        (Opens.comap ⟨Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U'),
          Hom.continuous_toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U')⟩ O) ≫
        ofRestrict A U).1 :=
    inferInstanceAs (AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      ((ofRestrict (A.restrictOpen U) _).1 ≫ (ofRestrict A U).1))
  have hrange : range (Hom.toFun (ofRestrict (A.restrictOpen U)
        (Opens.comap ⟨Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U'),
          Hom.continuous_toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U')⟩ O) ≫
        ofRestrict A U)) =
      range (Hom.toFun (ofRestrict A (Opens.comap ⟨Hom.toFun g, Hom.continuous_toFun g⟩ O))) := by
    rw [range_toFun_ofRestrict]
    ext a
    constructor
    · rintro ⟨v, rfl⟩
      change Hom.toFun g v.1.1 ∈ O
      rw [← hπ]
      exact v.2
    · intro ha
      refine ⟨Subtype.mk (Subtype.mk a (hOU a ha)) ?_, rfl⟩
      change Hom.toFun (Hom.restrictTo g U U' h ≫ ofRestrict Z U') (Subtype.mk a (hOU a ha)) ∈
        (O : Set Z)
      exact Set.mem_of_eq_of_mem (hπ (Subtype.mk a (hOU a ha))) ha
  refine ⟨(isoOfRangeEq _ _ hrange).hom, Iso.isIso_hom _, ?_⟩
  rw [isoOfRangeEq_hom_comp, Category.assoc, Hom.restrictTo_comp_ofRestrict g U U' h]

end AnalyticSpace.KLocallyRingedSpace

end
