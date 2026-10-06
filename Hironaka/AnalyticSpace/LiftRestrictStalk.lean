/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.GlueHomAffine
import Hironaka.AnalyticSpace.HomOfSectionsCompat
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.QuotientMap
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Stalk maps of a morphism into an open subspace

For `l : A ⟶ B|V` with `l ≫ ofRestrict B V = g`, the stalk map of `l` at `x` is conjugate to the
stalk map of `g` at `x` by the stalk isomorphism of the open immersion `B|V ⟶ B` (Mathlib's
`restrictStalkIso`) and the identification of the stalks of `B` at the two (equal) base points
(`stalkMap_ofRestrict_comp_stalkMap_of_comp_eq`, `stalkMap_apply_stalkMap_ofRestrict_of_comp_eq`).
Hence `l` and `g` have bijective, respectively surjective, stalk maps at the same points
(`bijective_stalkMap_iff_of_comp_eq`, `surjective_stalkMap_iff_of_comp_eq`), and the germ of a
section of `B` on `V`, read in `B|V`, is sent by the stalk map of `l` to what the stalk map of `g`
does to its germ in `B` (`stalkMap_germ_of_comp_eq`, `stalkMap_germ_top_of_comp_eq`). The same
conjugation for a factorization `ρ ≫ h' = g₀` through a morphism `ρ` with bijective stalk map at
`x` (`stalkMap_apply_stalkMap_of_comp_eq`, `surjective_stalkMap_of_comp_eq_of_bijective`,
`stalkMap_eq_zero_iff_of_comp_eq_of_bijective`: the stalk map of `h'` at `ρ x` is surjective when
that of `g₀` is, and its kernel is read off from that of `g₀`), and the algebra behind it: the
stalk map of a specialization along an equality of points is bijective
(`bijective_stalkSpecializes_of_eq`), a bijective ring homomorphism preserves membership in spans
(`mem_span_range_iff_of_bijective`), and the stalk maps of an isomorphism are bijective
(`bijective_stalkMap_of_isIso`). Used by `Hironaka/AnalyticSpace/RestrictToIso.lean`. Routine.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology

universe u

namespace AnalyticSpace

/-- The stalk specialization map between the stalks at two equal points is bijective. -/
theorem bijective_stalkSpecializes_of_eq {X : TopCat.{u}} (F : X.Presheaf CommRingCat.{u})
    {p q : X} (hpq : p = q) :
    Function.Bijective (F.stalkSpecializes (specializes_of_eq hpq)).hom := by
  subst hpq
  have h : F.stalkSpecializes (specializes_of_eq rfl) = 𝟙 _ := F.stalkSpecializes_refl p
  rw [h]
  exact Function.bijective_id

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K] {A B : KLocallyRingedSpace.{u} K} {V : Opens B}

/-- The stalk maps of an isomorphism are bijective. Duplicates `KIso.bijective_stalkMap` of
`Hironaka/AnalyticSpace/StalkMapLemmas.lean` in the `[IsIso φ]` form. -/
theorem bijective_stalkMap_of_isIso (φ : A ⟶ B) [IsIso φ] (x : A) :
    Function.Bijective (φ.1.stalkMap x).hom := by
  have h1 : IsIso φ.1 := (isIso_iff_isIso_val φ).mp inferInstance
  have h2 : IsIso (φ.1.stalkMap x) :=
    @PresheafedSpace.stalkMap.isIso CommRingCat _ _ _ _ φ.1.1
      (SheafedSpace.forgetToPresheafedSpace.map_isIso
        (LocallyRingedSpace.forgetToSheafedSpace.map φ.1)) x
  exact ConcreteCategory.bijective_of_isIso _

/-- For `l ≫ ofRestrict B V = g`: the stalk map of the open immersion followed by the stalk map of
`l` is the identification of the stalks at the equal base points followed by the stalk map of
`g`. -/
theorem stalkMap_ofRestrict_comp_stalkMap_of_comp_eq (l : A ⟶ B.restrictOpen V) (g : A ⟶ B)
    (hl : l ≫ ofRestrict B V = g) (x : A) :
    (ofRestrict B V).1.stalkMap (l.1.base x) ≫ l.1.stalkMap x =
      B.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm)) ≫
        g.1.stalkMap x := by
  have hEq : l.1 ≫ (ofRestrict B V).1 = g.1 := by rw [← Hom.comp_val, hl]
  rw [← LocallyRingedSpace.stalkMap_comp]
  exact LocallyRingedSpace.stalkMap_congr_hom _ _ hEq x

/-- For `ρ ≫ h' = g₀`: the stalk map of `ρ` after the stalk map of `h'` at `ρ x` is the stalk map of
`g₀` after the identification of the stalks at the equal base points (function form). -/
theorem stalkMap_apply_stalkMap_of_comp_eq {C : KLocallyRingedSpace.{u} K} (ρ : A ⟶ B)
    (h' : B ⟶ C) (g₀ : A ⟶ C) (hρ : ρ ≫ h' = g₀) (x : A)
    (a : C.toLocallyRingedSpace.presheaf.stalk (h'.1.base (ρ.1.base x))) :
    ρ.1.stalkMap x (h'.1.stalkMap (ρ.1.base x) a) =
      g₀.1.stalkMap x (C.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ C => φ.1.base x) hρ.symm)) a) := by
  have hEq : ρ.1 ≫ h'.1 = g₀.1 := by rw [← Hom.comp_val, hρ]
  have h1 : (ρ.1 ≫ h'.1).stalkMap x a = ρ.1.stalkMap x (h'.1.stalkMap (ρ.1.base x) a) :=
    congrArg (fun φ => φ.hom a) (LocallyRingedSpace.stalkMap_comp ρ.1 h'.1 x)
  have h2 := congrArg (fun φ => φ.hom a) (LocallyRingedSpace.stalkMap_congr_hom _ _ hEq x)
  simp only [CommRingCat.hom_comp] at h2
  exact h1.symm.trans h2

/-- The function form of `stalkMap_ofRestrict_comp_stalkMap_of_comp_eq`. -/
theorem stalkMap_apply_stalkMap_ofRestrict_of_comp_eq (l : A ⟶ B.restrictOpen V) (g : A ⟶ B)
    (hl : l ≫ ofRestrict B V = g) (x : A)
    (γ : B.toLocallyRingedSpace.presheaf.stalk (l.1.base x).1) :
    l.1.stalkMap x ((ofRestrict B V).1.stalkMap (l.1.base x) γ) =
      g.1.stalkMap x (B.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm)) γ) := by
  have h := congrArg (fun φ => φ.hom γ) (stalkMap_ofRestrict_comp_stalkMap_of_comp_eq l g hl x)
  simp only [CommRingCat.hom_comp] at h
  exact h

/-- For `ρ ≫ h' = g₀` with bijective stalk maps of `ρ`: the stalk map of `h'` at `ρ x` is
surjective when that of `g₀` at `x` is. -/
theorem surjective_stalkMap_of_comp_eq_of_bijective {C : KLocallyRingedSpace.{u} K} (ρ : A ⟶ B)
    (h' : B ⟶ C) (g₀ : A ⟶ C) (hρ : ρ ≫ h' = g₀) (x : A)
    (hb : Function.Bijective (ρ.1.stalkMap x).hom)
    (hs : Function.Surjective (g₀.1.stalkMap x).hom) :
    Function.Surjective (h'.1.stalkMap (ρ.1.base x)).hom := by
  intro t
  obtain ⟨b, hb'⟩ := hs (ρ.1.stalkMap x t)
  obtain ⟨a, rfl⟩ := (bijective_stalkSpecializes_of_eq C.toLocallyRingedSpace.presheaf
    (congrArg (fun φ : A ⟶ C => φ.1.base x) hρ.symm)).2 b
  refine ⟨a, hb.1 ?_⟩
  rw [stalkMap_apply_stalkMap_of_comp_eq ρ h' g₀ hρ x a]
  exact hb'

/-- For `ρ ≫ h' = g₀` with bijective stalk maps of `ρ`: `a` is in the kernel of the stalk map of
`h'` at `ρ x` iff its transport is in the kernel of the stalk map of `g₀` at `x`. -/
theorem stalkMap_eq_zero_iff_of_comp_eq_of_bijective {C : KLocallyRingedSpace.{u} K} (ρ : A ⟶ B)
    (h' : B ⟶ C) (g₀ : A ⟶ C) (hρ : ρ ≫ h' = g₀) (x : A)
    (hb : Function.Bijective (ρ.1.stalkMap x).hom)
    (a : C.toLocallyRingedSpace.presheaf.stalk (h'.1.base (ρ.1.base x))) :
    h'.1.stalkMap (ρ.1.base x) a = 0 ↔
      g₀.1.stalkMap x (C.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ C => φ.1.base x) hρ.symm)) a) = 0 := by
  rw [← stalkMap_apply_stalkMap_of_comp_eq ρ h' g₀ hρ x a]
  exact (map_eq_zero_iff _ hb.1).symm

end KLocallyRingedSpace

/-- An element is in the ideal generated by a family iff its image under a bijective ring
homomorphism is in the ideal generated by the images. -/
theorem mem_span_range_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S] (Φ : R →+* S)
    (hΦ : Function.Bijective Φ) {ι : Type*} (v : ι → R) (a : R) :
    Φ a ∈ Ideal.span (Set.range fun i => Φ (v i)) ↔ a ∈ Ideal.span (Set.range v) := by
  have h : Ideal.span (Set.range fun i => Φ (v i)) = Ideal.map Φ (Ideal.span (Set.range v)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [h]
  exact (Ideal.mem_comap (f := Φ)).symm.trans
    (Iff.of_eq (congrArg (a ∈ ·) (Ideal.comap_map_of_bijective Φ hΦ)))

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K] {A B : KLocallyRingedSpace.{u} K} {V : Opens B}

/-- The stalk map of `l : A ⟶ B|V` is bijective exactly when that of `g = l ≫ ofRestrict B V` is. -/
theorem bijective_stalkMap_iff_of_comp_eq (l : A ⟶ B.restrictOpen V) (g : A ⟶ B)
    (hl : l ≫ ofRestrict B V = g) (x : A) :
    Function.Bijective (l.1.stalkMap x).hom ↔ Function.Bijective (g.1.stalkMap x).hom := by
  have ho : Function.Bijective ((ofRestrict B V).1.stalkMap (l.1.base x)).hom :=
    have := KLocallyRingedSpace.isIso_ofRestrict_stalkMap B V (l.1.base x)
    ConcreteCategory.bijective_of_isIso _
  have hs := bijective_stalkSpecializes_of_eq B.toLocallyRingedSpace.presheaf
    (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm)
  have hfun : (l.1.stalkMap x).hom ∘ ((ofRestrict B V).1.stalkMap (l.1.base x)).hom =
      (g.1.stalkMap x).hom ∘ (B.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm))).hom :=
    funext fun γ => stalkMap_apply_stalkMap_ofRestrict_of_comp_eq l g hl x γ
  have h1 := Function.Bijective.of_comp_iff (l.1.stalkMap x).hom ho
  have h2 := Function.Bijective.of_comp_iff (g.1.stalkMap x).hom hs
  have h3 : Function.Bijective ((l.1.stalkMap x).hom ∘
      ((ofRestrict B V).1.stalkMap (l.1.base x)).hom) ↔
      Function.Bijective ((g.1.stalkMap x).hom ∘ (B.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm))).hom) :=
    Iff.of_eq (congrArg Function.Bijective hfun)
  exact h1.symm.trans (h3.trans h2)

/-- The stalk map of `l : A ⟶ B|V` is surjective exactly when that of `g = l ≫ ofRestrict B V`
is. -/
theorem surjective_stalkMap_iff_of_comp_eq (l : A ⟶ B.restrictOpen V) (g : A ⟶ B)
    (hl : l ≫ ofRestrict B V = g) (x : A) :
    Function.Surjective (l.1.stalkMap x).hom ↔ Function.Surjective (g.1.stalkMap x).hom := by
  have ho : Function.Bijective ((ofRestrict B V).1.stalkMap (l.1.base x)).hom :=
    have := KLocallyRingedSpace.isIso_ofRestrict_stalkMap B V (l.1.base x)
    ConcreteCategory.bijective_of_isIso _
  have hs := bijective_stalkSpecializes_of_eq B.toLocallyRingedSpace.presheaf
    (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm)
  have hfun : (l.1.stalkMap x).hom ∘ ((ofRestrict B V).1.stalkMap (l.1.base x)).hom =
      (g.1.stalkMap x).hom ∘ (B.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm))).hom :=
    funext fun γ => stalkMap_apply_stalkMap_ofRestrict_of_comp_eq l g hl x γ
  have h1 := Function.Surjective.of_comp_iff (l.1.stalkMap x).hom ho.2
  have h2 := Function.Surjective.of_comp_iff (g.1.stalkMap x).hom hs.2
  have h3 : Function.Surjective ((l.1.stalkMap x).hom ∘
      ((ofRestrict B V).1.stalkMap (l.1.base x)).hom) ↔
      Function.Surjective ((g.1.stalkMap x).hom ∘
        (B.toLocallyRingedSpace.presheaf.stalkSpecializes
          (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm))).hom) :=
    Iff.of_eq (congrArg Function.Surjective hfun)
  exact h1.symm.trans (h3.trans h2)

/-- The stalk map of `l : A ⟶ B|V` on the germ of a section `τ` of `B|V` on `T` (a section of `B` on
the image of `T`) is the stalk map of `g = l ≫ ofRestrict B V` on the germ of `τ` in `B`. -/
theorem stalkMap_germ_of_comp_eq (l : A ⟶ B.restrictOpen V) (g : A ⟶ B)
    (hl : l ≫ ofRestrict B V = g) (x : A) (T : Opens (B.restrictOpen V)) (hT : l.1.base x ∈ T)
    (τ : B.toLocallyRingedSpace.presheaf.obj (op (imgOpens B V T))) :
    l.1.stalkMap x ((B.restrictOpen V).toLocallyRingedSpace.presheaf.germ T (l.1.base x) hT τ) =
      g.1.stalkMap x (B.toLocallyRingedSpace.presheaf.germ (imgOpens B V T) (Hom.toFun g x)
        (by rw [← hl]; exact mem_imgOpens_of_mem B (l.1.base x).2 hT) τ) := by
  have hB := restrictStalkIso_inv_germ B V T (l.1.base x).2 hT τ
  change (resIso B V (l.1.base x).2).inv (B.toLocallyRingedSpace.presheaf.germ (imgOpens B V T)
    (l.1.base x).1 _ τ) = (B.restrictOpen V).toLocallyRingedSpace.presheaf.germ T (l.1.base x)
    hT τ at hB
  rw [← hB, resIso_inv_eq_stalkMap_ofRestrict B V (l.1.base x)]
  refine (stalkMap_apply_stalkMap_ofRestrict_of_comp_eq l g hl x _).trans ?_
  congr 1
  have hH := congrArg (fun φ => φ.hom τ) (TopCat.Presheaf.germ_stalkSpecializes
    B.toLocallyRingedSpace.presheaf (U := imgOpens B V T)
    (mem_imgOpens_of_mem B (l.1.base x).2 hT)
    (specializes_of_eq (congrArg (fun φ : A ⟶ B => φ.1.base x) hl.symm)))
  simp only [CommRingCat.hom_comp] at hH
  exact hH

/-- `stalkMap_germ_of_comp_eq` for a section of `B` on `V` read as a global section of `B|V`. -/
theorem stalkMap_germ_top_of_comp_eq (l : A ⟶ B.restrictOpen V) (g : A ⟶ B)
    (hl : l ≫ ofRestrict B V = g) (x : A) (τ : B.toLocallyRingedSpace.presheaf.obj (op V)) :
    l.1.stalkMap x ((B.restrictOpen V).toLocallyRingedSpace.presheaf.germ ⊤ (l.1.base x) trivial
        (B.toLocallyRingedSpace.presheaf.map (homOfLE (imgOpens_top_le B V)).op τ)) =
      g.1.stalkMap x (B.toLocallyRingedSpace.presheaf.germ V (Hom.toFun g x)
        (by rw [← hl]; exact (l.1.base x).2) τ) := by
  rw [stalkMap_germ_of_comp_eq l g hl x ⊤ trivial]
  congr 1
  exact TopCat.Presheaf.germ_res_apply B.toLocallyRingedSpace.presheaf
    (homOfLE (imgOpens_top_le B V)) (Hom.toFun g x) _ τ

end KLocallyRingedSpace

end AnalyticSpace
