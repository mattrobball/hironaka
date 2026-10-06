/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace.Defs
import Hironaka.AnalyticSpace.KSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Lifts along open immersions of `K`-spaces, and double restrictions

Bookkeeping for the gluing modules: a `K`-morphism into the source of an open immersion `a : B ⟶ A`
is determined by its composite with `a` (`hom_ext_of_comp_eq`, open immersions being monomorphisms),
and a `K`-morphism `g : C ⟶ A` whose range lies in that of `a` lifts uniquely through `a`
(`liftAlong`, `liftAlong_comp`, `liftAlong_unique`; `Hom.restrictTo` of
`Hironaka.AnalyticSpace.Complexification` is the case `a = ofRestrict`). The inclusion
`incl₂ A U W : (A | U) | W ⟶ A` of a double restriction is an open immersion with range the trace of
`W` on `A` (`mem_range_toFun_incl₂`).

Conventions. `A | U` is the open subspace `restrictOpen`; a point of `(A | U) | W` is a pair of
subtypes, `x.1.1 : A`. For `a = 𝟙 A` the lift is `g` itself; for `W = ⊤`, `incl₂` is `ofRestrict` up
to the identification of `Hironaka.AnalyticSpace.OpenSubspaceLemmas`. Not in the sources.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- Two `K`-morphisms into the source of an open immersion agree if they agree after it. -/
theorem hom_ext_of_comp_eq {A B C : KLocallyRingedSpace.{u} K} (a : B ⟶ A)
    [LocallyRingedSpace.IsOpenImmersion a.1] {g g' : C ⟶ B} (h : g ≫ a = g' ≫ a) : g = g' := by
  apply Hom.ext
  have h' : g.1 ≫ a.1 = g'.1 ≫ a.1 := by rw [← Hom.comp_val, ← Hom.comp_val, h]
  exact (cancel_mono a.1).mp h'

/-- The lift of `g : C ⟶ A` through the open immersion `a : B ⟶ A`, when the range of `g` lies in
the range of `a`. -/
noncomputable def liftAlong {A B C : KLocallyRingedSpace.{u} K} (a : B ⟶ A)
    [LocallyRingedSpace.IsOpenImmersion a.1] (g : C ⟶ A)
    (h : Set.range (KLocallyRingedSpace.Hom.toFun g) ⊆ Set.range
        (KLocallyRingedSpace.Hom.toFun a)) : C ⟶ B :=
  Hom.ofFac g a (LocallyRingedSpace.IsOpenImmersion.lift a.1 g.1 h)
    (LocallyRingedSpace.IsOpenImmersion.lift_fac a.1 g.1 h)

theorem liftAlong_comp {A B C : KLocallyRingedSpace.{u} K} (a : B ⟶ A)
    [LocallyRingedSpace.IsOpenImmersion a.1] (g : C ⟶ A)
    (h : Set.range (KLocallyRingedSpace.Hom.toFun g) ⊆ Set.range
        (KLocallyRingedSpace.Hom.toFun a)) : liftAlong a g h ≫ a = g :=
  Hom.ext (LocallyRingedSpace.IsOpenImmersion.lift_fac a.1 g.1 h)

theorem toFun_liftAlong {A B C : KLocallyRingedSpace.{u} K} (a : B ⟶ A)
    [LocallyRingedSpace.IsOpenImmersion a.1] (g : C ⟶ A)
    (h : Set.range (KLocallyRingedSpace.Hom.toFun g) ⊆ Set.range (KLocallyRingedSpace.Hom.toFun a))
        (x : C) :
    KLocallyRingedSpace.Hom.toFun a (KLocallyRingedSpace.Hom.toFun
        (liftAlong a g h) x) = KLocallyRingedSpace.Hom.toFun g x :=
  congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ x) (liftAlong_comp a g h)

theorem liftAlong_unique {A B C : KLocallyRingedSpace.{u} K} (a : B ⟶ A)
    [LocallyRingedSpace.IsOpenImmersion a.1] (g : C ⟶ A)
    (h : Set.range (KLocallyRingedSpace.Hom.toFun g) ⊆ Set.range (KLocallyRingedSpace.Hom.toFun a))
        (l : C ⟶ B) (hl : l ≫ a = g) :
    l = liftAlong a g h :=
  hom_ext_of_comp_eq a (by rw [liftAlong_comp, hl])

/-! ### Double restrictions -/

/-- The inclusion of the double restriction `(A | U) | W` into `A`. -/
noncomputable def incl₂ (A : KLocallyRingedSpace.{u} K) (U : Opens A)
    (W : Opens (A.restrictOpen U)) : (A.restrictOpen U).restrictOpen W ⟶ A :=
  ofRestrict (A.restrictOpen U) W ≫ ofRestrict A U

instance (A : KLocallyRingedSpace.{u} K) (U : Opens A) (W : Opens (A.restrictOpen U)) :
    LocallyRingedSpace.IsOpenImmersion (incl₂ A U W).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
    ((ofRestrict (A.restrictOpen U) W).1 ≫ (ofRestrict A U).1))

theorem toFun_incl₂ (A : KLocallyRingedSpace.{u} K) (U : Opens A) (W : Opens (A.restrictOpen U))
    (x : (A.restrictOpen U).restrictOpen W) : KLocallyRingedSpace.Hom.toFun
        (incl₂ A U W) x = x.1.1 :=
  rfl

theorem mem_range_toFun_incl₂ (A : KLocallyRingedSpace.{u} K) (U : Opens A)
    (W : Opens (A.restrictOpen U)) (y : A) :
    y ∈ Set.range (KLocallyRingedSpace.Hom.toFun (incl₂ A U W)) ↔ ∃ h : y ∈ U, (⟨y,
        h⟩ : A.restrictOpen U) ∈ W := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1.2, x.2⟩
  · rintro ⟨h, hW⟩
    exact ⟨⟨⟨y, h⟩, hW⟩, rfl⟩

end AnalyticSpace.Glue
