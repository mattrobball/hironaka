/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientFactorizationTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Isomorphisms over an open of the target: composition, monotonicity, transport

The predicate `f.IsIsoOver V` (`f` restricts to an isomorphism `f⁻¹V → V`; condition (2) of a
resolution in [Hir64, Introduction], clause (2) of [Kol07, Theorem 45]) and its bookkeeping, needed
to read off that the resolution morphism is an isomorphism over the simple locus piece by piece:

* `Hom.restrictSet_comp`: the restriction of a composite is the composite of the restrictions;
* `Hom.isIsoOver_of_isOpenImmersion`: an open immersion is an isomorphism over every open subset
  of its range (the point-level criterion `isIso_restrictTo_of_bijOn_of_bijective_stalkMap`);
* `Hom.IsIsoOver.comp`: `f ≫ g` is an isomorphism over `V` when `g` is over `V` and `f` over
  `g⁻¹V`;
* `Hom.IsIsoOver.mono`: an isomorphism over the open `V` is one over every open `P ⊆ V` (the
  criterion again, from `injOn`/`surjOn`/the stalk maps over `V`);
* `Hom.IsIsoOver.of_isIso_restrictSet_comm`: `IsIsoOver` transports along an isomorphism over the
  base (`exists_restrictSet_isIso_of_restrictSet_isIso_of_subset` of
  `Hironaka/Resolution/Analytic/Kol07Thm45/AmbientFactorizationTransport.lean`).

Routine; used by `Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverIsoReg.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/CoproductLevelPair.lean`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology AlgebraicGeometry

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- **The restriction of a composite to opens is the composite of the restrictions**: both agree
after the open immersion `Z|U'' ⟶ Z` (`Hom.restrictTo_comp_ofRestrict`). -/
theorem Hom.restrictTo_comp {A B Z : KLocallyRingedSpace.{u} K} (f : A ⟶ B) (g : B ⟶ Z)
    (U : Opens A) (U' : Opens B) (U'' : Opens Z) (hf : ∀ a ∈ U, Hom.toFun f a ∈ U')
    (hg : ∀ b ∈ U', Hom.toFun g b ∈ U'') (h : ∀ a ∈ U, Hom.toFun (f ≫ g) a ∈ U'') :
    Hom.restrictTo (f ≫ g) U U'' h = Hom.restrictTo f U U' hf ≫ Hom.restrictTo g U' U'' hg := by
  refine Hom.ext_of_comp_ofRestrict ?_
  rw [Hom.restrictTo_comp_ofRestrict, Category.assoc, Hom.restrictTo_comp_ofRestrict,
    ← Category.assoc (Hom.restrictTo f U U' hf), Hom.restrictTo_comp_ofRestrict, Category.assoc]

end AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- **The restriction of a composite is the composite of the restrictions** — `Hom.restrictTo_comp`
at the opens `openOf` (the two spellings of `(f ≫ g)⁻¹V` are definitionally equal). -/
theorem Hom.restrictSet_comp {A B X : AnalyticSpace.{u} K} (f : A ⟶ B) (g : B ⟶ X) (V : Set X) :
    Hom.restrictSet (f ≫ g) V =
      Hom.restrictSet f (g ⁻¹' V) ≫ Hom.restrictSet g V :=
  KLocallyRingedSpace.Hom.restrictTo_comp f g (openOf A (KLocallyRingedSpace.Hom.toFun f ⁻¹'
      (KLocallyRingedSpace.Hom.toFun g ⁻¹' V)))
    (openOf B (KLocallyRingedSpace.Hom.toFun g ⁻¹' V)) (openOf X V)
    (Hom.mapsTo_openOf f (KLocallyRingedSpace.Hom.toFun g ⁻¹' V)) (Hom.mapsTo_openOf g V)
    (Hom.mapsTo_openOf (f ≫ g) V)

/-- **An open immersion is an isomorphism over every open subset of its range**: on `g⁻¹V → V` it is
a bijection with bijective stalk maps (`isIso_restrictTo_of_bijOn_of_bijective_stalkMap`). -/
theorem Hom.isIsoOver_of_isOpenImmersion {B X : AnalyticSpace.{u} K} (g : B ⟶ X)
    [hg : LocallyRingedSpace.IsOpenImmersion g.1] {V : Set X} (hV : IsOpen V)
    (hsub : V ⊆ range (KLocallyRingedSpace.Hom.toFun g)) :
    g.IsIsoOver V := by
  change CategoryTheory.IsIso (C := AnalyticSpace.{u} K) (Hom.restrictSet g V)
  refine isIso_of_isIso_toKLocallyRingedSpace _ ?_
  rw [Hom.restrictSet_eq_restrictTo]
  refine isIso_restrictTo_of_bijOn_of_bijective_stalkMap g _ _ _ ?_ ?_
  · rw [openOf_of_isOpen B (hV.preimage (KLocallyRingedSpace.Hom.continuous_toFun g)),
      openOf_of_isOpen X hV]
    refine ⟨fun b hb => hb, (KLocallyRingedSpace.Hom.isOpenEmbedding_toFun g).injective.injOn,
      fun x hx => ?_⟩
    obtain ⟨b, rfl⟩ := hsub hx
    exact ⟨b, hx, rfl⟩
  · intro u _
    have hiso : CategoryTheory.IsIso (g.1.stalkMap u) :=
      LocallyRingedSpace.IsOpenImmersion.stalk_iso g.1 u
    exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

/-- **`f ≫ g` is an isomorphism over `V` when `g` is one over `V` and `f` one over `g⁻¹V`**
(`Hom.restrictSet_comp`). -/
theorem Hom.IsIsoOver.comp {A B X : AnalyticSpace.{u} K} {f : A ⟶ B} {g : B ⟶ X} {V : Set X}
    (hf : f.IsIsoOver (g ⁻¹' V)) (hg : g.IsIsoOver V) :
    (f ≫ g).IsIsoOver V := by
  have hf' : CategoryTheory.IsIso (Hom.restrictSet f (g ⁻¹' V)) := hf
  have hg' : CategoryTheory.IsIso (Hom.restrictSet g V) := hg
  have hc : CategoryTheory.IsIso
      (Hom.restrictSet f (g ⁻¹' V) ≫ Hom.restrictSet g V) :=
    inferInstance
  change CategoryTheory.IsIso (C := AnalyticSpace.{u} K) (Hom.restrictSet (f ≫ g) V)
  rw [Hom.restrictSet_comp]
  exact hc

/-- **An isomorphism over the open `V` is one over every open `P ⊆ V`**: on `f⁻¹P → P` the map is a
bijection (`injOn`/`surjOn` over `V`) with bijective stalk maps
(`bijective_stalkMap_of_isIso_restrictSet`), so the point-level criterion applies. -/
theorem Hom.IsIsoOver.mono {X Y : AnalyticSpace.{u} K} {f : Y ⟶ X} {V P : Set X} (hV : IsOpen V)
    (hP : IsOpen P) (hPV : P ⊆ V) (h : f.IsIsoOver V) :
    f.IsIsoOver P := by
  have hV' : CategoryTheory.IsIso (Hom.restrictSet f V) := h
  change CategoryTheory.IsIso (C := AnalyticSpace.{u} K) (Hom.restrictSet f P)
  refine isIso_of_isIso_toKLocallyRingedSpace _ ?_
  rw [Hom.restrictSet_eq_restrictTo]
  refine isIso_restrictTo_of_bijOn_of_bijective_stalkMap f _ _ _ ?_ ?_
  · rw [openOf_of_isOpen Y (hP.preimage (KLocallyRingedSpace.Hom.continuous_toFun f)),
      openOf_of_isOpen X hP]
    refine ⟨fun y hy => hy, (injOn_of_isIso_restrictSet f hV).mono fun y hy => hPV hy,
      fun x hx => ?_⟩
    obtain ⟨y, -, rfl⟩ := surjOn_of_isIso_restrictSet f hV (hPV hx)
    exact ⟨y, hx, rfl⟩
  · intro u hu
    have hu' : KLocallyRingedSpace.Hom.toFun f u ∈ P :=
      (SetLike.ext_iff.mp (openOf_of_isOpen Y
        (hP.preimage (KLocallyRingedSpace.Hom.continuous_toFun f))) u).mp hu
    exact bijective_stalkMap_of_isIso_restrictSet f hV u (hPV hu')

/-- **`IsIsoOver` transports along an isomorphism over the base**: with `e : Y|f⁻¹O ≅ Y'|f'⁻¹O` over
`X|O` and an open `P ⊆ O`, `f'` an isomorphism over `P` makes `f` one — `f|P = e' ≫ f'|P` for the
restriction `e'` of `e` (`exists_restrictSet_isIso_of_restrictSet_isIso_of_subset`). -/
theorem Hom.IsIsoOver.of_isIso_restrictSet_comm {X Y Y' : AnalyticSpace.{u} K} (f : Y ⟶ X)
    (f' : Y' ⟶ X) {O P : Set X}
    (e : Y.restrictSet (KLocallyRingedSpace.Hom.toFun f ⁻¹' O) ⟶
      Y'.restrictSet (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O)) (he : CategoryTheory.IsIso e)
    (hcomm : e ≫ Hom.restrictSet f' O = Hom.restrictSet f O) (hP : IsOpen P) (hPO : P ⊆ O)
    (h : f'.IsIsoOver P) :
    f.IsIsoOver P := by
  obtain ⟨e', he', hcomm'⟩ :=
    exists_restrictSet_isIso_of_restrictSet_isIso_of_subset f f' e he hcomm hP hPO
  have h' : CategoryTheory.IsIso (Hom.restrictSet f' P) := h
  change CategoryTheory.IsIso (C := AnalyticSpace.{u} K) (Hom.restrictSet f P)
  refine isIso_of_isIso_toKLocallyRingedSpace _ ?_
  rw [← hcomm']
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ he' (isIso_toKLocallyRingedSpace_of_isIso _)

end AnalyticSpace

end
