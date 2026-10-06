/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Chart
public import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.Manifold.Germ.StalkMap
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lifting a morphism to `Kⁿ` into a manifold through a chart

A `K`-morphism `χ : X → (Kⁿ, 𝒜)` from a `K`-local-ringed space whose values lie in
`G = ψ(Φ.target)`, the domain of a chart `Φ` of a manifold `M'`, lifts to a `K`-morphism
`chartLift : X → Sp(M')` with image in `Φ.source`, namely `X ≅ X|⊤ → (Kⁿ, 𝒜)|G ≅ Sp(G) → Sp(M')`
(`restrictOpenTopIso`, `Hom.restrictTo`, `ofManifold_restrictOpen_iso`, and `Sp` of the inverse
chart `chartFromOpens` of `Hironaka/AnalyticSpace/Manifold/Chart.lean`). Its base point is
`Φ⁻¹ (ψ⁻¹ (χ x))` (`chartLift_base`) and it pulls the coordinate germs `u_j` of `Φ` back to the
pulled-back coordinates `χ^* z_j` (`stalkMap_chartLift_coord`); with the morphisms from sections of
`Hironaka/AnalyticSpace/HomOfSections.lean` this produces the local lifts through the charted
blow-up. The open subspace `(G, 𝒜_G)` is Hironaka's
[Hir64, Ch. 0, §1, p. 119]; that a morphism into `(Kⁿ, 𝒜)` is determined by its coordinate functions
is the library's (`hom_ext_of_coord`, `Hironaka/AnalyticSpace/HomExt.lean`; compare the local
`Kⁿ`-coordinations of [Hir64, Ch. 0, §1, p. 120]). The lemmas are general (any `K`-local-ringed
space `X`, any chart of any analytic manifold); also used by
`Hironaka/Manifold/Sequence/Restrict/`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-- The stalk map of a composite of `K`-morphisms, elementwise. -/
theorem stalkMap_comp_apply {X Y W : KLocallyRingedSpace.{u} K} (f : X ⟶ Y) (g : Y ⟶ W) (x : X)
    (s : W.toLocallyRingedSpace.presheaf.stalk (g.1.base (f.1.base x))) :
    ((f ≫ g).1.stalkMap x).hom s = (f.1.stalkMap x).hom ((g.1.stalkMap (f.1.base x)).hom s) := by
  change ((f.1 ≫ g.1).stalkMap x).hom s = _
  exact congrArg (fun φ => φ.hom s) (LocallyRingedSpace.stalkMap_comp f.1 g.1 x)

/-- The isomorphism `X | ⊤ ≅ X` (`restrictOpenTopIso`) is, as a morphism, the open immersion
`X | ⊤ ⟶ X`. -/
theorem restrictOpenTopIso_hom (X : KLocallyRingedSpace.{u} K) :
    (restrictOpenTopIso X).hom = ofRestrict X ⊤ := by
  have : LocallyRingedSpace.IsOpenImmersion (𝟙 X : X ⟶ X).1 :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 X.toLocallyRingedSpace))
  exact (Category.comp_id _).symm.trans (isoOfRangeEq_hom_comp (ofRestrict X ⊤) (𝟙 X) _)

/-- `X ⟶ X | ⊤ ⟶ X` is the identity. -/
theorem restrictOpenTopIso_inv_comp_ofRestrict (X : KLocallyRingedSpace.{u} K) :
    (restrictOpenTopIso X).inv ≫ ofRestrict X ⊤ = 𝟙 X := by
  rw [← restrictOpenTopIso_hom, Iso.inv_hom_id]

/-- Transport of a pulled-back coordinate germ of `Kⁿ` along an equality of morphisms. -/
theorem stalkMap_apply_coordAt_congr {n : ℕ} {Y : KLocallyRingedSpace.{u} K}
    {F₁ F₂ : Y ⟶ affine.{u} K n} (h : F₁ = F₂) (y : Y) (j : Fin n) :
    (F₁.1.stalkMap y).hom (coordAt K n (F₁.1.base y) j) =
      (F₂.1.stalkMap y).hom (coordAt K n (F₂.1.base y) j) := by
  subst h
  rfl

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ} (ψ : E ≃L[K] (Fin n → K))
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']
  {Φ : OpenPartialHomeomorph M' E} (hΦ : Φ ∈ maximalAtlas 𝓘(K, E) ω M')

include hΦ

/-- The inverse chart `G → M'`, `y ↦ Φ⁻¹ (ψ⁻¹ y)`, is analytic (`chartFromOpens`). -/
theorem contMDiff_val_chartFromOpens :
    ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K, E) ω
      (fun y : chartOpens ψ Φ => (chartFromOpens ψ Φ y : M')) :=
  contMDiff_subtype_val.comp (contMDiff_chartFromOpens ψ hΦ)

/-- `Sp(G) → Sp(M')`, `y ↦ Φ⁻¹ (ψ⁻¹ y)`. -/
noncomputable def chartFromOpensHom :
    ofManifold K (Kn.{u} K n) (chartOpens ψ Φ) ⟶ ofManifold K E M' :=
  ofManifoldHom (fun y : chartOpens ψ Φ => (chartFromOpens ψ Φ y : M'))
    (contMDiff_val_chartFromOpens ψ hΦ)

/-- `(Kⁿ, 𝒜)|G ⟶ Sp(M')`. -/
noncomputable def chartOpensHom :
    (affine.{u} K n).restrictOpen (chartOpens ψ Φ) ⟶ ofManifold K E M' :=
  (ofManifold_restrictOpen_iso (chartOpens ψ Φ)).hom ≫ chartFromOpensHom ψ hΦ

/-- The inverse chart `Sp(G) → Sp(M')` pulls the coordinate germ `u_j` of `Φ` back to the coordinate
germ `z_j` of `Kⁿ`, both read on `G ⊆ Kⁿ`. -/
theorem germMap_chartFromOpens_coord (c : chartOpens ψ Φ)
    (hc : (chartFromOpens ψ Φ c : M') ∈ Φ.source) (j : Fin n) :
    germMap (fun y : chartOpens ψ Φ => (chartFromOpens ψ Φ y : M'))
        (contMDiff_val_chartFromOpens ψ hΦ) c (coord E ψ Φ hΦ hc j) =
      germMap (Subtype.val : chartOpens ψ Φ → Kn.{u} K n) contMDiff_subtype_val c
        (coordAt K n c.1 j) := by
  apply stalkToGerm_injective 𝓘(K, Kn.{u} K n) ω (chartOpens ψ Φ) c
  rw [stalkToGerm_germMap, stalkToGerm_germMap, stalkToGerm_coord, stalkToGerm_coord,
    Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto, Filter.Germ.coe_eq]
  filter_upwards with x
  rw [Function.comp_apply, Function.comp_apply,
    extendSection_of_mem K E _ (Φ.map_target ((mem_chartOpens ψ Φ).mp x.2)),
    extendSection_of_mem K (Kn.{u} K n) _ (Set.mem_univ x.1)]
  change ψ (Φ (Φ.symm (ψ.symm x.1.down))) j = _
  rw [Φ.right_inv ((mem_chartOpens ψ Φ).mp x.2), ψ.apply_symm_apply]
  rfl

variable {X : KLocallyRingedSpace.{u} K} (χ : X ⟶ affine.{u} K n)
  (hval : ∀ x, Hom.toFun χ x ∈ chartOpens ψ Φ)

/-- The lift into `Sp(M')` through the chart `Φ` of a `K`-morphism `χ : X → Kⁿ` with values in
`ψ(Φ.target)`. -/
noncomputable def chartLift : X ⟶ ofManifold K E M' :=
  (restrictOpenTopIso X).inv ≫
    (Hom.restrictTo χ ⊤ (chartOpens ψ Φ) (fun x _ => hval x) ≫ chartOpensHom ψ hΦ)

/-- The base point of the chart lift: `Φ⁻¹ (ψ⁻¹ (χ x))`. -/
theorem chartLift_base (x : X) :
    (chartLift ψ hΦ χ hval).1.base x = Φ.symm (ψ.symm (χ.1.base x).down) := by
  have h1 : (Hom.toFun (restrictOpenTopIso X).inv x).1 = x :=
    congrArg (fun F : X ⟶ X => Hom.toFun F x) (restrictOpenTopIso_inv_comp_ofRestrict X)
  have h2 := Hom.toFun_restrictTo χ ⊤ (chartOpens ψ Φ) (fun x _ => hval x)
    (Hom.toFun (restrictOpenTopIso X).inv x)
  have h3 : ∀ b : (affine.{u} K n).restrictOpen (chartOpens ψ Φ),
      (Hom.toFun (ofManifold_restrictOpen_iso (chartOpens ψ Φ)).hom b).1 = b.1 :=
    fun b => congrArg (fun F => Hom.toFun F b)
      (ofManifold_restrictOpen_iso_hom_comp (chartOpens ψ Φ))
  change Φ.symm (ψ.symm (Hom.toFun (ofManifold_restrictOpen_iso (chartOpens ψ Φ)).hom
    (Hom.toFun (Hom.restrictTo χ ⊤ (chartOpens ψ Φ) (fun x _ => hval x))
      (Hom.toFun (restrictOpenTopIso X).inv x))).1.down) = _
  rw [h3, h2, h1]
  rfl

/-- The chart lift lands in the chart's source. -/
theorem chartLift_base_mem (x : X) : (chartLift ψ hΦ χ hval).1.base x ∈ Φ.source := by
  rw [chartLift_base]
  exact Φ.map_target ((mem_chartOpens ψ Φ).mp (hval x))

/-- The chart lift pulls the coordinate germs `u_j` of `Φ` back to the pulled-back coordinate germs
`χ^* z_j` — the stalk-level description of the lift, through the four factors
`X ≅ X|⊤ → (Kⁿ,𝒜)|G ≅ Sp(G) → Sp(M')`. -/
theorem stalkMap_chartLift_coord (x : X) (j : Fin n) :
    ((chartLift ψ hΦ χ hval).1.stalkMap x).hom
        (coord E ψ Φ hΦ (chartLift_base_mem ψ hΦ χ hval x) j) =
      (χ.1.stalkMap x).hom (coordAt K n (χ.1.base x) j) := by
  set A := (restrictOpenTopIso X).inv with hA
  set B := Hom.restrictTo χ ⊤ (chartOpens ψ Φ) (fun x _ => hval x) with hB
  set C := (ofManifold_restrictOpen_iso (K := K) (E := Kn.{u} K n) (chartOpens ψ Φ)).hom with hC
  set D := chartFromOpensHom ψ hΦ with hD
  have hBR : B ≫ ofRestrict (affine.{u} K n) (chartOpens ψ Φ) = ofRestrict X ⊤ ≫ χ :=
    Hom.restrictTo_comp_ofRestrict χ ⊤ _ _
  have hAχ : A ≫ (ofRestrict X ⊤ ≫ χ) = χ := by
    rw [hA, ← Category.assoc, restrictOpenTopIso_inv_comp_ofRestrict, Category.id_comp]
  have e0 := stalkMap_comp_apply A (B ≫ (C ≫ D)) x
    (coord E ψ Φ hΦ (chartLift_base_mem ψ hΦ χ hval x) j)
  have e1 := stalkMap_comp_apply B (C ≫ D) (A.1.base x)
    (coord E ψ Φ hΦ (chartLift_base_mem ψ hΦ χ hval x) j)
  have e2 := stalkMap_comp_apply C D (B.1.base (A.1.base x))
    (coord E ψ Φ hΦ (chartLift_base_mem ψ hΦ χ hval x) j)
  have e3 : (D.1.stalkMap (C.1.base (B.1.base (A.1.base x)))).hom
      (coord E ψ Φ hΦ (chartLift_base_mem ψ hΦ χ hval x) j) =
      ((ofManifoldHom (Subtype.val : chartOpens ψ Φ → Kn.{u} K n)
        contMDiff_subtype_val).1.stalkMap (C.1.base (B.1.base (A.1.base x)))).hom
        (coordAt K n (C.1.base (B.1.base (A.1.base x))).1 j) :=
    (stalkMap_ofManifoldHom_eq_germMap _ _ _ _).trans
      ((germMap_chartFromOpens_coord ψ hΦ (C.1.base (B.1.base (A.1.base x)))
        (chartLift_base_mem ψ hΦ χ hval x) j).trans
        (stalkMap_ofManifoldHom_eq_germMap _ _ _ _).symm)
  have e4 : (C.1.stalkMap (B.1.base (A.1.base x))).hom
      (((ofManifoldHom (Subtype.val : chartOpens ψ Φ → Kn.{u} K n)
        contMDiff_subtype_val).1.stalkMap (C.1.base (B.1.base (A.1.base x)))).hom
        (coordAt K n (C.1.base (B.1.base (A.1.base x))).1 j)) =
      ((ofRestrict (affine.{u} K n) (chartOpens ψ Φ)).1.stalkMap (B.1.base (A.1.base x))).hom
        (coordAt K n ((ofRestrict (affine.{u} K n) (chartOpens ψ Φ)).1.base
          (B.1.base (A.1.base x))) j) :=
    (stalkMap_comp_apply C _ _ _).symm.trans (stalkMap_apply_coordAt_congr
      (ofManifold_restrictOpen_iso_hom_comp (K := K) (E := Kn.{u} K n) (chartOpens ψ Φ)) _ j)
  have e5 : (B.1.stalkMap (A.1.base x)).hom
      (((ofRestrict (affine.{u} K n) (chartOpens ψ Φ)).1.stalkMap (B.1.base (A.1.base x))).hom
        (coordAt K n ((ofRestrict (affine.{u} K n) (chartOpens ψ Φ)).1.base
          (B.1.base (A.1.base x))) j)) =
      ((ofRestrict X ⊤ ≫ χ).1.stalkMap (A.1.base x)).hom
        (coordAt K n ((ofRestrict X ⊤ ≫ χ).1.base (A.1.base x)) j) :=
    (stalkMap_comp_apply B _ _ _).symm.trans (stalkMap_apply_coordAt_congr hBR _ j)
  have e6 : (A.1.stalkMap x).hom (((ofRestrict X ⊤ ≫ χ).1.stalkMap (A.1.base x)).hom
        (coordAt K n ((ofRestrict X ⊤ ≫ χ).1.base (A.1.base x)) j)) =
      (χ.1.stalkMap x).hom (coordAt K n (χ.1.base x) j) :=
    (stalkMap_comp_apply A _ _ _).symm.trans (stalkMap_apply_coordAt_congr hAχ x j)
  exact e0.trans ((congrArg (A.1.stalkMap x).hom (e1.trans ((congrArg (B.1.stalkMap _).hom
    (e2.trans ((congrArg (C.1.stalkMap _).hom e3).trans e4))).trans e5))).trans e6)

end Chart

end AnalyticSpace.KLocallyRingedSpace
