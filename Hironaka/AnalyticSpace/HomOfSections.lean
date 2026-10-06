/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.GlueHomAffine
public import Hironaka.AnalyticSpace.Model
import Hironaka.AnalyticSpace.HomOfSectionsModel
import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `K`-morphisms into `(Kⁿ, 𝒜_{Kⁿ})` from `n` global sections

A `K`-morphism from an analytic `K`-space `X` into `(Kⁿ, 𝒜_{Kⁿ})` is the same as `n` global
sections of `𝒪_X`: `AnalyticSpace.homOfSections X t : X ⟶ (Kⁿ, 𝒜_{Kⁿ})` with
`(homOfSections X t).pullbackΓ (coordSection K n i) = t i`, unique by `hom_ext_of_coord`
(`Hironaka/AnalyticSpace/HomExt.lean`); the two together are
`AnalyticSpace.existsUnique_hom_pullbackΓ_coord`, `Hom(X, Kⁿ) ≃ Γ(X, 𝒪_X)ⁿ`. This is the form in
which local coordinations [Hir64, Ch. 0, §1, p. 120] and the extended coordinations of a
complexification are produced. Also the chart form: a `K`-morphism into `(Kⁿ, 𝒜_{Kⁿ})` with
image in an open `V` factors uniquely through `(Kⁿ, 𝒜_{Kⁿ})|V` (`Hom.liftRestrict`,
`existsUnique_hom_restrictOpen_of_range`).

**Assembly.** Around every point `x` a chart `e : X|U ≅ L` onto a local model; the sections
`σ_i := e.inv^*(t_i|U)` of `L` define `localModel.homOfSections σ : L ⟶ Kⁿ`
(`Hironaka/AnalyticSpace/HomOfSectionsModel.lean`), and
`e.hom ≫ localModel.homOfSections σ : X|U ⟶ Kⁿ` has coordinate pullbacks `t_i|U`
(functoriality of the pullback, `e.hom ≫ e.inv = 𝟙`). These pieces have the same germs of
coordinate pullbacks at every point (the germ of `t_i`), hence agree on base points and on germs
of all pullbacks (`Hironaka/AnalyticSpace/HomOfSectionsCompat.lean`), and glue by `glueHomAffine`
(`Hironaka/AnalyticSpace/GlueHomAffine.lean`). Not in the sources as a stated result.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u


open AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K] {n : ℕ}

namespace AnalyticSpace

variable (X : AnalyticSpace.{u} K) (t : Fin n → X.toLocallyRingedSpace.presheaf.obj (op ⊤))

/-- Chart data at a point: an open neighbourhood and a `K`-isomorphism onto a local model, with a
`K`-morphism of the chart into `(Kⁿ, 𝒜_{Kⁿ})` whose coordinate pullbacks are the restrictions of
the `t i`. -/
structure ChartPiece (x : X) where
  /-- The chart's open neighbourhood. -/
  U : Opens X
  mem : x ∈ U
  /-- The morphism of the chart into `Kⁿ`. -/
  φ : X.toKLocallyRingedSpace.restrictOpen U ⟶ affine.{u} K n
  coord : ∀ i, φ.pullbackΓ (coordSection K n i) =
    (ofRestrict X.toKLocallyRingedSpace U).pullbackΓ (t i)

theorem nonempty_chartPiece (x : X) : Nonempty (ChartPiece X t x) := by
  obtain ⟨U, hxU, m, k, G, f, ⟨e⟩⟩ := exists_kIso_localModel X x
  let σ : Fin n → (localModel K m G f).toLocallyRingedSpace.presheaf.obj (op ⊤) :=
    fun i => e.inv.pullbackΓ ((ofRestrict X.toKLocallyRingedSpace U).pullbackΓ (t i))
  refine ⟨⟨U, hxU, e.hom ≫ localModel.homOfSections m G f σ, fun i => ?_⟩⟩
  have h1 := Hom.pullbackΓ_comp e.hom (localModel.homOfSections m G f σ) (coordSection K n i)
  have h2 := localModel.pullbackΓ_homOfSections_coordSection m G f σ i
  rw [h1, h2]
  exact Iso.hom_pullbackΓ_inv_pullbackΓ e _

/-- A choice of chart piece at every point. -/
def chartPiece (x : X) : ChartPiece X t x := Classical.choice (nonempty_chartPiece X t x)

/-- The germ at `z ∈ U x` of the coordinate pullback of the piece at `x` is the germ of `t i`. -/
theorem germ_pullbackΓ_chartPiece_coord (x : X) {z : X} (hz : z ∈ (chartPiece X t x).U)
    (i : Fin n) :
    X.toLocallyRingedSpace.presheaf.germ (imgOpens X.toKLocallyRingedSpace (chartPiece X t x).U ⊤)
        z (mem_imgOpens_of_mem _ hz trivial) ((chartPiece X t x).φ.pullbackΓ (coordSection K n i)) =
      X.toLocallyRingedSpace.presheaf.germ ⊤ z trivial (t i) := by
  rw [(chartPiece X t x).coord i]
  exact germ_pullbackΓ_ofRestrict (chartPiece X t x).U hz (t i)

theorem hcoord_chartPiece (x x' : X) {z : X} (hz : z ∈ (chartPiece X t x).U)
    (hz' : z ∈ (chartPiece X t x').U) (i : Fin n) :
    X.toLocallyRingedSpace.presheaf.germ (imgOpens X.toKLocallyRingedSpace (chartPiece X t x).U ⊤)
        z (mem_imgOpens_of_mem _ hz trivial) ((chartPiece X t x).φ.pullbackΓ (coordSection K n i)) =
      X.toLocallyRingedSpace.presheaf.germ
        (imgOpens X.toKLocallyRingedSpace (chartPiece X t x').U ⊤) z
        (mem_imgOpens_of_mem _ hz' trivial)
        ((chartPiece X t x').φ.pullbackΓ (coordSection K n i)) :=
  (germ_pullbackΓ_chartPiece_coord X t x hz i).trans
    (germ_pullbackΓ_chartPiece_coord X t x' hz' i).symm

theorem chartPiece_hbase : ∀ (x x' : X) (z : X) (hz : z ∈ (fun x => (chartPiece X t x).U) x)
    (hz' : z ∈ (fun x => (chartPiece X t x).U) x'),
    (chartPiece X t x).φ.1.base ⟨z, hz⟩ = (chartPiece X t x').φ.1.base ⟨z, hz'⟩ :=
  fun x x' _ hz hz' => base_eq_of_germ_pullbackΓ_coord X.toKLocallyRingedSpace _ _ hz hz'
    (hcoord_chartPiece X t x x' hz hz')

theorem chartPiece_hgerm (x x' : X) (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) (z : X)
    (hzi : z ∈ locV X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
      (fun x => (chartPiece X t x).φ) x V)
    (hzj : z ∈ locV X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
      (fun x => (chartPiece X t x).φ) x' V) :
    X.toLocallyRingedSpace.presheaf.germ (locV X.toKLocallyRingedSpace
        (fun x => (chartPiece X t x).U) (fun x => (chartPiece X t x).φ) x V) z hzi
        (locSec X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
          (fun x => (chartPiece X t x).φ) x V F) =
      X.toLocallyRingedSpace.presheaf.germ (locV X.toKLocallyRingedSpace
        (fun x => (chartPiece X t x).U) (fun x => (chartPiece X t x).φ) x' V) z hzj
        (locSec X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
          (fun x => (chartPiece X t x).φ) x' V F) := by
  obtain ⟨hz, hV⟩ := (mem_locV X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
    (fun x => (chartPiece X t x).φ)).mp hzi
  obtain ⟨hz', hV'⟩ := (mem_locV X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
    (fun x => (chartPiece X t x).φ)).mp hzj
  exact germ_c_app_eq_of_germ_pullbackΓ_coord X.toKLocallyRingedSpace _ _ hz hz'
    (hcoord_chartPiece X t x x' hz hz') (X.isNoetherianRing_stalk z) V hV hV' F

/-- **The `K`-morphism `X ⟶ (Kⁿ, 𝒜_{Kⁿ})` with coordinate functions `t₁, …, tₙ`**, for an analytic
`K`-space `X`. -/
def homOfSections : X.toKLocallyRingedSpace ⟶ affine.{u} K n :=
  glueHomAffine X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
    (fun z => ⟨z, (chartPiece X t z).mem⟩) (fun x => (chartPiece X t x).φ) (chartPiece_hbase X t)
    (fun x x' V F z hzi hzj => chartPiece_hgerm X t x x' V F z hzi hzj)

/-- The coordinate pullbacks of `homOfSections X t` are the `t i`. -/
theorem pullbackΓ_homOfSections_coordSection (i : Fin n) :
    (homOfSections X t).pullbackΓ (coordSection K n i) = t i := by
  apply TopCat.Presheaf.section_ext X.toLocallyRingedSpace.𝒪
  intro z hz
  have h1 := germ_pullbackΓ_glueHomAffine X.toKLocallyRingedSpace (fun x => (chartPiece X t x).U)
    (fun z => ⟨z, (chartPiece X t z).mem⟩) (fun x => (chartPiece X t x).φ) (chartPiece_hbase X t)
    (fun x x' V F z hzi hzj => chartPiece_hgerm X t x x' V F z hzi hzj) (coordSection K n i) z
    (chartPiece X t z).mem
  have h2 := germ_pullbackΓ_chartPiece_coord X t z (chartPiece X t z).mem i
  exact h1.trans h2

/-- `Hom(X, Kⁿ) ≃ Γ(X, 𝒪_X)ⁿ`: there is exactly one `K`-morphism `X ⟶ (Kⁿ, 𝒜_{Kⁿ})` with
prescribed coordinate pullbacks. -/
theorem existsUnique_hom_pullbackΓ_coord :
    ∃! φ : X.toKLocallyRingedSpace ⟶ affine.{u} K n,
      ∀ i, φ.pullbackΓ (coordSection K n i) = t i :=
  ⟨homOfSections X t, pullbackΓ_homOfSections_coordSection X t, fun φ hφ =>
    hom_ext_of_coord X φ (homOfSections X t) fun i =>
      (hφ i).trans (pullbackΓ_homOfSections_coordSection X t i).symm⟩

/-- The morphism with the coordinate pullbacks of `φ` is `φ` (uniqueness). -/
theorem homOfSections_pullbackΓ_coord (φ : X.toKLocallyRingedSpace ⟶ affine.{u} K n) :
    homOfSections X (fun i => φ.pullbackΓ (coordSection K n i)) = φ :=
  hom_ext_of_coord X _ φ fun i => pullbackΓ_homOfSections_coordSection X _ i

end AnalyticSpace

namespace AnalyticSpace.KLocallyRingedSpace

variable {X Y : KLocallyRingedSpace.{u} K}

/-- The lift of a `K`-morphism `g : X ⟶ Y` with `g(X) ⊆ U` through the open immersion `Y|U ⟶ Y`
(Mathlib's universal property of open immersions of locally ringed spaces; the `K`-condition is
inherited from `g`). Hironaka's `(G, 𝒜_G)` is `(Kⁿ, 𝒜_{Kⁿ})|G` [Hir64, Ch. 0, §1], so a morphism
into `Kⁿ` landing in `G` is a morphism into `(G, 𝒜_G)`. -/
def Hom.liftRestrict (g : X ⟶ Y) (U : Opens Y) (h : ∀ x, Hom.toFun g x ∈ U) :
    X ⟶ Y.restrictOpen U :=
  have h₁ : LocallyRingedSpace.IsOpenImmersion (ofRestrict Y U).1 := inferInstance
  have hr : Set.range g.1.base ⊆ Set.range (ofRestrict Y U).1.base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨Hom.toFun g x, h x⟩, rfl⟩
  Hom.ofFac g (ofRestrict Y U)
    (LocallyRingedSpace.IsOpenImmersion.lift (H := h₁) (ofRestrict Y U).1 g.1 hr)
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁) _ _ _)

theorem Hom.liftRestrict_comp_ofRestrict (g : X ⟶ Y) (U : Opens Y) (h : ∀ x, Hom.toFun g x ∈ U) :
    Hom.liftRestrict g U h ≫ ofRestrict Y U = g :=
  Hom.ext (by
    rw [Hom.comp_val, Hom.liftRestrict, Hom.ofFac_val]
    exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)

/-- Open immersions are monomorphisms: two `K`-morphisms into `Y|U` with the same composite into `Y`
are equal. -/
theorem Hom.ext_of_comp_ofRestrict {U : Opens Y} {φ ψ : X ⟶ Y.restrictOpen U}
    (h : φ ≫ ofRestrict Y U = ψ ≫ ofRestrict Y U) : φ = ψ :=
  Hom.ext ((cancel_mono (ofRestrict Y U).1).mp (congrArg Subtype.val h))

/-- A `K`-morphism `X ⟶ (Kⁿ, 𝒜_{Kⁿ})` whose image lies in the open `V` factors uniquely through
`(Kⁿ, 𝒜_{Kⁿ})|V`. -/
theorem existsUnique_hom_restrictOpen_of_range (X : KLocallyRingedSpace.{u} K)
    (V : Opens (Kn.{u} K n)) (φ₀ : X ⟶ affine.{u} K n) (h : ∀ x : X, Hom.toFun φ₀ x ∈ V) :
    ∃! φ : X ⟶ (affine.{u} K n).restrictOpen V, φ ≫ ofRestrict (affine.{u} K n) V = φ₀ :=
  ⟨Hom.liftRestrict φ₀ V h, Hom.liftRestrict_comp_ofRestrict φ₀ V h, fun _ hφ =>
    Hom.ext_of_comp_ofRestrict (hφ.trans (Hom.liftRestrict_comp_ofRestrict φ₀ V h).symm)⟩

end AnalyticSpace.KLocallyRingedSpace

