/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace
public import Hironaka.AnalyticSpace.Model
public import Hironaka.AnalyticSpace.RegPoints
public import Hironaka.AnalyticSpace.Restrict.Defs
import Hironaka.AnalyticSpace.ClosedSubspaceLemmas
import Hironaka.AnalyticSpace.Complexification
import Hironaka.AnalyticSpace.HomExt
import Hironaka.AnalyticSpace.HomLocal
import Hironaka.AnalyticSpace.HomOfSections
import Hironaka.AnalyticSpace.HomOfSectionsModel
import Hironaka.AnalyticSpace.LiftRestrictStalk
import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Hironaka.AnalyticSpace.QuotientMap
import Hironaka.AnalyticSpace.RegDensityLemmas
import Hironaka.AnalyticSpace.RestrictToIso
import Hironaka.Manifold.StructureSheaf.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Morphisms out of a non-singular space are determined on a dense open subset

Two `K`-morphisms `h₁ h₂ : A ⟶ Y` of analytic `K`-spaces with `A` non-singular that agree after
restriction to a dense open subspace `A|_D` are equal (`AnalyticSpace.hom_ext_of_dense`). This is
the rigidity behind the uniqueness of the lift of a local analytic isomorphism to the resolutions
([Wlo09, Theorem 2.0.1 (3)]: the lift is "natural"; [Kol07, Theorem 45 (5)]): two lifts agree over
the simple locus, where the resolution is an isomorphism, which is a dense open subset of the
resolving manifold. Not stated in the sources; the argument:

* **Sections** (`AnalyticSpace.eq_zero_of_pullbackΓ_ofRestrict_eq_zero_of_dense`): a global section
  of a non-singular space `Z` whose restriction to a dense open `D` vanishes is zero. Near a point,
  `Z` is `K`-isomorphic to an open subspace `(G, 𝒜_G)` of `Kⁿ` (Hironaka's characterization of the
  simple points [Hir64, Ch. 0, §1, p. 121], `isRegular_stalk_iff_exists_manifold_nhd`), whose
  sections are analytic functions (`Manifold.structureSheaf`); the transported section is a
  continuous function vanishing on a dense subset of its domain, hence zero
  (`Set.EqOn.of_subset_closure`), so the germ of the section at the point vanishes, the stalk map
  of the chart being injective. Over `ℝ` the non-singularity cannot be weakened to reducedness:
  the reduced space `x(x² + y²) = 0` near the origin of `ℝ²` has support the line `x = 0`, and the
  section `x` vanishes on the complement of the origin, where `x² + y²` is a unit, but not at the
  origin.
* **Morphisms** (`AnalyticSpace.hom_ext_of_dense`): the base maps agree, being continuous into a
  Hausdorff space and equal on a dense set (`Continuous.ext_on`). Equality of morphisms is local
  on the source (`hom_ext_of_cover`); near a point of `A` the target is a local model `L ⊆ Kᵐ`
  (`exists_kIso_localModel`), so both morphisms factor through `Y|_U ≅ L ⟶ (Kᵐ, 𝒜)`, and a
  morphism into `(Kᵐ, 𝒜)` from a space with Noetherian stalks is determined by the pull-backs of
  the `m` coordinate functions (`hom_ext_of_coord`), global sections of the non-singular open
  subspace which agree on the dense open subset; the embedding of the model is a monomorphism
  (`eq_of_comp_localModel_ι_eq`).
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open AnalyticSpace KLocallyRingedSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- An open subspace of a non-singular analytic `K`-space is non-singular: the stalks are those of
the space (`isRegularLocalRing_stalk_restrictOpen_iff`). -/
theorem isNonsingular_restrictOpen {X : AnalyticSpace.{u} K} (hX : X.IsNonsingular)
    (U : Opens X) : (AnalyticSpace.restrictOpen X U).IsNonsingular := by
  rw [isNonsingular_iff] at hX ⊢
  intro x
  exact (isRegularLocalRing_stalk_restrictOpen_iff X.toKLocallyRingedSpace U x).mpr (hX x.1)

/-- The preimage of a dense set under the open immersion `X|_U ⟶ X` is dense. -/
theorem dense_preimage_toFun_ofRestrict (X : KLocallyRingedSpace.{u} K) (U : Opens X) {D : Set X}
    (hD : Dense D) : Dense (KLocallyRingedSpace.Hom.toFun (ofRestrict X U) ⁻¹' D) :=
  hD.preimage U.isOpen.isOpenMap_subtype_val

/-! ### Sections of the model `(G, 𝒜_G)` -/

section Model

variable {n : ℕ} (G : Opens (Kn.{u} K n))

/-- A global section of `(G, 𝒜_G)` — an analytic function on `G` — whose restriction to a dense
open subset `O ⊆ G` is zero is zero: it is a continuous function vanishing on a dense subset of its
domain (`Set.EqOn.of_subset_closure`). -/
theorem eq_zero_of_pullbackΓ_ofRestrict_eq_zero_of_dense_analyticSpaceOfOpen
    (O : Opens (analyticSpaceOfOpen K n G)) (hO : Dense (O : Set (analyticSpaceOfOpen K n G)))
    (t : LocallyRingedSpace.Γ.obj (op (analyticSpaceOfOpen K n G).toLocallyRingedSpace))
    (ht : (ofRestrict (analyticSpaceOfOpen K n G) O).pullbackΓ t = 0) : t = 0 := by
  -- `t` is an analytic function `t'` on the open `G' := G` (as the image of `⊤`) of `Kⁿ`
  let G' : Opens (TopCat.of (Kn.{u} K n)) :=
    (Opens.isOpenEmbedding (X := TopCat.of (Kn.{u} K n)) G).functor.obj ⊤
  let t' : (Manifold.structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.obj (op G') := t
  -- the restriction of `t` to the open `O₂` of the model (the set `O`) is zero
  let O₂ : Opens (analyticSpaceOfOpen K n G) := (Opens.isOpenEmbedding O).isOpenMap.functor.obj
    ((Opens.map (ofRestrict (analyticSpaceOfOpen K n G) O).1.base).obj ⊤)
  have hres : (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.map
      ((Opens.isOpenEmbedding O).isOpenMap.adjunction.counit.app ⊤).op t = 0 := ht
  -- the germ of `t` at every point of `O` vanishes, so the function `t'` vanishes there
  have hval : ∀ q : G', q.1 ∈ Subtype.val '' (O : Set (analyticSpaceOfOpen K n G)) → t' q = 0 := by
    rintro q ⟨o, ho, hoq⟩
    have hoO₂ : o ∈ O₂ := ⟨⟨o, ho⟩, trivial, rfl⟩
    have hg0 : (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ o trivial t =
        0 := by
      have := TopCat.Presheaf.germ_res_apply
        (analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf
        ((Opens.isOpenEmbedding O).isOpenMap.adjunction.counit.app ⊤) o hoO₂ t
      rw [hres, map_zero] at this
      exact this.symm
    -- read on `Kⁿ`: the germ of `t'` at `o` in the structure sheaf of `Kⁿ` vanishes
    have hg1 : (Manifold.structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.germ G' o.1
        ⟨o, trivial, rfl⟩ t' = 0 := by
      have h := PresheafedSpace.restrictStalkIso_hom_eq_germ (affine K n).toPresheafedSpace
        (Opens.isOpenEmbedding (X := TopCat.of (Kn.{u} K n)) G) ⊤ o trivial
      have h' : (PresheafedSpace.restrictStalkIso (affine K n).toPresheafedSpace
          (Opens.isOpenEmbedding (X := TopCat.of (Kn.{u} K n)) G) o).hom
            ((analyticSpaceOfOpen K n G).toLocallyRingedSpace.presheaf.germ ⊤ o trivial t) =
          (Manifold.structureSheaf K (Kn.{u} K n) (Kn.{u} K n)).presheaf.germ G' o.1
            ⟨o, trivial, rfl⟩ t' :=
        ConcreteCategory.congr_hom h t
      rw [hg0] at h'
      exact h'.symm.trans (map_zero _)
    -- hence the function `t'` vanishes at `o`
    have h2 := congrArg (Manifold.stalkToGerm 𝓘(K, Kn.{u} K n) ω (Kn.{u} K n) o.1) hg1
    rw [map_zero] at h2
    erw [Manifold.stalkToGerm_germ] at h2
    have h3 : Manifold.extendBy0 𝓘(K, Kn.{u} K n) ω (Kn.{u} K n) t' o.1 = 0 :=
      (Filter.Germ.coe_eq.mp (h2.trans (Filter.Germ.coe_zero).symm)).eq_of_nhds
    rw [Manifold.extendBy0_of_mem 𝓘(K, Kn.{u} K n) ω (Kn.{u} K n) t'
      (⟨o, trivial, rfl⟩ : o.1 ∈ G')] at h3
    have hq : (⟨o.1, (⟨o, trivial, rfl⟩ : o.1 ∈ G')⟩ : G') = q := Subtype.ext hoq
    rw [← hq]
    exact h3
  -- the image of `O` is dense in `G'`
  have hdense : (Set.univ : Set G') ⊆
      closure {q : G' | q.1 ∈ Subtype.val '' (O : Set (analyticSpaceOfOpen K n G))} := by
    intro q _
    obtain ⟨g, -, hgq⟩ : q.1 ∈ Subtype.val '' (Set.univ : Set (analyticSpaceOfOpen K n G)) := q.2
    have hg : g ∈ closure (O : Set (analyticSpaceOfOpen K n G)) := hO g
    have h1 : q.1 ∈ closure (Subtype.val '' (O : Set (analyticSpaceOfOpen K n G))) := by
      rw [← hgq]
      exact map_mem_closure continuous_subtype_val hg fun _ h => Set.mem_image_of_mem _ h
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    refine Set.mem_preimage.mpr (closure_mono ?_ h1)
    rintro _ ⟨o, ho, rfl⟩
    exact ⟨⟨o.1, ⟨o, trivial, rfl⟩⟩, ⟨o, ho, rfl⟩, rfl⟩
  -- a continuous function vanishing on a dense subset vanishes
  have hcm : ContMDiff 𝓘(K, Kn.{u} K n) 𝓘(K) ω (fun q : G' => t' q) := t'.2
  have hcont : Continuous (fun q : G' => t' q) := hcm.continuous
  have heq : Set.EqOn (fun q : G' => t' q) (fun _ => (0 : K)) Set.univ :=
    Set.EqOn.of_subset_closure (fun q hq => hval q hq) hcont.continuousOn continuousOn_const
      (Set.subset_univ _) hdense
  change t' = 0
  exact Subtype.ext (funext fun q => heq (Set.mem_univ q))

end Model

/-! ### Sections of a non-singular space -/

/-- A global section of a non-singular analytic `K`-space `Z` whose restriction to a dense open
`D` is zero is zero. -/
theorem eq_zero_of_pullbackΓ_ofRestrict_eq_zero_of_dense {Z : AnalyticSpace.{u} K}
    (hZ : Z.IsNonsingular) (D : Opens Z) (hD : Dense (D : Set Z))
    (s : LocallyRingedSpace.Γ.obj (op Z.toLocallyRingedSpace))
    (hs : (ofRestrict Z.toKLocallyRingedSpace D).pullbackΓ s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext Z.toLocallyRingedSpace.sheaf ⊤ _ _ fun a _ => ?_
  -- a manifold neighbourhood of `a`
  have ha : a ∈ regularLocus Z := by rw [hZ]; exact Set.mem_univ a
  obtain ⟨d, -, V, haV, G', ⟨e⟩⟩ := (isRegular_stalk_iff_exists_manifold_nhd Z a).mp ha
  -- the chart `f : (G', 𝒜) ⟶ Z`, an open immersion on points
  set f : analyticSpaceOfOpen K d G' ⟶ Z.toKLocallyRingedSpace := e.inv ≫ ofRestrict _ V with hf
  set p : Z.toKLocallyRingedSpace.restrictOpen V := ⟨a, haV⟩ with hp
  set m : analyticSpaceOfOpen K d G' := KLocallyRingedSpace.Hom.toFun e.hom p with hm
  have hinvm : KLocallyRingedSpace.Hom.toFun e.inv m = p := by
    have h : KLocallyRingedSpace.Hom.toFun (e.hom ≫ e.inv) p = p := by
      rw [e.hom_inv_id]; rfl
    rw [KLocallyRingedSpace.Hom.toFun_comp] at h
    exact h
  have hfm : KLocallyRingedSpace.Hom.toFun f m = a := by
    rw [hf, KLocallyRingedSpace.Hom.toFun_comp, Function.comp_apply, hinvm]
    rfl
  have hopen : IsOpenMap (KLocallyRingedSpace.Hom.toFun f) := by
    rw [hf, KLocallyRingedSpace.Hom.toFun_comp]
    have hinv : KLocallyRingedSpace.Hom.toFun e.inv = ⇑(KIso.homeomorph e.symm) :=
      funext fun q => (KIso.homeomorph_apply e.symm q).symm
    rw [hinv]
    exact V.isOpen.isOpenMap_subtype_val.comp (KIso.homeomorph e.symm).isOpenMap
  -- the pulled-back section vanishes on the dense open `f⁻¹D`, hence vanishes
  set O : Opens (analyticSpaceOfOpen K d G') := (Opens.map f.1.base).obj D with hO
  have hOd : Dense (O : Set (analyticSpaceOfOpen K d G')) := hD.preimage hopen
  have ht : (ofRestrict (analyticSpaceOfOpen K d G') O).pullbackΓ (f.pullbackΓ s) = 0 := by
    rw [← KLocallyRingedSpace.Hom.pullbackΓ_comp]
    have hsq : ofRestrict (analyticSpaceOfOpen K d G') O ≫ f =
        KLocallyRingedSpace.Hom.restrictTo f O D (fun _ h => h) ≫
          ofRestrict Z.toKLocallyRingedSpace D :=
      (KLocallyRingedSpace.Hom.restrictTo_comp_ofRestrict f O D _).symm
    rw [hsq, KLocallyRingedSpace.Hom.pullbackΓ_comp, hs, map_zero]
  have ht0 := eq_zero_of_pullbackΓ_ofRestrict_eq_zero_of_dense_analyticSpaceOfOpen G' O hOd
    (f.pullbackΓ s) ht
  -- the germ of `s` at `a = f m` is carried by the injective stalk map of `f` to the germ of the
  -- pulled-back section
  have hgerm := germ_top_pullbackΓ f s m
  have hinj : Function.Injective (f.1.stalkMap m).hom :=
    ((bijective_stalkMap_iff_of_comp_eq e.inv f hf.symm m).mp
      (bijective_stalkMap_of_isIso e.inv m)).injective
  have hz : f.1.stalkMap m (Z.toLocallyRingedSpace.presheaf.germ ⊤ (f.1.base m) trivial s) =
      f.1.stalkMap m 0 := by
    rw [← hgerm, ht0]
    exact (map_zero _).trans (map_zero _).symm
  have := hinj hz
  change Z.toLocallyRingedSpace.presheaf.germ ⊤ (KLocallyRingedSpace.Hom.toFun f m) trivial s =
    0 at this
  rw [hfm] at this
  exact this.trans (map_zero _).symm

/-! ### Morphisms -/

/-- Two `K`-morphisms from a non-singular analytic `K`-space into `(Kᵐ, 𝒜_{Kᵐ})` that agree on a
dense open subspace are equal: the pull-backs of the coordinate functions agree on the dense open
(`eq_zero_of_pullbackΓ_ofRestrict_eq_zero_of_dense` at their difference), and a morphism into
`(Kᵐ, 𝒜_{Kᵐ})` is determined by them (`hom_ext_of_coord`). -/
theorem hom_ext_of_dense_affine {Z : AnalyticSpace.{u} K} (hZ : Z.IsNonsingular) (D : Opens Z)
    (hD : Dense (D : Set Z)) {m : ℕ} (g₁ g₂ : Z.toKLocallyRingedSpace ⟶ affine K m)
    (h : ofRestrict Z.toKLocallyRingedSpace D ≫ g₁ = ofRestrict Z.toKLocallyRingedSpace D ≫ g₂) :
    g₁ = g₂ := by
  refine hom_ext_of_coord Z g₁ g₂ fun j => ?_
  rw [← sub_eq_zero]
  refine eq_zero_of_pullbackΓ_ofRestrict_eq_zero_of_dense hZ D hD _ ?_
  have e₁ : (ofRestrict Z.toKLocallyRingedSpace D).pullbackΓ (g₁.pullbackΓ (coordSection K m j)) =
      (ofRestrict Z.toKLocallyRingedSpace D ≫ g₁).pullbackΓ (coordSection K m j) :=
    (KLocallyRingedSpace.Hom.pullbackΓ_comp _ _ _).symm
  have e₂ : (ofRestrict Z.toKLocallyRingedSpace D).pullbackΓ (g₂.pullbackΓ (coordSection K m j)) =
      (ofRestrict Z.toKLocallyRingedSpace D ≫ g₂).pullbackΓ (coordSection K m j) :=
    (KLocallyRingedSpace.Hom.pullbackΓ_comp _ _ _).symm
  rw [map_sub, e₁, e₂, h, sub_self]

/-- **Morphisms out of a non-singular space are determined on a dense open subset**: two
`K`-morphisms `h₁ h₂ : A ⟶ Y` of analytic `K`-spaces with `A` non-singular that agree after
restriction to a dense open `D ⊆ A` are equal. The base maps agree by continuity; near each point
the target is a local model `L ⊆ Kᵐ` and both morphisms, restricted to the preimage of the model
neighbourhood (a non-singular open subspace in which `D` is dense), are determined by their
composites with `Y|_U ≅ L ⟶ (Kᵐ, 𝒜)`, which agree by `hom_ext_of_dense_affine`. -/
theorem hom_ext_of_dense {A Y : AnalyticSpace.{u} K} (hA : A.IsNonsingular) (D : Opens A)
    (hD : Dense (D : Set A)) (h₁ h₂ : A ⟶ Y)
    (h : ofRestrict A.toKLocallyRingedSpace D ≫ h₁ = ofRestrict A.toKLocallyRingedSpace D ≫ h₂) :
    h₁ = h₂ := by
  -- the base maps agree
  have hb : ∀ a : A, KLocallyRingedSpace.Hom.toFun h₁ a = KLocallyRingedSpace.Hom.toFun h₂ a := by
    have hcont₁ : Continuous (KLocallyRingedSpace.Hom.toFun h₁) :=
      KLocallyRingedSpace.Hom.continuous_toFun h₁
    have hcont₂ : Continuous (KLocallyRingedSpace.Hom.toFun h₂) :=
      KLocallyRingedSpace.Hom.continuous_toFun h₂
    have heq : Set.EqOn (KLocallyRingedSpace.Hom.toFun h₁) (KLocallyRingedSpace.Hom.toFun h₂)
        (D : Set A) := fun a ha => by
      have := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ (⟨a, ha⟩ : D)) h
      exact this
    exact fun a => (heq.of_subset_closure hcont₁.continuousOn hcont₂.continuousOn
      (Set.subset_univ _) fun x _ => hD x) (Set.mem_univ a)
  -- equality is local on the source: at `a`, a local model of `Y` at `h₁ a`
  have hloc : ∀ a : A, ∃ W : Opens A, a ∈ W ∧
      ofRestrict A.toKLocallyRingedSpace W ≫ h₁ = ofRestrict A.toKLocallyRingedSpace W ≫ h₂ := by
    intro a
    obtain ⟨U, hyU, m, k, G, f, ⟨e⟩⟩ :=
      Y.exists_kIso_localModel (KLocallyRingedSpace.Hom.toFun h₁ a)
    -- the open `W` over which both morphisms land in `Y|_U`
    set W : Opens A := (Opens.map h₁.1.base).obj U ⊓ (Opens.map h₂.1.base).obj U with hWdef
    have haW : a ∈ W :=
      ⟨hyU, by change KLocallyRingedSpace.Hom.toFun h₂ a ∈ U; rw [← hb a]; exact hyU⟩
    refine ⟨W, haW, ?_⟩
    -- the lifts of the restrictions through `Y|_U ⟶ Y`
    have hl₁ : ∀ w : A.toKLocallyRingedSpace.restrictOpen W,
        KLocallyRingedSpace.Hom.toFun (ofRestrict A.toKLocallyRingedSpace W ≫ h₁) w ∈ U :=
      fun w => w.2.1
    have hl₂ : ∀ w : A.toKLocallyRingedSpace.restrictOpen W,
        KLocallyRingedSpace.Hom.toFun (ofRestrict A.toKLocallyRingedSpace W ≫ h₂) w ∈ U :=
      fun w => w.2.2
    set l₁ := KLocallyRingedSpace.Hom.liftRestrict (ofRestrict A.toKLocallyRingedSpace W ≫ h₁) U
      hl₁ with hl₁def
    set l₂ := KLocallyRingedSpace.Hom.liftRestrict (ofRestrict A.toKLocallyRingedSpace W ≫ h₂) U
      hl₂ with hl₂def
    have hl₁c := KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict
      (ofRestrict A.toKLocallyRingedSpace W ≫ h₁) U hl₁
    have hl₂c := KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict
      (ofRestrict A.toKLocallyRingedSpace W ≫ h₂) U hl₂
    -- the lifts agree on the dense open `D' := D ∩ W` of `A|_W`
    set D' : Opens (A.toKLocallyRingedSpace.restrictOpen W) :=
      (Opens.map (ofRestrict A.toKLocallyRingedSpace W).1.base).obj D with hD'
    have hD'd : Dense (D' : Set (A.toKLocallyRingedSpace.restrictOpen W)) :=
      dense_preimage_toFun_ofRestrict A.toKLocallyRingedSpace W hD
    have hr : ∀ p : (A.toKLocallyRingedSpace.restrictOpen W).restrictOpen D',
        KLocallyRingedSpace.Hom.toFun (ofRestrict (A.toKLocallyRingedSpace.restrictOpen W) D' ≫
          ofRestrict A.toKLocallyRingedSpace W) p ∈ D := fun p => p.2
    have hfac := KLocallyRingedSpace.Hom.liftRestrict_comp_ofRestrict
      (ofRestrict (A.toKLocallyRingedSpace.restrictOpen W) D' ≫
        ofRestrict A.toKLocallyRingedSpace W) D hr
    have hagree : ofRestrict (A.toKLocallyRingedSpace.restrictOpen W) D' ≫ l₁ =
        ofRestrict (A.toKLocallyRingedSpace.restrictOpen W) D' ≫ l₂ := by
      apply KLocallyRingedSpace.Hom.ext_of_comp_ofRestrict
      have e1 : ofRestrict (A.toKLocallyRingedSpace.restrictOpen W) D' ≫
            ofRestrict A.toKLocallyRingedSpace W ≫ h₁ =
          ofRestrict (A.toKLocallyRingedSpace.restrictOpen W) D' ≫
            ofRestrict A.toKLocallyRingedSpace W ≫ h₂ := by
        rw [← Category.assoc, ← hfac, Category.assoc, h, ← Category.assoc, hfac, Category.assoc]
      rw [Category.assoc, Category.assoc, hl₁c, hl₂c]
      exact e1
    -- compose with the model embedding and compare the coordinates
    have hZ : (A.restrictOpen W).IsNonsingular := isNonsingular_restrictOpen hA W
    have hκ : l₁ ≫ e.hom ≫ localModel.ι K m G f = l₂ ≫ e.hom ≫ localModel.ι K m G f :=
      hom_ext_of_dense_affine hZ D' hD'd _ _ (by
        have := congrArg (fun φ => φ ≫ e.hom ≫ localModel.ι K m G f) hagree
        exact (Category.assoc _ _ _).symm.trans (this.trans (Category.assoc _ _ _)))
    have hl : l₁ = l₂ := by
      have := eq_of_comp_localModel_ι_eq G f (l₁ ≫ e.hom) (l₂ ≫ e.hom)
        (by rw [Category.assoc, Category.assoc]; exact hκ)
      exact (cancel_mono e.hom).mp this
    rw [← hl₁c, ← hl₂c]
    exact congrArg (fun φ => φ ≫ ofRestrict Y.toKLocallyRingedSpace U) hl
  choose W hW using hloc
  exact hom_ext_of_cover h₁ h₂ W (fun a => ⟨a, (hW a).1⟩) fun a => (hW a).2

end AnalyticSpace

end
