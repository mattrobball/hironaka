/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace
public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.ModelSupport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Gluing `K`-morphisms into `(Kⁿ, 𝒜_{Kⁿ})` along an open cover

A `K`-local-ringed space `Z` covered by opens `U i`, with `K`-morphisms
`h i : Z|U i ⟶ (Kⁿ, 𝒜_{Kⁿ})` that agree on the overlaps — the same base point, and the same germ
of the pullback of every function of `𝒜_{Kⁿ}` at every point of `U i ∩ U j` — has a `K`-morphism
`Z ⟶ (Kⁿ, 𝒜_{Kⁿ})` (`glueHomAffine`) which agrees with `h i` on `U i` in the same two senses:
on base points (`toFun_glueHomAffine_eq`) and on the germs of pulled-back sections
(`germ_pullbackΓ_glueHomAffine`); the equation `ofRestrict Z (U i) ≫ glueHomAffine … = h i`
itself is not proved here. The agreement hypotheses are
stated on germs, so that everything is decided by `TopCat.Presheaf.section_ext` and the sheaf
property of `𝒪_Z`; in the application (a morphism `X ⟶ (Kⁿ, 𝒜_{Kⁿ})` of an analytic `K`-space
from `n` global sections, `Hironaka/AnalyticSpace/HomOfSections.lean`) the agreement comes from the
uniqueness `ringHom_ext_of_coord` on the stalks. This is the gluing step in the construction of
Hironaka's extended coordination `h'` [Hir64, Ch. 0, §1, p. 120]. Elementary sheaf theory; not
in the sources.

**Construction.** The base map is `z ↦ (h i).base z` for any `i` with `z ∈ U i` (well defined and
continuous because it is so on each `U i`). For an open `V ⊆ Kⁿ` and `F ∈ 𝒜(V)`, the sections
`(h i)^*F` over `U i ∩ b⁻¹(V)` are compatible (equal germs, hence equal by `section_ext`), and
glue to a section over `b⁻¹(V)` (`existsUnique_gluing'`); uniqueness of the gluing gives the
naturality and the ring-homomorphism axioms of the sheaf map. The stalk map at `z ∈ U i` is the
stalk map of `h i` (through the isomorphism of the stalk of `Z|U i` with that of `Z`), hence
local, and the constants pull back to constants because they do so for each `h i`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-! ### The image of an open of an open subspace -/

section ImgOpens

variable (Z : KLocallyRingedSpace.{u} K)

/-- The image in `Z` of an open `T` of the open subspace `Z|V`: the functor of the open embedding
`V → Z`. Sections of `𝒪_{Z|V}` over `T` are, by definition of the restriction, sections of `𝒪_Z`
over `imgOpens Z V T`. -/
abbrev imgOpens (V : Opens Z) (T : Opens (Z.restrictOpen V)) : Opens Z :=
  (Opens.isOpenEmbedding V).isOpenMap.functor.obj T

theorem mem_imgOpens {V : Opens Z} {T : Opens (Z.restrictOpen V)} {z : Z} :
    z ∈ imgOpens Z V T ↔ ∃ hz : z ∈ V, (⟨z, hz⟩ : V) ∈ T := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyT, hyz⟩
    have hyz' : y = z := hyz
    subst hyz'
    exact ⟨hy, hyT⟩
  · rintro ⟨hz, hT⟩
    exact ⟨⟨z, hz⟩, hT, rfl⟩

theorem mem_imgOpens_of_mem {V : Opens Z} {T : Opens (Z.restrictOpen V)} {z : Z} (hz : z ∈ V)
    (hT : (⟨z, hz⟩ : V) ∈ T) : z ∈ imgOpens Z V T :=
  (mem_imgOpens Z).mpr ⟨hz, hT⟩

/-- The image of the whole open subspace `Z|W` is contained in `W`. -/
theorem imgOpens_top_le (W : Opens Z) : imgOpens Z W ⊤ ≤ W := by
  rintro _ ⟨w, -, rfl⟩
  exact w.2

end ImgOpens

/-! ### The glued base map -/

section Glue

variable {n : ℕ} (Z : KLocallyRingedSpace.{u} K) {ι : Type*} (U : ι → Opens Z)
  (hU : ∀ z : Z, ∃ i, z ∈ U i) (h : ∀ i, Z.restrictOpen (U i) ⟶ affine.{u} K n)

/-- An index of the cover containing `z`. -/
def glueIdx (z : Z) : ι := (hU z).choose

theorem mem_glueIdx (z : Z) : z ∈ U (glueIdx Z U hU z) := (hU z).choose_spec

/-- The glued base map `z ↦ (h i).base z`, `z ∈ U i`. -/
def glueBase (z : Z) : Kn.{u} K n := (h (glueIdx Z U hU z)).1.base ⟨z, mem_glueIdx Z U hU z⟩

variable (hbase : ∀ (i j : ι) (z : Z) (hi : z ∈ U i) (hj : z ∈ U j),
  (h i).1.base ⟨z, hi⟩ = (h j).1.base ⟨z, hj⟩)

include hbase in
theorem glueBase_eq (i : ι) (z : Z) (hi : z ∈ U i) : glueBase Z U hU h z = (h i).1.base ⟨z, hi⟩ :=
  hbase _ _ _ _ _

include hbase in
theorem continuous_glueBase : Continuous (glueBase Z U hU h) := by
  rw [continuous_iff_continuousAt]
  intro z
  obtain ⟨i, hi⟩ := hU z
  refine ContinuousOn.continuousAt ?_ ((U i).isOpen.mem_nhds hi)
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : (U i : Set Z).domRestrict (glueBase Z U hU h) = fun p => (h i).1.base p :=
    funext fun p => glueBase_eq Z U hU h hbase i p.1 p.2
  rw [hfun]
  exact (h i).1.base.hom.continuous

/-- The glued base map as a morphism of `TopCat`. -/
def glueBaseHom :
    Z.toLocallyRingedSpace.toTopCat ⟶ (affine.{u} K n).toLocallyRingedSpace.toTopCat :=
  TopCat.ofHom ⟨glueBase Z U hU h, continuous_glueBase Z U hU h hbase⟩

theorem glueBaseHom_apply (z : Z) : glueBaseHom Z U hU h hbase z = glueBase Z U hU h z := rfl

/-! ### The glued sections -/

/-- The preimage of `V ⊆ Kⁿ` under the glued base map. -/
abbrev preV (V : Opens (Kn.{u} K n)) : Opens Z := (Opens.map (glueBaseHom Z U hU h hbase)).obj V

/-- The piece `U i ∩ b⁻¹(V)` of the preimage, as the image of the preimage of `V` under `h i`. -/
abbrev locV (i : ι) (V : Opens (Kn.{u} K n)) : Opens Z :=
  imgOpens Z (U i) ((Opens.map (h i).1.base).obj V)

theorem mem_locV {i : ι} {V : Opens (Kn.{u} K n)} {z : Z} :
    z ∈ locV Z U h i V ↔ ∃ hi : z ∈ U i, (h i).1.base ⟨z, hi⟩ ∈ V :=
  mem_imgOpens Z

theorem locV_le_preV (i : ι) (V : Opens (Kn.{u} K n)) : locV Z U h i V ≤ preV Z U hU h hbase V := by
  intro z hz
  obtain ⟨hi, hV⟩ := (mem_locV Z U h).mp hz
  change glueBase Z U hU h z ∈ V
  rw [glueBase_eq Z U hU h hbase i z hi]
  exact hV

theorem preV_le_iSup (V : Opens (Kn.{u} K n)) :
    preV Z U hU h hbase V ≤ ⨆ i, locV Z U h i V := by
  intro z hz
  obtain ⟨i, hi⟩ := hU z
  refine Opens.mem_iSup.mpr ⟨i, (mem_locV Z U h).mpr ⟨hi, ?_⟩⟩
  rw [← glueBase_eq Z U hU h hbase i z hi]
  exact hz

theorem mem_locV_of_mem_preV {V : Opens (Kn.{u} K n)} {z : Z} (hz : z ∈ preV Z U hU h hbase V)
    {i : ι} (hi : z ∈ U i) : z ∈ locV Z U h i V :=
  (mem_locV Z U h).mpr ⟨hi, by rw [← glueBase_eq Z U hU h hbase i z hi]; exact hz⟩

/-- The pullback of `F ∈ 𝒜(V)` along `h i`, as a section of `𝒪_Z` over `U i ∩ b⁻¹(V)`. -/
abbrev locSec (i : ι) (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    Z.toLocallyRingedSpace.presheaf.obj (op (locV Z U h i V)) :=
  (h i).1.c.app (op V) F

variable (hgerm : ∀ (i j : ι) (V : Opens (Kn.{u} K n))
  (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) (z : Z)
  (hzi : z ∈ locV Z U h i V) (hzj : z ∈ locV Z U h j V),
  Z.toLocallyRingedSpace.presheaf.germ (locV Z U h i V) z hzi (locSec Z U h i V F) =
    Z.toLocallyRingedSpace.presheaf.germ (locV Z U h j V) z hzj (locSec Z U h j V F))

include hgerm in
theorem isCompatible_locSec (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    TopCat.Presheaf.IsCompatible Z.toLocallyRingedSpace.presheaf (fun i => locV Z U h i V)
      (fun i => locSec Z U h i V F) := by
  intro i j
  apply TopCat.Presheaf.section_ext Z.toLocallyRingedSpace.𝒪
  intro z hz
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  exact hgerm i j V F z hz.1 hz.2

include hgerm in
theorem existsUnique_glueSec (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    ∃! t : Z.toLocallyRingedSpace.presheaf.obj (op (preV Z U hU h hbase V)),
      ∀ i, Z.toLocallyRingedSpace.presheaf.map (homOfLE (locV_le_preV Z U hU h hbase i V)).op t =
        locSec Z U h i V F :=
  Z.toLocallyRingedSpace.𝒪.existsUnique_gluing' (fun i => locV Z U h i V) (preV Z U hU h hbase V)
    (fun i => homOfLE (locV_le_preV Z U hU h hbase i V)) (preV_le_iSup Z U hU h hbase V)
    (fun i => locSec Z U h i V F) (isCompatible_locSec Z U h hgerm V F)

/-- The glued pullback of `F ∈ 𝒜(V)`: the section of `𝒪_Z` over `b⁻¹(V)` restricting to `(h i)^*F`
on every `U i ∩ b⁻¹(V)`. -/
def glueSec (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    Z.toLocallyRingedSpace.presheaf.obj (op (preV Z U hU h hbase V)) :=
  (existsUnique_glueSec Z U hU h hbase hgerm V F).exists.choose

theorem glueSec_res (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) (i : ι) :
    Z.toLocallyRingedSpace.presheaf.map (homOfLE (locV_le_preV Z U hU h hbase i V)).op
      (glueSec Z U hU h hbase hgerm V F) = locSec Z U h i V F :=
  (existsUnique_glueSec Z U hU h hbase hgerm V F).exists.choose_spec i

theorem glueSec_unique (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V))
    (t : Z.toLocallyRingedSpace.presheaf.obj (op (preV Z U hU h hbase V)))
    (ht : ∀ i, Z.toLocallyRingedSpace.presheaf.map
      (homOfLE (locV_le_preV Z U hU h hbase i V)).op t = locSec Z U h i V F) :
    t = glueSec Z U hU h hbase hgerm V F :=
  (existsUnique_glueSec Z U hU h hbase hgerm V F).unique ht (glueSec_res Z U hU h hbase hgerm V F)

/-- The germ of the glued section at `z ∈ U i` is the germ of `(h i)^*F`. -/
theorem germ_glueSec (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) {z : Z}
    (hz : z ∈ preV Z U hU h hbase V) {i : ι} (hi : z ∈ U i) :
    Z.toLocallyRingedSpace.presheaf.germ (preV Z U hU h hbase V) z hz
        (glueSec Z U hU h hbase hgerm V F) =
      Z.toLocallyRingedSpace.presheaf.germ (locV Z U h i V) z
        (mem_locV_of_mem_preV Z U hU h hbase hz hi) (locSec Z U h i V F) := by
  rw [← glueSec_res Z U hU h hbase hgerm V F i, Z.toLocallyRingedSpace.presheaf.germ_res_apply]

/-- Two sections over `b⁻¹(V)` with the same germs as the local pullbacks are equal: the
uniqueness in `existsUnique_glueSec`, at the level of germs. -/
theorem eq_glueSec_of_germ (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V))
    (t : Z.toLocallyRingedSpace.presheaf.obj (op (preV Z U hU h hbase V)))
    (ht : ∀ (z : Z) (hz : z ∈ preV Z U hU h hbase V) (i : ι) (hi : z ∈ U i),
      Z.toLocallyRingedSpace.presheaf.germ (preV Z U hU h hbase V) z hz t =
        Z.toLocallyRingedSpace.presheaf.germ (locV Z U h i V) z
          (mem_locV_of_mem_preV Z U hU h hbase hz hi) (locSec Z U h i V F)) :
    t = glueSec Z U hU h hbase hgerm V F := by
  apply TopCat.Presheaf.section_ext Z.toLocallyRingedSpace.𝒪
  intro z hz
  obtain ⟨i, hi⟩ := hU z
  exact (ht z hz i hi).trans (germ_glueSec Z U hU h hbase hgerm V F hz hi).symm

/-! ### The glued sheaf map -/

/-- The component at `V` of the glued sheaf map, as a ring homomorphism `F ↦ glueSec F`. -/
def glueCApp (V : Opens (Kn.{u} K n)) :
    (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V) →+*
      Z.toLocallyRingedSpace.presheaf.obj (op (preV Z U hU h hbase V)) where
  toFun F := glueSec Z U hU h hbase hgerm V F
  map_one' := by
    symm
    apply eq_glueSec_of_germ
    intro z hz i hi
    simp only [locSec, map_one]
    erw [map_one]
  map_mul' F G := by
    symm
    apply eq_glueSec_of_germ
    intro z hz i hi
    simp only [locSec, map_mul]
    rw [germ_glueSec Z U hU h hbase hgerm V F hz hi, germ_glueSec Z U hU h hbase hgerm V G hz hi]
    erw [map_mul]
  map_zero' := by
    symm
    apply eq_glueSec_of_germ
    intro z hz i hi
    simp only [locSec, map_zero]
    erw [map_zero]
  map_add' F G := by
    symm
    apply eq_glueSec_of_germ
    intro z hz i hi
    simp only [locSec, map_add]
    rw [germ_glueSec Z U hU h hbase hgerm V F hz hi, germ_glueSec Z U hU h hbase hgerm V G hz hi]
    erw [map_add]

theorem glueCApp_apply (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    glueCApp Z U hU h hbase hgerm V F = glueSec Z U hU h hbase hgerm V F := rfl

/-- The sheaf map `𝒜_{Kⁿ} ⟶ b_* 𝒪_Z` of the glued morphism: `F ↦ glueSec F`. -/
def glueC : (affine.{u} K n).toLocallyRingedSpace.presheaf ⟶
    glueBaseHom Z U hU h hbase _* Z.toLocallyRingedSpace.presheaf where
  app V := CommRingCat.ofHom (glueCApp Z U hU h hbase hgerm (unop V))
  naturality V W g := by
    ext F
    change glueSec Z U hU h hbase hgerm (unop W)
        ((affine.{u} K n).toLocallyRingedSpace.presheaf.map g F) =
      Z.toLocallyRingedSpace.presheaf.map
        ((Opens.map (glueBaseHom Z U hU h hbase)).map g.unop).op
        (glueSec Z U hU h hbase hgerm (unop V) F)
    symm
    apply eq_glueSec_of_germ
    intro z hz i hi
    erw [TopCat.Presheaf.germ_res_apply]
    rw [germ_glueSec Z U hU h hbase hgerm (unop V) F _ hi]
    -- both sides are germs of pullbacks along `h i`, related by the naturality of `(h i).c`
    have hnat := congrArg (fun φ => φ F) ((h i).1.c.naturality g)
    change (h i).1.c.app W ((affine.{u} K n).toLocallyRingedSpace.presheaf.map g F) =
      (Z.restrictOpen (U i)).toLocallyRingedSpace.presheaf.map
        ((Opens.map (h i).1.base).map g.unop).op ((h i).1.c.app V F) at hnat
    change _ = Z.toLocallyRingedSpace.presheaf.germ _ z _ ((h i).1.c.app W
      ((affine.{u} K n).toLocallyRingedSpace.presheaf.map g F))
    rw [hnat]
    exact (TopCat.Presheaf.germ_res_apply Z.toLocallyRingedSpace.presheaf
      ((Opens.isOpenEmbedding (U i)).isOpenMap.functor.map
        ((Opens.map (h i).1.base).map g.unop)) z _ ((h i).1.c.app V F)).symm

theorem glueC_app_apply (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) :
    (glueC Z U hU h hbase hgerm).app (op V) F = glueSec Z U hU h hbase hgerm V F := rfl

/-! ### The glued morphism -/

/-- The glued morphism of presheafed spaces. -/
def glueAux : Z.toLocallyRingedSpace.toPresheafedSpace ⟶
    (affine.{u} K n).toLocallyRingedSpace.toPresheafedSpace where
  base := glueBaseHom Z U hU h hbase
  c := glueC Z U hU h hbase hgerm

theorem glueAux_base_apply (z : Z) : (glueAux Z U hU h hbase hgerm).base z = glueBase Z U hU h z :=
  rfl

/-- The stalk map of the glued morphism on a germ: the germ of the local pullback `(h i)^*F`. -/
theorem stalkMap_glueAux_germ (V : Opens (Kn.{u} K n)) {z : Z}
    (hz : (glueAux Z U hU h hbase hgerm).base z ∈ V)
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) {i : ι} (hi : z ∈ U i) :
    ((glueAux Z U hU h hbase hgerm).stalkMap z).hom
        ((affine.{u} K n).toLocallyRingedSpace.presheaf.germ V
          ((glueAux Z U hU h hbase hgerm).base z) hz F) =
      Z.toLocallyRingedSpace.presheaf.germ (locV Z U h i V) z
        (mem_locV_of_mem_preV Z U hU h hbase hz hi) (locSec Z U h i V F) := by
  have e := PresheafedSpace.stalkMap_germ_apply (glueAux Z U hU h hbase hgerm) V z hz F
  erw [e]
  exact germ_glueSec Z U hU h hbase hgerm V F hz hi

/-- The isomorphism of the stalk of `Z` at `z ∈ W` with the stalk of `Z|W` on a germ: a section of
`𝒪_Z` over the image of an open `T` of `Z|W` is a section of `𝒪_{Z|W}` over `T`, with the
corresponding germ (Mathlib's `restrictStalkIso_inv_eq_germ`). -/
theorem restrictStalkIso_inv_germ (W : Opens Z) (T : Opens (Z.restrictOpen W)) {z : Z} (hz : z ∈ W)
    (hT : (⟨z, hz⟩ : W) ∈ T) (s : Z.toLocallyRingedSpace.presheaf.obj (op (imgOpens Z W T))) :
    ((PresheafedSpace.restrictStalkIso Z.toLocallyRingedSpace.toPresheafedSpace
        (Opens.isOpenEmbedding W) ⟨z, hz⟩).inv).hom
        (Z.toLocallyRingedSpace.presheaf.germ (imgOpens Z W T) z (mem_imgOpens_of_mem Z hz hT) s) =
      (Z.restrictOpen W).toLocallyRingedSpace.presheaf.germ T ⟨z, hz⟩ hT s :=
  congrArg (fun φ => φ.hom s) (PresheafedSpace.restrictStalkIso_inv_eq_germ
    Z.toLocallyRingedSpace.toPresheafedSpace (Opens.isOpenEmbedding W) T ⟨z, hz⟩ hT)

include hbase hgerm in
/-- The stalk maps of the glued morphism are local: a germ whose glued pullback is a unit has a
nonzero value, because the pullback along `h i` is a unit and `h i` is a `K`-morphism. -/
theorem isLocalHom_stalkMap_glueAux (z : Z) :
    IsLocalHom ((glueAux Z U hU h hbase hgerm).stalkMap z).hom := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨V, hV, F, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (affine.{u} K n).toLocallyRingedSpace.presheaf a
  obtain ⟨i, hi⟩ := hU z
  rw [stalkMap_glueAux_germ Z U hU h hbase hgerm V hV F hi] at ha
  -- push the unit to the stalk of `Z|U i`, where it is the stalk map of `h i` on the germ of `F`
  have hVi : (h i).1.base ⟨z, hi⟩ ∈ V := by rw [← glueBase_eq Z U hU h hbase i z hi]; exact hV
  have ha' := ha.map ((PresheafedSpace.restrictStalkIso Z.toLocallyRingedSpace.toPresheafedSpace
    (Opens.isOpenEmbedding (U i)) ⟨z, hi⟩).inv).hom
  erw [restrictStalkIso_inv_germ Z (U i) ((Opens.map (h i).1.base).obj V) hi hVi] at ha'
  have e := PresheafedSpace.stalkMap_germ_apply (h i).1.1 V ⟨z, hi⟩ hVi F
  erw [← e] at ha'
  have hu := ((h i).1.prop ⟨z, hi⟩).map_nonunit _ ha'
  rw [isUnit_germ_affine_iff K n V ⟨_, hVi⟩ F] at hu
  rw [isUnit_germ_affine_iff K n V ⟨_, hV⟩ F]
  intro h0
  apply hu
  have : (⟨(h i).1.base ⟨z, hi⟩, hVi⟩ : V) = ⟨(glueAux Z U hU h hbase hgerm).base z, hV⟩ :=
    Subtype.ext (glueBase_eq Z U hU h hbase i z hi).symm
  rw [this]
  exact h0

/-- **The glued `K`-morphism** `Z ⟶ (Kⁿ, 𝒜_{Kⁿ})` of compatible morphisms `h i` on an open cover
of `Z`. -/
def glueHomAffine : Z ⟶ affine.{u} K n :=
  ⟨⟨glueAux Z U hU h hbase hgerm, isLocalHom_stalkMap_glueAux Z U hU h hbase hgerm⟩, by
    rw [LocallyRingedSpace.Γ_map_op]
    refine RingHom.ext fun c => ?_
    change glueSec Z U hU h hbase hgerm ⊤ ((affine.{u} K n).algebraMap c) = Z.algebraMap c
    symm
    refine eq_glueSec_of_germ Z U hU h hbase hgerm ⊤ ((affine.{u} K n).algebraMap c)
      (Z.algebraMap c) ?_
    intro z hz i hi
    -- the constant `c` pulls back to the constant `c` along `h i`
    have hc := congrArg (fun φ => φ c) (h i).2
    rw [LocallyRingedSpace.Γ_map_op] at hc
    change (h i).1.c.app (op ⊤) ((affine.{u} K n).algebraMap c) =
      (Z.restrictOpen (U i)).algebraMap c at hc
    change _ = Z.toLocallyRingedSpace.presheaf.germ _ z _
      ((h i).1.c.app (op ⊤) ((affine.{u} K n).algebraMap c))
    rw [hc]
    change _ = Z.toLocallyRingedSpace.presheaf.germ _ z _
      ((LocallyRingedSpace.Γ.map (ofRestrict Z (U i)).1.op).hom (Z.algebraMap c))
    rw [LocallyRingedSpace.Γ_map_op]
    exact (TopCat.Presheaf.germ_res_apply Z.toLocallyRingedSpace.presheaf
      ((Opens.isOpenEmbedding (U i)).isOpenMap.adjunction.counit.app ⊤) z _ _).symm⟩

theorem toFun_glueHomAffine (z : Z) :
    Hom.toFun (glueHomAffine Z U hU h hbase hgerm) z = glueBase Z U hU h z := rfl

theorem toFun_glueHomAffine_eq {i : ι} (z : Z) (hi : z ∈ U i) :
    Hom.toFun (glueHomAffine Z U hU h hbase hgerm) z = (h i).1.base ⟨z, hi⟩ :=
  glueBase_eq Z U hU h hbase i z hi

/-- The germ at `z ∈ U i` of the pullback of a global section of `𝒜_{Kⁿ}` along the glued
morphism is the germ of its pullback along `h i`. -/
theorem germ_pullbackΓ_glueHomAffine
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op ⊤)) (z : Z) {i : ι}
    (hi : z ∈ U i) :
    Z.toLocallyRingedSpace.presheaf.germ ⊤ z (Opens.mem_top z)
        ((glueHomAffine Z U hU h hbase hgerm).pullbackΓ F) =
      Z.toLocallyRingedSpace.presheaf.germ (locV Z U h i ⊤) z
        ((mem_locV Z U h).mpr ⟨hi, Opens.mem_top _⟩) ((h i).pullbackΓ F) := by
  change Z.toLocallyRingedSpace.presheaf.germ ⊤ z (Opens.mem_top z)
      ((LocallyRingedSpace.Γ.map (glueHomAffine Z U hU h hbase hgerm).1.op).hom F) = _
  rw [LocallyRingedSpace.Γ_map_op]
  change Z.toLocallyRingedSpace.presheaf.germ _ z _ (glueSec Z U hU h hbase hgerm ⊤ F) = _
  rw [germ_glueSec Z U hU h hbase hgerm ⊤ F (Opens.mem_top z) hi]
  rfl

end Glue

end AnalyticSpace.KLocallyRingedSpace
