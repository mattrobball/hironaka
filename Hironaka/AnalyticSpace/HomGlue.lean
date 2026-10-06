/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.KSpace.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Gluing morphisms of locally ringed spaces along an open cover

Morphisms of locally ringed spaces `g i : X | Uᵢ → W` defined on the members of an open cover of
`X` and agreeing on the overlaps `X | (Uᵢ ⊓ Uⱼ)` glue to a morphism `X → W` restricting to the
`g i` — the existence half of the locality of morphisms (`Hironaka/AnalyticSpace/HomLocal.lean` is
the uniqueness half). Hironaka's universal mapping property (**) of a monoidal transformation
[Hir64, Ch. 0, §2] needs it: the lift of a test pair `(Y', f')` into the blow-up is constructed on
the members of an open cover of `Y'` (over the complement of the centre and in each blow-up
chart) and glued; the pieces agree on the overlaps by uniqueness. Elementary sheaf theory, not in
the sources; stated for general locally ringed spaces.

* `restrictIncl X h : X | V → X | W` for nested opens `V ≤ W` — the inclusion of subtypes with
  the restriction of sections along the inclusion of image opens as sheaf component, so that its
  sheaf component is a restriction map of `𝒪_X` and `restrictIncl ≫ ofRestrict W = ofRestrict V`.
  Compatibility of the pieces is stated with it: `GlueCompatible U g` says
  `restrictIncl ≫ g i = restrictIncl ≫ g j` on `X | (Uᵢ ⊓ Uⱼ)`.
* The base map is pasted from the bases of the pieces (`ContinuousMap.liftCover`).
* A section `s` of `𝒪_W` over `V` pulls back to the pieces `(g i)^* s` over the image opens
  `gluePieceOpens i V = Uᵢ ∩ b⁻¹ V`; they are compatible because their germs agree, through the
  overlap space, when the pieces do (`germ_gluePieceSection_of_overlap`,
  `gluePieceSection_isCompatible`), and glue uniquely (`TopCat.Sheaf.existsUnique_gluing'`) to
  `glueSection V s`; the glued sections form a ring homomorphism and a natural transformation by
  the uniqueness of the gluing.
* The stalk map of the glued morphism at `x ∈ Uᵢ` is the stalk map of `g i`, read through the
  identification of the image points and the stalk of the open subspace (`glueHom_stalkMap`),
  hence local; `ofRestrict ≫ glueOfCover = g i` by `SheafedSpace.hom_stalk_ext`.
* The `K`-morphism form (`KLocallyRingedSpace.glueOfCover`): the glued morphism respects the
  `K`-structures because its global sections restrict to those of the pieces.

Mathlib has `LocallyRingedSpace.GlueData` (gluing spaces), `IsOpenImmersion.lift` and the
sheaf-level `existsUnique_gluing'`, but no gluing of morphisms out of a space covered by opens;
`Scheme.OpenCover.glueMorphisms` is for schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AnalyticSpace

variable (X : LocallyRingedSpace.{u})

/-- The inclusion `X | V → X | W` of the restrictions to nested opens `V ≤ W`, as a morphism of
presheafed spaces: the inclusion of subtypes on points, restriction of sections along the inclusion
of image opens on sheaves. -/
def restrictInclHom {V W : Opens X} (h : V ≤ W) :
    (X.restrict V.isOpenEmbedding).toPresheafedSpace ⟶
      (X.restrict W.isOpenEmbedding).toPresheafedSpace where
  base := TopCat.ofHom ⟨fun p => ⟨p.1, h p.2⟩, (continuous_subtype_val.subtype_mk _)⟩
  c :=
    { app := fun V' => X.presheaf.map (homOfLE (by
        rintro x ⟨p, hp, rfl⟩
        exact ⟨⟨p.1, h p.2⟩, hp, rfl⟩)).op
      naturality := by
        intros
        change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _ ≫ X.presheaf.map _
        rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
        congr 1 }

theorem restrictInclHom_base_apply {V W : Opens X} (h : V ≤ W) (p : X.restrict V.isOpenEmbedding) :
    (restrictInclHom X h).base p = ⟨p.1, h p.2⟩ := rfl

-- The rewrite by `X.presheaf.map_comp` must identify the open sets of `X.toTopCat` with those of
-- `X.toPresheafedSpace`, which the transparency-respecting unifier refuses; the older behaviour is
-- restored for this declaration.
set_option backward.isDefEq.respectTransparency false in
/-- `X | V → X | W → X` is `X | V → X`. -/
theorem restrictInclHom_comp_ofRestrict {V W : Opens X} (h : V ≤ W) :
    restrictInclHom X h ≫ (X.ofRestrict W.isOpenEmbedding).1 =
      (X.ofRestrict V.isOpenEmbedding).1 := by
  refine PresheafedSpace.ext _ _ rfl ?_
  refine NatTrans.ext (funext fun V' => ?_)
  erw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, eqToHom_map, eqToHom_refl,
    Category.comp_id, PresheafedSpace.comp_c_app]
  change X.presheaf.map _ ≫ X.presheaf.map _ = X.presheaf.map _
  rw [← X.presheaf.map_comp]
  congr 1

/-- The stalk map of the inclusion `X | V → X | W` is an isomorphism (the two `ofRestrict` stalk
maps are). -/
instance restrictInclHom_stalkMap_isIso {V W : Opens X} (h : V ≤ W)
    (p : X.restrict V.isOpenEmbedding) : IsIso ((restrictInclHom X h).stalkMap p) := by
  have e := PresheafedSpace.stalkMap.comp (restrictInclHom X h) (X.ofRestrict W.isOpenEmbedding).1 p
  have h1 : IsIso ((restrictInclHom X h ≫ (X.ofRestrict W.isOpenEmbedding).1).stalkMap p) := by
    rw [restrictInclHom_comp_ofRestrict]
    exact PresheafedSpace.ofRestrict_stalkMap_isIso _ _ _
  rw [e] at h1
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace W.isOpenEmbedding _) h1

/-- The inclusion `X | V → X | W` of the restrictions to nested opens `V ≤ W`, as a morphism of
locally ringed spaces. -/
def restrictIncl {V W : Opens X} (h : V ≤ W) :
    X.restrict V.isOpenEmbedding ⟶ X.restrict W.isOpenEmbedding :=
  ⟨restrictInclHom X h, fun _ => isLocalHom_of_isIso _⟩

theorem restrictIncl_comp_ofRestrict {V W : Opens X} (h : V ≤ W) :
    restrictIncl X h ≫ X.ofRestrict W.isOpenEmbedding = X.ofRestrict V.isOpenEmbedding :=
  LocallyRingedSpace.Hom.ext' (restrictInclHom_comp_ofRestrict X h)

theorem restrictIncl_base_apply {V W : Opens X} (h : V ≤ W) (p : X.restrict V.isOpenEmbedding) :
    (restrictIncl X h).base p = ⟨p.1, h p.2⟩ := rfl

section Glue

variable {X} {ι : Type*} (U : ι → Opens X) {W : LocallyRingedSpace.{u}}
  (g : ∀ i, X.restrict (U i).isOpenEmbedding ⟶ W)

/-- The pieces `g i : X | Uᵢ → W` agree on the overlaps `X | (Uᵢ ⊓ Uⱼ)`. -/
def GlueCompatible : Prop :=
  ∀ i j, restrictIncl X (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
    restrictIncl X (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j

variable {U g}

theorem GlueCompatible.base_apply_eq (hg : GlueCompatible U g) (i j : ι) (x : X) (hi : x ∈ U i)
    (hj : x ∈ U j) : (g i).base ⟨x, hi⟩ = (g j).base ⟨x, hj⟩ :=
  congrArg (fun φ : X.restrict (U i ⊓ U j).isOpenEmbedding ⟶ W => φ.base ⟨x, ⟨hi, hj⟩⟩) (hg i j)

variable (U g)

/-- The members of the cover are neighbourhoods of every point. -/
theorem exists_mem_nhds_of_cover (hU : ∀ x : X, ∃ i, x ∈ U i) (x : X) :
    ∃ i, (U i : Set X) ∈ nhds x :=
  let ⟨i, hi⟩ := hU x; ⟨i, (U i).2.mem_nhds hi⟩

/-- The glued base map: `x ↦ (g i).base x` for any `i` with `x ∈ Uᵢ`. -/
noncomputable def glueCoverBase (hU : ∀ x : X, ∃ i, x ∈ U i) (hg : GlueCompatible U g) :
    X.toTopCat ⟶ W.toTopCat :=
  TopCat.ofHom (ContinuousMap.liftCover (fun i => (U i : Set X))
    (fun i => ⟨fun p => (g i).base p, (g i).base.hom.continuous⟩)
    (fun i j x hxi hxj => hg.base_apply_eq i j x hxi hxj) (exists_mem_nhds_of_cover U hU))

theorem glueCoverBase_apply (hU : ∀ x : X, ∃ i, x ∈ U i) (hg : GlueCompatible U g) (i : ι)
    (p : U i) :
    glueCoverBase U g hU hg p = (g i).base p :=
  ContinuousMap.liftCover_coe (S := fun i => (U i : Set X)) (hS := exists_mem_nhds_of_cover U hU) p

/-- The image in `X` of `(g i).base ⁻¹ V ⊆ Uᵢ`: the open on which the piece `(g i)^* s` lives. -/
def gluePieceOpens (i : ι) (V : Opens W) : Opens X :=
  (U i).isOpenEmbedding.functor.obj ((Opens.map (g i).base).obj V)

theorem mem_gluePieceOpens {i : ι} {V : Opens W} {x : X} :
    x ∈ gluePieceOpens U g i V ↔ ∃ hi : x ∈ U i, (g i).base ⟨x, hi⟩ ∈ V := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hi, hV⟩
    exact ⟨⟨x, hi⟩, hV, rfl⟩

/-- The piece `(g i)^* s`, a section of `X` over `gluePieceOpens i V`. -/
def gluePieceSection (i : ι) (V : Opens W) (s : W.presheaf.obj (op V)) :
    X.presheaf.obj (op (gluePieceOpens U g i V)) :=
  (g i).c.app (op V) s

theorem gluePieceOpens_le (hU : ∀ x : X, ∃ i, x ∈ U i) (hg : GlueCompatible U g) (i : ι)
    (V : Opens W) : gluePieceOpens U g i V ≤ (Opens.map (glueCoverBase U g hU hg)).obj V := by
  rintro x ⟨p, hp, rfl⟩
  change glueCoverBase U g hU hg p.1 ∈ V
  rw [glueCoverBase_apply U g hU hg i p]
  exact hp

theorem le_iSup_gluePieceOpens (hU : ∀ x : X, ∃ i, x ∈ U i) (hg : GlueCompatible U g)
    (V : Opens W) :
    (Opens.map (glueCoverBase U g hU hg)).obj V ≤ ⨆ i, gluePieceOpens U g i V := by
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  refine Opens.mem_iSup.mpr ⟨i, ⟨⟨x, hi⟩, ?_, rfl⟩⟩
  change (g i).base ⟨x, hi⟩ ∈ V
  rw [← glueCoverBase_apply U g hU hg i ⟨x, hi⟩]
  exact hx

/-- The germ of a piece at a point, through the overlap space `X | (Uᵢ ⊓ Uⱼ)`: the piece of `g k`
restricted along `X | (Uᵢ ⊓ Uⱼ) → X | U_k` has the germ of the piece itself. -/
theorem germ_gluePieceSection_of_overlap (i j k : ι) (hk : U i ⊓ U j ≤ U k) (V : Opens W)
    (s : W.presheaf.obj (op V)) {x : X} (hi : x ∈ U i) (hj : x ∈ U j)
    (hV : (g k).base ⟨x, hk ⟨hi, hj⟩⟩ ∈ V) :
    (X.toPresheafedSpace.restrictStalkIso (U i ⊓ U j).isOpenEmbedding ⟨x, ⟨hi, hj⟩⟩).hom
        ((X.restrict (U i ⊓ U j).isOpenEmbedding).presheaf.germ
          ((Opens.map (restrictIncl X hk ≫ g k).base).obj V)
          ⟨x, ⟨hi, hj⟩⟩ hV ((restrictIncl X hk ≫ g k).c.app (op V) s)) =
      X.presheaf.germ (gluePieceOpens U g k V) x ((mem_gluePieceOpens U g).mpr ⟨hk ⟨hi, hj⟩, hV⟩)
        (gluePieceSection U g k V s) := by
  have h := congrArg (fun φ => φ.hom ((restrictIncl X hk ≫ g k).c.app (op V) s))
    (PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace
      (U i ⊓ U j).isOpenEmbedding ((Opens.map (restrictIncl X hk ≫ g k).base).obj V)
      ⟨x, ⟨hi, hj⟩⟩ hV)
  simp only [CommRingCat.hom_comp] at h
  refine h.trans ?_
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE _) x _ (gluePieceSection U g k V s)

/-- The pieces `(g i)^* s` are compatible on the overlaps (their germs agree, through the overlap
space, because the pieces agree there). -/
theorem gluePieceSection_isCompatible (hg : GlueCompatible U g) (V : Opens W)
    (s : W.presheaf.obj (op V)) :
    TopCat.Presheaf.IsCompatible X.presheaf (fun i => gluePieceOpens U g i V)
      (fun i => gluePieceSection U g i V s) := by
  intro i j
  apply TopCat.Presheaf.section_ext X.sheaf
  intro x hx
  refine (TopCat.Presheaf.germ_res_apply X.presheaf (Opens.infLELeft _ _) x hx _).trans
    (Eq.trans ?_ (TopCat.Presheaf.germ_res_apply X.presheaf (Opens.infLERight _ _) x hx _).symm)
  obtain ⟨hi, hVi⟩ := (mem_gluePieceOpens U g).mp hx.1
  obtain ⟨hj, hVj⟩ := (mem_gluePieceOpens U g).mp hx.2
  have main : ∀ (A B : X.restrict (U i ⊓ U j).isOpenEmbedding ⟶ W), A = B →
      ∀ (hA : A.base ⟨x, ⟨hi, hj⟩⟩ ∈ V) (hB : B.base ⟨x, ⟨hi, hj⟩⟩ ∈ V),
      (X.toPresheafedSpace.restrictStalkIso (U i ⊓ U j).isOpenEmbedding ⟨x, ⟨hi, hj⟩⟩).hom
          ((X.restrict (U i ⊓ U j).isOpenEmbedding).presheaf.germ ((Opens.map A.base).obj V)
            ⟨x, ⟨hi, hj⟩⟩ hA (A.c.app (op V) s)) =
        (X.toPresheafedSpace.restrictStalkIso (U i ⊓ U j).isOpenEmbedding ⟨x, ⟨hi, hj⟩⟩).hom
          ((X.restrict (U i ⊓ U j).isOpenEmbedding).presheaf.germ ((Opens.map B.base).obj V)
            ⟨x, ⟨hi, hj⟩⟩ hB (B.c.app (op V) s)) := by
    rintro A B rfl hA hB
    rfl
  have e := main _ _ (hg i j) hVi hVj
  exact (germ_gluePieceSection_of_overlap U g i j i inf_le_left V s hi hj hVi).symm.trans
    (e.trans (germ_gluePieceSection_of_overlap U g i j j inf_le_right V s hi hj hVj))

variable (hU : ∀ x : X, ∃ i, x ∈ U i) (hg : GlueCompatible U g)

/-- The glued section over `b⁻¹ V`, `b` the glued base map: the unique section restricting to the
piece `(g i)^* s` on every `gluePieceOpens i V`. -/
noncomputable def glueSection (V : Opens W) (s : W.presheaf.obj (op V)) :
    X.presheaf.obj (op ((Opens.map (glueCoverBase U g hU hg)).obj V)) :=
  (X.sheaf.existsUnique_gluing' (fun i => gluePieceOpens U g i V)
    ((Opens.map (glueCoverBase U g hU hg)).obj V)
    (fun i => homOfLE (gluePieceOpens_le U g hU hg i V)) (le_iSup_gluePieceOpens U g hU hg V)
    (fun i => gluePieceSection U g i V s) (gluePieceSection_isCompatible U g hg V s)).choose

theorem glueSection_res (V : Opens W) (s : W.presheaf.obj (op V)) (i : ι) :
    X.presheaf.map (homOfLE (gluePieceOpens_le U g hU hg i V)).op (glueSection U g hU hg V s) =
      gluePieceSection U g i V s :=
  (X.sheaf.existsUnique_gluing' (fun i => gluePieceOpens U g i V)
    ((Opens.map (glueCoverBase U g hU hg)).obj V)
    (fun i => homOfLE (gluePieceOpens_le U g hU hg i V)) (le_iSup_gluePieceOpens U g hU hg V)
    (fun i => gluePieceSection U g i V s)
    (gluePieceSection_isCompatible U g hg V s)).choose_spec.1 i

theorem eq_glueSection (V : Opens W) (s : W.presheaf.obj (op V))
    (t : X.presheaf.obj (op ((Opens.map (glueCoverBase U g hU hg)).obj V)))
    (ht : ∀ i, X.presheaf.map (homOfLE (gluePieceOpens_le U g hU hg i V)).op t =
      gluePieceSection U g i V s) :
    t = glueSection U g hU hg V s :=
  (X.sheaf.existsUnique_gluing' (fun i => gluePieceOpens U g i V)
    ((Opens.map (glueCoverBase U g hU hg)).obj V)
    (fun i => homOfLE (gluePieceOpens_le U g hU hg i V)) (le_iSup_gluePieceOpens U g hU hg V)
    (fun i => gluePieceSection U g i V s)
    (gluePieceSection_isCompatible U g hg V s)).choose_spec.2 t ht

/-- The glued sections form a ring homomorphism `𝒪_W(V) → 𝒪_X(b⁻¹ V)`. -/
noncomputable def glueSectionHom (V : Opens W) :
    W.presheaf.obj (op V) ⟶ X.presheaf.obj (op ((Opens.map (glueCoverBase U g hU hg)).obj V)) :=
  CommRingCat.ofHom
    { toFun := glueSection U g hU hg V
      map_one' := (eq_glueSection U g hU hg V 1 1 fun i => by
        simp only [map_one, gluePieceSection]; rfl).symm
      map_mul' := fun s t => (eq_glueSection U g hU hg V (s * t) _ fun i => by
        simp only [map_mul, glueSection_res, gluePieceSection]; rfl).symm
      map_zero' := (eq_glueSection U g hU hg V 0 0 fun i => by
        simp only [map_zero, gluePieceSection]; rfl).symm
      map_add' := fun s t => (eq_glueSection U g hU hg V (s + t) _ fun i => by
        simp only [map_add, glueSection_res, gluePieceSection]; rfl).symm }

theorem glueSectionHom_apply (V : Opens W) (s : W.presheaf.obj (op V)) :
    (glueSectionHom U g hU hg V).hom s = glueSection U g hU hg V s := rfl

/-- The sheaf component of the glued morphism. -/
noncomputable def glueCoverC : W.presheaf ⟶ (glueCoverBase U g hU hg) _* X.presheaf where
  app V := glueSectionHom U g hU hg (unop V)
  naturality {V V'} f := by
    ext s
    change glueSection U g hU hg (unop V') (W.presheaf.map f s) =
      X.presheaf.map ((Opens.map (glueCoverBase U g hU hg)).op.map f)
        (glueSection U g hU hg (unop V) s)
    refine (eq_glueSection U g hU hg (unop V') _ _ fun i => ?_).symm
    -- the piece of `V'` is the restriction of the piece of `V` (naturality of `(g i).c`)
    have h1 := congrArg (fun φ => φ.hom s) ((g i).c.naturality f)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
    change X.presheaf.map _ (X.presheaf.map _ (glueSection U g hU hg (unop V) s)) =
      (g i).c.app V' (W.presheaf.map f s)
    rw [h1]
    change _ = X.presheaf.map _ (gluePieceSection U g i (unop V) s)
    rw [← glueSection_res U g hU hg (unop V) s i]
    have key : X.presheaf.map ((Opens.map (glueCoverBase U g hU hg)).op.map f) ≫
        X.presheaf.map (homOfLE (gluePieceOpens_le U g hU hg i (unop V'))).op =
        X.presheaf.map (homOfLE (gluePieceOpens_le U g hU hg i (unop V))).op ≫
          X.presheaf.map
            ((U i).isOpenEmbedding.functor.op.map ((Opens.map (g i).base).op.map f)) := by
      rw [← X.presheaf.map_comp]
      exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)
    exact congrArg (fun φ => φ.hom (glueSection U g hU hg (unop V) s)) key

/-- The glued morphism of presheafed spaces. -/
noncomputable def glueHom : X.toPresheafedSpace ⟶ W.toPresheafedSpace where
  base := glueCoverBase U g hU hg
  c := glueCoverC U g hU hg

theorem glueHom_base_apply (i : ι) (p : U i) : (glueHom U g hU hg).base (p : X) = (g i).base p :=
  glueCoverBase_apply U g hU hg i p

theorem inseparable_glueCoverBase (i : ι) {x : X} (hi : x ∈ U i) :
    Inseparable (glueCoverBase U g hU hg x) ((g i).base ⟨x, hi⟩) := by
  rw [show glueCoverBase U g hU hg x = (g i).base ⟨x, hi⟩ from
    glueCoverBase_apply U g hU hg i ⟨x, hi⟩]

/-- The stalk map of the glued morphism at a point of `Uᵢ` is the stalk map of `g i`, read through
the identification of the image points and the stalk of the open subspace. -/
theorem glueHom_stalkMap (i : ι) {x : X} (hi : x ∈ U i) :
    (glueHom U g hU hg).stalkMap x =
      (W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i hi)).hom ≫
        (g i).stalkMap ⟨x, hi⟩ ≫
          (X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding ⟨x, hi⟩).hom := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hV
  ext s
  change (glueHom U g hU hg).stalkMap x (W.presheaf.germ V _ hV s) =
    (X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding ⟨x, hi⟩).hom
      ((g i).stalkMap ⟨x, hi⟩
        ((W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i hi)).hom
          (W.presheaf.germ V _ hV s)))
  have hVi : (g i).base ⟨x, hi⟩ ∈ V := by
    rw [← glueCoverBase_apply U g hU hg i ⟨x, hi⟩]; exact hV
  have e1 := congrArg (fun φ => φ.hom s) (PresheafedSpace.stalkMap_germ (glueHom U g hU hg) V x hV)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  have e2 := congrArg (fun φ => φ.hom s) (TopCat.Presheaf.germ_stalkSpecializes W.presheaf hV
    (inseparable_glueCoverBase U g hU hg i hi).ge)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  have e3 := congrArg (fun φ => φ.hom ((g i).c.app (op V) s))
    (PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace (U i).isOpenEmbedding
      ((Opens.map (g i).base).obj V) ⟨x, hi⟩ hVi)
  simp only [CommRingCat.hom_comp] at e3
  rw [e1, TopCat.Presheaf.stalkCongr_hom]
  refine Eq.trans ?_ (congrArg (fun t => (X.toPresheafedSpace.restrictStalkIso
    (U i).isOpenEmbedding ⟨x, hi⟩).hom ((g i).stalkMap ⟨x, hi⟩ t)) e2).symm
  refine Eq.trans ?_ (congrArg (fun t => (X.toPresheafedSpace.restrictStalkIso
    (U i).isOpenEmbedding ⟨x, hi⟩).hom t)
    (LocallyRingedSpace.stalkMap_germ_apply (g i) V ⟨x, hi⟩ hVi s)).symm
  refine Eq.trans ?_ e3.symm
  change X.presheaf.germ _ x hV (glueSection U g hU hg V s) =
    X.presheaf.germ _ x _ (gluePieceSection U g i V s)
  rw [← glueSection_res U g hU hg V s i]
  exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (gluePieceOpens_le U g hU hg i V)) x _
    (glueSection U g hU hg V s)).symm

theorem isLocalHom_glueHom_stalkMap (x : X) : IsLocalHom ((glueHom U g hU hg).stalkMap x).hom := by
  obtain ⟨i, hi⟩ := hU x
  rw [glueHom_stalkMap U g hU hg i hi]
  change IsLocalHom
    (((X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding ⟨x, hi⟩).hom).hom.comp
    (((g i).stalkMap ⟨x, hi⟩).hom.comp
      ((W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i hi)).hom).hom))
  have h1 : IsLocalHom ((g i).stalkMap ⟨x, hi⟩).hom := (g i).2 ⟨x, hi⟩
  have h2 : IsLocalHom
      ((X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding ⟨x, hi⟩).hom).hom :=
    isLocalHom_of_isIso _
  have h3 : IsLocalHom
      ((W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i hi)).hom).hom :=
    isLocalHom_of_isIso _
  exact ⟨fun t ht => h3.map_nonunit t (h1.map_nonunit _ (h2.map_nonunit _ ht))⟩

/-- **The morphism of locally ringed spaces glued from compatible pieces** `g i : X | Uᵢ → W`
along an open cover of `X`. -/
noncomputable def glueOfCover : X ⟶ W :=
  ⟨glueHom U g hU hg, isLocalHom_glueHom_stalkMap U g hU hg⟩

theorem glueOfCover_base_apply (i : ι) (p : U i) :
    (glueOfCover U g hU hg).base (p : X) = (g i).base p :=
  glueCoverBase_apply U g hU hg i p

/-- The glued morphism restricts to the pieces. -/
theorem ofRestrict_comp_glueOfCover (i : ι) :
    X.ofRestrict (U i).isOpenEmbedding ≫ glueOfCover U g hU hg = g i := by
  have h := SheafedSpace.hom_stalk_ext
    (X.ofRestrict (U i).isOpenEmbedding ≫ glueOfCover U g hU hg).toShHom
    (g i).toShHom ?_ ?_
  · exact LocallyRingedSpace.Hom.ext' (congrArg (fun φ => φ.hom) h)
  · ext p
    exact glueCoverBase_apply U g hU hg i p
  · intro p
    change (X.ofRestrict (U i).isOpenEmbedding ≫ glueOfCover U g hU hg).stalkMap p = _
    rw [LocallyRingedSpace.stalkMap_comp]
    change (glueHom U g hU hg).stalkMap p.1 ≫ (X.ofRestrict (U i).isOpenEmbedding).stalkMap p = _
    rw [glueHom_stalkMap U g hU hg i p.2]
    have e : (X.ofRestrict (U i).isOpenEmbedding).stalkMap p =
        (X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding p).inv :=
      (PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace _ p).symm
    rw [e]
    change ((W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i p.2)).hom ≫
        (g i).stalkMap p ≫ (X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding p).hom) ≫
        (X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding p).inv =
      (W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i p.2)).hom ≫ (g i).stalkMap p
    rw [Category.assoc]
    exact congrArg
      (fun φ => (W.presheaf.stalkCongr (inseparable_glueCoverBase U g hU hg i p.2)).hom ≫ φ)
      ((Category.assoc _ _ _).trans ((congrArg (fun φ => (g i).stalkMap p ≫ φ)
        (Iso.hom_inv_id (X.toPresheafedSpace.restrictStalkIso (U i).isOpenEmbedding p))).trans
          (Category.comp_id _)))

end Glue

namespace KLocallyRingedSpace

variable {K : Type} [RCLike K] (X : KLocallyRingedSpace.{u} K)

/-- The inclusion `X | V → X | W` of the open subspaces of nested opens `V ≤ W`, as a `K`-morphism
(the factorization of `X | V → X` through `X | W → X`). -/
noncomputable def restrictIncl {V W : Opens X} (h : V ≤ W) : X.restrictOpen V ⟶ X.restrictOpen W :=
  Hom.ofFac (ofRestrict X V) (ofRestrict X W)
    (AnalyticSpace.restrictIncl X.toLocallyRingedSpace h)
    (AnalyticSpace.restrictIncl_comp_ofRestrict X.toLocallyRingedSpace h)

theorem restrictIncl_comp_ofRestrict {V W : Opens X} (h : V ≤ W) :
    KLocallyRingedSpace.restrictIncl X h ≫ ofRestrict X W = ofRestrict X V :=
  Hom.ext (AnalyticSpace.restrictIncl_comp_ofRestrict X.toLocallyRingedSpace h)

theorem restrictIncl_val {V W : Opens X} (h : V ≤ W) :
    (restrictIncl X h).1 = AnalyticSpace.restrictIncl X.toLocallyRingedSpace h := rfl

variable {X} {ι : Type*} (U : ι → Opens X) {W : KLocallyRingedSpace.{u} K}
  (g : ∀ i, X.restrictOpen (U i) ⟶ W)

/-- The `K`-morphisms `g i : X | Uᵢ → W` agree on the overlaps `X | (Uᵢ ⊓ Uⱼ)`. -/
def GlueCompatible : Prop :=
  ∀ i j, KLocallyRingedSpace.restrictIncl X (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
    KLocallyRingedSpace.restrictIncl X (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j

theorem GlueCompatible.val (hg : GlueCompatible U g) :
    AnalyticSpace.GlueCompatible U fun i => (g i).1 :=
  fun i j => congrArg Subtype.val (hg i j)

/-- The `K`-morphism glued from compatible `K`-morphisms `g i : X | Uᵢ → W` along an open cover of
`X`: the glued morphism of locally ringed spaces, which respects the `K`-structures because its
global sections restrict to those of the pieces. -/
noncomputable def glueOfCover (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hg : KLocallyRingedSpace.GlueCompatible U g) : X ⟶ W :=
  ⟨AnalyticSpace.glueOfCover U (fun i => (g i).1) hU (GlueCompatible.val U g hg), by
    refine RingHom.ext fun c => ?_
    change glueSection U (fun i => (g i).1) hU (GlueCompatible.val U g hg) ⊤ (W.algebraMap c) =
      X.algebraMap c
    refine (eq_glueSection U (fun i => (g i).1) hU (GlueCompatible.val U g hg) ⊤ (W.algebraMap c)
      (X.algebraMap c)
      fun i => ?_).symm
    have h := congrArg (fun φ => φ c) (g i).2
    change (g i).1.c.app (op ⊤) (W.algebraMap c) =
      X.presheaf.map (homOfLE le_top).op (X.algebraMap c) at h
    change X.presheaf.map _ (X.algebraMap c) = (g i).1.c.app (op ⊤) (W.algebraMap c)
    rw [h]
    exact congrArg (fun φ => X.presheaf.map φ (X.algebraMap c)) (Subsingleton.elim _ _)⟩

theorem ofRestrict_comp_glueOfCover (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hg : KLocallyRingedSpace.GlueCompatible U g) (i : ι) :
    ofRestrict X (U i) ≫ KLocallyRingedSpace.glueOfCover U g hU hg = g i :=
  Hom.ext (AnalyticSpace.ofRestrict_comp_glueOfCover U (fun i => (g i).1) hU
    (GlueCompatible.val U g hg) i)

theorem glueOfCover_toFun_apply (hU : ∀ x : X, ∃ i, x ∈ U i)
    (hg : KLocallyRingedSpace.GlueCompatible U g) (i : ι)
    (p : U i) :
    Hom.toFun (KLocallyRingedSpace.glueOfCover U g hU hg) (p : X) = Hom.toFun (g i) p :=
  glueOfCover_base_apply U (fun i => (g i).1) hU (GlueCompatible.val U g hg) i p

end KLocallyRingedSpace

end AnalyticSpace
