/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Complexification
public import Hironaka.AnalyticSpace.HomOfSectionsAffine
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `K`-morphisms from a local model into `(Kⁿ, 𝒜)` from `n` sections

The local-model case of the existence of a morphism into `Kⁿ` with prescribed coordinate
functions: a local analytic `K`-space `L = V(f₁, …, f_k) ⊆ G ⊆ Kᵐ` and `n` global sections `σ_i`
of `𝒪_L`. Near a point of `L` the `σ_i` are the classes of ambient analytic functions `a_i` on an
open `W ⊆ Kᵐ` (the sections of the quotient sheaf are locally the class families of ambient
sections); on such an open `V ⊆ L` the morphism is the closed-immersion restriction
`L|V ⟶ (Kᵐ, 𝒜)|W` followed by the affine morphism of the `a_i` (`modelPiece`), and its
coordinate pullbacks are the classes of the `a_i` (`germ_pullbackΓ_modelPiece_coord`), hence the
`σ_i`; the pieces glue by `glueHomAffine` (`localModel.homOfSections`). Routine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace.KLocallyRingedSpace

variable {K : Type} [RCLike K]

/-! ### Functoriality of the pullback of global sections -/

section PullbackΓ

variable {X Y Z : KLocallyRingedSpace.{u} K}

theorem Hom.pullbackΓ_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : LocallyRingedSpace.Γ.obj (op Z.toLocallyRingedSpace)) :
    (f ≫ g).pullbackΓ s = f.pullbackΓ (g.pullbackΓ s) := by
  simp only [Hom.pullbackΓ, Hom.comp_val, op_comp, Functor.map_comp, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem Hom.pullbackΓ_id (s : LocallyRingedSpace.Γ.obj (op X.toLocallyRingedSpace)) :
    (𝟙 X : X ⟶ X).pullbackΓ s = s := by
  change (LocallyRingedSpace.Γ.map (𝟙 X.toLocallyRingedSpace).op).hom s = s
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The pullback along `e.hom` inverts the pullback along `e.inv`. -/
theorem Iso.hom_pullbackΓ_inv_pullbackΓ (e : X ≅ Y)
    (s : LocallyRingedSpace.Γ.obj (op X.toLocallyRingedSpace)) :
    e.hom.pullbackΓ (e.inv.pullbackΓ s) = s := by
  rw [← Hom.pullbackΓ_comp, e.hom_inv_id, Hom.pullbackΓ_id]

/-- The germ of a global section pulled back along an open immersion `X|U ⟶ X`. -/
theorem germ_pullbackΓ_ofRestrict (U : Opens X) {x : X} (hx : x ∈ U)
    (s : LocallyRingedSpace.Γ.obj (op X.toLocallyRingedSpace)) :
    X.toLocallyRingedSpace.presheaf.germ (imgOpens X U ⊤) x (mem_imgOpens_of_mem X hx trivial)
        ((ofRestrict X U).pullbackΓ s) =
      X.toLocallyRingedSpace.presheaf.germ ⊤ x trivial s := by
  change X.toLocallyRingedSpace.presheaf.germ _ x _
    ((LocallyRingedSpace.Γ.map (ofRestrict X U).1.op).hom s) = _
  rw [LocallyRingedSpace.Γ_map_op]
  exact TopCat.Presheaf.germ_res_apply X.toLocallyRingedSpace.presheaf
    ((Opens.isOpenEmbedding U).isOpenMap.adjunction.counit.app ⊤) x _ _

end PullbackΓ

/-! ### The piece of a local model -/

section Model

variable {n : ℕ} (m : ℕ) (G : Opens (Kn.{u} K m)) {k : ℕ} (f : Fin k → AnalyticFun K m G)

/-- The morphism `L|V ⟶ (Kⁿ, 𝒜)` of a local model `L ⊆ G ⊆ Kᵐ` given by ambient analytic
functions `a_i` on an open `W ⊆ Kᵐ` with `V ⊆ W`: the restriction of the closed immersion
`L ⟶ (Kᵐ, 𝒜)` to `L|V ⟶ (Kᵐ, 𝒜)|W`, followed by the affine morphism of the `a_i`. -/
def modelPiece (V : Opens (localModel K m G f)) (W : Opens (Kn.{u} K m))
    (hVW : ∀ v ∈ V, Hom.toFun (localModel.ι K m G f) v ∈ W)
    (a : Fin n → (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W)) :
    (localModel K m G f).restrictOpen V ⟶ affine.{u} K n :=
  Hom.restrictTo (localModel.ι K m G f) V W hVW ≫ homOfSectionsAffine W a

/-- The affine morphism of the `a_i` on the coordinate germ: the stalk map of the open immersion
`(Kᵐ, 𝒜)|W ⟶ (Kᵐ, 𝒜)` on the germ of `a i`. -/
theorem stalkMap_homOfSectionsAffine_coordAt (W : Opens (Kn.{u} K m))
    (a : Fin n → (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W))
    (w : (affine.{u} K m).restrictOpen W) (i : Fin n) :
    (homOfSectionsAffine W a).1.stalkMap w
        (coordAt K n ((homOfSectionsAffine W a).1.base w) i) =
      (ofRestrict (affine.{u} K m) W).1.stalkMap w
        ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ w.2 (a i)) := by
  have h1 := resIso_germ_pullbackΓ_homOfSectionsAffine_coord W a w i
  rw [← AnalyticSpace.stalkMap_coordAt ((affine.{u} K m).restrictOpen W)
    (homOfSectionsAffine W a) w i] at h1
  have h2 : (homOfSectionsAffine W a).1.stalkMap w
      (coordAt K n ((homOfSectionsAffine W a).1.base w) i) =
      (resIso (affine.{u} K m) W w.2).inv
        ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W w.1 w.2 (a i)) := by
    rw [← h1]
    change _ = ((resIso (affine.{u} K m) W w.2).hom ≫ (resIso (affine.{u} K m) W w.2).inv) _
    rw [Iso.hom_inv_id]
    rfl
  rw [h2, resIso_inv_eq_stalkMap_ofRestrict (affine.{u} K m) W w]
  rfl

/-- The germ at `v ∈ V` of the coordinate pullback of the piece is the germ of the class of
`a i` (the pullback of `a i` along the closed immersion `L ⟶ (Kᵐ, 𝒜)`). -/
theorem germ_pullbackΓ_modelPiece_coord (V : Opens (localModel K m G f)) (W : Opens (Kn.{u} K m))
    (hVW : ∀ v ∈ V, Hom.toFun (localModel.ι K m G f) v ∈ W)
    (a : Fin n → (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W))
    {v : localModel K m G f} (hv : v ∈ V) (i : Fin n) :
    (localModel K m G f).toLocallyRingedSpace.presheaf.germ (imgOpens (localModel K m G f) V ⊤) v
        (mem_imgOpens_of_mem _ hv trivial)
        ((modelPiece m G f V W hVW a).pullbackΓ (coordSection K n i)) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (localModel.ι K m G f).1.base).obj W) v (hVW v hv)
        ((localModel.ι K m G f).1.c.app (op W) (a i)) := by
  suffices key : (resIso (localModel K m G f) V hv).hom
      (((localModel K m G f).restrictOpen V).toLocallyRingedSpace.presheaf.germ ⊤ ⟨v, hv⟩ trivial
        ((modelPiece m G f V W hVW a).pullbackΓ (coordSection K n i))) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (localModel.ι K m G f).1.base).obj W) v (hVW v hv)
        ((localModel.ι K m G f).1.c.app (op W) (a i)) from
    (resIso_hom_germ _ V hv ⊤ trivial _).symm.trans key
  set τ := Hom.restrictTo (localModel.ι K m G f) V W hVW with hτ
  set Φ := homOfSectionsAffine W a with hΦ
  -- (A) the germ of the pullback is the stalk map on the coordinate germ
  rw [← AnalyticSpace.stalkMap_coordAt ((localModel K m G f).restrictOpen V)
    (modelPiece m G f V W hVW a) ⟨v, hv⟩ i]
  -- (B) the stalk map of the composite `τ ≫ Φ`
  have hB : (modelPiece m G f V W hVW a).1.stalkMap ⟨v, hv⟩ =
      Φ.1.stalkMap (τ.1.base ⟨v, hv⟩) ≫ τ.1.stalkMap ⟨v, hv⟩ :=
    LocallyRingedSpace.stalkMap_comp τ.1 Φ.1 ⟨v, hv⟩
  rw [hB]
  change (resIso _ V hv).hom (τ.1.stalkMap ⟨v, hv⟩ (Φ.1.stalkMap (τ.1.base ⟨v, hv⟩)
    (coordAt K n (Φ.1.base (τ.1.base ⟨v, hv⟩)) i))) = _
  -- (C) `Φ` on the coordinate germ
  rw [stalkMap_homOfSectionsAffine_coordAt m W a (τ.1.base ⟨v, hv⟩) i]
  -- (D) `τ ≫ ofRestrict W = ofRestrict L V ≫ ι`
  have hF := congrArg (fun φ => φ.hom ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _
    (τ.1.base ⟨v, hv⟩).2 (a i))) (LocallyRingedSpace.stalkMap_comp τ.1
      (ofRestrict (affine.{u} K m) W).1 ⟨v, hv⟩)
  change (τ.1 ≫ (ofRestrict (affine.{u} K m) W).1).stalkMap ⟨v, hv⟩ _ =
    τ.1.stalkMap ⟨v, hv⟩ ((ofRestrict (affine.{u} K m) W).1.stalkMap (τ.1.base ⟨v, hv⟩)
      ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (τ.1.base ⟨v, hv⟩).2 (a i))) at hF
  erw [← hF]
  have hEq : τ.1 ≫ (ofRestrict (affine.{u} K m) W).1 =
      (ofRestrict (localModel K m G f) V).1 ≫ (localModel.ι K m G f).1 := by
    rw [← Hom.comp_val, ← Hom.comp_val, Hom.restrictTo_comp_ofRestrict]
  have hG := LocallyRingedSpace.stalkMap_congr_hom _ _ hEq ⟨v, hv⟩
  rw [hG]
  change (resIso _ V hv).hom
    (((ofRestrict (localModel K m G f) V).1 ≫ (localModel.ι K m G f).1).stalkMap ⟨v, hv⟩
      ((affine.{u} K m).toLocallyRingedSpace.presheaf.stalkSpecializes _
        ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (τ.1.base ⟨v, hv⟩).2 (a i)))) = _
  have hH := congrArg (fun φ => φ.hom (a i)) (TopCat.Presheaf.germ_stalkSpecializes
    (affine.{u} K m).toLocallyRingedSpace.presheaf (U := W) (τ.1.base ⟨v, hv⟩).2
    (specializes_of_eq (congrArg (fun φ => φ.base ⟨v, hv⟩) hEq.symm)))
  change (affine.{u} K m).toLocallyRingedSpace.presheaf.stalkSpecializes _
    ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (τ.1.base ⟨v, hv⟩).2 (a i)) =
    (affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ _ (a i) at hH
  erw [hH]
  -- (E) the composite `ofRestrict L V ≫ ι` on the germ of `a i`
  have hK := congrArg (fun φ => φ.hom ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _
    (hVW v hv) (a i))) (LocallyRingedSpace.stalkMap_comp (ofRestrict (localModel K m G f) V).1
      (localModel.ι K m G f).1 ⟨v, hv⟩)
  change ((ofRestrict (localModel K m G f) V).1 ≫ (localModel.ι K m G f).1).stalkMap ⟨v, hv⟩ _ =
    (ofRestrict (localModel K m G f) V).1.stalkMap ⟨v, hv⟩ ((localModel.ι K m G f).1.stalkMap v
      ((affine.{u} K m).toLocallyRingedSpace.presheaf.germ W _ (hVW v hv) (a i))) at hK
  erw [hK]
  have hI := PresheafedSpace.stalkMap_germ_apply (localModel.ι K m G f).1.1 W v (hVW v hv) (a i)
  erw [hI]
  have hJ := PresheafedSpace.stalkMap_germ_apply (ofRestrict (localModel K m G f) V).1.1
    ((Opens.map (localModel.ι K m G f).1.base).obj W) ⟨v, hv⟩ (hVW v hv)
    ((localModel.ι K m G f).1.c.app (op W) (a i))
  erw [hJ]
  refine (resIso_hom_germ _ V hv _ (hVW v hv) _).trans ?_
  exact TopCat.Presheaf.germ_res_apply (localModel K m G f).toLocallyRingedSpace.presheaf
    ((Opens.isOpenEmbedding V).isOpenMap.adjunction.counit.app _) v _ _

/-! ### Local lifts of a global section of a local model -/

/-- The sheaf map of the closed immersion `ι : L ⟶ (Kᵐ, 𝒜)` on a section over `W`, at a point:
the class of the germ of the restriction of the section to `G`. -/
theorem ι_c_app_apply (W : Opens (Kn.{u} K m))
    (a : (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W))
    (z : (Opens.map (localModel.ι K m G f).1.base).obj W) :
    ((localModel.ι K m G f).1.c.app (op W) a).1 z =
      Ideal.Quotient.mk _ (((affine.{u} K m).restrictOpen G).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (ofRestrict (affine.{u} K m) G).1.base).obj W) z.1.1 z.2
        ((ofRestrict (affine.{u} K m) G).1.c.app (op W) a)) :=
  rfl

/-- A global section `σ` of a local model is, near every point `y`, the class family of an
ambient analytic function `a` on an open `W ⊆ Kᵐ`: the germ of `ι^*a` at every point of an open
`V ∋ y` is the germ of `σ`. -/
theorem exists_lift_near (σ : (localModel K m G f).toLocallyRingedSpace.presheaf.obj (op ⊤))
    (y : localModel K m G f) :
    ∃ (V : Opens (localModel K m G f)) (_ : y ∈ V) (W : Opens (Kn.{u} K m))
      (hVW : ∀ v ∈ V, Hom.toFun (localModel.ι K m G f) v ∈ W)
      (a : (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W)),
      ∀ v (hv : v ∈ V),
        (localModel K m G f).toLocallyRingedSpace.presheaf.germ
            ((Opens.map (localModel.ι K m G f).1.base).obj W) v (hVW v hv)
            ((localModel.ι K m G f).1.c.app (op W) a) =
          (localModel K m G f).toLocallyRingedSpace.presheaf.germ ⊤ v trivial σ := by
  obtain ⟨V', hyV', iV, W₀, a₀, h⟩ := σ.2 ⟨y, trivial⟩
  set W := imgOpens (affine.{u} K m) G W₀ with hWdef
  have hVW : ∀ v ∈ V', Hom.toFun (localModel.ι K m G f) v ∈ W := by
    intro v hv
    obtain ⟨hz, -⟩ := h ⟨v, hv⟩
    exact mem_imgOpens_of_mem (affine.{u} K m) v.1.2 hz
  refine ⟨V', hyV', W, hVW, a₀, fun v hv => ?_⟩
  refine TopCat.Presheaf.germ_ext _ V' hv (homOfLE fun p hp => hVW p hp) iV ?_
  apply Subtype.ext
  funext z
  obtain ⟨hz, hσ⟩ := h z
  beta_reduce at hσ
  change ((localModel.ι K m G f).1.c.app (op W) a₀).1 ⟨z.1, hVW z.1 z.2⟩ = σ.1 (iV z)
  rw [hσ]
  refine (ι_c_app_apply m G f W a₀ ⟨z.1, hVW z.1 z.2⟩).trans ?_
  congr 1
  apply (ConcreteCategory.bijective_of_isIso (resIso (affine.{u} K m) G z.1.1.2).hom).1
  refine (resIso_hom_germ (affine.{u} K m) G z.1.1.2 _ (hVW z.1 z.2) _).trans ?_
  refine Eq.trans ?_ (resIso_hom_germ (affine.{u} K m) G z.1.1.2 W₀ hz a₀).symm
  exact TopCat.Presheaf.germ_res_apply (affine.{u} K m).toLocallyRingedSpace.presheaf
    ((Opens.isOpenEmbedding (X := (affine.{u} K m).toLocallyRingedSpace.toTopCat)
      G).isOpenMap.adjunction.counit.app W) z.1.1.1 _ a₀

/-! ### The morphism of a local model from `n` global sections -/

variable (σ : Fin n → (localModel K m G f).toLocallyRingedSpace.presheaf.obj (op ⊤))

/-- Lift data at a point `y` for `n` global sections simultaneously. -/
structure LiftData (y : localModel K m G f) where
  /-- The open neighbourhood of `y` on which the lifts exist. -/
  V : Opens (localModel K m G f)
  mem : y ∈ V
  /-- The ambient open of `Kᵐ`. -/
  W : Opens (Kn.{u} K m)
  hVW : ∀ v ∈ V, Hom.toFun (localModel.ι K m G f) v ∈ W
  /-- The ambient lifts. -/
  a : Fin n → (affine.{u} K m).toLocallyRingedSpace.presheaf.obj (op W)
  spec : ∀ (i : Fin n) (v) (hv : v ∈ V),
    (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        ((Opens.map (localModel.ι K m G f).1.base).obj W) v (hVW v hv)
        ((localModel.ι K m G f).1.c.app (op W) (a i)) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ ⊤ v trivial (σ i)

theorem nonempty_liftData (y : localModel K m G f) : Nonempty (LiftData m G f σ y) := by
  choose V hyV W hVW a h using fun i => exists_lift_near m G f (σ i) y
  have hVle : ∀ i, Finset.univ.inf V ≤ V i := fun i => Finset.inf_le (Finset.mem_univ i)
  have hWle : ∀ i, Finset.univ.inf W ≤ W i := fun i => Finset.inf_le (Finset.mem_univ i)
  have hmem : ∀ {α : Type u} [TopologicalSpace α] (T : Fin n → Opens α) (x : α),
      (∀ i, x ∈ T i) → x ∈ Finset.univ.inf T := by
    intro α _ T x hx
    rw [← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simp only [Set.mem_iInter, Function.comp_apply, SetLike.mem_coe]
    exact fun i _ => hx i
  refine ⟨⟨Finset.univ.inf V, hmem V y (hyV ·), Finset.univ.inf W,
    fun v hv => hmem W (Hom.toFun (localModel.ι K m G f) v) fun i => hVW i v (hVle i hv),
    fun i => (affine.{u} K m).toLocallyRingedSpace.presheaf.map (homOfLE (hWle i)).op (a i),
    fun i v hv => ?_⟩⟩
  have hnat := congrArg (fun φ => φ (a i))
    ((localModel.ι K m G f).1.c.naturality (homOfLE (hWle i)).op)
  change (localModel.ι K m G f).1.c.app (op (Finset.univ.inf W))
      ((affine.{u} K m).toLocallyRingedSpace.presheaf.map (homOfLE (hWle i)).op (a i)) =
    (localModel K m G f).toLocallyRingedSpace.presheaf.map
      ((Opens.map (localModel.ι K m G f).1.base).map (homOfLE (hWle i))).op
      ((localModel.ι K m G f).1.c.app (op (W i)) (a i)) at hnat
  rw [hnat]
  exact (TopCat.Presheaf.germ_res_apply _ _ v _ _).trans (h i v (hVle i hv))

/-- A choice of lift data at every point. -/
def liftData (y : localModel K m G f) : LiftData m G f σ y :=
  Classical.choice (nonempty_liftData m G f σ y)

/-- The piece at `y`. -/
abbrev liftPiece (y : localModel K m G f) :
    (localModel K m G f).restrictOpen (liftData m G f σ y).V ⟶ affine.{u} K n :=
  modelPiece m G f (liftData m G f σ y).V (liftData m G f σ y).W (liftData m G f σ y).hVW
    (liftData m G f σ y).a

/-- The germ of the coordinate pullback of the piece at `y` is the germ of `σ i`. -/
theorem germ_pullbackΓ_liftPiece_coord (y : localModel K m G f) {z : localModel K m G f}
    (hz : z ∈ (liftData m G f σ y).V) (i : Fin n) :
    (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        (imgOpens (localModel K m G f) (liftData m G f σ y).V ⊤) z
        (mem_imgOpens_of_mem _ hz trivial) ((liftPiece m G f σ y).pullbackΓ (coordSection K n i)) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ ⊤ z trivial (σ i) :=
  (germ_pullbackΓ_modelPiece_coord m G f _ _ _ _ hz i).trans ((liftData m G f σ y).spec i z hz)

theorem hcoord_liftPiece (y y' : localModel K m G f) {z : localModel K m G f}
    (hz : z ∈ (liftData m G f σ y).V) (hz' : z ∈ (liftData m G f σ y').V) (i : Fin n) :
    (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        (imgOpens (localModel K m G f) (liftData m G f σ y).V ⊤) z
        (mem_imgOpens_of_mem _ hz trivial) ((liftPiece m G f σ y).pullbackΓ (coordSection K n i)) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        (imgOpens (localModel K m G f) (liftData m G f σ y').V ⊤) z
        (mem_imgOpens_of_mem _ hz' trivial)
        ((liftPiece m G f σ y').pullbackΓ (coordSection K n i)) :=
  (germ_pullbackΓ_liftPiece_coord m G f σ y hz i).trans
    (germ_pullbackΓ_liftPiece_coord m G f σ y' hz' i).symm

/-- The germ of the coordinate pullback of the piece at `y`, over the open in the form of
`glueHomAffine`'s `locV`. -/
theorem germ_pullbackΓ_liftPiece_coord' (y : localModel K m G f) {z : localModel K m G f}
    (hz : z ∈ (liftData m G f σ y).V) (i : Fin n) :
    (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        (imgOpens (localModel K m G f) (liftData m G f σ y).V
          ((Opens.map (liftPiece m G f σ y).1.base).obj ⊤)) z
        (mem_imgOpens_of_mem _ hz (Opens.mem_top _))
        ((liftPiece m G f σ y).pullbackΓ (coordSection K n i)) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ ⊤ z trivial (σ i) :=
  germ_pullbackΓ_liftPiece_coord m G f σ y hz i

theorem base_liftPiece_eq (y y' : localModel K m G f) {z : localModel K m G f}
    (hz : z ∈ (liftData m G f σ y).V) (hz' : z ∈ (liftData m G f σ y').V) :
    (liftPiece m G f σ y).1.base ⟨z, hz⟩ = (liftPiece m G f σ y').1.base ⟨z, hz'⟩ :=
  base_eq_of_germ_pullbackΓ_coord (localModel K m G f) (liftPiece m G f σ y) (liftPiece m G f σ y')
    hz hz' (hcoord_liftPiece m G f σ y y' hz hz')

theorem germ_c_app_liftPiece_eq (y y' : localModel K m G f) (V : Opens (Kn.{u} K n))
    (F : (affine.{u} K n).toLocallyRingedSpace.presheaf.obj (op V)) (z : localModel K m G f)
    (hzi : z ∈ locV (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftPiece m G f σ) y V)
    (hzj : z ∈ locV (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftPiece m G f σ) y'
      V) :
    (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        (locV (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftPiece m G f σ) y V) z hzi
        (locSec (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftPiece m G f σ) y V F) =
      (localModel K m G f).toLocallyRingedSpace.presheaf.germ
        (locV (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftPiece m G f σ) y' V) z hzj
        (locSec (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftPiece m G f σ) y' V
          F) := by
  obtain ⟨hz, hV⟩ := (mem_locV (localModel K m G f) (fun y => (liftData m G f σ y).V)
    (liftPiece m G f σ)).mp hzi
  obtain ⟨hz', hV'⟩ := (mem_locV (localModel K m G f) (fun y => (liftData m G f σ y).V)
    (liftPiece m G f σ)).mp hzj
  exact germ_c_app_eq_of_germ_pullbackΓ_coord (localModel K m G f) (liftPiece m G f σ y)
    (liftPiece m G f σ y') hz hz' (hcoord_liftPiece m G f σ y y' hz hz')
    (isNoetherianRing_stalk_localModel K m G f z) V hV hV' F

/-- The cover of `L` by the lifting opens. -/
theorem liftCover (z : localModel K m G f) : ∃ y, z ∈ (fun y => (liftData m G f σ y).V) y :=
  ⟨z, (liftData m G f σ z).mem⟩

theorem liftPiece_hbase : ∀ (y y' : localModel K m G f) (z : localModel K m G f)
    (hz : z ∈ (fun y => (liftData m G f σ y).V) y) (hz' : z ∈ (fun y => (liftData m G f σ y).V) y'),
    (liftPiece m G f σ y).1.base ⟨z, hz⟩ = (liftPiece m G f σ y').1.base ⟨z, hz'⟩ :=
  fun y y' _ hz hz' => base_liftPiece_eq m G f σ y y' hz hz'

/-- The local-model case: the `K`-morphism `L ⟶ (Kⁿ, 𝒜)` with coordinate pullbacks `σ₁, …, σₙ`,
glued from the pieces. -/
def localModel.homOfSections : localModel K m G f ⟶ affine.{u} K n :=
  glueHomAffine (localModel K m G f) (fun y => (liftData m G f σ y).V) (liftCover m G f σ)
    (liftPiece m G f σ) (liftPiece_hbase m G f σ)
    (fun y y' V F z hzi hzj => germ_c_app_liftPiece_eq m G f σ y y' V F z hzi hzj)

/-- The coordinate pullbacks of `localModel.homOfSections σ` are the `σ i`. -/
theorem localModel.pullbackΓ_homOfSections_coordSection (i : Fin n) :
    (localModel.homOfSections m G f σ).pullbackΓ (coordSection K n i) = σ i := by
  apply TopCat.Presheaf.section_ext (localModel K m G f).toLocallyRingedSpace.𝒪
  intro z hz
  have h1 := germ_pullbackΓ_glueHomAffine (localModel K m G f) (fun y => (liftData m G f σ y).V)
    (liftCover m G f σ) (liftPiece m G f σ) (liftPiece_hbase m G f σ)
    (fun y y' V F z hzi hzj => germ_c_app_liftPiece_eq m G f σ y y' V F z hzi hzj)
    (coordSection K n i) z (liftData m G f σ z).mem
  have h2 := germ_pullbackΓ_liftPiece_coord' m G f σ z (liftData m G f σ z).mem i
  exact h1.trans h2

end Model

end AnalyticSpace.KLocallyRingedSpace
