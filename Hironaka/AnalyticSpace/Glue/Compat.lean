/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Space
import Hironaka.AnalyticSpace.Glue.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The constants of the pieces agree on the overlaps of a glued space

For `K`-gluing data `D`, the constant sections `constOn c i` on the images of the pieces
(`Hironaka.AnalyticSpace.Glue.Space`) form a compatible family for Mathlib's sheaf gluing: on
`pieceOpens i ⊓ pieceOpens j` the restrictions of `constOn c i` and `constOn c j` coincide
(`isCompatible_constOn`). The reason is that the transitions `t i j` are `K`-morphisms: they carry
the constant `c` of `Y j | W j i` to the constant `c` of `Y i | W i j`. This is the compatibility
that makes the glued space a `K`-space (`Hironaka.AnalyticSpace.Glue.KSpace`).

Conventions. `constSec X U c` is the restriction of the constant `c ∈ Γ(X)` to the open subset `U`;
a `K`-morphism pulls `constSec` back to `constSec` (`c_app_constSec`, from the defining property of
`K`-morphisms on global sections and the naturality of the sheaf component). Sections on an open
subset inside the range of an open immersion are compared after pulling back along it
(`c_app_injective_of_le_range`, Mathlib's `c_iso`). The glue condition
`f i j ≫ ι i = t i j ≫ f j i ≫ ι j` enters through `PresheafedSpace.congr_app`. For `i = j` both
sides are the restriction of `constOn c i`; for disjoint pieces the overlap is empty.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-! ### Constant sections and `K`-morphisms -/

/-- The constant `c` as a global section of the structure sheaf. -/
noncomputable def globalConst (X : KLocallyRingedSpace.{u} K) (c : K) :
    X.toLocallyRingedSpace.presheaf.obj (op ⊤) :=
  X.algebraMap c

/-- The constant `c` restricted to the open `U` of a `K`-space. -/
noncomputable def constSec (X : KLocallyRingedSpace.{u} K) (U : Opens X) (c : K) :
    X.toLocallyRingedSpace.presheaf.obj (op U) :=
  (X.toLocallyRingedSpace.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (globalConst X c)

/-- Restricting a constant section (along any morphism of the opposite category of opens) gives
the constant section. -/
theorem map_constSec (X : KLocallyRingedSpace.{u} K) {U V : Opens X} (φ : op V ⟶ op U) (c : K) :
    (X.toLocallyRingedSpace.presheaf.map φ).hom (constSec X V c) = constSec X U c := by
  unfold constSec
  have h := congrArg (fun ψ => ψ.hom (globalConst X c))
    (X.toLocallyRingedSpace.presheaf.map_comp (homOfLE (le_top : V ≤ ⊤)).op φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  have e : ((homOfLE (le_top : V ≤ ⊤)).op ≫ φ) = (homOfLE (le_top : U ≤ ⊤)).op :=
    Subsingleton.elim _ _
  rw [e]

/-- A restriction of the global constant along any morphism of opens is the constant section. -/
theorem map_globalConst (X : KLocallyRingedSpace.{u} K) {U : Opens X} (i : op ⊤ ⟶ op U) (c : K) :
    (X.toLocallyRingedSpace.presheaf.map i).hom (globalConst X c) = constSec X U c := by
  unfold constSec
  have e : i = (homOfLE (le_top : U ≤ ⊤)).op := Subsingleton.elim _ _
  rw [e]

/-- A `K`-morphism sends the global constant to the global constant. -/
theorem c_app_top_globalConst {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (c : K) :
    (g.1.c.app (op ⊤)).hom (globalConst B c) = globalConst A c :=
  congrArg (fun φ : K →+* _ => φ c) g.2

/-- A `K`-morphism pulls the constant sections back to the constant sections. -/
theorem c_app_constSec {A B : KLocallyRingedSpace.{u} K} (g : A ⟶ B) (U : Opens B) (c : K) :
    (g.1.c.app (op U)).hom (constSec B U c) = constSec A ((Opens.map g.1.base).obj U) c := by
  have hnat := congrArg (fun φ => φ.hom (globalConst B c))
    (g.1.c.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.pushforward_obj_map] at hnat
  unfold constSec
  rw [hnat, c_app_top_globalConst]
  exact map_globalConst A _ c

/-! ### The sheaf component of an open immersion inside its range -/

/-- An open inside the range of an open immersion is the image of its preimage. -/
theorem opensFunctor_map_eq_of_subset {A B : LocallyRingedSpace.{u}} (g : A ⟶ B)
    [LocallyRingedSpace.IsOpenImmersion g] (O : Opens B) (hO : (O : Set B) ⊆ Set.range g.base) :
    (LocallyRingedSpace.IsOpenImmersion.opensFunctor g).obj ((Opens.map g.base).obj O) = O := by
  apply Opens.ext
  exact Set.image_preimage_eq_of_subset hO

/-- The sheaf component of an open immersion is an isomorphism on opens inside its range. -/
theorem isIso_c_app_of_le_range {A B : LocallyRingedSpace.{u}} (g : A ⟶ B)
    [LocallyRingedSpace.IsOpenImmersion g] (O : Opens B) (hO : (O : Set B) ⊆ Set.range g.base) :
    IsIso (g.c.app (op O)) := by
  rw [← opensFunctor_map_eq_of_subset g O hO]
  exact (inferInstance : PresheafedSpace.IsOpenImmersion g.1).c_iso _

theorem c_app_injective_of_le_range {A B : LocallyRingedSpace.{u}} (g : A ⟶ B)
    [LocallyRingedSpace.IsOpenImmersion g] (O : Opens B) (hO : (O : Set B) ⊆ Set.range g.base) :
    Function.Injective (g.c.app (op O)).hom :=
  ((ConcreteCategory.isIso_iff_bijective _).mp (isIso_c_app_of_le_range g O hO)).injective

namespace KGlueData

variable (D : KGlueData.{u} K)

/-- Pulling the constant of the `i`-th image back along `ι i` gives the constant of `Y i`. -/
theorem c_app_constOn (c : K) (i : D.J) :
    ((D.ι i).c.app (op (D.pieceOpens i))).hom (D.constOn c i) =
      constSec (D.Y i) ((Opens.map (D.ι i).base).obj (D.pieceOpens i)) c := by
  exact (LocallyRingedSpace.IsOpenImmersion.invApp_app_apply (D.ι i) ⊤
    (globalConst (D.Y i) c)).trans (map_globalConst (D.Y i) _ c)

/-- Pulling the constant of the `j`-th image back along `ι i` gives the constant of `Y i` on
`(ι i)⁻¹ (pieceOpens j)`: the glue condition and the `K`-morphism property of `t i j`. -/
theorem c_app_constOn_other (c : K) (i j : D.J) :
    ((D.ι i).c.app (op (D.pieceOpens j))).hom (D.constOn c j) =
      constSec (D.Y i) ((Opens.map (D.ι i).base).obj (D.pieceOpens j)) c := by
  have hsub : (((Opens.map (D.ι i).base).obj (D.pieceOpens j) : Opens (D.Y i)) : Set (D.Y i)) ⊆
      Set.range (D.f i j).base := by
    rw [D.map_pieceOpens_eq i j]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  apply c_app_injective_of_le_range (D.f i j) _ hsub
  rw [c_app_constSec (ofRestrict (D.Y i) (D.W i j)) _ c]
  have hglue : D.f i j ≫ D.ι i = (D.t i j).1 ≫ D.f j i ≫ D.ι j :=
    (D.toLRSGlueData.toGlueData.glue_condition i j).symm
  have hcongr := PresheafedSpace.congr_app (congrArg (fun φ => φ.toHom) hglue) (op (D.pieceOpens j))
  have hval := congrArg (fun φ => φ.hom (D.constOn c j)) hcongr
  refine Eq.trans ?_ (Eq.trans hval ?_)
  · rfl
  · rw [CommRingCat.hom_comp, RingHom.comp_apply]
    have h₁ : (((D.t i j).1 ≫ D.f j i ≫ D.ι j).c.app (op (D.pieceOpens j))).hom (D.constOn c j) =
        ((D.t i j).1.c.app (op ((Opens.map (D.f j i).base).obj
          ((Opens.map (D.ι j).base).obj (D.pieceOpens j))))).hom
          (((D.f j i).c.app (op ((Opens.map (D.ι j).base).obj (D.pieceOpens j)))).hom
            (((D.ι j).c.app (op (D.pieceOpens j))).hom (D.constOn c j))) := rfl
    rw [h₁, D.c_app_constOn c j, c_app_constSec (ofRestrict (D.Y j) (D.W j i)),
      c_app_constSec (D.t i j)]
    exact map_constSec _ _ c

/-- The constants of the pieces form a compatible family on the images. -/
theorem isCompatible_constOn (c : K) :
    TopCat.Presheaf.IsCompatible D.glued.presheaf D.pieceOpens (D.constOn c) := by
  intro i j
  apply D.c_app_injective_of_le (D.pieceOpens i ⊓ D.pieceOpens j) inf_le_left
  have hnatL := congrArg (fun φ => φ.hom (D.constOn c i))
    ((D.ι i).c.naturality (Opens.infLELeft (D.pieceOpens i) (D.pieceOpens j)).op)
  have hnatR := congrArg (fun φ => φ.hom (D.constOn c j))
    ((D.ι i).c.naturality (Opens.infLERight (D.pieceOpens i) (D.pieceOpens j)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.pushforward_obj_map]
    at hnatL hnatR
  rw [hnatL, hnatR, D.c_app_constOn c i, D.c_app_constOn_other c i j, map_constSec, map_constSec]

end KGlueData

end AnalyticSpace.Glue
