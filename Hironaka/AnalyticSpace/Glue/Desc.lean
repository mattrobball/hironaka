/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.KSpace
import Hironaka.AnalyticSpace.Glue.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# `K`-morphisms out of a glued `K`-space

For `K`-gluing data `D` (`Hironaka.AnalyticSpace.Glue.Data`) and `K`-morphisms `g i : Y i ⟶ Z`
compatible with the transitions (`f i j ≫ g i = t i j ≫ f j i ≫ g j` on the overlaps), the universal
property of the multicoequalizer gives a morphism `descLRS g : glued ⟶ Z` of locally ringed spaces
with `ι i ≫ descLRS g = g i`; it is a `K`-morphism `descK g : gluedK ⟶ Z`
(`Hironaka.AnalyticSpace.Glue.KSpace`): the constant `c` of `Z` pulls back to the glued constant,
because on every image `ι i '' ⊤` its pull-back is the constant of `Y i` (the `K`-morphism property
of `g i`) and the glued constant is the unique section with these restrictions. Two `K`-morphisms
out of the glued `K`-space agreeing after every `ιK i` are equal (`hom_ext_gluedK`).

Conventions. The compatibility is stated at the level of locally ringed spaces (`(g i).1`), in the
parenthesisation of Mathlib's multispan diagram (`D.f i j`, `D.t i j ≫ D.f j i`). With one piece,
`descK g` is `g 0` up to the identification of the glued space with the piece; for `Z = gluedK` and
`g i = ιK i` the descent is the identity (`hom_ext_gluedK`).

This is how the morphism from the complexified space into the glued space is assembled from the
local complexifications (`Hironaka.AnalyticSpace.Glue.Morphism`), and how the map from a glued space
of local resolutions to the base is defined (`Hironaka.AnalyticSpace.Glue.Over`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue.KGlueData

universe u

variable {K : Type} [RCLike K] (D : KGlueData.{u} K) {Z : KLocallyRingedSpace.{u} K}
  (g : ∀ i, D.Y i ⟶ Z)
  (hg : ∀ i j, D.f i j ≫ (g i).1 = ((D.t i j).1 ≫ D.f j i) ≫ (g j).1)

/-- Every point of the glued space comes from a piece (Mathlib's `ι_jointly_surjective`, restated
with the index and piece types of the `K`-gluing data). -/
theorem exists_ι_base_eq (z : D.glued) : ∃ (i : D.J) (y : D.Y i), (D.ι i).base y = z :=
  D.toLRSGlueData.ι_jointly_surjective z

/-- The descent of compatible morphisms on the pieces to the glued locally ringed space. -/
noncomputable def descLRS : D.glued ⟶ Z.toLocallyRingedSpace :=
  Multicoequalizer.desc D.toLRSGlueData.toGlueData.diagram _ (fun i => (g i).1)
    (fun p => hg p.1 p.2)

theorem ι_descLRS (i : D.J) : D.ι i ≫ D.descLRS g hg = (g i).1 :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The pull-back of the constant `c` of `Z` along the descent is the glued constant. -/
theorem c_app_top_descLRS (c : K) :
    ((D.descLRS g hg).c.app (op ⊤)).hom (globalConst Z c) = D.glueConst c := by
  apply D.glueConst_unique
  intro i
  apply D.c_app_injective_of_le (D.pieceOpens i) le_rfl
  rw [D.c_app_constOn]
  set s : D.glued.presheaf.obj (op ⊤) := ((D.descLRS g hg).c.app (op ⊤)).hom (globalConst Z c)
    with hs
  have hnat : ((D.ι i).c.app (op (D.pieceOpens i))).hom
      ((D.glued.presheaf.map (homOfLE (le_top : D.pieceOpens i ≤ ⊤)).op).hom s) =
      ((D.Y i).toLocallyRingedSpace.presheaf.map
        ((Opens.map (D.ι i).base).map (homOfLE (le_top : D.pieceOpens i ≤ ⊤))).op).hom
        (((D.ι i).c.app (op ⊤)).hom s) :=
    congrArg (fun φ => φ.hom s)
      ((D.ι i).c.naturality (homOfLE (le_top : D.pieceOpens i ≤ ⊤)).op)
  rw [hnat]
  let cZ : LocallyRingedSpace.Γ.obj (op Z.toLocallyRingedSpace) := globalConst Z c
  have hΓ := congrArg
    (fun φ : (D.Y i).toLocallyRingedSpace ⟶ Z.toLocallyRingedSpace =>
      (LocallyRingedSpace.Γ.map φ.op).hom cZ)
    (D.ι_descLRS g hg i)
  have hcomp : (LocallyRingedSpace.Γ.map (D.ι i ≫ D.descLRS g hg).op).hom cZ =
      ((D.ι i).c.app (op ⊤)).hom s := by
    rw [op_comp, Functor.map_comp, hs]
    rfl
  have hgi : (LocallyRingedSpace.Γ.map (g i).1.op).hom cZ = globalConst (D.Y i) c :=
    c_app_top_globalConst (g i) c
  have h₁ : ((D.ι i).c.app (op ⊤)).hom s = globalConst (D.Y i) c :=
    hcomp.symm.trans (hΓ.trans hgi)
  rw [h₁]
  exact map_globalConst (D.Y i) _ c

/-- The descent as a `K`-morphism out of the glued `K`-space. -/
noncomputable def descK : D.gluedK ⟶ Z :=
  ⟨D.descLRS g hg, RingHom.ext fun c => D.c_app_top_descLRS g hg c⟩

theorem descK_val : (D.descK g hg).1 = D.descLRS g hg := rfl

theorem ιK_descK (i : D.J) : D.ιK i ≫ D.descK g hg = g i :=
  Hom.ext (D.ι_descLRS g hg i)

theorem toFun_descK_ιK (i : D.J) (y : D.Y i) :
    KLocallyRingedSpace.Hom.toFun (D.descK g hg) (KLocallyRingedSpace.Hom.toFun
        (D.ιK i) y) = KLocallyRingedSpace.Hom.toFun (g i) y :=
  congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ y) (D.ιK_descK g hg i)

/-- Two `K`-morphisms out of the glued `K`-space agreeing on every piece are equal. -/
theorem hom_ext_gluedK {h h' : D.gluedK ⟶ Z} (H : ∀ i, D.ιK i ≫ h = D.ιK i ≫ h') : h = h' :=
  Hom.ext (Multicoequalizer.hom_ext _ _ _ fun i => congrArg Subtype.val (H i))

end AnalyticSpace.Glue.KGlueData
