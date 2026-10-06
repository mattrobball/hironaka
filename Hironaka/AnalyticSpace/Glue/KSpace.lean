/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Compat
public import Hironaka.AnalyticSpace.Glue.Topology
public import Hironaka.AnalyticSpace.Glue.OfCover
import Hironaka.AnalyticSpace.Glue.Constants
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The glued `K`-space

The locally ringed space glued from `K`-gluing data `D` (`Hironaka.AnalyticSpace.Glue.Data`) is a
`K`-space (`gluedK`): the constants of the pieces (`Hironaka.AnalyticSpace.Glue.Space`), compatible
on the overlaps (`Hironaka.AnalyticSpace.Glue.Compat`), glue to global sections by the sheaf
condition (Mathlib's `existsUnique_gluing'`; `glueConst`), the ring-homomorphism laws follow from
the uniqueness of the gluing (`algebraMapGlued`), and the open immersions `ι i` of the pieces become
`K`-morphisms `ιK i : Y i ⟶ gluedK`, each piece being `K`-isomorphic to its image (`imageIso`). With
a countable index type, Hausdorffness (the criterion of `Hironaka.AnalyticSpace.Glue.Topology`,
transported along the comparison isomorphism `topIso`: `t2Space_of_isClosed_transitionGraph`) and
analytic pieces, the glued `K`-space is an analytic `K`-space (`gluedAnalytic`, through
`AnalyticSpace.ofOpenCover` of `Hironaka.AnalyticSpace.Glue.OfCover`).

Conventions. `glueConst c` is the unique global section restricting to `constOn c i` on every image;
`gluedK` is an `abbrev`, so that its underlying locally ringed space is `glued` definitionally. The
Hausdorff hypothesis is stated on the topological gluing data `topGlueData` (closed transition
graphs for `i ≠ j`). With one piece the glued `K`-space is `K`-isomorphic to
the piece; with an empty index type it is the empty analytic space.

This is the assembly step of the gluing of local complexifications [BW59, Proposition 1] and of the
gluing of local resolutions over a base (`Hironaka.AnalyticSpace.Glue.Over`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue.KGlueData

universe u

variable {K : Type} [RCLike K] (D : KGlueData.{u} K)

/-! ### The glued constants -/

theorem top_le_iSup_pieceOpens : (⊤ : Opens D.glued) ≤ ⨆ i, D.pieceOpens i :=
  le_of_eq D.iSup_pieceOpens_eq_top.symm

/-- The unique gluing of the constants of the pieces. -/
theorem existsUnique_glueConst (c : K) :
    ∃! s : D.glued.presheaf.obj (op ⊤),
      ∀ i, (D.glued.presheaf.map (homOfLE (le_top : D.pieceOpens i ≤ ⊤)).op).hom s =
        D.constOn c i :=
  D.glued.toSheafedSpace.sheaf.existsUnique_gluing' D.pieceOpens ⊤ (fun _ => homOfLE le_top)
    D.top_le_iSup_pieceOpens (D.constOn c) (D.isCompatible_constOn c)

/-- The constant `c` of the glued space: the gluing of the constants of the pieces. -/
noncomputable def glueConst (c : K) : D.glued.presheaf.obj (op ⊤) :=
  Classical.choose (D.existsUnique_glueConst c).exists

theorem map_glueConst (c : K) (i : D.J) :
    (D.glued.presheaf.map (homOfLE (le_top : D.pieceOpens i ≤ ⊤)).op).hom (D.glueConst c) =
      D.constOn c i :=
  Classical.choose_spec (D.existsUnique_glueConst c).exists i

theorem glueConst_unique (c : K) (s : D.glued.presheaf.obj (op ⊤))
    (hs : ∀ i, (D.glued.presheaf.map (homOfLE (le_top : D.pieceOpens i ≤ ⊤)).op).hom s =
      D.constOn c i) : s = D.glueConst c :=
  (D.existsUnique_glueConst c).unique hs (D.map_glueConst c)

theorem constOn_add (c c' : K) (i : D.J) :
    D.constOn (c + c') i = D.constOn c i + D.constOn c' i :=
  (congrArg (fun s : (D.Y i).toLocallyRingedSpace.presheaf.obj (op ⊤) =>
    (LocallyRingedSpace.IsOpenImmersion.invApp (D.ι i) ⊤).hom s)
    (map_add (D.Y i).algebraMap c c')).trans (map_add _ _ _)

theorem constOn_mul (c c' : K) (i : D.J) :
    D.constOn (c * c') i = D.constOn c i * D.constOn c' i :=
  (congrArg (fun s : (D.Y i).toLocallyRingedSpace.presheaf.obj (op ⊤) =>
    (LocallyRingedSpace.IsOpenImmersion.invApp (D.ι i) ⊤).hom s)
    (map_mul (D.Y i).algebraMap c c')).trans (map_mul _ _ _)

theorem constOn_one (i : D.J) : D.constOn 1 i = 1 :=
  (congrArg (fun s : (D.Y i).toLocallyRingedSpace.presheaf.obj (op ⊤) =>
    (LocallyRingedSpace.IsOpenImmersion.invApp (D.ι i) ⊤).hom s)
    (map_one (D.Y i).algebraMap)).trans (map_one _)

theorem constOn_zero (i : D.J) : D.constOn 0 i = 0 :=
  (congrArg (fun s : (D.Y i).toLocallyRingedSpace.presheaf.obj (op ⊤) =>
    (LocallyRingedSpace.IsOpenImmersion.invApp (D.ι i) ⊤).hom s)
    (map_zero (D.Y i).algebraMap)).trans (map_zero _)

/-- The `K`-structure of the glued space. -/
noncomputable def algebraMapGlued : K →+* D.glued.presheaf.obj (op ⊤) where
  toFun := D.glueConst
  map_one' := by
    symm
    apply D.glueConst_unique
    intro i
    rw [map_one, D.constOn_one]
  map_mul' c c' := by
    symm
    apply D.glueConst_unique
    intro i
    rw [map_mul, D.map_glueConst, D.map_glueConst, D.constOn_mul]
  map_zero' := by
    symm
    apply D.glueConst_unique
    intro i
    rw [map_zero, D.constOn_zero]
  map_add' c c' := by
    symm
    apply D.glueConst_unique
    intro i
    rw [map_add, D.map_glueConst, D.map_glueConst, D.constOn_add]

/-- The glued `K`-space. -/
noncomputable abbrev gluedK : KLocallyRingedSpace.{u} K where
  toLocallyRingedSpace := D.glued
  algebraMap := D.algebraMapGlued

/-! ### The pieces map into the glued `K`-space by `K`-morphisms -/

/-- The preimage in a piece of its own image is everything. -/
theorem map_pieceOpens_self (i : D.J) : (Opens.map (D.ι i).base).obj (D.pieceOpens i) = ⊤ := by
  rw [D.map_pieceOpens_eq i i, D.W_id]

/-- Pulling the glued constant back to a piece gives the constant of the piece. -/
theorem c_app_top_glueConst (c : K) (i : D.J) :
    ((D.ι i).c.app (op ⊤)).hom (D.glueConst c) = globalConst (D.Y i) c := by
  have hnat := congrArg (fun φ => φ.hom (D.glueConst c))
    ((D.ι i).c.naturality (homOfLE (le_top : D.pieceOpens i ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.pushforward_obj_map,
    Quiver.Hom.unop_op] at hnat
  rw [D.map_glueConst, D.c_app_constOn] at hnat
  -- `hnat : constSec (Y i) O' c = (Y i).map ψ (A)`, `O' = ⊤`; restriction along `ψ` is injective
  have hO := D.map_pieceOpens_self i
  have hiso : IsIso ((Opens.map (D.ι i).base).map (homOfLE (le_top : D.pieceOpens i ≤ ⊤))) := by
    refine ⟨⟨homOfLE ?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    rw [hO]
    exact le_top
  have hinj : Function.Injective ((D.Y i).toLocallyRingedSpace.presheaf.map
      ((Opens.map (D.ι i).base).map (homOfLE (le_top : D.pieceOpens i ≤ ⊤))).op).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).injective
  have key : ((D.Y i).toLocallyRingedSpace.presheaf.map
      ((Opens.map (D.ι i).base).map (homOfLE (le_top : D.pieceOpens i ≤ ⊤))).op).hom
        (((D.ι i).c.app (op ⊤)).hom (D.glueConst c)) =
      ((D.Y i).toLocallyRingedSpace.presheaf.map
      ((Opens.map (D.ι i).base).map (homOfLE (le_top : D.pieceOpens i ≤ ⊤))).op).hom
        (globalConst (D.Y i) c) :=
    hnat.symm.trans (map_globalConst (D.Y i) _ c).symm
  exact hinj key

/-- The open immersion of a piece, as a `K`-morphism into the glued `K`-space. -/
noncomputable def ιK (i : D.J) : D.Y i ⟶ D.gluedK :=
  ⟨D.ι i, RingHom.ext fun c => D.c_app_top_glueConst c i⟩

instance (i : D.J) : LocallyRingedSpace.IsOpenImmersion (D.ιK i).1 :=
  inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (D.ι i))

theorem toFun_ιK (i : D.J) : KLocallyRingedSpace.Hom.toFun (D.ιK i) = (D.ι i).base := rfl

/-- A piece is `K`-isomorphic to its image in the glued `K`-space. -/
noncomputable def imageIso (i : D.J) : KIso (D.Y i) (D.gluedK.restrictOpen (D.pieceOpens i)) :=
  isoOfRangeEq (D.ιK i) (ofRestrict D.gluedK (D.pieceOpens i)) (by
    rw [range_toFun_ofRestrict, toFun_ιK]
    ext z
    rw [SetLike.mem_coe, D.mem_pieceOpens_iff]
    rfl)

/-! ### Hausdorffness and the analytic structure -/

/-- The topological gluing data underlying `D`. -/
noncomputable abbrev topGlueData : TopCat.GlueData.{u} :=
  D.toLRSGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

/-- The glued space is Hausdorff when the pieces are and the transition graphs are closed (the
criterion of `Hironaka.AnalyticSpace.Glue.Topology`, transported along `topIso`). -/
theorem t2Space_of_isClosed_transitionGraph (hT2 : ∀ i, T2Space (D.Y i))
    (hgraph : ∀ i j, i ≠ j → IsClosed (transitionGraph D.topGlueData i j)) :
    T2Space D.glued := by
  have : ∀ i, T2Space (D.topGlueData.U i) := fun i => hT2 i
  have hT : T2Space D.topGlueData.toGlueData.glued :=
    t2Space_glued_of_isClosed_transitionGraph D.topGlueData hgraph
  exact (TopCat.homeoOfIso D.topIso).t2Space

/-- The glued `K`-space is an analytic `K`-space when it is Hausdorff, the index type is countable
and every piece is `K`-isomorphic to an analytic space. -/
noncomputable def gluedAnalytic [Countable D.J] (hT2 : T2Space D.glued)
    (Z : D.J → AnalyticSpace.{u} K) (e : ∀ i, KIso (D.Y i) (Z i).toKLocallyRingedSpace) :
    AnalyticSpace.{u} K :=
  haveI : T2Space D.gluedK := hT2
  AnalyticSpace.ofOpenCover D.gluedK D.pieceOpens (by
      apply Set.eq_univ_of_forall
      intro z
      obtain ⟨i, y, hy⟩ := D.toLRSGlueData.ι_jointly_surjective z
      exact Set.mem_iUnion.mpr ⟨i, (D.mem_pieceOpens_iff i z).mpr ⟨y, hy⟩⟩)
    Z (fun i => (D.imageIso i).symm ≪≫ e i)

end AnalyticSpace.Glue.KGlueData
