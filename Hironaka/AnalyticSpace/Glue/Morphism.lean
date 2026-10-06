/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.CocycleData
public import Hironaka.AnalyticSpace.Glue.Trivial
import Hironaka.AnalyticSpace.Manifold.Restrict
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The morphism from `X(ℂ)` to the glued space

The complexified space `X(ℂ)` is covered by the open subsets `U'_i = {x ∈ U_i | f_i x ∈ A_i}` (every
`x` lies in some `V_i`, and `f_i(closure V_i) = core i ⊆ A_i`); on `X(ℂ) | U'_i` the morphism `g_i`
is `f_i` lifted into the piece `Y_i | A_i`, followed by the open immersion `ιK i` into the glued
`K`-space (`coverHom`); on an overlap `U'_i ∩ U'_j` the two lifts agree because `f_i` lands in
`W_ij` there, the transition carries it to `f_j` (`PairIso.compat_restrict`), and the glue condition
identifies `ι_i` with `t_ij ≫ ι_j` on `W_ij`. Presenting `X(ℂ)` as the gluing of its own cover
(`coverIso`, `Hironaka.AnalyticSpace.Glue.Trivial`) and descending (`descK`), the `g_i` assemble to
`toGluedK : X(ℂ) ⟶ gluedK` with `ofRestrict U'_i ≫ toGluedK = g_i`; on points,
`toGluedK x = ι_i (f_i x)` for any `i` with `x ∈ U'_i`.

Conventions. `pieceLiftOn i hV : (X | V)(ℂ) ⟶ Y_i | A_i` is `pairLift` of `f_i` for `V ≤ U'_i`;
`overlapIso` identifies the overlap piece `(X(ℂ) | U'_i) | U'_j` of the gluing data of the cover
with `X(ℂ) | (U'_i ⊓ U'_j)`, and `comp_complexifyRestrictIso_inv` moves any inclusion of it into
`X(ℂ) | U'_k` through the identification `(X | U)(ℂ) ≅ X(ℂ) | U` (`complexifyRestrictIso`). For
`i = j`, `W_ii = ⊤` and the compatibility is the identity; for disjoint `U'_i`, `U'_j` the overlap
piece is empty.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- The glue condition of `K`-gluing data at the level of `K`-morphisms. -/
theorem KGlueData.ofRestrict_comp_ιK (D : KGlueData.{u} K) (i j : D.J) :
    ofRestrict (D.Y i) (D.W i j) ≫ D.ιK i = D.t i j ≫ ofRestrict (D.Y j) (D.W j i) ≫ D.ιK j :=
  Hom.ext (D.toLRSGlueData.toGlueData.glue_condition i j).symm

variable {X : AnalyticSpace.{u} ℝ} {D : LocalData X} {huniq : Huniq X}

namespace Shrunk

variable (S : Shrunk D huniq)

/-! ### The cover `U'_i = f_i⁻¹(A_i)` of `X` -/

theorem isOpen_coverSet (i : D.J) :
    IsOpen {x : X | ∃ h : x ∈ D.U i, KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨x, h⟩ ∈ S.A i} := by
  have h : {x : X | ∃ h : x ∈ D.U i, KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨x, h⟩ ∈ S.A i} =
      Subtype.val '' {u : X.restrictOpen (D.U i) | KLocallyRingedSpace.Hom.toFun
          (D.C i).f u ∈ S.A i} := by
    ext x
    constructor
    · rintro ⟨hx, hA⟩
      exact ⟨⟨x, hx⟩, hA, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
  rw [h]
  exact (D.U i).isOpen.isOpenMap_subtype_val _
    ((S.A i).isOpen.preimage (D.C i).f.1.base.hom.continuous)

/-- The open `U'_i = {x ∈ U_i | f_i x ∈ A_i}`. -/
noncomputable def coverOpens (i : D.J) : Opens X :=
  ⟨{x : X | ∃ h : x ∈ D.U i, KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨x, h⟩ ∈ S.A i},
      S.isOpen_coverSet i⟩

theorem mem_coverOpens {i : D.J} {x : X} :
    x ∈ S.coverOpens i ↔ ∃ h : x ∈ D.U i, KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨x, h⟩ ∈ S.A i :=
        Iff.rfl

theorem coverOpens_le (i : D.J) : S.coverOpens i ≤ D.U i := by
  intro x hx
  obtain ⟨h, -⟩ := S.mem_coverOpens.mp hx
  exact h

theorem toFun_mem_A {i : D.J} {V : Opens X} (hV : V ≤ S.coverOpens i) (v : X.restrictOpen V) :
    KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨v.1, (hV.trans (S.coverOpens_le i)) v.2⟩ ∈ S.A i := by
  obtain ⟨h, hA⟩ := S.mem_coverOpens.mp (hV v.2)
  exact hA

/-- The `U'_i` cover `X`: `x ∈ V_i` gives `f_i x ∈ core i ⊆ A_i`. -/
theorem exists_mem_coverOpens (x : complexify X.toKLocallyRingedSpace) :
    ∃ i, x ∈ S.coverOpens i := by
  have hx : x ∈ ⋃ i, (D.V i : Set X) := D.V_cover ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hU : x ∈ D.U i := D.closure_V_subset i (subset_closure hi)
  exact ⟨i, hU, S.core_subset i ⟨⟨x, hU⟩, subset_closure hi, rfl⟩⟩

/-! ### The lifts of the `f_i` into the pieces -/

/-- `f_i` on `(X | V)(ℂ)`, `V ≤ U'_i`, lifted into the piece `Y_i | A_i`. -/
noncomputable def pieceLiftOn (i : D.J) {V : Opens X} (hV : V ≤ S.coverOpens i) :
    complexify (X.restrictOpen V).toKLocallyRingedSpace ⟶ S.piece i :=
  pairLift (D.C i) (hV.trans (S.coverOpens_le i)) (S.A i) (S.toFun_mem_A hV)

theorem pieceLiftOn_comp_ofRestrict (i : D.J) {V : Opens X} (hV : V ≤ S.coverOpens i) :
    S.pieceLiftOn i hV ≫ ofRestrict (D.C i).Y.toKLocallyRingedSpace (S.A i) =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace (hV.trans (S.coverOpens_le i))) ≫
        (D.C i).f :=
  pairLift_comp _ _ _ _

@[reassoc]
theorem complexifyIncl_comp_pieceLiftOn (i : D.J) {V V' : Opens X} (hV : V ≤ S.coverOpens i)
    (hV' : V' ≤ V) :
    complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV') ≫ S.pieceLiftOn i hV =
      S.pieceLiftOn i (hV'.trans hV) :=
  complexifyIncl_comp_pairLift _ _ _ _ _

theorem toFun_pieceLiftOn_val (i : D.J) {V : Opens X} (hV : V ≤ S.coverOpens i)
    (v : X.restrictOpen V) :
    (KLocallyRingedSpace.Hom.toFun (S.pieceLiftOn i hV) v).1 =
      KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨v.1, (hV.trans (S.coverOpens_le i)) v.2⟩ :=
  toFun_pairLift_val _ _ _ _ v

/-! ### The compatibility on the overlaps -/

theorem overlap_le_left (i j : D.J) : S.coverOpens i ⊓ S.coverOpens j ≤ D.U i ⊓ D.U j :=
  inf_le_inf (S.coverOpens_le i) (S.coverOpens_le j)

/-- On the overlap, `f_i` lands in the gluing open `W_ij`. -/
theorem toFun_mem_WOpen_overlap (i j : D.J)
    (v : X.restrictOpen (S.coverOpens i ⊓ S.coverOpens j)) :
    KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨v.1,
      ((inf_le_left : S.coverOpens i ⊓ S.coverOpens j ≤ S.coverOpens i).trans
        (S.coverOpens_le i)) v.2⟩ ∈ S.WOpen i j := by
  by_cases h : i = j
  · subst h
    exact S.mem_WOpen_self i _
  · have hUij : v.1 ∈ D.U i ⊓ D.U j := S.overlap_le_left i j v.2
    have hj : j ∈ D.rel i := ⟨v.1, hUij.1, hUij.2⟩
    rw [S.WOpen_of_ne_of_mem h hj]
    have hΩ := (D.P i j).mem_Ωi ⟨v.1, hUij⟩
    refine ⟨⟨S.toFun_mem_A inf_le_left v, hΩ⟩, ((D.P i j).mem_pullOpens (S.A j) _).mpr ⟨hΩ, ?_⟩⟩
    exact Set.mem_of_eq_of_mem ((D.P i j).toFun_e_hom_val ⟨v.1, hUij⟩)
      (S.toFun_mem_A inf_le_right ⟨v.1, v.2⟩)

theorem range_pieceLiftOn_overlap_subset (i j : D.J) :
    Set.range (KLocallyRingedSpace.Hom.toFun (S.pieceLiftOn i
        (inf_le_left : S.coverOpens i ⊓ S.coverOpens j ≤ _))) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict (S.piece i) (S.W i j))) := by
  rintro _ ⟨v, rfl⟩
  rw [range_toFun_ofRestrict]
  exact (S.mem_W _).mpr
    (Set.mem_of_eq_of_mem (S.toFun_pieceLiftOn_val i _ v) (S.toFun_mem_WOpen_overlap i j v))

/-- `f_i` on the overlap, lifted into `(Y_i | A_i) | W_ij`. -/
noncomputable def overlapLift (i j : D.J) :
    complexify (X.restrictOpen (S.coverOpens i ⊓ S.coverOpens j)).toKLocallyRingedSpace ⟶
      (S.piece i).restrictOpen (S.W i j) :=
  liftAlong (ofRestrict (S.piece i) (S.W i j)) (S.pieceLiftOn i inf_le_left)
    (S.range_pieceLiftOn_overlap_subset i j)

theorem overlapLift_comp_ofRestrict (i j : D.J) :
    S.overlapLift i j ≫ ofRestrict (S.piece i) (S.W i j) = S.pieceLiftOn i inf_le_left :=
  liftAlong_comp _ _ _

theorem overlapLift_comp_ι (i j : D.J) :
    S.overlapLift i j ≫ S.ι i j =
      pairLift (D.C i) ((S.overlap_le_left i j).trans inf_le_left) (D.P i j).Ωi
        (fun v => (D.P i j).mem_Ωi ⟨v.1, S.overlap_le_left i j v.2⟩) := by
  apply hom_ext_of_comp_eq (ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i j).Ωi)
  rw [Category.assoc, S.ι_comp_ofRestrict, pairLift_comp]
  unfold incl₂
  rw [← Category.assoc, S.overlapLift_comp_ofRestrict]
  exact S.pieceLiftOn_comp_ofRestrict i _

/-- The transition carries the lift of `f_i` to the lift of `f_j` (`PairIso.compat` restricted to
the overlap). -/
theorem overlapLift_comp_t (i j : D.J) :
    S.overlapLift i j ≫ S.t i j ≫ ofRestrict (S.piece j) (S.W j i) =
      S.pieceLiftOn j inf_le_right := by
  apply hom_ext_of_comp_eq (ofRestrict (D.C j).Y.toKLocallyRingedSpace (S.A j))
  have h₁ : ofRestrict (S.piece j) (S.W j i) ≫ ofRestrict (D.C j).Y.toKLocallyRingedSpace (S.A j) =
      incl₂ (D.C j).Y.toKLocallyRingedSpace (S.A j) (S.W j i) := rfl
  simp only [Category.assoc]
  rw [h₁, S.t_comp_incl₂']
  unfold tW
  rw [← Category.assoc, S.overlapLift_comp_ι]
  exact ((D.P i j).compat_restrict (S.overlap_le_left i j)).trans
    (S.pieceLiftOn_comp_ofRestrict j _).symm

/-- The two lifts of the overlap into the glued `K`-space agree. -/
theorem pieceLiftOn_comp_ιK (i j : D.J) :
    S.pieceLiftOn i (inf_le_left : S.coverOpens i ⊓ S.coverOpens j ≤ _) ≫ S.data.ιK i =
      S.pieceLiftOn j (inf_le_right : S.coverOpens i ⊓ S.coverOpens j ≤ _) ≫ S.data.ιK j := by
  rw [← S.overlapLift_comp_ofRestrict i j, Category.assoc, S.data.ofRestrict_comp_ιK i j,
    ← S.overlapLift_comp_t i j]
  simp only [Category.assoc]

/-! ### The morphisms on the cover and their descent -/

/-- The morphism `X(ℂ) | U'_i ⟶ gluedK`: `f_i` lifted into the piece, then the open immersion. -/
noncomputable def coverHom (i : D.J) :
    (complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i) ⟶ S.data.gluedK :=
  (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i)).inv ≫
    S.pieceLiftOn i le_rfl ≫ S.data.ιK i

/-- The overlap piece of the trivial gluing data of the cover is `X(ℂ) | (U'_i ⊓ U'_j)`. -/
noncomputable def overlapIso (i j : D.J) :
    ((complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i)).restrictOpen
        (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j) ≅
      (complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i ⊓ S.coverOpens j) :=
  isoOfRangeEq (incl₂ (complexify X.toKLocallyRingedSpace) (S.coverOpens i)
      (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j))
    (ofRestrict (complexify X.toKLocallyRingedSpace) (S.coverOpens i ⊓ S.coverOpens j)) (by
    rw [range_toFun_incl₂_coverW, range_toFun_ofRestrict]
    rfl)

theorem overlapIso_hom_comp (i j : D.J) :
    (S.overlapIso i j).hom ≫
        ofRestrict (complexify X.toKLocallyRingedSpace) (S.coverOpens i ⊓ S.coverOpens j) =
      incl₂ (complexify X.toKLocallyRingedSpace) (S.coverOpens i)
        (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j) :=
  isoOfRangeEq_hom_comp _ _ _

/-- Any inclusion of the overlap piece into `X(ℂ) | U'_k`, followed by the identification with
`(X | U'_k)(ℂ)`, is the identification of the overlap followed by the complexified inclusion. -/
theorem comp_complexifyRestrictIso_inv {i j k : D.J}
    (hk : S.coverOpens i ⊓ S.coverOpens j ≤ S.coverOpens k)
    (a : ((complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i)).restrictOpen
        (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j) ⟶
      (complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens k))
    (ha : a ≫ ofRestrict (complexify X.toKLocallyRingedSpace) (S.coverOpens k) =
      incl₂ (complexify X.toKLocallyRingedSpace) (S.coverOpens i)
        (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j)) :
    a ≫ (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens k)).inv =
      (S.overlapIso i j).hom ≫
        (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i ⊓ S.coverOpens j)).inv ≫
          complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hk) := by
  rw [Iso.comp_inv_eq]
  apply hom_ext_of_comp_eq (ofRestrict (complexify X.toKLocallyRingedSpace) (S.coverOpens k))
  rw [ha]
  simp only [Category.assoc]
  rw [complexifyRestrictIso_hom_comp_ofRestrict, ← complexifyHom_comp,
    restrictOpenIncl_comp_ofRestrict, ← complexifyRestrictIso_hom_comp_ofRestrict,
    Iso.inv_hom_id_assoc, S.overlapIso_hom_comp]

theorem ofRestrict_comp_coverHom (i j : D.J) :
    ofRestrict ((complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i))
        (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j) ≫ S.coverHom i =
      (S.overlapIso i j).hom ≫
        (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i ⊓ S.coverOpens j)).inv ≫
          S.pieceLiftOn i inf_le_left ≫ S.data.ιK i := by
  unfold coverHom
  rw [← Category.assoc, S.comp_complexifyRestrictIso_inv inf_le_left _ rfl]
  simp only [Category.assoc]
  exact congrArg (fun φ => (S.overlapIso i j).hom ≫
    (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i ⊓ S.coverOpens j)).inv ≫ φ)
    (S.complexifyIncl_comp_pieceLiftOn_assoc i le_rfl inf_le_left (S.data.ιK i))

theorem coverT_comp_ofRestrict_comp_coverHom (i j : D.J) :
    (coverT (complexify X.toKLocallyRingedSpace) S.coverOpens i j ≫
        ofRestrict ((complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens j))
          (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens j i)) ≫ S.coverHom j =
      (S.overlapIso i j).hom ≫
        (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i ⊓ S.coverOpens j)).inv ≫
          S.pieceLiftOn j inf_le_right ≫ S.data.ιK j := by
  unfold coverHom
  rw [← Category.assoc, S.comp_complexifyRestrictIso_inv inf_le_right _ (by
    rw [Category.assoc]
    exact coverT_comp_incl₂ _ _ i j)]
  simp only [Category.assoc]
  exact congrArg (fun φ => (S.overlapIso i j).hom ≫
    (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i ⊓ S.coverOpens j)).inv ≫ φ)
    (S.complexifyIncl_comp_pieceLiftOn_assoc j le_rfl inf_le_right (S.data.ιK j))

/-- The compatibility of the `g_i` on the overlaps, in the form the descent takes. -/
theorem compat (i j : D.J) :
    (coverData (complexify X.toKLocallyRingedSpace) S.coverOpens).f i j ≫ (S.coverHom i).1 =
      (((coverData (complexify X.toKLocallyRingedSpace) S.coverOpens).t i j).1 ≫
        (coverData (complexify X.toKLocallyRingedSpace) S.coverOpens).f j i) ≫
          (S.coverHom j).1 := by
  have h : ofRestrict ((complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i))
      (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens i j) ≫ S.coverHom i =
      (coverT (complexify X.toKLocallyRingedSpace) S.coverOpens i j ≫
        ofRestrict ((complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens j))
          (coverW (complexify X.toKLocallyRingedSpace) S.coverOpens j i)) ≫ S.coverHom j := by
    rw [S.ofRestrict_comp_coverHom, S.coverT_comp_ofRestrict_comp_coverHom]
    exact congrArg (fun φ => (S.overlapIso i j).hom ≫
      (complexifyRestrictIso X.toKLocallyRingedSpace (S.coverOpens i ⊓ S.coverOpens j)).inv ≫ φ)
      (S.pieceLiftOn_comp_ιK i j)
  exact congrArg Subtype.val h

/-- The morphism `X(ℂ) ⟶ gluedK`: the descent of the `g_i` along the presentation of `X(ℂ)` as the
gluing of its cover. -/
noncomputable def toGluedK : complexify X.toKLocallyRingedSpace ⟶ S.data.gluedK :=
  (coverIso (complexify X.toKLocallyRingedSpace) S.coverOpens S.exists_mem_coverOpens).inv ≫
    (coverData (complexify X.toKLocallyRingedSpace) S.coverOpens).descK S.coverHom S.compat

theorem ofRestrict_comp_toGluedK (i : D.J) :
    ofRestrict (complexify X.toKLocallyRingedSpace) (S.coverOpens i) ≫ S.toGluedK =
      S.coverHom i := by
  unfold toGluedK
  rw [← ιK_comp_coverIso_hom (complexify X.toKLocallyRingedSpace) S.coverOpens
    S.exists_mem_coverOpens i, Category.assoc, Iso.hom_inv_id_assoc]
  exact (coverData _ _).ιK_descK S.coverHom S.compat i

/-- On points, `toGluedK x = ι_i (f_i x)` for `x ∈ U'_i`. -/
theorem toFun_toGluedK (i : D.J)
    (x : (complexify X.toKLocallyRingedSpace).restrictOpen (S.coverOpens i)) :
    KLocallyRingedSpace.Hom.toFun S.toGluedK x.1 =
      KLocallyRingedSpace.Hom.toFun (S.data.ιK i) (KLocallyRingedSpace.Hom.toFun
          (S.pieceLiftOn i le_rfl) x) :=
  congrFun (congrArg KLocallyRingedSpace.Hom.toFun (S.ofRestrict_comp_toGluedK i)) x

end Shrunk

end AnalyticSpace.Glue
