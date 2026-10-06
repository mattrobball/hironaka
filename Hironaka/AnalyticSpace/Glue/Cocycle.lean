/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Normalize
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.Glue.Data
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The cocycle of three transition data near the real points

For three normalized transition data `P_ij`, `P_jk`, `P_ik`
(`Hironaka.AnalyticSpace.Glue.Normalize`) between the local complexifications of `X | U_i`, `X |
U_j`, `X | U_k`, the two morphisms `φ_jk ∘ φ_ij` and `φ_ik` out of the common domain `D = Ω_ij ∩
φ_ij⁻¹(Ω_jk) ∩ Ω_ik ⊆ Y_i` agree on an open subset `N ⊆ D` containing `f_i(U_i ∩ U_j ∩ U_k)`: the
cocycle condition holds on a neighbourhood of the real points (`exists_cocycle_nhd`), under the
hypothesis `huniq` that two morphisms out of a neighbourhood of the real points of one
complexification into another, both compatible with the structure maps `f`, agree near the real
points; the statement needs it. This is as in the proof of [Car57, §3, Proposition 2], where the set
on which the cocycle identity holds is an open set containing the closed subspace.
This is `exists_eq_near_of_huniq` applied to the composite and the direct transition, whose
compatibility with `f_i`, `f_k` and whose ranges are checked from the fields of the data.

Conventions. The range hypotheses of `exists_eq_near_of_huniq` (the two morphisms land in
`Y_k ∖ f_k(U_k ∖ (U_i ∩ U_j ∩ U_k))`) hold because the real points of every transition domain lie
over its overlap (`Ωi_le`, `Ωj_le` of each datum), transitions carry real points to real points
(`toFun_e_hom_val`) and only real points to real points (`exists_eq_of_toFun_e_hom_eq`). Basic
tools come first: composition of the inclusions of open
subspaces (`restrictOpenIncl_trans`), the lift of `f` restricted to a smaller open subset
(`complexifyIncl_comp_pairLift`), the pulled-back open subset `P.pullOpens T ⊆ Y_i` of `T ⊆ Y_j`
under the transition (`imageOpens` of the preimage in the restricted space) and
`PairIso.mem_of_toFun_eq` (real points of the domain lie over `V`). For `U_i ∩ U_j ∩ U_k = ∅`, `N`
may be empty; for `j = i` or `k = i` with the diagonal datum, the composite is the transition itself
and `N = D` works.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- The inclusions of open subspaces compose. -/
theorem restrictOpenIncl_trans (A : KLocallyRingedSpace.{u} K) {U V W : Opens A} (h₁ : U ≤ V)
    (h₂ : V ≤ W) :
    restrictOpenIncl A h₁ ≫ restrictOpenIncl A h₂ = restrictOpenIncl A (h₁.trans h₂) := by
  apply hom_ext_of_comp_eq (ofRestrict A W)
  rw [Category.assoc, restrictOpenIncl_comp_ofRestrict, restrictOpenIncl_comp_ofRestrict,
    restrictOpenIncl_comp_ofRestrict]

variable {X : AnalyticSpace.{u} ℝ}

/-- The lift of `f ∘ incl_V` into `Ω`, restricted to `V' ≤ V`, is the lift of `f ∘ incl_{V'}`. -/
theorem complexifyIncl_comp_pairLift {U : Opens X} (C : Complexification (X.restrictOpen U))
    {V V' : Opens X} (hV : V ≤ U) (hV' : V' ≤ V) (Ω : Opens C.Y)
    (h : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩ ∈ Ω) :
    complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV') ≫ pairLift C hV Ω h =
      pairLift C (hV'.trans hV) Ω (fun v => h ⟨v.1, hV' v.2⟩) := by
  apply hom_ext_of_comp_eq (ofRestrict C.Y.toKLocallyRingedSpace Ω)
  have l := (Category.assoc _ _ _).trans (congrArg
    (fun φ => complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV') ≫ φ)
    (pairLift_comp C hV Ω h))
  have r := pairLift_comp C (hV'.trans hV) Ω (fun v => h ⟨v.1, hV' v.2⟩)
  have m : complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV') ≫
      (complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace hV) ≫ C.f) =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace (hV'.trans hV)) ≫ C.f :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ C.f)
      ((complexifyHom_comp (restrictOpenIncl X.toKLocallyRingedSpace hV')
        (restrictOpenIncl X.toKLocallyRingedSpace hV)).symm.trans
        (congrArg complexifyHom (restrictOpenIncl_trans X.toKLocallyRingedSpace hV' hV))))
  exact l.trans (m.trans r.symm)

namespace PairIso

variable {Ui Uj : Opens X} {Ci : Complexification (X.restrictOpen Ui)}
  {Cj : Complexification (X.restrictOpen Uj)} {V : Opens X} {hVi : V ≤ Ui} {hVj : V ≤ Uj}

/-- The preimage of an open subset `T ⊆ Y_j` under the transition, as an open subset of `Y_i`. -/
noncomputable def pullOpens (P : PairIso Ci Cj V hVi hVj) (T : Opens Cj.Y) : Opens Ci.Y :=
  imageOpens P.Ωi
    ((Opens.map (P.e.hom ≫ ofRestrict Cj.Y.toKLocallyRingedSpace P.Ωj).1.base).obj T)

theorem mem_pullOpens (P : PairIso Ci Cj V hVi hVj) (T : Opens Cj.Y) (y : Ci.Y) :
    y ∈ P.pullOpens T ↔ ∃ h : y ∈ P.Ωi, (KLocallyRingedSpace.Hom.toFun P.e.hom ⟨y, h⟩).1 ∈ T := by
  unfold pullOpens
  rw [mem_imageOpens]
  rfl

theorem pullOpens_le (P : PairIso Ci Cj V hVi hVj) (T : Opens Cj.Y) : P.pullOpens T ≤ P.Ωi :=
  fun y hy => ((P.mem_pullOpens T y).mp hy).fst

/-- A real point of the domain lies over `V`. -/
theorem mem_of_toFun_eq (P : PairIso Ci Cj V hVi hVj) (u : X.restrictOpen Ui)
    (hu : KLocallyRingedSpace.Hom.toFun Ci.f u ∈ P.Ωi) : u.1 ∈ V :=
  Ci.mem_restrictLeOpens.mp (P.Ωi_le hu) u rfl

theorem mem_of_toFun_eq' (P : PairIso Ci Cj V hVi hVj) (u : X.restrictOpen Uj)
    (hu : KLocallyRingedSpace.Hom.toFun Cj.f u ∈ P.Ωj) : u.1 ∈ V :=
  Cj.mem_restrictLeOpens.mp (P.Ωj_le hu) u rfl

end PairIso


/-! ### Compatibility restricted to a smaller open -/

/-- Two complexified inclusions compose (`h₁.trans h₂`), followed by any `g`. -/
theorem complexifyIncl_comp_complexifyIncl_comp {U V W : Opens X} (h₁ : U ≤ V) (h₂ : V ≤ W)
    {Z : KLocallyRingedSpace.{u} ℂ}
    (g : complexify (X.toKLocallyRingedSpace.restrictOpen W) ⟶ Z) :
    complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace h₁) ≫
      (complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace h₂) ≫ g) =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace (h₁.trans h₂)) ≫ g :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun φ => φ ≫ g)
    ((complexifyHom_comp (restrictOpenIncl X.toKLocallyRingedSpace h₁)
      (restrictOpenIncl X.toKLocallyRingedSpace h₂)).symm.trans
      (congrArg complexifyHom (restrictOpenIncl_trans X.toKLocallyRingedSpace h₁ h₂))))

/-- The lift into `D ≤ Ω` followed by the inclusion `D ≤ Ω` is the lift into `Ω`. -/
theorem pairLift_comp_restrictOpenIncl {U : Opens X} (C : Complexification (X.restrictOpen U))
    {V : Opens X} (hV : V ≤ U) (D Ω : Opens C.Y) (hDΩ : D ≤ Ω)
    (hD : ∀ v : X.restrictOpen V, KLocallyRingedSpace.Hom.toFun C.f ⟨v.1, hV v.2⟩ ∈ D) :
    pairLift C hV D hD ≫ restrictOpenIncl C.Y.toKLocallyRingedSpace hDΩ =
      pairLift C hV Ω (fun v => hDΩ (hD v)) := by
  apply hom_ext_of_comp_eq (ofRestrict C.Y.toKLocallyRingedSpace Ω)
  rw [Category.assoc, restrictOpenIncl_comp_ofRestrict, pairLift_comp, pairLift_comp]

namespace PairIso

variable {Ui Uj : Opens X} {Ci : Complexification (X.restrictOpen Ui)}
  {Cj : Complexification (X.restrictOpen Uj)} {V' : Opens X} {hVi' : V' ≤ Ui} {hVj' : V' ≤ Uj}

/-- The compatibility of a datum over `V'`, restricted to `V ≤ V'`. -/
theorem compat_restrict (P : PairIso Ci Cj V' hVi' hVj') {V : Opens X} (h : V ≤ V') :
    pairLift Ci (h.trans hVi') P.Ωi (fun v => P.mem_Ωi ⟨v.1, h v.2⟩) ≫ P.e.hom ≫
      ofRestrict Cj.Y.toKLocallyRingedSpace P.Ωj =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace (h.trans hVj')) ≫ Cj.f :=
  (congrArg (fun φ => φ ≫ P.e.hom ≫ ofRestrict Cj.Y.toKLocallyRingedSpace P.Ωj)
    (complexifyIncl_comp_pairLift Ci hVi' h P.Ωi P.mem_Ωi).symm).trans
    ((Category.assoc _ _ _).trans ((congrArg
      (fun φ => complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace h) ≫ φ) P.compat).trans
      (complexifyIncl_comp_complexifyIncl_comp h hVj' Cj.f)))

end PairIso

/-! ### The cocycle near the real points -/

section Triple

variable {Ui Uj Uk : Opens X} {Ci : Complexification (X.restrictOpen Ui)}
  {Cj : Complexification (X.restrictOpen Uj)} {Ck : Complexification (X.restrictOpen Uk)}
  (Pij : PairIso Ci Cj (Ui ⊓ Uj) inf_le_left inf_le_right)
  (Pjk : PairIso Cj Ck (Uj ⊓ Uk) inf_le_left inf_le_right)
  (Pik : PairIso Ci Ck (Ui ⊓ Uk) inf_le_left inf_le_right)

/-- The common domain `Ω_ij ∩ φ_ij⁻¹(Ω_jk) ∩ Ω_ik ⊆ Y_i` of the composite and the direct
transition. -/
noncomputable def tripleDomain : Opens Ci.Y := Pij.Ωi ⊓ Pij.pullOpens Pjk.Ωi ⊓ Pik.Ωi

theorem tripleDomain_le_Ωij : tripleDomain Pij Pjk Pik ≤ Pij.Ωi :=
  inf_le_left.trans inf_le_left

theorem tripleDomain_le_Ωik : tripleDomain Pij Pjk Pik ≤ Pik.Ωi := inf_le_right

theorem mem_pullOpens_of_mem_tripleDomain {y : Ci.Y} (hy : y ∈ tripleDomain Pij Pjk Pik) :
    (KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨y, tripleDomain_le_Ωij Pij Pjk Pik hy⟩).1 ∈ Pjk.Ωi :=
        by
  obtain ⟨h, hmem⟩ := (Pij.mem_pullOpens Pjk.Ωi y).mp hy.1.2
  exact hmem

theorem range_tripleFirst_subset :
    Set.range (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl Ci.Y.toKLocallyRingedSpace
      (tripleDomain_le_Ωij Pij Pjk Pik) ≫ Pij.e.hom ≫
        ofRestrict Cj.Y.toKLocallyRingedSpace Pij.Ωj)) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict Cj.Y.toKLocallyRingedSpace Pjk.Ωi)) := by
  rintro _ ⟨y, rfl⟩
  rw [range_toFun_ofRestrict]
  change (KLocallyRingedSpace.Hom.toFun Pij.e.hom (KLocallyRingedSpace.Hom.toFun
      (restrictOpenIncl Ci.Y.toKLocallyRingedSpace
    (tripleDomain_le_Ωij Pij Pjk Pik)) y)).1 ∈ (Pjk.Ωi : Set Cj.Y)
  rw [toFun_restrictOpenIncl]
  exact mem_pullOpens_of_mem_tripleDomain Pij Pjk Pik y.2

/-- The first factor of the composite: `D ⟶ Y_j | Ω_jk`. -/
noncomputable def tripleFirst :
    Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik) ⟶
      Cj.Y.toKLocallyRingedSpace.restrictOpen Pjk.Ωi :=
  liftAlong (ofRestrict Cj.Y.toKLocallyRingedSpace Pjk.Ωi)
    (restrictOpenIncl Ci.Y.toKLocallyRingedSpace (tripleDomain_le_Ωij Pij Pjk Pik) ≫ Pij.e.hom ≫
      ofRestrict Cj.Y.toKLocallyRingedSpace Pij.Ωj)
    (range_tripleFirst_subset Pij Pjk Pik)

/-- The composite transition `φ_jk ∘ φ_ij` on the common domain. -/
noncomputable def compTrans :
    Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik) ⟶
      Ck.Y.toKLocallyRingedSpace :=
  tripleFirst Pij Pjk Pik ≫ Pjk.e.hom ≫ ofRestrict Ck.Y.toKLocallyRingedSpace Pjk.Ωj

/-- The direct transition `φ_ik` on the common domain. -/
noncomputable def directTrans :
    Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik) ⟶
      Ck.Y.toKLocallyRingedSpace :=
  restrictOpenIncl Ci.Y.toKLocallyRingedSpace (tripleDomain_le_Ωik Pij Pjk Pik) ≫ Pik.e.hom ≫
    ofRestrict Ck.Y.toKLocallyRingedSpace Pik.Ωj

theorem toFun_tripleFirst_val
    (y : Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik)) :
    (KLocallyRingedSpace.Hom.toFun (tripleFirst Pij Pjk Pik) y).1 =
      (KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨y.1, tripleDomain_le_Ωij Pij Pjk Pik y.2⟩).1 := by
  have h := toFun_liftAlong (ofRestrict Cj.Y.toKLocallyRingedSpace Pjk.Ωi)
    (restrictOpenIncl Ci.Y.toKLocallyRingedSpace (tripleDomain_le_Ωij Pij Pjk Pik) ≫ Pij.e.hom ≫
      ofRestrict Cj.Y.toKLocallyRingedSpace Pij.Ωj) (range_tripleFirst_subset Pij Pjk Pik) y
  change (KLocallyRingedSpace.Hom.toFun (tripleFirst Pij Pjk Pik) y).1 =
    (KLocallyRingedSpace.Hom.toFun Pij.e.hom (KLocallyRingedSpace.Hom.toFun
        (restrictOpenIncl _ _) y)).1 at h
  rw [h, toFun_restrictOpenIncl]

theorem toFun_directTrans_val
    (y : Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik)) :
    KLocallyRingedSpace.Hom.toFun (directTrans Pij Pjk Pik) y =
      (KLocallyRingedSpace.Hom.toFun Pik.e.hom ⟨y.1, tripleDomain_le_Ωik Pij Pjk Pik y.2⟩).1 := by
  change (KLocallyRingedSpace.Hom.toFun Pik.e.hom (KLocallyRingedSpace.Hom.toFun
      (restrictOpenIncl _ _) y)).1 = _
  rw [toFun_restrictOpenIncl]

theorem toFun_compTrans_val
    (y : Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik)) :
    KLocallyRingedSpace.Hom.toFun (compTrans Pij Pjk Pik) y =
      (KLocallyRingedSpace.Hom.toFun Pjk.e.hom ⟨(KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨y.1,
          tripleDomain_le_Ωij Pij Pjk Pik y.2⟩).1,
        mem_pullOpens_of_mem_tripleDomain Pij Pjk Pik y.2⟩).1 := by
  have h : KLocallyRingedSpace.Hom.toFun (tripleFirst Pij Pjk Pik) y =
      ⟨(KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨y.1, tripleDomain_le_Ωij Pij Pjk Pik y.2⟩).1,
        mem_pullOpens_of_mem_tripleDomain Pij Pjk Pik y.2⟩ :=
    Subtype.ext (toFun_tripleFirst_val Pij Pjk Pik y)
  change (KLocallyRingedSpace.Hom.toFun Pjk.e.hom (KLocallyRingedSpace.Hom.toFun
      (tripleFirst Pij Pjk Pik) y)).1 = _
  rw [h]

theorem tripleV_le_Ui : Ui ⊓ Uj ⊓ Uk ≤ Ui := inf_le_left.trans inf_le_left
theorem tripleV_le_Uj : Ui ⊓ Uj ⊓ Uk ≤ Uj := inf_le_left.trans inf_le_right
theorem tripleV_le_Uk : Ui ⊓ Uj ⊓ Uk ≤ Uk := inf_le_right

/-- `f_i(U_i ∩ U_j ∩ U_k)` lies in the common domain. -/
theorem mem_tripleDomain (v : X.restrictOpen (Ui ⊓ Uj ⊓ Uk)) :
    KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, tripleV_le_Ui v.2⟩ ∈ tripleDomain Pij Pjk Pik := by
  have hij : KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, tripleV_le_Ui v.2⟩ ∈ Pij.Ωi := Pij.mem_Ωi
      ⟨v.1, v.2.1⟩
  refine ⟨⟨hij, ?_⟩, Pik.mem_Ωi ⟨v.1, ⟨v.2.1.1, v.2.2⟩⟩⟩
  refine (Pij.mem_pullOpens Pjk.Ωi _).mpr ⟨hij, ?_⟩
  have h := Pij.toFun_e_hom_val ⟨v.1, v.2.1⟩
  change (KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, _⟩,
      _⟩).1 = _ at h
  rw [h]
  exact Pjk.mem_Ωi ⟨v.1, ⟨v.2.1.2, v.2.2⟩⟩

/-- The real points of the common domain lie over `U_i ∩ U_j ∩ U_k`. -/
theorem tripleDomain_le_restrictLeOpens :
    tripleDomain Pij Pjk Pik ≤ Ci.restrictLeOpens (Ui ⊓ Uj ⊓ Uk) := by
  intro y hy
  refine Ci.mem_restrictLeOpens.mpr fun u hu => ?_
  have h₁ : u.1 ∈ Ui ⊓ Uj := Pij.mem_of_toFun_eq u (hu ▸ tripleDomain_le_Ωij Pij Pjk Pik hy)
  have h₂ : u.1 ∈ Ui ⊓ Uk := Pik.mem_of_toFun_eq u (hu ▸ tripleDomain_le_Ωik Pij Pjk Pik hy)
  exact ⟨h₁, h₂.2⟩

/-- The direct transition is compatible with `f_i`, `f_k` on the triple overlap. -/
theorem pairLift_comp_directTrans :
    pairLift Ci (tripleV_le_Ui) (tripleDomain Pij Pjk Pik) (mem_tripleDomain Pij Pjk Pik) ≫
      directTrans Pij Pjk Pik =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace tripleV_le_Uk) ≫ Ck.f := by
  unfold directTrans
  rw [← Category.assoc, pairLift_comp_restrictOpenIncl]
  exact Pik.compat_restrict (V := Ui ⊓ Uj ⊓ Uk) (fun x hx => ⟨hx.1.1, hx.2⟩)

/-- The composite transition is compatible with `f_i`, `f_k` on the triple overlap. -/
theorem pairLift_comp_compTrans :
    pairLift Ci (tripleV_le_Ui) (tripleDomain Pij Pjk Pik) (mem_tripleDomain Pij Pjk Pik) ≫
      compTrans Pij Pjk Pik =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace tripleV_le_Uk) ≫ Ck.f := by
  have h₁ : pairLift Ci tripleV_le_Ui (tripleDomain Pij Pjk Pik) (mem_tripleDomain Pij Pjk Pik) ≫
      tripleFirst Pij Pjk Pik =
      pairLift Cj tripleV_le_Uj Pjk.Ωi (fun v => Pjk.mem_Ωi ⟨v.1, ⟨v.2.1.2, v.2.2⟩⟩) := by
    apply hom_ext_of_comp_eq (ofRestrict Cj.Y.toKLocallyRingedSpace Pjk.Ωi)
    rw [Category.assoc, pairLift_comp]
    unfold tripleFirst
    rw [liftAlong_comp, ← Category.assoc, pairLift_comp_restrictOpenIncl]
    exact Pij.compat_restrict (V := Ui ⊓ Uj ⊓ Uk) (fun x hx => hx.1)
  unfold compTrans
  rw [← Category.assoc, h₁]
  exact Pjk.compat_restrict (V := Ui ⊓ Uj ⊓ Uk) (fun x hx => ⟨hx.1.2, hx.2⟩)

/-- The direct transition sends the common domain into `Y_k ∖ f_k(U_k ∖ (U_i ∩ U_j ∩ U_k))`. -/
theorem toFun_directTrans_mem
    (y : Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik)) :
    KLocallyRingedSpace.Hom.toFun (directTrans Pij Pjk Pik) y ∈ Ck.restrictLeOpens
        (Ui ⊓ Uj ⊓ Uk) := by
  refine Ck.mem_restrictLeOpens.mpr fun u hu => ?_
  have hy : KLocallyRingedSpace.Hom.toFun (directTrans Pij Pjk Pik) y =
      (KLocallyRingedSpace.Hom.toFun Pik.e.hom ⟨y.1, tripleDomain_le_Ωik Pij Pjk Pik y.2⟩).1 := by
    change (KLocallyRingedSpace.Hom.toFun Pik.e.hom (KLocallyRingedSpace.Hom.toFun
        (restrictOpenIncl _ _) y)).1 = _
    rw [toFun_restrictOpenIncl]
  rw [hy] at hu
  obtain ⟨v, hv⟩ := Pik.exists_eq_of_toFun_e_hom_eq ⟨y.1, tripleDomain_le_Ωik Pij Pjk Pik y.2⟩ u
    hu.symm
  have hvij : v.1 ∈ Ui ⊓ Uj := Pij.mem_of_toFun_eq ⟨v.1, v.2.1⟩
    (Set.mem_of_eq_of_mem hv.symm (tripleDomain_le_Ωij Pij Pjk Pik y.2))
  have hy' : (⟨y.1, tripleDomain_le_Ωik Pij Pjk Pik y.2⟩ :
      Ci.Y.toKLocallyRingedSpace.restrictOpen Pik.Ωi) =
      ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, (inf_le_left : Ui ⊓ Uk ≤ Ui) v.2⟩, Pik.mem_Ωi v⟩ :=
          Subtype.ext hv
  rw [hy', Pik.toFun_e_hom_val v] at hu
  have huv : u = ⟨v.1, v.2.2⟩ := Ck.injective_toFun hu
  rw [huv]
  exact ⟨hvij, v.2.2⟩

/-- The composite transition sends the common domain into `Y_k ∖ f_k(U_k ∖ (U_i ∩ U_j ∩ U_k))`. -/
theorem toFun_compTrans_mem
    (y : Ci.Y.toKLocallyRingedSpace.restrictOpen (tripleDomain Pij Pjk Pik)) :
    KLocallyRingedSpace.Hom.toFun (compTrans Pij Pjk Pik) y ∈ Ck.restrictLeOpens (Ui ⊓ Uj ⊓ Uk) :=
        by
  refine Ck.mem_restrictLeOpens.mpr fun u hu => ?_
  -- the first factor on points
  have hfirst : KLocallyRingedSpace.Hom.toFun (tripleFirst Pij Pjk Pik) y =
      ⟨(KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨y.1, tripleDomain_le_Ωij Pij Pjk Pik y.2⟩).1,
        mem_pullOpens_of_mem_tripleDomain Pij Pjk Pik y.2⟩ := by
    apply Subtype.ext
    have h := toFun_liftAlong (ofRestrict Cj.Y.toKLocallyRingedSpace Pjk.Ωi)
      (restrictOpenIncl Ci.Y.toKLocallyRingedSpace (tripleDomain_le_Ωij Pij Pjk Pik) ≫ Pij.e.hom ≫
        ofRestrict Cj.Y.toKLocallyRingedSpace Pij.Ωj) (range_tripleFirst_subset Pij Pjk Pik) y
    change (KLocallyRingedSpace.Hom.toFun (tripleFirst Pij Pjk Pik) y).1 =
      (KLocallyRingedSpace.Hom.toFun Pij.e.hom (KLocallyRingedSpace.Hom.toFun
          (restrictOpenIncl _ _) y)).1 at h
    rw [h, toFun_restrictOpenIncl]
  have hy : KLocallyRingedSpace.Hom.toFun (compTrans Pij Pjk Pik) y =
      (KLocallyRingedSpace.Hom.toFun Pjk.e.hom (KLocallyRingedSpace.Hom.toFun
          (tripleFirst Pij Pjk Pik) y)).1 := rfl
  rw [hy] at hu
  obtain ⟨w, hw⟩ := Pjk.exists_eq_of_toFun_e_hom_eq (KLocallyRingedSpace.Hom.toFun
      (tripleFirst Pij Pjk Pik) y) u
    hu.symm
  have hw' : (KLocallyRingedSpace.Hom.toFun Pij.e.hom ⟨y.1, tripleDomain_le_Ωij Pij Pjk Pik y.2⟩).1
      =
      KLocallyRingedSpace.Hom.toFun Cj.f ⟨w.1, w.2.1⟩ := by
    rw [hfirst] at hw
    exact hw
  obtain ⟨v, hv⟩ := Pij.exists_eq_of_toFun_e_hom_eq ⟨y.1, tripleDomain_le_Ωij Pij Pjk Pik y.2⟩
    ⟨w.1, w.2.1⟩ hw'
  -- `y = f_i v`, `φ_ij (f_i v) = f_j v = f_j w`, hence `w = v` over `X`, and `φ_jk (f_j w) = f_k w`
  have hy' : (⟨y.1, tripleDomain_le_Ωij Pij Pjk Pik y.2⟩ :
      Ci.Y.toKLocallyRingedSpace.restrictOpen Pij.Ωi) =
      ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, (inf_le_left : Ui ⊓ Uj ≤ Ui) v.2⟩, Pij.mem_Ωi v⟩ :=
          Subtype.ext hv
  have hw₂ := hw'
  rw [hy', Pij.toFun_e_hom_val v] at hw₂
  have hvw : (⟨v.1, (inf_le_right : Ui ⊓ Uj ≤ Uj) v.2⟩ : X.restrictOpen Uj) = ⟨w.1, w.2.1⟩ :=
    Cj.injective_toFun hw₂
  have hvw' : v.1 = w.1 := congrArg Subtype.val hvw
  have hfirst' : KLocallyRingedSpace.Hom.toFun (tripleFirst Pij Pjk Pik) y =
      ⟨KLocallyRingedSpace.Hom.toFun Cj.f ⟨w.1, w.2.1⟩, Pjk.mem_Ωi w⟩ := by
    rw [hfirst]
    exact Subtype.ext hw'
  rw [hfirst', Pjk.toFun_e_hom_val w] at hu
  have huw : u = ⟨w.1, w.2.2⟩ := Ck.injective_toFun hu
  rw [huw]
  exact ⟨⟨hvw' ▸ v.2.1, w.2.1⟩, w.2.2⟩

/-- **The cocycle near the real points.** Under the uniqueness hypothesis `huniq` (two morphisms out
of a neighbourhood of the real points of one complexification into another, both compatible with
the structure maps, agree on a smaller such neighbourhood), the composite `φ_jk ∘ φ_ij` and the
direct `φ_ik` agree on an open subset `N ⊆ D` containing `f_i(U_i ∩ U_j ∩ U_k)`. -/
theorem exists_cocycle_nhd
    (huniq : ∀ (V : Opens X) (C C' : Complexification (X.restrictOpen V)) (W : Opens C.Y)
      (hW : ∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W)
      (g₁ g₂ : C.Y.toKLocallyRingedSpace.restrictOpen W ⟶ C'.Y.toKLocallyRingedSpace),
      Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ g₁ = ofRestrict _ ⊤ ≫ C'.f →
      Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ g₂ = ofRestrict _ ⊤ ≫ C'.f →
      ∃ (W₀ : Opens C.Y) (hle : W₀ ≤ W), (∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W₀) ∧
        restrictOpenIncl C.Y.toKLocallyRingedSpace hle ≫ g₁ =
          restrictOpenIncl C.Y.toKLocallyRingedSpace hle ≫ g₂) :
    ∃ (N : Opens Ci.Y) (hle : N ≤ tripleDomain Pij Pjk Pik),
      (∀ v : X.restrictOpen (Ui ⊓ Uj ⊓ Uk), KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1,
          tripleV_le_Ui v.2⟩ ∈ N) ∧
      restrictOpenIncl Ci.Y.toKLocallyRingedSpace hle ≫ compTrans Pij Pjk Pik =
        restrictOpenIncl Ci.Y.toKLocallyRingedSpace hle ≫ directTrans Pij Pjk Pik :=
  exists_eq_near_of_huniq huniq Ci Ck (Ui ⊓ Uj ⊓ Uk) tripleV_le_Ui tripleV_le_Uk
    (tripleDomain Pij Pjk Pik) (mem_tripleDomain Pij Pjk Pik)
    (tripleDomain_le_restrictLeOpens Pij Pjk Pik) (compTrans Pij Pjk Pik) (directTrans Pij Pjk Pik)
    (pairLift_comp_compTrans Pij Pjk Pik) (pairLift_comp_directTrans Pij Pjk Pik)
    (toFun_compTrans_mem Pij Pjk Pik) (toFun_directTrans_mem Pij Pjk Pik)

end Triple

end AnalyticSpace.Glue
