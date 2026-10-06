/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Assemble
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The cocycle identity of the shrunk gluing data

The `K`-gluing core of the shrunk pieces (`Hironaka.AnalyticSpace.Glue.Assemble`) satisfies the
cocycle identity `tRes i j k ≫ tRes j k i ≫ tRes k i j = 𝟙` on the triple pieces
`Z_ijk = (Y_i | A_i) | (W_ij ⊓ W_ik)` (`Shrunk.cocycle`), hence is `K`-gluing data (`Shrunk.data`,
`Hironaka.AnalyticSpace.Glue.Data`) and glues to a `K`-space (`Hironaka.AnalyticSpace.Glue.KSpace`).
The identity is a morphism identity, not a pointwise one: the points of `Z_ijk` lie in the cocycle
neighbourhoods `N_ijk` and `N_iki` (`Hironaka.AnalyticSpace.Glue.TripleSet`, through the shrinking
constraints), on which the transitions satisfy `φ_jk ∘ φ_ij = φ_ik` and `φ_ki ∘ φ_ik = φ_ii = id` as
morphisms (`cocycleNhd_eq`, the cocycle on a neighbourhood of the real points, as in the proof of
[Car57, §3, Proposition 2]); the three restricted transitions, pushed into the ambient
complexifications, are these composites restricted along the inclusion of `Z_ijk` (uniqueness of
lifts along open immersions).

Conventions. `inclZTo Ω` is the inclusion of `Z_ijk` into `Y_i | Ω` for an open subset `Ω ⊆ Y_i`
containing its points; every morphism of the argument out of `Z_ijk` into a restriction of `Y_i` is
identified with such an inclusion by `eq_inclZTo` (uniqueness of lifts), and the chains of
inclusions collapse by `inclZTo_comp_restrictOpenIncl`. Repeated indices need no case split:
`W_ii = ⊤` and `P i i = refl`, so `φ_ii = id` (`e_P_diag_comp_ofRestrict`), and `t_comp_incl₂'`
covers the diagonal transition; for an empty `W_ij ⊓ W_ik` the identity holds on the empty space by
the same argument.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-- The inclusion of a smaller open of a restriction, followed by the double-restriction inclusion,
is the double-restriction inclusion of the smaller open. -/
@[reassoc]
theorem restrictOpenIncl_comp_incl₂ (A : KLocallyRingedSpace.{u} K) (U : Opens A)
    {W W' : Opens (A.restrictOpen U)} (h : W ≤ W') :
    restrictOpenIncl (A.restrictOpen U) h ≫ incl₂ A U W' = incl₂ A U W := by
  unfold incl₂
  rw [← Category.assoc, restrictOpenIncl_comp_ofRestrict]

variable {X : AnalyticSpace.{u} ℝ} {D : LocalData X} {huniq : Huniq X}

namespace LocalData

/-- On the diagonal the transition is the identity of `Y_i`: `e_ii ≫ ofRestrict = ofRestrict`. -/
theorem e_P_diag_comp_ofRestrict (i : D.J) :
    (D.P i i).e.hom ≫ ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i i).Ωj =
      ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i i).Ωi := by
  rw [D.P_diag i]
  exact Category.id_comp _

end LocalData

namespace Shrunk

variable (S : Shrunk D huniq)

/-! ### Points of the triple pieces lie in the cocycle neighbourhoods -/

theorem mem_WOpen_self (i : D.J) (y : (D.C i).Y) : y ∈ S.WOpen i i := by
  rw [S.WOpen_self i]
  exact Set.mem_univ y

theorem mem_rel'_of_mem_WOpen {i j : D.J} {y : (D.C i).Y} (hy : y ∈ S.WOpen i j) :
    j ∈ D.rel' i := by
  by_cases h : i = j
  · subst h
    exact D.self_mem_rel' i
  · exact D.mem_rel'_of_mem_rel (S.mem_rel_of_mem_WOpen h hy)

theorem toFun_e_mem_A_of_mem_WOpen' {i j : D.J} {y : (D.C i).Y} (hA : y ∈ S.A i)
    (hy : y ∈ S.WOpen i j) :
    (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨y, S.mem_Ω_of_mem_WOpen hy⟩).1 ∈ S.A j := by
  by_cases h : i = j
  · subst h
    exact Set.mem_of_eq_of_mem (D.toFun_e_P_diag i _) hA
  · exact S.toFun_e_mem_A_of_mem_WOpen h hy

/-- A point of `A_i ∩ W_ij ∩ W_ik` lies in the cocycle neighbourhood `N_ijk`: the triple
constraint of the shrinking. -/
theorem mem_cocycleNhd_of_mem_WOpen₂ {i j k : D.J} {y : (D.C i).Y} (hA : y ∈ S.A i)
    (hy : y ∈ S.WOpen i j) (hy' : y ∈ S.WOpen i k) : y ∈ D.cocycleNhd huniq i j k :=
  (mem_cocycleNhd_of_mem_nhd' (S.mem_nhd'_of_mem (S.mem_rel'_of_mem_WOpen hy)
    (S.mem_rel'_of_mem_WOpen hy') hA (S.mem_Ω_of_mem_WOpen hy) (S.mem_Ω_of_mem_WOpen hy')
    (S.toFun_e_mem_A_of_mem_WOpen' hA hy) (S.toFun_e_mem_A_of_mem_WOpen' hA hy'))).1

theorem mem_cocycleNhd_of_Z (i j k : D.J) (x : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k)) :
    x.1.1 ∈ D.cocycleNhd huniq i j k :=
  S.mem_cocycleNhd_of_mem_WOpen₂ x.1.2 x.2.1 x.2.2

theorem mem_cocycleNhd_iki_of_Z (i j k : D.J)
    (x : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k)) : x.1.1 ∈ D.cocycleNhd huniq i k i :=
  S.mem_cocycleNhd_of_mem_WOpen₂ x.1.2 x.2.2 (S.mem_WOpen_self i x.1.1)

/-! ### The inclusions of the triple pieces -/

/-- The inclusion of the triple piece `Z_ijk = (Y_i | A_i) | (W_ij ⊓ W_ik)` into `Y_i | Ω`, for an
open `Ω` containing its points. -/
noncomputable def inclZTo (i j k : D.J) (Ω : Opens (D.C i).Y)
    (h : ∀ x : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k), x.1.1 ∈ Ω) :
    (S.piece i).restrictOpen (S.W i j ⊓ S.W i k) ⟶
      (D.C i).Y.toKLocallyRingedSpace.restrictOpen Ω :=
  liftAlong (ofRestrict (D.C i).Y.toKLocallyRingedSpace Ω)
    (incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j ⊓ S.W i k)) (by
      rintro _ ⟨x, rfl⟩
      rw [range_toFun_ofRestrict]
      exact h x)

@[reassoc]
theorem inclZTo_comp_ofRestrict (i j k : D.J) (Ω : Opens (D.C i).Y)
    (h : ∀ x : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k), x.1.1 ∈ Ω) :
    S.inclZTo i j k Ω h ≫ ofRestrict (D.C i).Y.toKLocallyRingedSpace Ω =
      incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j ⊓ S.W i k) :=
  liftAlong_comp _ _ _

/-- Uniqueness of lifts: a morphism of `Z_ijk` into `Y_i | Ω` over the inclusion of `Z_ijk` into
`Y_i` is the inclusion. -/
theorem eq_inclZTo {i j k : D.J} {Ω : Opens (D.C i).Y}
    (h : ∀ x : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k), x.1.1 ∈ Ω)
    {g : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k) ⟶
      (D.C i).Y.toKLocallyRingedSpace.restrictOpen Ω}
    (hg : g ≫ ofRestrict (D.C i).Y.toKLocallyRingedSpace Ω =
      incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j ⊓ S.W i k)) :
    g = S.inclZTo i j k Ω h :=
  liftAlong_unique _ _ _ g hg

@[reassoc]
theorem inclZTo_comp_restrictOpenIncl (i j k : D.J) {Ω Ω' : Opens (D.C i).Y} (hΩ : Ω ≤ Ω')
    (h : ∀ x : (S.piece i).restrictOpen (S.W i j ⊓ S.W i k), x.1.1 ∈ Ω) :
    S.inclZTo i j k Ω h ≫ restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace hΩ =
      S.inclZTo i j k Ω' (fun x => hΩ (h x)) :=
  S.eq_inclZTo _ (by
    rw [Category.assoc, restrictOpenIncl_comp_ofRestrict, S.inclZTo_comp_ofRestrict])

@[reassoc]
theorem restrictOpenIncl_comp_ι_left (i j k : D.J) :
    restrictOpenIncl (S.piece i) (inf_le_left : S.W i j ⊓ S.W i k ≤ S.W i j) ≫ S.ι i j =
      S.inclZTo i j k (D.P i j).Ωi (fun x => S.mem_Ω_of_mem_WOpen x.2.1) :=
  S.eq_inclZTo _ (by
    rw [Category.assoc, S.ι_comp_ofRestrict, restrictOpenIncl_comp_incl₂])

@[reassoc]
theorem restrictOpenIncl_comp_ι_right (i j k : D.J) :
    restrictOpenIncl (S.piece i) (inf_le_right : S.W i j ⊓ S.W i k ≤ S.W i k) ≫ S.ι i k =
      S.inclZTo i j k (D.P i k).Ωi (fun x => S.mem_Ω_of_mem_WOpen x.2.2) :=
  S.eq_inclZTo _ (by
    rw [Category.assoc, S.ι_comp_ofRestrict, restrictOpenIncl_comp_incl₂])

/-! ### The restricted transitions, pushed into the ambient complexifications -/

/-- The transition followed by the inclusion into `Y_j`, on the diagonal included. -/
theorem t_comp_incl₂' (i j : D.J) :
    S.t i j ≫ incl₂ (D.C j).Y.toKLocallyRingedSpace (S.A j) (S.W j i) = S.tW i j := by
  by_cases h : i = j
  · subst h
    rw [S.t_self, Category.id_comp]
    unfold tW
    rw [D.e_P_diag_comp_ofRestrict, S.ι_comp_ofRestrict]
  · exact S.t_comp_incl₂ h

/-- The restricted transition `tRes i j k`, pushed into `Y_j`, is `φ_ij` on the points of `Z_ijk`.
-/
@[reassoc]
theorem tRes_comp_incl₂ (i j k : D.J) :
    S.core.tRes i j k ≫ incl₂ (D.C j).Y.toKLocallyRingedSpace (S.A j) (S.W j k ⊓ S.W j i) =
      restrictOpenIncl (S.piece i) (inf_le_left : S.W i j ⊓ S.W i k ≤ S.W i j) ≫ S.tW i j := by
  have h₁ : S.core.tRes i j k ≫ ofRestrict (S.piece j) (S.W j k ⊓ S.W j i) =
      restrictOpenIncl (S.piece i) inf_le_left ≫ S.t i j ≫ ofRestrict (S.piece j) (S.W j i) :=
    S.core.tRes_comp_ofRestrict i j k
  rw [← S.t_comp_incl₂' i j]
  unfold incl₂
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]

/-- The first restricted transition, pushed into `Y_j | Ω_jk`: the first factor of the composite
transition `compTrans` restricted to `Z_ijk ⊆ N_ijk`. -/
@[reassoc]
theorem tRes_comp_restrictOpenIncl_comp_ι (i j k : D.J) :
    S.core.tRes i j k ≫
      restrictOpenIncl (S.piece j) (inf_le_left : S.W j k ⊓ S.W j i ≤ S.W j k) ≫ S.ι j k =
      S.inclZTo i j k (D.cocycleNhd huniq i j k) (S.mem_cocycleNhd_of_Z i j k) ≫
        restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i j k) ≫
        tripleFirst (D.P i j) (D.P j k) (D.P i k) := by
  apply hom_ext_of_comp_eq (ofRestrict (D.C j).Y.toKLocallyRingedSpace (D.P j k).Ωi)
  have hTF : tripleFirst (D.P i j) (D.P j k) (D.P i k) ≫
      ofRestrict (D.C j).Y.toKLocallyRingedSpace (D.P j k).Ωi =
      restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (tripleDomain_le_Ωij _ _ _) ≫
        (D.P i j).e.hom ≫ ofRestrict (D.C j).Y.toKLocallyRingedSpace (D.P i j).Ωj :=
    liftAlong_comp _ _ _
  simp only [Category.assoc]
  rw [hTF, S.ι_comp_ofRestrict, restrictOpenIncl_comp_incl₂, S.tRes_comp_incl₂]
  unfold tW
  rw [S.restrictOpenIncl_comp_ι_left_assoc]
  simp only [S.inclZTo_comp_restrictOpenIncl_assoc]

/-- The first two restricted transitions, pushed into `Y_k | Ω_ki`: by the cocycle on `N_ijk`
they are `φ_ik` on the points of `Z_ijk`, the first factor of `compTrans` for the triple
`(i, k, i)` restricted to `Z_ijk ⊆ N_iki`. -/
@[reassoc]
theorem tRes_comp_tRes_comp_restrictOpenIncl_comp_ι (i j k : D.J) :
    S.core.tRes i j k ≫ S.core.tRes j k i ≫
      restrictOpenIncl (S.piece k) (inf_le_left : S.W k i ⊓ S.W k j ≤ S.W k i) ≫ S.ι k i =
      S.inclZTo i j k (D.cocycleNhd huniq i k i) (S.mem_cocycleNhd_iki_of_Z i j k) ≫
        restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i k i) ≫
        tripleFirst (D.P i k) (D.P k i) (D.P i i) := by
  apply hom_ext_of_comp_eq (ofRestrict (D.C k).Y.toKLocallyRingedSpace (D.P k i).Ωi)
  have hTF : tripleFirst (D.P i k) (D.P k i) (D.P i i) ≫
      ofRestrict (D.C k).Y.toKLocallyRingedSpace (D.P k i).Ωi =
      restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (tripleDomain_le_Ωij _ _ _) ≫
        (D.P i k).e.hom ≫ ofRestrict (D.C k).Y.toKLocallyRingedSpace (D.P i k).Ωj :=
    liftAlong_comp _ _ _
  have hc : S.inclZTo i j k (D.cocycleNhd huniq i j k) (S.mem_cocycleNhd_of_Z i j k) ≫
      restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i j k) ≫
        tripleFirst (D.P i j) (D.P j k) (D.P i k) ≫ (D.P j k).e.hom ≫
          ofRestrict (D.C k).Y.toKLocallyRingedSpace (D.P j k).Ωj =
      S.inclZTo i j k (D.cocycleNhd huniq i j k) (S.mem_cocycleNhd_of_Z i j k) ≫
      restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i j k) ≫
        restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (tripleDomain_le_Ωik _ _ _) ≫
          (D.P i k).e.hom ≫ ofRestrict (D.C k).Y.toKLocallyRingedSpace (D.P i k).Ωj :=
    congrArg (fun g => S.inclZTo i j k (D.cocycleNhd huniq i j k)
      (S.mem_cocycleNhd_of_Z i j k) ≫ g) (D.cocycleNhd_eq huniq i j k)
  simp only [Category.assoc]
  rw [hTF, S.ι_comp_ofRestrict, restrictOpenIncl_comp_incl₂, S.tRes_comp_incl₂]
  unfold tW
  rw [S.tRes_comp_restrictOpenIncl_comp_ι_assoc, hc]
  simp only [S.inclZTo_comp_restrictOpenIncl_assoc]

/-! ### The cocycle identity and the gluing data -/

/-- The cocycle identity of the shrunk gluing core: by the cocycles on `N_ijk` and `N_iki` the
composite of the three restricted transitions, pushed into `Y_i`, is `φ_ii = id` on the points of
`Z_ijk`, hence the inclusion of `Z_ijk`. -/
theorem cocycle (i j k : D.J) :
    S.core.tRes i j k ≫ S.core.tRes j k i ≫ S.core.tRes k i j = 𝟙 _ := by
  apply hom_ext_of_comp_eq (incl₂ (D.C i).Y.toKLocallyRingedSpace (S.A i) (S.W i j ⊓ S.W i k))
  have hc : S.inclZTo i j k (D.cocycleNhd huniq i k i) (S.mem_cocycleNhd_iki_of_Z i j k) ≫
      restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i k i) ≫
        tripleFirst (D.P i k) (D.P k i) (D.P i i) ≫ (D.P k i).e.hom ≫
          ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P k i).Ωj =
      S.inclZTo i j k (D.cocycleNhd huniq i k i) (S.mem_cocycleNhd_iki_of_Z i j k) ≫
      restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i k i) ≫
        restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (tripleDomain_le_Ωik _ _ _) ≫
          (D.P i i).e.hom ≫ ofRestrict (D.C i).Y.toKLocallyRingedSpace (D.P i i).Ωj :=
    congrArg (fun g => S.inclZTo i j k (D.cocycleNhd huniq i k i)
      (S.mem_cocycleNhd_iki_of_Z i j k) ≫ g) (D.cocycleNhd_eq huniq i k i)
  rw [Category.id_comp]
  simp only [Category.assoc]
  rw [S.tRes_comp_incl₂]
  unfold tW
  rw [S.tRes_comp_tRes_comp_restrictOpenIncl_comp_ι_assoc, hc, D.e_P_diag_comp_ofRestrict]
  simp only [S.inclZTo_comp_restrictOpenIncl_assoc]
  exact S.inclZTo_comp_ofRestrict i j k _ _

/-- The `K`-gluing data of the shrunk pieces. -/
noncomputable abbrev data : KGlueData.{u} ℂ where
  toKGlueCore := S.core
  cocycle := S.cocycle

theorem data_toKGlueCore : S.data.toKGlueCore = S.core := rfl

end Shrunk

end AnalyticSpace.Glue
