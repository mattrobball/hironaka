/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Normalize
public import Hironaka.AnalyticSpace.Glue.GraphClosure
import Hironaka.AnalyticSpace.Glue.Data
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Tame transition data: the graph of a transition closes only on the graph

For a normalized transition datum `P` (`Hironaka.AnalyticSpace.Glue.Normalize`) between the local
complexifications `(Y_i, f_i)`, `(Y_j, f_j)` over `V`, write `P.graph ⊆ Y_i × Y_j` for the graph of
the transition on its domain, `P.realGraph = {(f_i x, f_j x) : x ∈ V}` and
`P.outer = f_i(U_i ∖ V) × f_j(U_j ∖ V)` (a closed set, `imageDiff`). `P` is *tame* when
`closure P.graph` avoids `P.outer`. Then:

* `graph_inter_real_eq`: the graph meets the real points only in the real graph;
* `closure_graph_inter_real_subset`: for tame `P`, the closure of the graph meets `R_i × R_j` only
  in the graph (the three cases of `closure_graphOn_inter_prod_subset`,
  `Hironaka.AnalyticSpace.Glue.GraphClosure`);
* `exists_tame`: for every datum over `V = U_i ⊓ U_j` there is a tame datum over `V` (the domain is
  shrunk by
  `exists_isOpen_graphOn_closure_disjoint`, the transition restricted along `KIso.restrictToImage`,
  defined here: the restriction of a `K`-isomorphism of open subspaces to a smaller open subset and
  its image).

Conventions. The closedness of the real graph uses `V = U_i ⊓ U_j` (the real graph is the image of
the diagonal of `U_i × U_j` under the closed embedding `f_i × f_j`); `Y_i × Y_j` is metrizable
(analytic spaces are regular and second countable). For `V = ∅` the real graph is empty,
`outer = R_i × R_j`, and tameness says that the closure of the graph contains no pair of real
points.

Tameness is the first arrangement in the gluing of local complexifications [BW59, Proposition 1]: it
is what makes the transition graphs of the shrunk pieces closed, hence the glued space Hausdorff.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {K : Type} [RCLike K]

/-! ### Restricting a `K`-isomorphism of open subspaces to a smaller open and its image -/

namespace KIso

variable {A B : KLocallyRingedSpace.{u} K} {Ω : Opens A} {Ω' : Opens B}

theorem toFun_hom_inv (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (z : B.restrictOpen Ω') :
    KLocallyRingedSpace.Hom.toFun e.hom (KLocallyRingedSpace.Hom.toFun e.inv z) = z :=
  congrFun (congrArg KLocallyRingedSpace.Hom.toFun e.inv_hom_id) z

theorem toFun_inv_hom (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (y : A.restrictOpen Ω) :
    KLocallyRingedSpace.Hom.toFun e.inv (KLocallyRingedSpace.Hom.toFun e.hom y) = y :=
  congrFun (congrArg KLocallyRingedSpace.Hom.toFun e.hom_inv_id) y

theorem restrictToImage_le (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (S : Opens A)
    (S' : Opens B) (hS' : (S' : Set B) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom ''
        {y | y.1 ∈ S})) :
    S' ≤ Ω' := by
  intro z hz
  have hz' : z ∈ (S' : Set B) := hz
  rw [hS'] at hz'
  obtain ⟨w, -, rfl⟩ := hz'
  exact w.2

theorem range_hom_subset (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (S : Opens A)
    (hS : S ≤ Ω) (S' : Opens B)
    (hS' : (S' : Set B) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' {y | y.1 ∈ S})) :
    Set.range (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl A hS ≫ e.hom ≫ ofRestrict B Ω')) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict B S')) := by
  rintro _ ⟨y, rfl⟩
  rw [range_toFun_ofRestrict]
  change (KLocallyRingedSpace.Hom.toFun e.hom (KLocallyRingedSpace.Hom.toFun
      (restrictOpenIncl A hS) y)).1 ∈ (S' : Set B)
  rw [hS']
  exact ⟨KLocallyRingedSpace.Hom.toFun e.hom (KLocallyRingedSpace.Hom.toFun
      (restrictOpenIncl A hS) y),
    ⟨KLocallyRingedSpace.Hom.toFun (restrictOpenIncl A hS) y,
        by rw [toFun_restrictOpenIncl]; exact y.2, rfl⟩, rfl⟩

theorem range_inv_subset (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (S : Opens A)
    (_hS : S ≤ Ω) (S' : Opens B)
    (hS' : (S' : Set B) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' {y | y.1 ∈ S})) :
    Set.range (KLocallyRingedSpace.Hom.toFun (restrictOpenIncl B
        (restrictToImage_le e S S' hS') ≫ e.inv ≫
      ofRestrict A Ω)) ⊆ Set.range (KLocallyRingedSpace.Hom.toFun (ofRestrict A S)) := by
  rintro _ ⟨z, rfl⟩
  rw [range_toFun_ofRestrict]
  change (KLocallyRingedSpace.Hom.toFun e.inv (KLocallyRingedSpace.Hom.toFun
      (restrictOpenIncl B _) z)).1 ∈ (S : Set A)
  have hz : z.1 ∈ (S' : Set B) := z.2
  rw [hS'] at hz
  obtain ⟨w, ⟨y, hy, rfl⟩, hw⟩ := hz
  have h₁ : KLocallyRingedSpace.Hom.toFun (restrictOpenIncl B (restrictToImage_le e S S' hS')) z =
      KLocallyRingedSpace.Hom.toFun e.hom y := by
    apply Subtype.ext
    rw [toFun_restrictOpenIncl]
    exact hw.symm
  rw [h₁, toFun_inv_hom]
  exact hy

/-- The restriction of a `K`-isomorphism `A | Ω ≅ B | Ω'` to an open `S ≤ Ω` and its image `S'`. -/
noncomputable def restrictToImage (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (S : Opens A)
    (hS : S ≤ Ω) (S' : Opens B)
    (hS' : (S' : Set B) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' {y | y.1 ∈ S})) :
    KIso (A.restrictOpen S) (B.restrictOpen S') where
  hom := liftAlong (ofRestrict B S') (restrictOpenIncl A hS ≫ e.hom ≫ ofRestrict B Ω')
    (range_hom_subset e S hS S' hS')
  inv := liftAlong (ofRestrict A S)
    (restrictOpenIncl B (restrictToImage_le e S S' hS') ≫ e.inv ≫ ofRestrict A Ω)
    (range_inv_subset e S hS S' hS')
  hom_inv_id := by
    apply hom_ext_of_comp_eq (ofRestrict A S)
    have h₁ : liftAlong (ofRestrict B S') (restrictOpenIncl A hS ≫ e.hom ≫ ofRestrict B Ω')
        (range_hom_subset e S hS S' hS') ≫ restrictOpenIncl B (restrictToImage_le e S S' hS') =
        restrictOpenIncl A hS ≫ e.hom := by
      apply hom_ext_of_comp_eq (ofRestrict B Ω')
      rw [Category.assoc, restrictOpenIncl_comp_ofRestrict, liftAlong_comp, Category.assoc]
    rw [Category.assoc, liftAlong_comp, ← Category.assoc, h₁, Category.assoc,
      Iso.hom_inv_id_assoc, restrictOpenIncl_comp_ofRestrict, Category.id_comp]
  inv_hom_id := by
    apply hom_ext_of_comp_eq (ofRestrict B S')
    have h₁ : liftAlong (ofRestrict A S)
        (restrictOpenIncl B (restrictToImage_le e S S' hS') ≫ e.inv ≫ ofRestrict A Ω)
        (range_inv_subset e S hS S' hS') ≫ restrictOpenIncl A hS =
        restrictOpenIncl B (restrictToImage_le e S S' hS') ≫ e.inv := by
      apply hom_ext_of_comp_eq (ofRestrict A Ω)
      rw [Category.assoc, restrictOpenIncl_comp_ofRestrict, liftAlong_comp, Category.assoc]
    rw [Category.assoc, liftAlong_comp, ← Category.assoc, h₁, Category.assoc,
      Iso.inv_hom_id_assoc, restrictOpenIncl_comp_ofRestrict, Category.id_comp]

theorem restrictToImage_hom_comp (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω')) (S : Opens A)
    (hS : S ≤ Ω) (S' : Opens B)
    (hS' : (S' : Set B) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' {y | y.1 ∈ S})) :
    (restrictToImage e S hS S' hS').hom ≫ ofRestrict B S' =
      restrictOpenIncl A hS ≫ e.hom ≫ ofRestrict B Ω' :=
  liftAlong_comp _ _ _

theorem toFun_restrictToImage_hom_val (e : KIso (A.restrictOpen Ω) (B.restrictOpen Ω'))
    (S : Opens A) (hS : S ≤ Ω) (S' : Opens B)
    (hS' : (S' : Set B) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' {y | y.1 ∈ S}))
    (y : A.restrictOpen S) :
    (KLocallyRingedSpace.Hom.toFun (restrictToImage e S hS S' hS').hom y).1 =
        (KLocallyRingedSpace.Hom.toFun e.hom ⟨y.1, hS y.2⟩).1 := by
  have h := congrFun (congrArg KLocallyRingedSpace.Hom.toFun (restrictToImage_hom_comp e S hS S'
      hS')) y
  change (KLocallyRingedSpace.Hom.toFun (restrictToImage e S hS S' hS').hom y).1 =
    (KLocallyRingedSpace.Hom.toFun e.hom (KLocallyRingedSpace.Hom.toFun
        (restrictOpenIncl A hS) y)).1 at h
  rw [h, toFun_restrictOpenIncl]

end KIso

/-! ### The graph of a transition datum -/

variable {X : AnalyticSpace.{u} ℝ} {Ui Uj : Opens X} {Ci : Complexification (X.restrictOpen Ui)}
  {Cj : Complexification (X.restrictOpen Uj)} {V : Opens X} {hVi : V ≤ Ui} {hVj : V ≤ Uj}

namespace PairIso

/-- The transition as a map on its domain, valued in `Y_j`. -/
noncomputable def toMap (P : PairIso Ci Cj V hVi hVj) : Set.Elem (P.Ωi : Set Ci.Y) → Cj.Y :=
  fun y => (KLocallyRingedSpace.Hom.toFun P.e.hom y).1

theorem continuous_toMap (P : PairIso Ci Cj V hVi hVj) : Continuous P.toMap :=
  continuous_subtype_val.comp P.e.hom.1.base.hom.continuous

/-- The inverse transition as a map on its domain, valued in `Y_i`. -/
noncomputable def invMap (P : PairIso Ci Cj V hVi hVj) : Set.Elem (P.Ωj : Set Cj.Y) → Ci.Y :=
  fun z => (KLocallyRingedSpace.Hom.toFun P.e.inv z).1

theorem continuous_invMap (P : PairIso Ci Cj V hVi hVj) : Continuous P.invMap :=
  continuous_subtype_val.comp P.e.inv.1.base.hom.continuous

/-- The graph of the transition. -/
def graph (P : PairIso Ci Cj V hVi hVj) : Set (Ci.Y × Cj.Y) := graphOn P.toMap P.Ωi

/-- The real graph `{(f_i x, f_j x) : x ∈ V}`. -/
def realGraph (_P : PairIso Ci Cj V hVi hVj) : Set (Ci.Y × Cj.Y) :=
  {p | ∃ v : X.restrictOpen V, p = (KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩,
      KLocallyRingedSpace.Hom.toFun Cj.f ⟨v.1, hVj v.2⟩)}

/-- The pairs of real points outside both domains, `f_i(U_i ∖ V) × f_j(U_j ∖ V)`. -/
def outer (_P : PairIso Ci Cj V hVi hVj) : Set (Ci.Y × Cj.Y) := Ci.imageDiff V ×ˢ Cj.imageDiff V

/-- A datum is tame when the closure of its graph avoids `outer`. -/
def Tame (P : PairIso Ci Cj V hVi hVj) : Prop := Disjoint (closure P.graph) P.outer

theorem isClosed_outer (P : PairIso Ci Cj V hVi hVj) : IsClosed P.outer :=
  (Ci.isClosed_imageDiff V).prod (Cj.isClosed_imageDiff V)

theorem realGraph_subset_graph (P : PairIso Ci Cj V hVi hVj) : P.realGraph ⊆ P.graph := by
  rintro _ ⟨v, rfl⟩
  exact ⟨⟨_, P.mem_Ωi v⟩, P.mem_Ωi v, Prod.ext rfl (P.toFun_e_hom_val v).symm⟩

theorem disjoint_realGraph_outer (P : PairIso Ci Cj V hVi hVj) : Disjoint P.realGraph P.outer := by
  rw [Set.disjoint_left]
  rintro _ ⟨v, rfl⟩ ⟨h₁, -⟩
  obtain ⟨u, hu, heq⟩ := Ci.mem_imageDiff.mp h₁
  have := Ci.injective_toFun heq
  exact hu (by rw [this]; exact v.2)

/-- For `V = U_i ⊓ U_j` the real graph is closed: it is the image of the diagonal of `U_i × U_j`
under the closed embedding `f_i × f_j`. -/
theorem isClosed_realGraph (P : PairIso Ci Cj V hVi hVj) (hV : Ui ⊓ Uj ≤ V) :
    IsClosed P.realGraph := by
  have h := isClosed_image_prodMap_of_eq (Y := Ci.Y) (Y' := Cj.Y) Ci.isClosedEmbedding
    Cj.isClosedEmbedding (a := fun u : X.restrictOpen Ui => u.1)
    (b := fun w : X.restrictOpen Uj => w.1) continuous_subtype_val continuous_subtype_val
  convert h using 1
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨v.1, hVi v.2⟩, ⟨v.1, hVj v.2⟩, rfl, rfl⟩
  · rintro ⟨u, w, huw, rfl⟩
    refine ⟨⟨u.1, hV ⟨u.2, huw ▸ w.2⟩⟩, ?_⟩
    have hw : w = ⟨u.1, huw ▸ w.2⟩ := Subtype.ext huw.symm
    exact Prod.ext rfl (congrArg (KLocallyRingedSpace.Hom.toFun Cj.f) hw)

/-- A real point of `Y_i` outside the domain lies over `U_i ∖ V`. -/
theorem mem_imageDiff_of_notMem (P : PairIso Ci Cj V hVi hVj) {y : Ci.Y}
    (hy : y ∈ Set.range (KLocallyRingedSpace.Hom.toFun Ci.f))
        (hΩ : y ∉ P.Ωi) : y ∈ Ci.imageDiff V := by
  obtain ⟨u, rfl⟩ := hy
  refine Ci.mem_imageDiff.mpr ⟨u, fun huV => hΩ ?_, rfl⟩
  exact P.mem_Ωi ⟨u.1, huV⟩

theorem mem_imageDiff_of_notMem' (P : PairIso Ci Cj V hVi hVj) {z : Cj.Y}
    (hz : z ∈ Set.range (KLocallyRingedSpace.Hom.toFun Cj.f))
        (hΩ : z ∉ P.Ωj) : z ∈ Cj.imageDiff V := by
  obtain ⟨u, rfl⟩ := hz
  refine Cj.mem_imageDiff.mpr ⟨u, fun huV => hΩ ?_, rfl⟩
  exact P.mem_Ωj ⟨u.1, huV⟩

/-- The graph meets the real points only in the real graph. -/
theorem graph_inter_real_eq (P : PairIso Ci Cj V hVi hVj) :
    P.graph ∩ Set.range (KLocallyRingedSpace.Hom.toFun Ci.f) ×ˢ Set.range
        (KLocallyRingedSpace.Hom.toFun Cj.f) = P.realGraph := by
  ext p
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, ⟨u, hu⟩, ⟨w, hw⟩⟩
    obtain ⟨v, hv⟩ := P.exists_eq_of_toFun_e_hom_eq y w hw.symm
    refine ⟨v, ?_⟩
    have hy' : y = ⟨KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, hVi v.2⟩, P.mem_Ωi v⟩ := Subtype.ext hv
    rw [hy']
    exact Prod.ext rfl (P.toFun_e_hom_val v)
  · intro hp
    exact ⟨P.realGraph_subset_graph hp, by
      obtain ⟨v, rfl⟩ := hp
      exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩⟩

/-- For a tame datum the closure of the graph meets the real points only in the graph. -/
theorem closure_graph_inter_real_subset (P : PairIso Ci Cj V hVi hVj) (hP : P.Tame) :
    closure P.graph ∩ Set.range (KLocallyRingedSpace.Hom.toFun Ci.f) ×ˢ Set.range
        (KLocallyRingedSpace.Hom.toFun Cj.f) ⊆ P.graph := by
  have hφΩ : ∀ y : Set.Elem (P.Ωi : Set Ci.Y), P.toMap y ∈ (P.Ωj : Set Cj.Y) := fun y =>
    (KLocallyRingedSpace.Hom.toFun P.e.hom y).2
  have hψΩ : ∀ z : Set.Elem (P.Ωj : Set Cj.Y), P.invMap z ∈ (P.Ωi : Set Ci.Y) := fun z =>
    (KLocallyRingedSpace.Hom.toFun P.e.inv z).2
  have hψφ : ∀ y : Set.Elem (P.Ωi : Set Ci.Y), P.invMap ⟨P.toMap y, hφΩ y⟩ = y := fun y =>
    congrArg Subtype.val (KIso.toFun_inv_hom P.e y)
  have hφψ : ∀ z : Set.Elem (P.Ωj : Set Cj.Y), P.toMap ⟨P.invMap z, hψΩ z⟩ = z := fun z =>
    congrArg Subtype.val (KIso.toFun_hom_inv P.e z)
  have hE : Disjoint (closure (graphOn P.toMap P.Ωi))
      ((Set.range (KLocallyRingedSpace.Hom.toFun Ci.f) \ P.Ωi) ×ˢ (Set.range
          (KLocallyRingedSpace.Hom.toFun Cj.f) \ P.Ωj)) := by
    refine hP.mono_right ?_
    rintro ⟨y, z⟩ ⟨⟨hy, hyΩ⟩, ⟨hz, hzΩ⟩⟩
    exact ⟨P.mem_imageDiff_of_notMem hy hyΩ, P.mem_imageDiff_of_notMem' hz hzΩ⟩
  exact closure_graphOn_inter_prod_subset P.Ωi.2 P.continuous_toMap P.Ωj.2 P.continuous_invMap
    hφΩ hψφ hψΩ hφψ hE

end PairIso

/-! ### For every datum over `U_i ⊓ U_j` there is a tame datum -/

theorem PairIso.exists_tame (P : PairIso Ci Cj (Ui ⊓ Uj) inf_le_left inf_le_right) :
    ∃ P' : PairIso Ci Cj (Ui ⊓ Uj) inf_le_left inf_le_right, P'.Tame := by
  obtain ⟨S, hS, hSΩ, hGS, hdisj⟩ := exists_isOpen_graphOn_closure_disjoint (Y := Ci.Y)
    (Y' := Cj.Y) P.Ωi.2 P.continuous_toMap P.realGraph_subset_graph P.isClosed_outer
    (by rw [(P.isClosed_realGraph le_rfl).closure_eq]; exact P.disjoint_realGraph_outer)
  let SΩ : Opens Ci.Y := ⟨S, hS⟩
  have hle : SΩ ≤ P.Ωi := hSΩ
  let S' : Opens Cj.Y := ⟨Subtype.val '' (KLocallyRingedSpace.Hom.toFun P.e.hom '' {y | y.1 ∈ SΩ}),
      by
    apply P.Ωj.2.isOpenMap_subtype_val
    exact (KIso.homeomorph P.e).isOpenMap _ (hS.preimage continuous_subtype_val)⟩
  have hS' : (S' : Set Cj.Y) = Subtype.val '' (KLocallyRingedSpace.Hom.toFun P.e.hom ''
      {y | y.1 ∈ SΩ}) := rfl
  have memi : ∀ v : X.restrictOpen (Ui ⊓ Uj),
      KLocallyRingedSpace.Hom.toFun Ci.f ⟨v.1, (inf_le_left : Ui ⊓ Uj ≤ Ui) v.2⟩ ∈ SΩ :=
    fun v => hGS ⟨_, ⟨v, rfl⟩, rfl⟩
  have memj : ∀ v : X.restrictOpen (Ui ⊓ Uj),
      KLocallyRingedSpace.Hom.toFun Cj.f ⟨v.1, (inf_le_right : Ui ⊓ Uj ≤ Uj) v.2⟩ ∈ S' := by
    intro v
    refine ⟨KLocallyRingedSpace.Hom.toFun P.e.hom ⟨_, P.mem_Ωi v⟩, ⟨⟨_, P.mem_Ωi v⟩, memi v, rfl⟩,
        ?_⟩
    exact P.toFun_e_hom_val v
  have hcompat : pairLift Ci inf_le_left SΩ memi ≫
      (KIso.restrictToImage P.e SΩ hle S' hS').hom ≫ ofRestrict Cj.Y.toKLocallyRingedSpace S' =
      complexifyHom (restrictOpenIncl X.toKLocallyRingedSpace inf_le_right) ≫ Cj.f := by
    have h₁ : pairLift Ci inf_le_left SΩ memi ≫ restrictOpenIncl Ci.Y.toKLocallyRingedSpace hle =
        pairLift Ci inf_le_left P.Ωi P.mem_Ωi := by
      apply hom_ext_of_comp_eq (ofRestrict Ci.Y.toKLocallyRingedSpace P.Ωi)
      rw [Category.assoc, restrictOpenIncl_comp_ofRestrict, pairLift_comp, pairLift_comp]
    rw [KIso.restrictToImage_hom_comp, ← Category.assoc, h₁]
    exact P.compat
  refine ⟨⟨SΩ, S', KIso.restrictToImage P.e SΩ hle S' hS', memi, memj,
    fun y hy => P.Ωi_le (hle hy),
    fun z hz => P.Ωj_le (KIso.restrictToImage_le P.e SΩ S' hS' hz), hcompat⟩, ?_⟩
  have hgraph : graphOn (fun y : Set.Elem (SΩ : Set Ci.Y) =>
      (KLocallyRingedSpace.Hom.toFun (KIso.restrictToImage P.e SΩ hle S' hS').hom y).1) SΩ =
          graphOn P.toMap S := by
    ext p
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, hle y.2⟩, hy, Prod.ext rfl
        (KIso.toFun_restrictToImage_hom_val P.e SΩ hle S' hS' y)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.1, hy⟩, hy, Prod.ext rfl
        (KIso.toFun_restrictToImage_hom_val P.e SΩ hle S' hS' ⟨y.1, hy⟩).symm⟩
  change Disjoint (closure (graphOn (fun y : Set.Elem (SΩ : Set Ci.Y) =>
    (KLocallyRingedSpace.Hom.toFun (KIso.restrictToImage P.e SΩ hle S' hS').hom y).1) SΩ))
    (Ci.imageDiff (Ui ⊓ Uj) ×ˢ Cj.imageDiff (Ui ⊓ Uj))
  rw [hgraph]
  exact hdisj

end AnalyticSpace.Glue
