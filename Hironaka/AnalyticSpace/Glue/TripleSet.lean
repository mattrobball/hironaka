/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Cocycle
public import Hironaka.AnalyticSpace.Glue.Setup
import Hironaka.AnalyticSpace.Glue.Shrink
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The constraint sets and the shrinking of the pieces

For the local data `D` (`Hironaka.AnalyticSpace.Glue.Setup`) and the uniqueness hypothesis `huniq`
(`Huniq`, defined here as a predicate) of the gluing theorem for complexifications [BW59,
Proposition 1]: the cocycle neighbourhoods `N_ijk ⊆ Y_i` (chosen from `exists_cocycle_nhd`,
`Hironaka.AnalyticSpace.Glue.Cocycle`), made empty when the triple overlap `U_i ∩ U_j ∩ U_k` is
empty (`nhd'`); the closed *pair boundaries* `closure Γ_ij ∖ Γ_ij` and the closures of the *triple
sets* `{(y, φ_ij y, φ_ik y) : y ∈ Ω_ij ∩ Ω_ik, y ∉ N'_ijk}` (`tripleSet`), both disjoint from the
products of real points (by tameness a real limit of the graph lies on the real graph, so its
`Y_i`-coordinate
is `f_i a` with `a ∈ U_i ∩ U_j ∩ U_k`, whence `f_i a ∈ N'_ijk`, an open set the approximants avoid);
the compact cores `K_i = f_i(closure V_i)`; the finite sets of indices relevant to `i` (`rel`, from
local finiteness and the compact closure of `U_i`); and the shrunk pieces `A_i ⊇ K_i` (`Shrunk`,
from `exists_shrink`, `Hironaka.AnalyticSpace.Glue.Shrink`) with `A_i × A_j` avoiding the pair
boundary and `A_i × A_j × A_k` avoiding the triple set for the relevant pairs and triples.

Conventions. Pairs and triples are constrained only when the other indices are relevant to the first
(`j ∈ rel' i`, `k ∈ rel' i`, where `rel' i` also contains `i`, so that the triples with repeated
indices are constrained); the gluing sets of the non-relevant pairs are empty by definition. The
triple set with `N' = ⊥` forces `W_ij ∩ W_ik = ∅` when `U_i ∩ U_j ∩ U_k = ∅`. For a finite index
type every index set is finite anyway; for `U_i ∩ U_j = ∅` the pair is not constrained.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue

universe u

variable {X : AnalyticSpace.{u} ℝ} (D : LocalData X)

/-- The uniqueness hypothesis of the gluing theorem for complexifications, as a predicate: two
morphisms out of a neighbourhood of the real points of one complexification into another, both
compatible with the structure maps `C.f`, `C'.f`, agree on a smaller neighbourhood of the real
points. -/
def Huniq (X : AnalyticSpace.{u} ℝ) : Prop :=
  ∀ (V : Opens X) (C C' : Complexification (X.restrictOpen V)) (W : Opens C.Y)
    (hW : ∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W)
    (g₁ g₂ : C.Y.toKLocallyRingedSpace.restrictOpen W ⟶ C'.Y.toKLocallyRingedSpace),
    Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ g₁ = ofRestrict _ ⊤ ≫ C'.f →
    Hom.restrictTo C.f ⊤ W (fun x _ => hW x) ≫ g₂ = ofRestrict _ ⊤ ≫ C'.f →
    ∃ (W₀ : Opens C.Y) (hle : W₀ ≤ W), (∀ x, KLocallyRingedSpace.Hom.toFun C.f x ∈ W₀) ∧
      restrictOpenIncl C.Y.toKLocallyRingedSpace hle ≫ g₁ =
        restrictOpenIncl C.Y.toKLocallyRingedSpace hle ≫ g₂

variable (huniq : Huniq X)

namespace LocalData

/-! ### The cocycle neighbourhoods -/

/-- The cocycle neighbourhood `N_ijk ⊆ Y_i` (chosen). -/
noncomputable def cocycleNhd (i j k : D.J) : Opens (D.C i).Y :=
  (exists_cocycle_nhd (D.P i j) (D.P j k) (D.P i k) huniq).choose

theorem cocycleNhd_le (i j k : D.J) :
    D.cocycleNhd huniq i j k ≤ tripleDomain (D.P i j) (D.P j k) (D.P i k) :=
  (exists_cocycle_nhd (D.P i j) (D.P j k) (D.P i k) huniq).choose_spec.fst

theorem mem_cocycleNhd (i j k : D.J) (v : X.restrictOpen (D.U i ⊓ D.U j ⊓ D.U k)) :
    KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨v.1, tripleV_le_Ui v.2⟩ ∈ D.cocycleNhd huniq i j k :=
  (exists_cocycle_nhd (D.P i j) (D.P j k) (D.P i k) huniq).choose_spec.snd.1 v

theorem cocycleNhd_eq (i j k : D.J) :
    restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i j k) ≫
      compTrans (D.P i j) (D.P j k) (D.P i k) =
    restrictOpenIncl (D.C i).Y.toKLocallyRingedSpace (D.cocycleNhd_le huniq i j k) ≫
      directTrans (D.P i j) (D.P j k) (D.P i k) :=
  (exists_cocycle_nhd (D.P i j) (D.P j k) (D.P i k) huniq).choose_spec.snd.2

/-- The trimmed cocycle neighbourhood: the cocycle neighbourhood when the triple overlap is
nonempty, empty otherwise. -/
noncomputable def nhd' (i j k : D.J) : Opens (D.C i).Y := by
  classical
  exact if ((D.U i ⊓ D.U j ⊓ D.U k : Opens X) : Set X).Nonempty then D.cocycleNhd huniq i j k else ⊥

theorem nhd'_le_cocycleNhd (i j k : D.J) : D.nhd' huniq i j k ≤ D.cocycleNhd huniq i j k := by
  unfold nhd'
  split_ifs
  · exact le_rfl
  · exact bot_le

theorem mem_nhd' (i j k : D.J) (v : X.restrictOpen (D.U i ⊓ D.U j ⊓ D.U k)) :
    KLocallyRingedSpace.Hom.toFun (D.C i).f ⟨v.1, tripleV_le_Ui v.2⟩ ∈ D.nhd' huniq i j k := by
  unfold nhd'
  split_ifs with h
  · exact D.mem_cocycleNhd huniq i j k v
  · exact absurd ⟨v.1, v.2⟩ h

/-! ### The closed constraint sets -/

/-- The boundary of the graph of the transition `φ_ij`. -/
def pairBoundary (i j : D.J) : Set ((D.C i).Y × (D.C j).Y) :=
  closure (D.P i j).graph \ (D.P i j).graph

theorem isClosed_pairBoundary (i j : D.J) : IsClosed (D.pairBoundary i j) :=
  isClosed_closure_diff_graphOn (D.P i j).continuous_toMap (D.P i j).Ωi.2 le_rfl

theorem disjoint_pairBoundary_real (i j : D.J) :
    Disjoint (D.pairBoundary i j)
      (Set.range (KLocallyRingedSpace.Hom.toFun (D.C i).f) ×ˢ Set.range
          (KLocallyRingedSpace.Hom.toFun (D.C j).f)) := by
  rw [Set.disjoint_left]
  rintro p ⟨hp, hpG⟩ hpR
  exact hpG ((D.P i j).closure_graph_inter_real_subset (D.tame i j) ⟨hp, hpR⟩)

/-- The triple set: the points of `Ω_ij ∩ Ω_ik` off the trimmed cocycle neighbourhood, with their
two images. -/
def tripleSet (i j k : D.J) : Set ((D.C i).Y × (D.C j).Y × (D.C k).Y) :=
  {p | ∃ (y : (D.C i).Y) (h₁ : y ∈ (D.P i j).Ωi) (h₂ : y ∈ (D.P i k).Ωi),
    y ∉ D.nhd' huniq i j k ∧
    p = (y, (KLocallyRingedSpace.Hom.toFun (D.P i j).e.hom ⟨y, h₁⟩).1,
        (KLocallyRingedSpace.Hom.toFun (D.P i k).e.hom ⟨y, h₂⟩).1)}

/-- A real limit of a tame graph has its first coordinate over the overlap: the `Y_i`-coordinate of
a point of `closure Γ_ij ∩ (R_i × R_j)` is `f_i a` with `a ∈ U_i ∩ U_j`. -/
theorem exists_mem_of_mem_closure_graph_real (i j : D.J) {a : X.restrictOpen (D.U i)}
    {b : X.restrictOpen (D.U j)}
    (h : (KLocallyRingedSpace.Hom.toFun (D.C i).f a, KLocallyRingedSpace.Hom.toFun
        (D.C j).f b) ∈ closure (D.P i j).graph) :
    a.1 ∈ D.U i ⊓ D.U j := by
  have hmem : (KLocallyRingedSpace.Hom.toFun (D.C i).f a, KLocallyRingedSpace.Hom.toFun
      (D.C j).f b) ∈ (D.P i j).realGraph := by
    rw [← (D.P i j).graph_inter_real_eq]
    exact ⟨(D.P i j).closure_graph_inter_real_subset (D.tame i j) ⟨h, ⟨a, rfl⟩, ⟨b, rfl⟩⟩,
      ⟨a, rfl⟩, ⟨b, rfl⟩⟩
  obtain ⟨v, hv⟩ := hmem
  have ha : a = ⟨v.1, (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) v.2⟩ :=
    (D.C i).injective_toFun (congrArg Prod.fst hv)
  rw [ha]
  exact v.2

theorem disjoint_closure_tripleSet_real (i j k : D.J) :
    Disjoint (closure (D.tripleSet huniq i j k))
      (Set.range (KLocallyRingedSpace.Hom.toFun (D.C i).f) ×ˢ
        (Set.range (KLocallyRingedSpace.Hom.toFun (D.C j).f) ×ˢ Set.range
            (KLocallyRingedSpace.Hom.toFun (D.C k).f))) := by
  rw [Set.disjoint_left]
  rintro p hp ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
  -- the two projections of the triple set lie on the graphs of `φ_ij`, `φ_ik`
  have hsub₁ : (fun q : (D.C i).Y × (D.C j).Y × (D.C k).Y => (q.1, q.2.1)) ''
      D.tripleSet huniq i j k ⊆ (D.P i j).graph := by
    rintro _ ⟨q, ⟨y, h₁, h₂, -, rfl⟩, rfl⟩
    exact ⟨⟨y, h₁⟩, h₁, rfl⟩
  have hsub₂ : (fun q : (D.C i).Y × (D.C j).Y × (D.C k).Y => (q.1, q.2.2)) ''
      D.tripleSet huniq i j k ⊆ (D.P i k).graph := by
    rintro _ ⟨q, ⟨y, h₁, h₂, -, rfl⟩, rfl⟩
    exact ⟨⟨y, h₂⟩, h₂, rfl⟩
  have hc₁ : (p.1, p.2.1) ∈ closure (D.P i j).graph :=
    closure_mono hsub₁ (image_closure_subset_closure_image
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)) ⟨p, hp, rfl⟩)
  have hc₂ : (p.1, p.2.2) ∈ closure (D.P i k).graph :=
    closure_mono hsub₂ (image_closure_subset_closure_image
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)) ⟨p, hp, rfl⟩)
  rw [← ha, ← hb] at hc₁
  rw [← ha, ← hc] at hc₂
  have haij := D.exists_mem_of_mem_closure_graph_real i j hc₁
  have haik := D.exists_mem_of_mem_closure_graph_real i k hc₂
  -- so `a` lies over the triple overlap and `f_i a ∈ N'`
  have hN : p.1 ∈ D.nhd' huniq i j k := by
    rw [← ha]
    exact D.mem_nhd' huniq i j k ⟨a.1, ⟨haij, haik.2⟩⟩
  -- the open `N' × univ × univ` contains `p` and meets the triple set, whose points avoid `N'`
  have hne : (((D.nhd' huniq i j k : Set (D.C i).Y) ×ˢ (Set.univ ×ˢ Set.univ)) ∩
      D.tripleSet huniq i j k).Nonempty :=
    mem_closure_iff.mp hp _ ((D.nhd' huniq i j k).2.prod (isOpen_univ.prod isOpen_univ))
      ⟨hN, trivial, trivial⟩
  obtain ⟨q, hqo, hqT⟩ := hne
  obtain ⟨y, h₁, h₂, hyN, hq⟩ := hqT
  rw [hq] at hqo
  exact hyN hqo.1

/-! ### The compact cores and the relevant indices -/

/-- The compact core `f_i(closure V_i)` of the piece `Y_i`. -/
def core (i : D.J) : Set (D.C i).Y :=
  KLocallyRingedSpace.Hom.toFun (D.C i).f '' {u : X.restrictOpen (D.U i) | u.1 ∈ closure
      (D.V i : Set X)}

theorem isCompact_core (i : D.J) : IsCompact (D.core i) := by
  apply IsCompact.image _ (D.C i).f.1.base.hom.continuous
  have hind : Topology.IsInducing (Subtype.val : X.restrictOpen (D.U i) → X) :=
    Topology.IsInducing.subtypeVal
  have himg : Subtype.val '' {u : X.restrictOpen (D.U i) | u.1 ∈ closure (D.V i : Set X)} =
      closure (D.V i : Set X) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x, D.closure_V_subset i hx⟩, hx, rfl⟩
  have hK : IsCompact
      (Subtype.val '' {u : X.restrictOpen (D.U i) | u.1 ∈ closure (D.V i : Set X)}) := by
    rw [himg]
    exact (D.cpt i).of_isClosed_subset isClosed_closure
      ((D.closure_V_subset i).trans subset_closure)
  exact hind.isCompact_iff.mpr hK

theorem core_subset_range (i : D.J) : D.core i ⊆ Set.range (KLocallyRingedSpace.Hom.toFun
    (D.C i).f) := by
  rintro _ ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

/-- The indices relevant to `i`: those whose open meets `U_i`. -/
def rel (i : D.J) : Set D.J := {j | ((D.U i : Set X) ∩ D.U j).Nonempty}

theorem finite_rel (i : D.J) : (D.rel i).Finite := by
  refine (D.lf.finite_nonempty_inter_compact (D.cpt i)).subset fun j hj => ?_
  obtain ⟨x, hxi, hxj⟩ := hj
  exact ⟨x, hxj, subset_closure hxi⟩

theorem rel_comm {i j : D.J} (h : j ∈ D.rel i) : i ∈ D.rel j := by
  obtain ⟨x, hxi, hxj⟩ := h
  exact ⟨x, hxj, hxi⟩

/-- The indices relevant to `i` together with `i` itself. -/
def rel' (i : D.J) : Set D.J := insert i (D.rel i)

theorem finite_rel' (i : D.J) : (D.rel' i).Finite := (D.finite_rel i).insert i

theorem self_mem_rel' (i : D.J) : i ∈ D.rel' i := Set.mem_insert i _

theorem mem_rel'_of_mem_rel {i j : D.J} (h : j ∈ D.rel i) : j ∈ D.rel' i :=
  Set.mem_insert_of_mem i h

theorem rel'_comm {i j : D.J} (h : j ∈ D.rel' i) : i ∈ D.rel' j := by
  rcases h with rfl | h
  · exact D.self_mem_rel' j
  · exact Set.mem_insert_of_mem j (D.rel_comm h)

/-! ### The shrunk pieces -/

end LocalData

/-- The shrunk pieces `A_i ⊇ K_i` avoiding the pair boundaries and the closures of the triple sets
of the relevant pairs and triples. -/
structure Shrunk (D : LocalData X) (huniq : Huniq X) where
  /-- The shrunk piece. -/
  A : ∀ i, Opens (D.C i).Y
  core_subset : ∀ i, D.core i ⊆ A i
  /-- The pair constraint: `A_i × A_j` avoids the boundary of the transition graph, so the graph is
  closed in `A_i × A_j`; a limit pair `(f_i x, z)` with `f_i x ∈ A_i`, `z ∈ A_j` lies on the graph,
  so `f_i x ∈ Ω_ij`, `x` lies over `U_i ∩ U_j` and `z = f_j x`. -/
  pair : ∀ i j, j ∈ D.rel' i →
    Disjoint ((A i : Set (D.C i).Y) ×ˢ (A j : Set (D.C j).Y)) (D.pairBoundary i j)
  triple : ∀ i j k, j ∈ D.rel' i → k ∈ D.rel' i →
    Disjoint ((A i : Set (D.C i).Y) ×ˢ ((A j : Set (D.C j).Y) ×ˢ (A k : Set (D.C k).Y)))
      (closure (D.tripleSet huniq i j k))

theorem exists_shrunk : Nonempty (Shrunk D huniq) := by
  classical
  obtain ⟨A, hAo, hKA, hpair, htriple⟩ := exists_shrink (ι := D.J) (Y := fun i => (D.C i).Y)
    D.core D.isCompact_core {p | p.2 ∈ D.rel' p.1} (fun p => D.pairBoundary p.1 p.2)
    (fun p _ => D.isClosed_pairBoundary p.1 p.2)
    (fun p _ => (D.disjoint_pairBoundary_real p.1 p.2).symm.mono_left
      (Set.prod_mono (D.core_subset_range p.1) (D.core_subset_range p.2)))
    (fun i => by
      refine ((((D.finite_rel' i).image fun j => (i, j)).union
        ((D.finite_rel' i).image fun j => (j, i))).subset ?_)
      rintro ⟨a, b⟩ ⟨hab, rfl | rfl⟩
      · exact Or.inl ⟨b, hab, rfl⟩
      · exact Or.inr ⟨a, D.rel'_comm hab, rfl⟩)
    {t | t.2.1 ∈ D.rel' t.1 ∧ t.2.2 ∈ D.rel' t.1}
    (fun t => closure (D.tripleSet huniq t.1 t.2.1 t.2.2)) (fun _ _ => isClosed_closure)
    (fun t _ => (D.disjoint_closure_tripleSet_real huniq t.1 t.2.1 t.2.2).symm.mono_left
      (Set.prod_mono (D.core_subset_range t.1)
        (Set.prod_mono (D.core_subset_range t.2.1) (D.core_subset_range t.2.2))))
    (fun i => by
      refine ((((D.finite_rel' i).prod (D.finite_rel' i)).image fun q => (i, q.1, q.2)).union
        (((D.finite_rel' i).biUnion fun a _ => (D.finite_rel' a).image fun c => (a, i, c)).union
          ((D.finite_rel' i).biUnion fun a _ =>
            (D.finite_rel' a).image fun b => (a, b, i)))).subset ?_
      rintro ⟨a, b, c⟩ ⟨⟨hab, hac⟩, rfl | rfl | rfl⟩
      · exact Or.inl ⟨(b, c), ⟨hab, hac⟩, rfl⟩
      · exact Or.inr (Or.inl (Set.mem_biUnion (D.rel'_comm hab) ⟨c, hac, rfl⟩))
      · exact Or.inr (Or.inr (Set.mem_biUnion (D.rel'_comm hac) ⟨b, hab, rfl⟩)))
  exact ⟨⟨fun i => ⟨A i, hAo i⟩, hKA, fun i j hj => hpair (i, j) hj,
    fun i j k hj hk => htriple (i, j, k) ⟨hj, hk⟩⟩⟩

end AnalyticSpace.Glue
