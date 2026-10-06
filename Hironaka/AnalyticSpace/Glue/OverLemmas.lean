/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
import Hironaka.AnalyticSpace.Glue.Cocycle
import Hironaka.AnalyticSpace.HomOfSections
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Gluing over a base from transitions: uniqueness gives the cocycle, continuity gives Hausdorffness

In Włodarczyk's gluing of local desingularizations [Wlo09, §4] the embeddings `(V_i ∩ V_j)~ → Ṽ_i`
are the unique lifts of the identity of the overlap (the desingularization of a germ is independent
of the choice of ambient manifold), so they satisfy the cocycle identity automatically; and "let `Ṽ`
be a manifold obtained by gluing `Ṽ_i` along `Ṽ_i ∩ Ṽ_j`" takes the Hausdorffness of `Ṽ` for
granted. Both are proved here once, for every gluing over a base whose transitions lie over the
base:

* `KLocallyRingedSpace.toFun_restrictOpenIncl_val`: the inclusion of open subspaces on points;
* `Glue.KGlueCore.isIso_tRes_of_comp_eq_id`: when the transitions of a gluing core are mutually
  inverse, their restrictions to the meets (`tRes`) are isomorphisms;
* `GlueOver.isClosed_transitionGraph_overData`, `t2Space_overData_of_compat`: the transition graphs
  are closed, the glued space is Hausdorff;
* `GlueOver.exists_glueOver_of_transitions`: a `GlueOver` from transitions that are isomorphisms
  over `X`, unique among such on the points over an open subset of the base;
* `GlueOver.toFun_π_t_eq`, `t_inter_of_compat`: the point-level content of `compat`, a transition
  preserves the fibre over `X`, hence maps the points over `dom k` to points over `dom k`;
* `GlueOver.t_comp_t_eq_id_of_uniq`, `t_id_of_uniq`: transitions that are isomorphisms over `X`,
  unique among such on the preimage open subsets, are mutually inverse and the identity on the
  diagonal.

`exists_glueOver_of_transitions` is how the gluing datum of the local resolutions is built
(`Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum`, `PieceGlueIndep`). Not in the sources as
separate statements.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace

universe u

variable {K : Type} [RCLike K]

namespace KLocallyRingedSpace

/-- The inclusion of open subspaces is the identity on points. -/
theorem toFun_restrictOpenIncl_val (A : KLocallyRingedSpace.{u} K) {U U' : Opens A} (h : U ≤ U')
    (x : A.restrictOpen U) : (Hom.toFun (restrictOpenIncl A h) x).1 = x.1 :=
  (Hom.toFun_restrictTo (𝟙 A) U U' _ x).trans (congrFun (Hom.toFun_id A) x.1)

end KLocallyRingedSpace

namespace Glue.KGlueCore

variable (D : KGlueCore.{u} K)

/-- When the transitions are mutually inverse, their restrictions to the meets are isomorphisms:
the inverse of `tRes i j k` is `tRes j i k` between the commuted meets. -/
theorem isIso_tRes_of_comp_eq_id (hinv : ∀ i j, D.t i j ≫ D.t j i = 𝟙 _) (i j k : D.J) :
    IsIso (D.tRes i j k) := by
  refine ⟨⟨restrictOpenIncl (D.Y j) (inf_comm _ _).le ≫ D.tRes j i k ≫
    restrictOpenIncl (D.Y i) (inf_comm _ _).le, ?_, ?_⟩⟩
  · apply Hom.ext_of_comp_ofRestrict
    rw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc,
      restrictOpenIncl_comp_ofRestrict, tRes_comp_ofRestrict,
      ← Category.assoc (restrictOpenIncl (D.Y j) _), restrictOpenIncl_trans,
      ← Category.assoc, tRes_comp_restrictOpenIncl, Category.assoc, ← Category.assoc (D.t i j),
      hinv, Category.id_comp, restrictOpenIncl_comp_ofRestrict]
  · apply Hom.ext_of_comp_ofRestrict
    rw [Category.id_comp, Category.assoc, Category.assoc, Category.assoc,
      tRes_comp_ofRestrict, ← Category.assoc (restrictOpenIncl (D.Y i) _),
      restrictOpenIncl_trans, ← Category.assoc (D.tRes j i k),
      tRes_comp_restrictOpenIncl, Category.assoc, ← Category.assoc (D.t j i),
      hinv, Category.id_comp, ← Category.assoc, restrictOpenIncl_trans,
      restrictOpenIncl_comp_ofRestrict]

end Glue.KGlueCore

namespace GlueOver

variable {X : AnalyticSpace.{u} K} {ι : Type u} {R : ι → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ι → Opens X}

/-- `compat` at the point level: a transition preserves the fibre over `X`. -/
theorem toFun_π_t_eq
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (compat : ∀ i j,
      ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j) ≫ π i =
        (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)) ≫ π j)
    (i j : ι) (x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j)) :
    KLocallyRingedSpace.Hom.toFun (π j) (KLocallyRingedSpace.Hom.toFun
        (t i j) x).1 = KLocallyRingedSpace.Hom.toFun (π i) x.1 := by
  have h := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ x) (compat i j)
  simp only [Hom.toFun_comp, Function.comp] at h
  exact h.symm

/-- The `t_inter` field from `compat`: the transition maps the points over `dom k` to points over
`dom k`. -/
theorem t_inter_of_compat (hrange : ∀ i, range (KLocallyRingedSpace.Hom.toFun (π i)) ⊆ dom i)
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (compat : ∀ i j,
      ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j) ≫ π i =
        (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)) ≫ π j)
    (i j k : ι) (x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j))
    (hx : x.1 ∈ glueOpens X R π dom i k) :
    (KLocallyRingedSpace.Hom.toFun (t i j) x).1 ∈ glueOpens X R π dom j k := by
  rw [mem_glueOpens] at hx ⊢
  rw [toFun_π_t_eq t compat i j x]
  exact ⟨by rw [← toFun_π_t_eq t compat i j x]; exact hrange j ⟨_, rfl⟩, hx.2⟩

/-- Transitions that are isomorphisms over `X`, unique among such on the points over an open of
the base, are mutually inverse. -/
theorem t_comp_t_eq_id_of_uniq
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (hiso : ∀ i j, IsIso (t i j))
    (compat : ∀ i j,
      ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j) ≫ π i =
        (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)) ≫ π j)
    (huniq : ∀ i j (O : Opens X), O ≤ dom i ⊓ dom j →
      ∀ s s' : (R i).toKLocallyRingedSpace.restrictOpen (overOpens π i O) ⟶
        (R j).toKLocallyRingedSpace.restrictOpen (overOpens π j O),
        IsIso s → IsIso s' →
        ofRestrict _ (overOpens π i O) ≫ π i = (s ≫ ofRestrict _ (overOpens π j O)) ≫ π j →
        ofRestrict _ (overOpens π i O) ≫ π i = (s' ≫ ofRestrict _ (overOpens π j O)) ≫ π j →
        s = s')
    (i j : ι) : t i j ≫ t j i = 𝟙 _ := by
  have hO : dom i ⊓ dom j ≤ dom i ⊓ dom i := le_inf inf_le_left inf_le_left
  have hc : ofRestrict _ (glueOpens X R π dom i j) ≫ π i =
      ((t i j ≫ t j i) ≫ ofRestrict _ (glueOpens X R π dom i j)) ≫ π i := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (t j i), ← compat j i,
      ← Category.assoc, ← compat i j]
  exact huniq i i (dom i ⊓ dom j) hO (t i j ≫ t j i) (𝟙 _)
    (@IsIso.comp_isIso _ _ _ _ _ (t i j) (t j i) (hiso i j) (hiso j i)) inferInstance hc
    (by rw [Category.id_comp])

/-- Transitions that are isomorphisms over `X`, unique among such, are the identity on the
diagonal: the `t_id` field. -/
theorem t_id_of_uniq
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (hiso : ∀ i j, IsIso (t i j))
    (compat : ∀ i j,
      ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j) ≫ π i =
        (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)) ≫ π j)
    (huniq : ∀ i j (O : Opens X), O ≤ dom i ⊓ dom j →
      ∀ s s' : (R i).toKLocallyRingedSpace.restrictOpen (overOpens π i O) ⟶
        (R j).toKLocallyRingedSpace.restrictOpen (overOpens π j O),
        IsIso s → IsIso s' →
        ofRestrict _ (overOpens π i O) ≫ π i = (s ≫ ofRestrict _ (overOpens π j O)) ≫ π j →
        ofRestrict _ (overOpens π i O) ≫ π i = (s' ≫ ofRestrict _ (overOpens π j O)) ≫ π j →
        s = s')
    (i : ι) : t i i = 𝟙 _ :=
  huniq i i (dom i ⊓ dom i) le_rfl (t i i) (𝟙 _) (hiso i i) inferInstance (compat i i)
    (by rw [Category.id_comp])

/-! ### The transition graphs are closed, the glued space is Hausdorff -/

section Hausdorff

variable (hrange : ∀ i, range (KLocallyRingedSpace.Hom.toFun (π i)) ⊆ dom i)
  (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
    (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
  (t_id : ∀ i, t i i = 𝟙 _)
  (t_inter : ∀ i j k (x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j)),
    x.1 ∈ glueOpens X R π dom i k → (KLocallyRingedSpace.Hom.toFun
        (t i j) x).1 ∈ glueOpens X R π dom j k)
  (hcompat : ∀ i j,
    ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j) ≫ π i =
      (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)) ≫ π j)
  (cocycle : ∀ i j k,
    (overCore X R π dom hrange t t_id t_inter).tRes i j k ≫
      (overCore X R π dom hrange t t_id t_inter).tRes j k i ≫
        (overCore X R π dom hrange t t_id t_inter).tRes k i j = 𝟙 _)

include hcompat

omit hcompat in
/-- The transition graph of the gluing over `X`, as the graph of the transition on points. -/
theorem transitionGraph_overData (i j : ι) :
    Glue.transitionGraph (overData X R π dom hrange t t_id t_inter cocycle).topGlueData i j =
      range fun x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) =>
        ((x.1, (KLocallyRingedSpace.Hom.toFun (t i j) x).1) : R i × R j) :=
  rfl

/-- The transition graph is closed: a limit `(p, q)` of graph points satisfies `π_i p = π_j q`
(`compat`, continuity, `X` Hausdorff), so `p` and `q` lie over the overlap, where the graph is the
closed graph of the continuous transition into the Hausdorff piece. -/
theorem isClosed_transitionGraph_overData (i j : ι) :
    IsClosed (Glue.transitionGraph
      (overData X R π dom hrange t t_id t_inter cocycle).topGlueData i j) := by
  change IsClosed
    (range fun x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) =>
      ((x.1, (KLocallyRingedSpace.Hom.toFun (t i j) x).1) : R i × R j))
  rw [← closure_subset_iff_isClosed]
  intro pq hpq
  -- the fibre condition holds on the closure
  have hE : IsClosed {pq : R i × R j | KLocallyRingedSpace.Hom.toFun
      (π i) pq.1 = KLocallyRingedSpace.Hom.toFun (π j) pq.2} :=
    isClosed_eq ((Hom.continuous_toFun (π i)).comp continuous_fst)
      ((Hom.continuous_toFun (π j)).comp continuous_snd)
  have hsub : (range fun x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) =>
      ((x.1, (KLocallyRingedSpace.Hom.toFun (t i j) x).1) : R i × R j)) ⊆
      {pq : R i × R j | KLocallyRingedSpace.Hom.toFun (π i) pq.1 = KLocallyRingedSpace.Hom.toFun
          (π j) pq.2} := by
    rintro _ ⟨x, rfl⟩
    exact (toFun_π_t_eq t hcompat i j x).symm
  have hfib : KLocallyRingedSpace.Hom.toFun (π i) pq.1 = KLocallyRingedSpace.Hom.toFun
      (π j) pq.2 := closure_minimal hsub hE hpq
  have h1 : pq.1 ∈ glueOpens X R π dom i j :=
    (mem_glueOpens X R π dom).mpr ⟨hrange i ⟨_, rfl⟩, hfib ▸ hrange j ⟨_, rfl⟩⟩
  have h2 : pq.2 ∈ glueOpens X R π dom j i :=
    (mem_glueOpens X R π dom).mpr ⟨hrange j ⟨_, rfl⟩, hfib ▸ hrange i ⟨_, rfl⟩⟩
  -- pull the closure back along the inducing product of the two inclusions
  let ι' : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ×
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i) → R i × R j :=
    Prod.map Subtype.val Subtype.val
  have hι : Topology.IsInducing ι' :=
    Topology.IsInducing.subtypeVal.prodMap Topology.IsInducing.subtypeVal
  let G' : Set ((R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ×
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i)) :=
    {xy | xy.2 = KLocallyRingedSpace.Hom.toFun (t i j) xy.1}
  have : T2Space ((R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i)) :=
    inferInstanceAs (T2Space (glueOpens X R π dom j i : Set (R j)))
  have hG' : IsClosed G' :=
    isClosed_eq continuous_snd ((Hom.continuous_toFun (t i j)).comp continuous_fst)
  have himg : (range fun x : (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) =>
      ((x.1, (KLocallyRingedSpace.Hom.toFun (t i j) x).1) : R i × R j)) ⊆ ι' '' G' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(x, KLocallyRingedSpace.Hom.toFun (t i j) x), rfl, rfl⟩
  have hpq' : (⟨pq.1, h1⟩, ⟨pq.2, h2⟩) ∈ closure G' := by
    rw [hι.closure_eq_preimage_closure_image]
    exact closure_mono himg hpq
  rw [hG'.closure_eq] at hpq'
  refine ⟨⟨pq.1, h1⟩, ?_⟩
  have hq : (⟨pq.2, h2⟩ :
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i)) =
      KLocallyRingedSpace.Hom.toFun (t i j) ⟨pq.1, h1⟩ := hpq'
  exact Prod.ext rfl (congrArg Subtype.val hq).symm

/-- A gluing over `X` whose transitions lie over `X` glues to a Hausdorff space (the closed-graph
criterion `t2Space_of_isClosed_transitionGraph`). -/
theorem t2Space_overData_of_compat :
    T2Space (overData X R π dom hrange t t_id t_inter cocycle).glued :=
  (overData X R π dom hrange t t_id t_inter cocycle).t2Space_of_isClosed_transitionGraph
    (fun i => inferInstanceAs (T2Space (R i)))
    (fun i j _ => isClosed_transitionGraph_overData (hrange := hrange) (t := t) (t_id := t_id)
      (t_inter := t_inter) (hcompat := hcompat) (cocycle := cocycle) i j)

end Hausdorff

/-! ### The gluing datum from transitions -/

/-- **The gluing datum from transitions** ([Wlo09, §4], with the uniqueness of the lifts):
transitions that are isomorphisms over `X` on the gluing open subsets, unique among such on the
points over every open subset of the base contained in the overlap, form a `GlueOver`: `t_id` and
the cocycle identity by uniqueness (against the identity), `t_inter` from `compat`, Hausdorffness by
`t2Space_overData_of_compat`. The cocycle's composite is an isomorphism over `X` by
`isIso_tRes_of_comp_eq_id`. -/
theorem exists_glueOver_of_transitions (hrange : ∀ i, range (KLocallyRingedSpace.Hom.toFun
    (π i)) ⊆ dom i)
    (t : ∀ i j, (R i).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom i j) ⟶
      (R j).toKLocallyRingedSpace.restrictOpen (glueOpens X R π dom j i))
    (hiso : ∀ i j, IsIso (t i j))
    (hcompat : ∀ i j,
      ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j) ≫ π i =
        (t i j ≫ ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)) ≫ π j)
    (huniq : ∀ i j (O : Opens X), O ≤ dom i ⊓ dom j →
      ∀ s s' : (R i).toKLocallyRingedSpace.restrictOpen (overOpens π i O) ⟶
        (R j).toKLocallyRingedSpace.restrictOpen (overOpens π j O),
        IsIso s → IsIso s' →
        ofRestrict _ (overOpens π i O) ≫ π i = (s ≫ ofRestrict _ (overOpens π j O)) ≫ π j →
        ofRestrict _ (overOpens π i O) ≫ π i = (s' ≫ ofRestrict _ (overOpens π j O)) ≫ π j →
        s = s') :
    Nonempty (GlueOver X R π dom) := by
  have hinv := t_comp_t_eq_id_of_uniq t hiso hcompat huniq
  have ht_id := t_id_of_uniq t hiso hcompat huniq
  have ht_inter := t_inter_of_compat hrange t hcompat
  have hcoc : ∀ i j k, (overCore X R π dom hrange t ht_id ht_inter).tRes i j k ≫
      (overCore X R π dom hrange t ht_id ht_inter).tRes j k i ≫
        (overCore X R π dom hrange t ht_id ht_inter).tRes k i j = 𝟙 _ := by
    intro i j k
    have hO : (dom i ⊓ dom j) ⊓ (dom i ⊓ dom k) ≤ dom i ⊓ dom i :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_left)
    have h1 := (overCore X R π dom hrange t ht_id ht_inter).isIso_tRes_of_comp_eq_id hinv i j k
    have h2 := (overCore X R π dom hrange t ht_id ht_inter).isIso_tRes_of_comp_eq_id hinv j k i
    have h3 := (overCore X R π dom hrange t ht_id ht_inter).isIso_tRes_of_comp_eq_id hinv k i j
    have hiso' : IsIso ((overCore X R π dom hrange t ht_id ht_inter).tRes i j k ≫
        (overCore X R π dom hrange t ht_id ht_inter).tRes j k i ≫
          (overCore X R π dom hrange t ht_id ht_inter).tRes k i j) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3)
    -- each restricted transition lies over `X`
    have e1 : ∀ a b c, (overCore X R π dom hrange t ht_id ht_inter).tRes a b c ≫
        ofRestrict _ ((overCore X R π dom hrange t ht_id ht_inter).W b c ⊓
          (overCore X R π dom hrange t ht_id ht_inter).W b a) ≫ π b =
          ofRestrict _ ((overCore X R π dom hrange t ht_id ht_inter).W a b ⊓
            (overCore X R π dom hrange t ht_id ht_inter).W a c) ≫ π a := by
      intro a b c
      rw [← Category.assoc, Glue.KGlueCore.tRes_comp_ofRestrict]
      dsimp only [overCore]
      simp only [Category.assoc]
      rw [← Category.assoc (t a b), ← hcompat a b, ← Category.assoc,
        Glue.restrictOpenIncl_comp_ofRestrict]
    have hover : ofRestrict _ ((overCore X R π dom hrange t ht_id ht_inter).W i j ⊓
          (overCore X R π dom hrange t ht_id ht_inter).W i k) ≫ π i =
        (((overCore X R π dom hrange t ht_id ht_inter).tRes i j k ≫
          (overCore X R π dom hrange t ht_id ht_inter).tRes j k i ≫
            (overCore X R π dom hrange t ht_id ht_inter).tRes k i j) ≫
          ofRestrict _ ((overCore X R π dom hrange t ht_id ht_inter).W i j ⊓
            (overCore X R π dom hrange t ht_id ht_inter).W i k)) ≫ π i := by
      simp only [Category.assoc]
      rw [e1 k i j, e1 j k i, e1 i j k]
    exact huniq i i _ hO _ (𝟙 _) hiso' inferInstance hover (by rw [Category.id_comp])
  exact ⟨GlueOver.mk hrange t ht_id ht_inter hcompat hcoc
    (t2Space_overData_of_compat (hrange := hrange) (t := t) (t_id := ht_id) (t_inter := ht_inter)
      (hcompat := hcompat) (cocycle := hcoc))⟩

end GlueOver

end AnalyticSpace

end
