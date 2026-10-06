/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Topology.Gluing

/-!
# The Hausdorff criterion for a glued space

Let `D` be topological gluing data (Mathlib's `TopCat.GlueData`: spaces `U i`, open subsets
`V (i, j) ⊆ U i` through the open embeddings `f i j`, transition homeomorphisms `t i j`). If every
`U i` is Hausdorff and, for `i ≠ j`, the graph `{(f i j x, f j i (t i j x))}` of the transition map
(`transitionGraph`) is closed in `U i × U j`, then the glued space is Hausdorff
(`t2Space_glued_of_isClosed_transitionGraph`). Mathlib's `TopCat.GlueData` carries no separation
statement; this is the separation lemma the gluing of local complexifications rests on, where the
whole difficulty is to arrange closed graphs by shrinking the pieces (following the shrinking
pattern of the proof of [Car57, §3, Proposition 2], which shrinks the covers for the sheaf
cocycle).

Conventions. Points of `D.glued` are `ι i y`, and `ι i y = ι j y'` iff `D.Rel ⟨i, y⟩ ⟨j, y'⟩`, that
is, iff `(y, y') = (f i j x, f j i (t i j x))` for some `x : V (i, j)` (Mathlib's `ι_eq_iff_rel`,
`mem_transitionGraph_iff_rel`). Two points `ι i y ≠ ι j y'` are separated by the images of disjoint
neighbourhoods when `i = j` (Hausdorffness of `U i`, injectivity of `ι i`) and by the images of a
product neighbourhood of `(y, y')` disjoint from the closed graph when `i ≠ j`. For a single space
the criterion is the Hausdorffness of `U`; for a disjoint gluing (`V (i, j) = ∅` for `i ≠ j`) the
graphs are empty and the glued space is the disjoint union. The converse (a Hausdorff glued space
has closed graphs) holds as well; nothing in the library requires it, so it is not proved here.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology

namespace AnalyticSpace.Glue

universe u

/-- The graph of the transition map from the `i`-th to the `j`-th piece, as a subset of
`U i × U j`. -/
def transitionGraph (D : TopCat.GlueData.{u}) (i j : D.J) : Set (D.U i × D.U j) :=
  Set.range fun x : D.V (i, j) => ((D.f i j x, D.f j i (D.t i j x)) : D.U i × D.U j)

theorem mem_transitionGraph_iff_rel (D : TopCat.GlueData.{u}) {i j : D.J} {y : D.U i}
    {y' : D.U j} : (y, y') ∈ transitionGraph D i j ↔ D.Rel ⟨i, y⟩ ⟨j, y'⟩ := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  · rintro ⟨x, h₁, h₂⟩
    exact ⟨x, Prod.ext h₁ h₂⟩

/-- The Hausdorff criterion: Hausdorff pieces and closed transition graphs give a Hausdorff glued
space. -/
theorem t2Space_glued_of_isClosed_transitionGraph (D : TopCat.GlueData.{u})
    [∀ i, T2Space (D.U i)] (hgraph : ∀ i j, i ≠ j → IsClosed (transitionGraph D i j)) :
    T2Space D.toGlueData.glued := by
  refine ⟨fun z z' hne => ?_⟩
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective z
  obtain ⟨j, y', rfl⟩ := D.ι_jointly_surjective z'
  by_cases hij : i = j
  · subst hij
    have hyy' : y ≠ y' := fun h => hne (congrArg _ h)
    obtain ⟨A, B, hA, hB, hyA, hy'B, hAB⟩ := t2_separation hyy'
    refine ⟨D.toGlueData.ι i '' A, D.toGlueData.ι i '' B,
      (D.ι_isOpenEmbedding i).isOpenMap A hA, (D.ι_isOpenEmbedding i).isOpenMap B hB,
      ⟨y, hyA, rfl⟩, ⟨y', hy'B, rfl⟩, ?_⟩
    rw [Set.disjoint_image_iff (D.ι_injective i)]
    exact hAB
  · have hnot : (y, y') ∉ transitionGraph D i j := fun h =>
      hne ((D.ι_eq_iff_rel i j y y').mpr ((mem_transitionGraph_iff_rel D).mp h))
    obtain ⟨A, B, hA, hB, hyA, hy'B, hAB⟩ :=
      isOpen_prod_iff.mp (hgraph i j hij).isOpen_compl y y' hnot
    refine ⟨D.toGlueData.ι i '' A, D.toGlueData.ι j '' B,
      (D.ι_isOpenEmbedding i).isOpenMap A hA, (D.ι_isOpenEmbedding j).isOpenMap B hB,
      ⟨y, hyA, rfl⟩, ⟨y', hy'B, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨a, haA, rfl⟩ ⟨b, hbB, hab⟩
    have hrel : D.Rel ⟨i, a⟩ ⟨j, b⟩ := (D.ι_eq_iff_rel i j a b).mp hab.symm
    exact hAB (Set.mem_prod.mpr ⟨haA, hbB⟩) ((mem_transitionGraph_iff_rel D).mpr hrel)

end AnalyticSpace.Glue
