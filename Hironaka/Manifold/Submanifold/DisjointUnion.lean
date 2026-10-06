/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.FiniteSuccession.Functor.LocalTriples
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Closed submanifolds of a disjoint-union cover

For a cover of `M` by pairwise disjoint analytic open embeddings `ιᵢ : Nᵢ → M`, the union of the
images of closed submanifolds of the pieces is a closed submanifold of the same codimension
(`IsClosedSubmanifold.iUnion_image`): closed as the complement of the open union of the images of
the complements, with adapted charts transported along the open embeddings (`transportChart` of
`Hironaka/Manifold/BlowUp/Functor.lean`). With the two set-theoretic lemmas
`iUnion_image_inter_range` and `compl_iUnion_image`. This is the step of Kollár's proof of
Theorem 103 in which the local hypersurfaces of maximal contact `H^{(j)} ⊂ X^{(j)}` are assembled
into the smooth hypersurface `H^* := ∐_j H^{(j)}` of the disjoint union `X^* := ∐_j X^{(j)}`
[Kol07, Theorem 103, proof, Step 3]; it is used in that role in
`Hironaka/Resolution/Analytic/OrderReduction/SigmaContact.lean`.
-/

public noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

section Union

variable {M : AnalyticManifold.{u} 𝕜 E} {σ : Type u} {N : σ → AnalyticManifold.{u} 𝕜 E}
  (ι : ∀ i, AnalyticMap (N i) M) (hι : ∀ i, IsAnalyticOpenEmbedding (ι i))
  (hdisj : Pairwise fun i j => Disjoint (Set.range (ι i)) (Set.range (ι j)))
  (hcov : (⋃ i, Set.range (ι i)) = Set.univ) (Y : ∀ i, Set (N i))

include hι hdisj in
/-- The union of the images meets the range of `ιᵢ` in the image of the `i`-th piece. -/
theorem iUnion_image_inter_range (i : σ) :
    (⋃ j, ⇑(ι j) '' Y j) ∩ Set.range (ι i) = ⇑(ι i) '' Y i := by
  ext x
  constructor
  · rintro ⟨hx, ⟨y, rfl⟩⟩
    obtain ⟨j, z, hz, hzy⟩ := Set.mem_iUnion.mp hx
    obtain rfl : j = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne) ⟨z, hzy⟩ ⟨y, rfl⟩
    rw [(hι j).2 hzy] at hz
    exact ⟨y, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Set.mem_iUnion.mpr ⟨i, y, hy, rfl⟩, y, rfl⟩

include hι hdisj hcov in
/-- The complement of the union of the images is the union of the images of the complements. -/
theorem compl_iUnion_image : (⋃ i, ⇑(ι i) '' Y i)ᶜ = ⋃ i, ⇑(ι i) '' (Y i)ᶜ := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋃ i, Set.range (ι i) := hcov ▸ Set.mem_univ x
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx'
    refine Set.mem_iUnion.mpr ⟨i, y, fun hy => hx ?_, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, y, hy, rfl⟩
  · intro hx hx'
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    have := (iUnion_image_inter_range ι hι hdisj Y i).subset ⟨hx', y, rfl⟩
    obtain ⟨z, hz, hzy⟩ := this
    exact hy ((hι i).2 hzy ▸ hz)

include hι hdisj hcov in
/-- The union of the images of closed submanifolds of the pieces of a disjoint-union cover is a
closed submanifold of the same codimension (Kollár's "the disjoint union `H^* := ∐_j H^{(j)}` is a
smooth hypersurface", [Kol07, Theorem 103, proof, Step 3]): closed as the complement of the open
union of the images of the complements, with adapted charts transported along the open
embeddings. -/
theorem IsClosedSubmanifold.iUnion_image {c : ℕ} (hY : ∀ i, IsClosedSubmanifold ψ₀ (Y i) c) :
    IsClosedSubmanifold ψ₀ (⋃ i, ⇑(ι i) '' Y i) c where
  isClosed := by
    rw [← isOpen_compl_iff, compl_iUnion_image ι hι hdisj hcov Y]
    exact isOpen_iUnion fun i => (hι i).1.isOpenMap _ (hY i).isClosed.isOpen_compl
  exists_adaptedChart := by
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    have : Nonempty (N i) := ⟨y⟩
    obtain ⟨φ, τ, hyφ, hφ⟩ := (hY i).exists_adaptedChart y hy
    refine ⟨transportChart (hι i).toPartialDiffeomorph φ, τ, ?_,
      isAdaptedChart_transportChart _ ?_ hφ⟩
    · rw [transportChart_source]
      refine ⟨Set.mem_range_self y, ?_⟩
      change Function.invFun (ι i) (ι i y) ∈ φ.source
      rw [Function.leftInverse_invFun (hι i).2 y]
      exact hyφ
    · change ⇑(ι i) '' (Y i ∩ Set.univ) = (⋃ j, ⇑(ι j) '' Y j) ∩ Set.range (ι i)
      rw [Set.inter_univ, iUnion_image_inter_range ι hι hdisj Y i]

end Union

end Manifold
