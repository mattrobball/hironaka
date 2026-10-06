/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The direct limit of a chain of analytic open embeddings: the space

An `ℕ`-chain `X 0 → X 1 → ⋯` of analytic manifolds along analytic open embeddings
`ι n : X n → X (n+1)` (`OpenEmbeddingChain`), and its direct limit `⋃ₙ X n` as a topological space:
Włodarczyk's manifold obtained by gluing the pieces `Ũ_i` along their overlaps [Wlo09, §4.1], in the
linear case of an exhaustion `M_0 ⊆ M_1 ⊆ ⋯` (Kollár's remark that resolution on neighbourhoods of
compact sets gives resolution of analytic spaces which are increasing unions of compact subsets
[Kol07, 44]; [BM97, §13]). It is used by `Hironaka/Resolution/Analytic/Functor/LimitFamily.lean` for
the end results of a compatible family along the embeddings of end results.

The limit is the quotient of the disjoint union `Σ n, X n` by the identification of two points
that agree in a common later piece under the composite embeddings `iter : X n → X m` (`n ≤ m`), an
equivalence relation because the composites are injective (`LimitRel`, `setoid`, `Limit`). Each
piece maps in by `toLimit n`, injectively, with `toLimit (n+1) ∘ ι n = toLimit n`; the union of
the images is everything. The quotient topology makes every `toLimit n` an open embedding: a set
of `X n` is open in the limit iff its saturation meets every piece `X m` in an open set, and that
trace is the preimage under `iter : X m → X (max m n)` of the image under
`iter : X n → X (max m n)`, open since the composites are open maps (`preimage_toLimit_image`,
`isOpenMap_toLimit`, `isOpenEmbedding_toLimit`). The manifold structure is
`DirectLimit/Manifold.lean`, the maps out of the limit `DirectLimit/Cocone.lean`.

* `OpenEmbeddingChain`, `iter` with `iter_self`, `iter_succ`, `iter_trans`, `iter_injective`,
  `isLocalDiffeomorph_iter`, `isAnalyticOpenEmbedding_iter`, `isOpenEmbedding_iter`.
* `LimitRel`, `setoid`, `Limit`, `toLimit` with `toLimit_eq_iff_iter`, `toLimit_iter`,
  `toLimit_succ`, `toLimit_injective`, `toLimit_surjective`, `exists_common_toLimit`,
  `range_toLimit_mono`, `iUnion_range_toLimit`.
* `limitTopologicalSpace`, `continuous_toLimit`, `preimage_toLimit_image`, `isOpenMap_toLimit`,
  `isOpenEmbedding_toLimit`, `isOpen_range_toLimit`.

The gluing is elementary and not in the sources in this form.
-/

@[expose] public noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An `ℕ`-chain of analytic manifolds `X 0 → X 1 → ⋯` along analytic open embeddings: the end
results of a compatible family along an exhaustion `M_0 ⊆ M_1 ⊆ ⋯` with the embeddings of end
results, abstractly ([Wlo09, §4.1]; [Kol07, 44]). -/
structure OpenEmbeddingChain (𝕜 : Type) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] where
  /-- The pieces. -/
  X : ℕ → AnalyticManifold.{u} 𝕜 E
  /-- The transition maps. -/
  ι : ∀ n, AnalyticMap (X n) (X (n + 1))
  /-- Each transition map is an analytic open embedding. -/
  isAnalyticOpenEmbedding : ∀ n, IsAnalyticOpenEmbedding (ι n)

namespace OpenEmbeddingChain

variable (c : OpenEmbeddingChain.{u} 𝕜 E)

/-! ### The composite embeddings -/

/-- The composite embedding `X n → X m` for `n ≤ m`, `ι (m-1) ∘ ⋯ ∘ ι n`
(`Nat.leRecOn`). -/
def iter : ∀ {n m : ℕ}, n ≤ m → AnalyticMap (c.X n) (c.X m) := fun {n _} h =>
  Nat.leRecOn (C := fun k => AnalyticMap (c.X n) (c.X k)) h (fun {k} g => (c.ι k).comp g)
    ContMDiffMap.id

/-- The composite from a piece to itself is the identity. -/
theorem iter_self (n : ℕ) : c.iter (le_refl n) = ContMDiffMap.id := Nat.leRecOn_self _

/-- `iter_self`, pointwise and for any proof of `n ≤ n`. -/
theorem iter_self_apply (n : ℕ) (h : n ≤ n) (x : c.X n) : c.iter h x = x := by
  rw [iter_self]
  rfl

/-- The composite to `m + 1` is `ι m` after the composite to `m`. -/
theorem iter_succ {n m : ℕ} (h : n ≤ m) (h' : n ≤ m + 1) :
    c.iter h' = (c.ι m).comp (c.iter h) := Nat.leRecOn_succ h _

/-- `iter_succ`, pointwise. -/
theorem iter_succ_apply {n m : ℕ} (h : n ≤ m) (h' : n ≤ m + 1) (x : c.X n) :
    c.iter h' x = c.ι m (c.iter h x) := by
  rw [iter_succ c h h']
  rfl

/-- The composite of one step is the transition map. -/
theorem iter_one_apply (n : ℕ) (h : n ≤ n + 1) (x : c.X n) : c.iter h x = c.ι n x := by
  rw [iter_succ_apply c (le_refl n) h, iter_self_apply]

/-- The composites compose (functoriality of `iter`). -/
theorem iter_trans {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x : c.X n) :
    c.iter h₂ (c.iter h₁ x) = c.iter (h₁.trans h₂) x := by
  induction k, h₂ using Nat.le_induction with
  | base => rw [iter_self_apply]
  | succ k hmk ih =>
    rw [iter_succ_apply c hmk (Nat.le_succ_of_le hmk), ih,
      iter_succ_apply c (h₁.trans hmk) (h₁.trans (Nat.le_succ_of_le hmk))]

/-- The composites are injective (each `ι n` is). -/
theorem iter_injective {n m : ℕ} (h : n ≤ m) : Function.Injective (c.iter h) := by
  induction m, h using Nat.le_induction with
  | base => intro x y hxy; rwa [iter_self_apply, iter_self_apply] at hxy
  | succ m hnm ih =>
    intro x y hxy
    rw [iter_succ_apply c hnm, iter_succ_apply c hnm] at hxy
    exact ih ((c.isAnalyticOpenEmbedding m).2 hxy)

/-- The composites are local analytic isomorphisms (each `ι n` is;
`BlowUpSequence.isLocalDiffeomorph_comp`). -/
theorem isLocalDiffeomorph_iter {n m : ℕ} (h : n ≤ m) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (c.iter h) := by
  induction m, h using Nat.le_induction with
  | base => rw [iter_self]; exact AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _
  | succ m hnm ih =>
    rw [iter_succ c hnm]
    exact AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (c.isAnalyticOpenEmbedding m).1 ih

/-- The composites are analytic open embeddings. -/
theorem isAnalyticOpenEmbedding_iter {n m : ℕ} (h : n ≤ m) :
    IsAnalyticOpenEmbedding (c.iter h) :=
  ⟨c.isLocalDiffeomorph_iter h, c.iter_injective h⟩

/-- The composites are topological open embeddings (a continuous injective open
map). -/
theorem isOpenEmbedding_iter {n m : ℕ} (h : n ≤ m) : IsOpenEmbedding (c.iter h) :=
  .of_continuous_injective_isOpenMap (c.iter h).contMDiff.continuous (c.iter_injective h)
    (c.isLocalDiffeomorph_iter h).isOpenMap

/-! ### The direct limit -/

/-- Two points of pieces are identified when they agree in a common later piece (the gluing of the
pieces along their overlaps, [Wlo09, §4.1]). -/
def LimitRel (a b : Σ n, (c.X n : Type u)) : Prop :=
  ∃ (k : ℕ) (h₁ : a.1 ≤ k) (h₂ : b.1 ≤ k), c.iter h₁ a.2 = c.iter h₂ b.2

/-- Identified points agree in EVERY common later piece (injectivity of the
composites at a piece above both). -/
theorem LimitRel.iter_eq {a b : Σ n, (c.X n : Type u)} (hab : c.LimitRel a b) {k : ℕ} (h₁ : a.1 ≤ k)
    (h₂ : b.1 ≤ k) : c.iter h₁ a.2 = c.iter h₂ b.2 := by
  obtain ⟨k', h₁', h₂', e⟩ := hab
  apply c.iter_injective (le_max_left k k')
  rw [iter_trans, iter_trans, ← iter_trans c h₁' (le_max_right k k'), e,
    iter_trans c h₂' (le_max_right k k')]

/-- The identification is reflexive. -/
theorem limitRel_refl (a : Σ n, (c.X n : Type u)) : c.LimitRel a a := ⟨a.1, le_rfl, le_rfl, rfl⟩

/-- The identification is symmetric. -/
theorem limitRel_symm {a b : Σ n, (c.X n : Type u)} (h : c.LimitRel a b) : c.LimitRel b a := by
  obtain ⟨k, h₁, h₂, e⟩ := h
  exact ⟨k, h₂, h₁, e.symm⟩

/-- The identification is transitive (compare in a piece above both witnesses). -/
theorem limitRel_trans {a b d : Σ n, (c.X n : Type u)} (hab : c.LimitRel a b)
    (hbd : c.LimitRel b d) : c.LimitRel a d := by
  obtain ⟨k, h₁, h₂, e⟩ := hab
  obtain ⟨k', h₃, h₄, e'⟩ := hbd
  refine ⟨max k k', h₁.trans (le_max_left k k'), h₄.trans (le_max_right k k'), ?_⟩
  rw [← iter_trans c h₁ (le_max_left k k'), e, iter_trans c h₂ (le_max_left k k'),
    ← iter_trans c h₄ (le_max_right k k'), ← e', iter_trans c h₃ (le_max_right k k')]

/-- The identification of the pieces along the chain, as a setoid. -/
def setoid : Setoid (Σ n, (c.X n : Type u)) :=
  ⟨c.LimitRel, ⟨c.limitRel_refl, c.limitRel_symm, c.limitRel_trans⟩⟩

/-- The direct limit `⋃ₙ X n`: the pieces identified along the chain (Włodarczyk's glued manifold
`M̃`, [Wlo09, §4.1]). -/
def Limit : Type u := Quotient c.setoid

/-- The inclusion of the `n`-th piece into the limit. -/
def toLimit (n : ℕ) (x : c.X n) : c.Limit := Quotient.mk c.setoid ⟨n, x⟩

/-- Two points of pieces have the same image iff they are identified. -/
theorem toLimit_eq_iff {n m : ℕ} {x : c.X n} {y : c.X m} :
    c.toLimit n x = c.toLimit m y ↔ c.LimitRel ⟨n, x⟩ ⟨m, y⟩ :=
  Quotient.eq

/-- Two points of pieces have the same image iff they agree in any given common
later piece. -/
theorem toLimit_eq_iff_iter {n m k : ℕ} (h₁ : n ≤ k) (h₂ : m ≤ k) {x : c.X n} {y : c.X m} :
    c.toLimit n x = c.toLimit m y ↔ c.iter h₁ x = c.iter h₂ y := by
  rw [toLimit_eq_iff]
  exact ⟨fun h => h.iter_eq c h₁ h₂, fun h => ⟨k, h₁, h₂, h⟩⟩

/-- The inclusions are compatible with the composite embeddings. -/
theorem toLimit_iter {n m : ℕ} (h : n ≤ m) (x : c.X n) : c.toLimit m (c.iter h x) = c.toLimit n x :=
  (c.toLimit_eq_iff_iter (le_refl m) h).mpr (c.iter_self_apply m _ _)

/-- The inclusions are compatible with the transition maps,
`toLimit (n+1) ∘ ι n = toLimit n`. -/
theorem toLimit_succ (n : ℕ) (x : c.X n) : c.toLimit (n + 1) (c.ι n x) = c.toLimit n x := by
  rw [← c.iter_one_apply n (Nat.le_succ n), toLimit_iter]

/-- Each inclusion is injective. -/
theorem toLimit_injective (n : ℕ) : Function.Injective (c.toLimit n) := fun x y h => by
  rw [c.toLimit_eq_iff_iter (le_refl n) (le_refl n), iter_self_apply, iter_self_apply] at h
  exact h

/-- Every point of the limit comes from some piece. -/
theorem toLimit_surjective (p : c.Limit) : ∃ (n : ℕ) (x : c.X n), c.toLimit n x = p :=
  Quotient.inductionOn p fun a => ⟨a.1, a.2, rfl⟩

/-- Two points of the limit come from a common piece. -/
theorem exists_common_toLimit (p q : c.Limit) :
    ∃ (k : ℕ) (x y : c.X k), c.toLimit k x = p ∧ c.toLimit k y = q := by
  obtain ⟨n, x, rfl⟩ := c.toLimit_surjective p
  obtain ⟨m, y, rfl⟩ := c.toLimit_surjective q
  exact ⟨max n m, c.iter (le_max_left n m) x, c.iter (le_max_right n m) y, c.toLimit_iter _ _,
    c.toLimit_iter _ _⟩

/-- The images of the pieces increase. -/
theorem range_toLimit_mono {n m : ℕ} (h : n ≤ m) :
    Set.range (c.toLimit n) ⊆ Set.range (c.toLimit m) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨c.iter h x, c.toLimit_iter h x⟩

/-- The images of the pieces cover the limit. -/
theorem iUnion_range_toLimit : ⋃ n, Set.range (c.toLimit n) = univ :=
  eq_univ_of_forall fun p => by
    obtain ⟨n, x, rfl⟩ := c.toLimit_surjective p
    exact mem_iUnion.mpr ⟨n, x, rfl⟩

/-! ### The topology of the limit -/

/-- The quotient topology on the limit. -/
instance limitTopologicalSpace : TopologicalSpace c.Limit :=
  inferInstanceAs (TopologicalSpace (Quotient c.setoid))

/-- The inclusions are continuous. -/
theorem continuous_toLimit (n : ℕ) : Continuous (c.toLimit n) :=
  continuous_quotient_mk'.comp continuous_sigmaMk

/-- The trace on the `m`-th piece of the saturation of a set `U` of the `n`-th
piece — the preimage under `X m → X (max m n)` of the image of `U` under `X n → X (max m n)`. -/
theorem preimage_toLimit_image (n m : ℕ) (U : Set (c.X n)) :
    Sigma.mk m ⁻¹' (Quotient.mk c.setoid ⁻¹' (c.toLimit n '' U)) =
      c.iter (le_max_left m n) ⁻¹' (c.iter (le_max_right m n) '' U) := by
  ext y
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (c.toLimit_eq_iff_iter (le_max_right m n) (le_max_left m n)).mp hxy⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, (c.toLimit_eq_iff_iter (le_max_right m n) (le_max_left m n)).mpr hxy⟩

/-- The inclusions are open maps — the saturation of an open set meets every piece
in an open set (`preimage_toLimit_image`, the composites being open embeddings). -/
theorem isOpenMap_toLimit (n : ℕ) : IsOpenMap (c.toLimit n) := by
  intro U hU
  have hsat : IsOpen (Quotient.mk c.setoid ⁻¹' (c.toLimit n '' U)) := by
    rw [isOpen_sigma_iff]
    intro m
    rw [preimage_toLimit_image]
    exact ((c.isOpenEmbedding_iter (le_max_right m n)).isOpenMap U hU).preimage
      (c.iter (le_max_left m n)).contMDiff.continuous
  exact (isQuotientMap_quotient_mk' (s := c.setoid)).isOpen_preimage.mp hsat

/-- The inclusions are open embeddings. -/
theorem isOpenEmbedding_toLimit (n : ℕ) : IsOpenEmbedding (c.toLimit n) :=
  .of_continuous_injective_isOpenMap (c.continuous_toLimit n) (c.toLimit_injective n)
    (c.isOpenMap_toLimit n)

/-- The image of each piece is open in the limit. -/
theorem isOpen_range_toLimit (n : ℕ) : IsOpen (Set.range (c.toLimit n)) :=
  (c.isOpenEmbedding_toLimit n).isOpen_range

end OpenEmbeddingChain

end Manifold
