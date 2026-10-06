/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.RestrictInj
public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
public import Hironaka.Manifold.SigmaManifold
import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
public import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaLocalDiffeo
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The fibre product of two coproducts of open embeddings

Step (ii) of the proof of [Kol07, Proposition 37] sets `X'' := ∐_{i≤j} Uᵢ ∩ Uⱼ` with the natural
maps `τ₁, τ₂ : X'' → X'` (`Uᵢ ∩ Uⱼ → Uᵢ` and `Uᵢ ∩ Uⱼ → Uⱼ`); the proof of [Kol07, Theorem 105]
uses `X'' := X' ×_X X'`. For two coproducts of open embeddings `g₁ : N₁ → M` (pieces `Uᵢ`) and
`g₂ : N₂ → M` (pieces `Vⱼ`, on which `g₂` is injective), the fibre product is the disjoint union
over the pairs `(i, j)` of the open subsets `Uᵢ ∩ g₁⁻¹(g₂ Vⱼ)` of `N₁`: the first projection is
the inclusion, the second is `(g₂|_{Vⱼ})⁻¹ ∘ g₁`; the pair is a bijection onto
`{(x, y) | g₁ x = g₂ y}` because the pieces of each coproduct partition its source. A coproduct's
pieces are first normalised to a countable family of nonempty pieces (second countability), so
that the disjoint union is one of the manifolds of the library (`sigmaManifold`).
-/

@[expose] public section

noncomputable section

open Set Topology Function TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N N₁ N₂ : AnalyticManifold.{u} 𝕜 E}

/-- The pieces of a coproduct of open embeddings can be taken countable and nonempty (second
countability: a pairwise disjoint family of nonempty open sets is countable). -/
theorem IsCoprodOfOpenEmbeddings.exists_countable {g : AnalyticMap N M}
    (hg : IsCoprodOfOpenEmbeddings g) :
    ∃ (σ : Type u) (_ : Countable σ) (U : σ → Set N), (∀ i, IsClopen (U i)) ∧
      Pairwise (Disjoint on U) ∧ (⋃ i, U i) = univ ∧ (∀ i, InjOn g (U i)) ∧
        ∀ i, (U i).Nonempty := by
  obtain ⟨-, σ, U, hclo, hdisj, hcov, hinj⟩ := hg
  have hdisj' : Pairwise (Disjoint on fun i : {i // (U i).Nonempty} => U i.1) :=
    fun i j hij => hdisj fun h => hij (Subtype.ext h)
  refine ⟨{i // (U i).Nonempty}, ?_, fun i => U i.1, fun i => hclo i.1, hdisj', ?_,
    fun i => hinj i.1, fun i => i.2⟩
  · exact Pairwise.countable_of_isOpen_disjoint hdisj' (fun i => (hclo i.1).2) fun i => i.2
  · refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ i, U i := hcov ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨i, ⟨x, hi⟩⟩, hi⟩

section Construction

variable {g₁ : AnalyticMap N₁ M} {g₂ : AnalyticMap N₂ M}
  (hg₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g₂) {σ₁ σ₂ : Type u}
  {U : σ₁ → Set N₁} {V : σ₂ → Set N₂} (hUo : ∀ i, IsOpen (U i)) (hVo : ∀ j, IsOpen (V j))
  (hVi : ∀ j, InjOn g₂ (V j)) (hVne : ∀ j, (V j).Nonempty)

/-- Kollár's `Uᵢ ∩ Uⱼ`: the open piece `Uᵢ ∩ g₁⁻¹(g₂ Vⱼ)` of `N₁`. -/
def fibrePieceSet (ij : σ₁ × σ₂) : Opens N₁ :=
  ⟨U ij.1 ∩ g₁ ⁻¹' (g₂ '' V ij.2),
    (hUo _).inter ((hg₂.isOpenMap _ (hVo _)).preimage g₁.contMDiff.continuous)⟩

/-- The piece as a manifold. -/
def fibrePiece (ij : σ₁ × σ₂) : AnalyticManifold.{u} 𝕜 E :=
  N₁.restrict (fibrePieceSet (g₁ := g₁) hg₂ hUo hVo ij)

/-- Kollár's `X'' := ∐ Uᵢ ∩ Uⱼ`: the disjoint union of the pieces. -/
def fibreManifold [Countable σ₁] [Countable σ₂] : AnalyticManifold.{u} 𝕜 E :=
  sigmaManifold (fibrePiece (g₁ := g₁) hg₂ hUo hVo)

/-- Kollár's `τ₁`: the first projection, the inclusion on each piece. -/
def fibreFst [Countable σ₁] [Countable σ₂] :
    AnalyticMap (fibreManifold (g₁ := g₁) hg₂ hUo hVo) N₁ :=
  ⟨fun w => N₁.inclusion (fibrePieceSet hg₂ hUo hVo w.1) w.2,
    ContMDiff.sigmaDesc (M := fun ij => (fibrePiece (g₁ := g₁) hg₂ hUo hVo ij : Type u))
      fun ij => (N₁.inclusion (fibrePieceSet hg₂ hUo hVo ij)).contMDiff⟩

theorem fibreFst_apply [Countable σ₁] [Countable σ₂]
    (w : fibreManifold (g₁ := g₁) hg₂ hUo hVo) :
    fibreFst (g₁ := g₁) hg₂ hUo hVo w = N₁.inclusion (fibrePieceSet hg₂ hUo hVo w.1) w.2 := rfl

/-- The local inverse of `g₂` on the piece `Vⱼ`. -/
def pieceInv (j : σ₂) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N₂ M ω :=
  haveI : Nonempty N₂ := ⟨(hVne j).some⟩
  hg₂.restrictInjOn (hVo j) (hVi j)

theorem pieceInv_source (j : σ₂) : (pieceInv hg₂ hVo hVi hVne j).source = V j := rfl

theorem pieceInv_target (j : σ₂) : (pieceInv hg₂ hVo hVi hVne j).target = g₂ '' V j := rfl

theorem pieceInv_apply (j : σ₂) (y : N₂) : pieceInv hg₂ hVo hVi hVne j y = g₂ y := rfl

/-- Kollár's `τ₂` on the piece `Uᵢ ∩ g₁⁻¹(g₂ Vⱼ)`: `(g₂|_{Vⱼ})⁻¹ ∘ g₁`. -/
def fibreSndFun (ij : σ₁ × σ₂) (x : fibrePiece (g₁ := g₁) hg₂ hUo hVo ij) : N₂ :=
  (pieceInv hg₂ hVo hVi hVne ij.2).symm (g₁ x.1)

theorem contMDiff_fibreSndFun (ij : σ₁ × σ₂) :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω (fibreSndFun (g₁ := g₁) hg₂ hUo hVo hVi hVne ij) := by
  intro x
  have hmem : g₁ x.1 ∈ (pieceInv hg₂ hVo hVi hVne ij.2).target := x.2.2
  exact ((pieceInv hg₂ hVo hVi hVne ij.2).symm.contMDiffOn_toFun.contMDiffAt
    ((pieceInv hg₂ hVo hVi hVne ij.2).open_target.mem_nhds hmem)).comp x
    (g₁.contMDiff.comp (N₁.inclusion (fibrePieceSet hg₂ hUo hVo ij)).contMDiff).contMDiffAt

theorem isLocalDiffeomorph_fibreSndFun (hg₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g₁)
    (ij : σ₁ × σ₂) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (fibreSndFun (g₁ := g₁) hg₂ hUo hVo hVi hVne ij) := by
  intro x
  have h1 : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (pieceInv hg₂ hVo hVi hVne ij.2).symm
      (g₁ x.1) :=
    IsLocalDiffeomorphAt.of_eqOn (pieceInv hg₂ hVo hVi hVne ij.2).symm x.2.2 fun _ _ => rfl
  have h2 : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
      (g₁ ∘ N₁.inclusion (fibrePieceSet hg₂ hUo hVo ij)) x :=
    (isLocalDiffeomorph_inclusion N₁ _ x).comp 𝓘(𝕜, E) M (hg₁ x.1)
  exact h2.comp 𝓘(𝕜, E) N₂ h1

/-- Kollár's `τ₂`: the second projection. -/
def fibreSnd [Countable σ₁] [Countable σ₂] :
    AnalyticMap (fibreManifold (g₁ := g₁) hg₂ hUo hVo) N₂ :=
  ⟨fun w => fibreSndFun hg₂ hUo hVo hVi hVne w.1 w.2,
    ContMDiff.sigmaDesc (M := fun ij => (fibrePiece (g₁ := g₁) hg₂ hUo hVo ij : Type u))
      (contMDiff_fibreSndFun hg₂ hUo hVo hVi hVne)⟩

theorem fibreSnd_apply [Countable σ₁] [Countable σ₂]
    (w : fibreManifold (g₁ := g₁) hg₂ hUo hVo) :
    fibreSnd hg₂ hUo hVo hVi hVne w = (pieceInv hg₂ hVo hVi hVne w.1.2).symm (g₁ w.2.1) := rfl

/-- [Kol07, Proposition 37] (ii) / Theorem 105: `(∐ Uᵢ ∩ g₁⁻¹(g₂ Vⱼ), τ₁, τ₂)` is a
fibre product of `g₁` and `g₂`. -/
theorem isFibreProduct_fibre [Countable σ₁] [Countable σ₂]
    (hg₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g₁)
    (hUd : Pairwise (Disjoint on U)) (hUcov : (⋃ i, U i) = univ) (hVd : Pairwise (Disjoint on V))
    (hVcov : (⋃ j, V j) = univ) :
    IsFibreProduct g₁ g₂ (fibreFst (g₁ := g₁) hg₂ hUo hVo) (fibreSnd hg₂ hUo hVo hVi hVne) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsLocalDiffeomorph.sigmaDesc
      (M := fun ij => (fibrePiece (g₁ := g₁) hg₂ hUo hVo ij : Type u))
      fun ij => isLocalDiffeomorph_inclusion N₁ _
  · exact IsLocalDiffeomorph.sigmaDesc
      (M := fun ij => (fibrePiece (g₁ := g₁) hg₂ hUo hVo ij : Type u))
      (isLocalDiffeomorph_fibreSndFun hg₂ hUo hVo hVi hVne hg₁)
  · rintro ⟨ij, x⟩
    change g₁ x.1 = g₂ ((pieceInv hg₂ hVo hVi hVne ij.2).symm (g₁ x.1))
    exact ((pieceInv hg₂ hVo hVi hVne ij.2).right_inv x.2.2).symm
  · intro x y hxy
    have hx : x ∈ ⋃ i, U i := hUcov ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hy : y ∈ ⋃ j, V j := hVcov ▸ mem_univ y
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    have hxij : x ∈ fibrePieceSet (g₁ := g₁) hg₂ hUo hVo (i, j) := ⟨hi, ⟨y, hj, hxy.symm⟩⟩
    refine ⟨⟨(i, j), ⟨x, hxij⟩⟩, ⟨rfl, ?_⟩, ?_⟩
    · change (pieceInv hg₂ hVo hVi hVne j).symm (g₁ x) = y
      rw [hxy]
      exact (pieceInv hg₂ hVo hVi hVne j).left_inv hj
    · rintro ⟨⟨i', j'⟩, ⟨x', hx'⟩⟩ ⟨h1, h2⟩
      change x' = x at h1
      change (pieceInv hg₂ hVo hVi hVne j').symm (g₁ x') = y at h2
      subst h1
      have hi' : i' = i := by
        by_contra hne
        have hd : Disjoint (U i') (U i) := hUd hne
        exact hd.notMem_of_mem_left hx'.1 hi
      have hj' : j' = j := by
        by_contra hne
        have hmem : (pieceInv hg₂ hVo hVi hVne j').symm (g₁ x') ∈ V j' :=
          (pieceInv hg₂ hVo hVi hVne j').map_target hx'.2
        rw [h2] at hmem
        have hd : Disjoint (V j') (V j) := hVd hne
        exact hd.notMem_of_mem_left hmem hj
      subst hi'
      subst hj'
      rfl

end Construction

/-- Two coproducts of open embeddings into `M` have a fibre product. -/
theorem exists_isFibreProduct (g₁ : AnalyticMap N₁ M) (g₂ : AnalyticMap N₂ M)
    (h₁ : IsCoprodOfOpenEmbeddings g₁) (h₂ : IsCoprodOfOpenEmbeddings g₂) :
    ∃ (P : AnalyticManifold.{u} 𝕜 E) (p₁ : AnalyticMap P N₁) (p₂ : AnalyticMap P N₂),
      IsFibreProduct g₁ g₂ p₁ p₂ := by
  obtain ⟨σ₁, hσ₁, U, hUclo, hUd, hUcov, -, -⟩ := h₁.exists_countable
  obtain ⟨σ₂, hσ₂, V, hVclo, hVd, hVcov, hVi, hVne⟩ := h₂.exists_countable
  have := hσ₁
  have := hσ₂
  exact ⟨fibreManifold (g₁ := g₁) h₂.1 (fun i => (hUclo i).2) (fun j => (hVclo j).2),
    fibreFst h₂.1 _ _, fibreSnd h₂.1 _ _ hVi hVne,
    isFibreProduct_fibre h₂.1 _ _ hVi hVne h₁.1 hUd hUcov hVd hVcov⟩

/-- The fibre product exists as soon as one factor is a coproduct of open embeddings (the other any
local analytic isomorphism): the instance of `isFibreProduct_fibre` with the one piece `N₁`. -/
theorem exists_isFibreProduct_of_isLocalDiffeomorph (g₁ : AnalyticMap N₁ M) (g₂ : AnalyticMap N₂ M)
    (hg₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g₁) (h₂ : IsCoprodOfOpenEmbeddings g₂) :
    ∃ (P : AnalyticManifold.{u} 𝕜 E) (p₁ : AnalyticMap P N₁) (p₂ : AnalyticMap P N₂),
      IsFibreProduct g₁ g₂ p₁ p₂ := by
  obtain ⟨σ₂, hσ₂, V, hVclo, hVd, hVcov, hVi, hVne⟩ := h₂.exists_countable
  have := hσ₂
  exact ⟨fibreManifold (g₁ := g₁) (σ₁ := PUnit.{u + 1}) (U := fun _ => univ) h₂.1
      (fun _ => isOpen_univ) (fun j => (hVclo j).2),
    fibreFst h₂.1 _ _, fibreSnd h₂.1 _ _ hVi hVne,
    isFibreProduct_fibre h₂.1 _ _ hVi hVne hg₁ (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      (iUnion_const univ) hVd hVcov⟩

end Manifold

end
