/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Fibre products of local covers: the closed embedding `(p₁, p₂)`, restriction to opens

The proof of [Kol07, Proposition 37] compares the two pull-backs of a blow-up sequence to
`X'' := ∐_{i ≤ j} Uᵢ ∩ Uⱼ`, the fibre product of the cover with itself (`IsFibreProduct`). For the
family functors the values live on relatively compact opens, so the comparison must be run on a
relatively compact open of the fibre product: for a fibre product `(P, p₁, p₂)` of `g₁ : N₁ → M`
with a coproduct of open embeddings `g₂ : N₂ → M`, the joint map `(p₁, p₂) : P → N₁ × N₂` is a
closed embedding onto the set-theoretic fibre product (`IsFibreProduct.isClosedEmbedding_prodMk`),
so the open `p₁⁻¹(O₁) ∩ p₂⁻¹(O₂)` over relatively compact opens `O₁, O₂` has compact closure
(`isCompact_closure_restrictOpens`), and the restricted projections form a fibre product of the
restricted maps `g₁|_{O₁}, g₂|_{O₂} : Oᵢ → V` (`isFibreProduct_restrict`;
`AnalyticMap.restrictMap`). These are the tools of the globalization of family functors.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Function Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N₁ N₂ P : AnalyticManifold.{u} 𝕜 E}

namespace IsFibreProduct

open Hironaka.Manifold

variable {g₁ : AnalyticMap N₁ M} {g₂ : AnalyticMap N₂ M} {p₁ : AnalyticMap P N₁}
  {p₂ : AnalyticMap P N₂} (hp : IsFibreProduct g₁ g₂ p₁ p₂)
include hp

/-- The joint map `(p₁, p₂)` is injective (the uniqueness clause of the fibre product). -/
theorem injective_prodMk : Function.Injective (fun z : P => (p₁ z, p₂ z)) := by
  intro z w h
  simp only [Prod.mk.injEq] at h
  obtain ⟨u, -, hu⟩ := hp.2.2.2 (p₁ z) (p₂ z) (hp.2.2.1 z)
  exact (hu z ⟨rfl, rfl⟩).trans (hu w ⟨h.1.symm, h.2.symm⟩).symm

/-- The range of `(p₁, p₂)` is the set-theoretic fibre product. -/
theorem range_prodMk :
    Set.range (fun z : P => (p₁ z, p₂ z)) = {xy : N₁ × N₂ | g₁ xy.1 = g₂ xy.2} := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hz⟩
    simp only [Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact hp.2.2.1 z
  · intro h
    obtain ⟨z, ⟨hz₁, hz₂⟩, -⟩ := hp.2.2.2 x y h
    exact ⟨z, Prod.ext hz₁ hz₂⟩

theorem isClosed_range_prodMk : IsClosed (Set.range (fun z : P => (p₁ z, p₂ z))) := by
  rw [hp.range_prodMk]
  exact isClosed_eq (g₁.contMDiff.continuous.comp continuous_fst)
    (g₂.contMDiff.continuous.comp continuous_snd)

omit hp in
theorem continuous_prodMk : Continuous (fun z : P => (p₁ z, p₂ z)) :=
  p₁.contMDiff.continuous.prodMk p₂.contMDiff.continuous

/-- `(p₁, p₂)` is inducing when `g₂` is a coproduct of open embeddings: near `z`, a point `w` with
`p₁ w` in a small image `p₁(Z₀)` and `p₂ w` in the clopen piece of `p₂ z` equals the point of `Z₀`
over `p₁ w`, by the injectivity of `p₁` on `p₂⁻¹` of a piece (`injOn_fst`). -/
theorem isInducing_prodMk (hg₂ : IsCoprodOfOpenEmbeddings g₂) :
    IsInducing (fun z : P => (p₁ z, p₂ z)) := by
  refine isInducing_iff_nhds.mpr fun z => le_antisymm ?_ ?_
  · exact ((continuous_prodMk (p₁ := p₁) (p₂ := p₂)).tendsto z).le_comap
  · intro Z hZ
    rw [mem_comap]
    obtain ⟨Φ, hzΦ, hΦ⟩ := (hp.1 z).exists_partialDiffeomorph
    obtain ⟨-, σ, V, hVclo, -, hVcov, hVi⟩ := hg₂
    have hz₂ : p₂ z ∈ ⋃ j, V j := by rw [hVcov]; exact mem_univ _
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz₂
    set Z₀ : Set P := interior Z ∩ Φ.source ∩ p₂ ⁻¹' V j with hZ₀
    have hZ₀o : IsOpen Z₀ :=
      (isOpen_interior.inter Φ.open_source).inter ((hVclo j).2.preimage p₂.contMDiff.continuous)
    have hzZ₀ : z ∈ Z₀ := ⟨⟨mem_interior_iff_mem_nhds.mpr hZ, hzΦ⟩, hj⟩
    have himg : ⇑p₁ '' Z₀ = Φ '' Z₀ := EqOn.image_eq (hΦ.mono fun w hw => hw.1.2)
    have hopen : IsOpen (⇑p₁ '' Z₀) := by
      rw [himg]
      exact (Φ.toOpenPartialHomeomorph.isOpen_image_iff_of_subset_source
        fun w hw => hw.1.2).mpr hZ₀o
    refine ⟨(⇑p₁ '' Z₀) ×ˢ V j, (hopen.prod (hVclo j).2).mem_nhds ⟨⟨z, hzZ₀, rfl⟩, hj⟩, ?_⟩
    rintro w ⟨⟨w', hw', hww'⟩, hw₂⟩
    have hw'₂ : w' ∈ p₂ ⁻¹' V j := hw'.2
    have : w' = w := hp.injOn_fst (hVi j) hw'₂ hw₂ hww'
    rw [← this]
    exact interior_subset hw'.1.1

/-- [Kol07, Proposition 37] at the family level, the topological core: `(p₁, p₂)` is a closed
embedding when `g₂` is a coproduct of open embeddings. -/
theorem isClosedEmbedding_prodMk (hg₂ : IsCoprodOfOpenEmbeddings g₂) :
    IsClosedEmbedding (fun z : P => (p₁ z, p₂ z)) :=
  ⟨⟨hp.isInducing_prodMk hg₂, hp.injective_prodMk⟩, hp.isClosed_range_prodMk⟩

omit hp in
/-- The open `p₁⁻¹(O₁) ∩ p₂⁻¹(O₂)` of the fibre product over opens `O₁ ⊆ N₁`, `O₂ ⊆ N₂`. -/
def restrictOpens (p₁ : AnalyticMap P N₁) (p₂ : AnalyticMap P N₂) (O₁ : Opens N₁) (O₂ : Opens N₂) :
    Opens P :=
  ⟨⇑p₁ ⁻¹' (O₁ : Set N₁) ∩ ⇑p₂ ⁻¹' (O₂ : Set N₂),
    (O₁.isOpen.preimage p₁.contMDiff.continuous).inter (O₂.isOpen.preimage p₂.contMDiff.continuous)⟩

omit hp in
theorem mem_restrictOpens {O₁ : Opens N₁} {O₂ : Opens N₂} {z : P} :
    z ∈ (restrictOpens p₁ p₂ O₁ O₂ : Set P) ↔ p₁ z ∈ (O₁ : Set N₁) ∧ p₂ z ∈ (O₂ : Set N₂) :=
  Iff.rfl

omit hp in
theorem image_fst_restrictOpens (O₁ : Opens N₁) (O₂ : Opens N₂) :
    ⇑p₁ '' (restrictOpens p₁ p₂ O₁ O₂ : Set P) ⊆ O₁ := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz.1

omit hp in
theorem image_snd_restrictOpens (O₁ : Opens N₁) (O₂ : Opens N₂) :
    ⇑p₂ '' (restrictOpens p₁ p₂ O₁ O₂ : Set P) ⊆ O₂ := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz.2

/-- The first projection maps `p₁⁻¹(O₁) ∩ p₂⁻¹(O₂)` onto `O₁` when `g₁(O₁) ⊆ g₂(O₂)`. -/
theorem image_fst_restrictOpens_eq {O₁ : Opens N₁} {O₂ : Opens N₂}
    (h : ⇑g₁ '' (O₁ : Set N₁) ⊆ ⇑g₂ '' (O₂ : Set N₂)) :
    ⇑p₁ '' (restrictOpens p₁ p₂ O₁ O₂ : Set P) = O₁ := by
  refine subset_antisymm (image_fst_restrictOpens O₁ O₂) fun x hx => ?_
  obtain ⟨y, hy, hyx⟩ := h (mem_image_of_mem g₁ hx)
  obtain ⟨z, ⟨hz₁, hz₂⟩, -⟩ := hp.2.2.2 x y hyx.symm
  exact ⟨z, ⟨by rw [mem_preimage, hz₁]; exact hx, by rw [mem_preimage, hz₂]; exact hy⟩, hz₁⟩

/-- The second projection maps `p₁⁻¹(O₁) ∩ p₂⁻¹(O₂)` onto `O₂` when `g₂(O₂) ⊆ g₁(O₁)`. -/
theorem image_snd_restrictOpens_eq {O₁ : Opens N₁} {O₂ : Opens N₂}
    (h : ⇑g₂ '' (O₂ : Set N₂) ⊆ ⇑g₁ '' (O₁ : Set N₁)) :
    ⇑p₂ '' (restrictOpens p₁ p₂ O₁ O₂ : Set P) = O₂ := by
  refine subset_antisymm (image_snd_restrictOpens O₁ O₂) fun y hy => ?_
  obtain ⟨x, hx, hxy⟩ := h (mem_image_of_mem g₂ hy)
  obtain ⟨z, ⟨hz₁, hz₂⟩, -⟩ := hp.2.2.2 x y hxy
  exact ⟨z, ⟨by rw [mem_preimage, hz₁]; exact hx, by rw [mem_preimage, hz₂]; exact hy⟩, hz₂⟩

/-- The restriction of a fibre product to opens `O₁ ⊆ N₁`, `O₂ ⊆ N₂` mapping into `V ⊆ M` is a
fibre product of the restricted maps `g₁|_{O₁}, g₂|_{O₂} : Oᵢ → V`. -/
theorem isFibreProduct_restrict (O₁ : Opens N₁) (O₂ : Opens N₂) (V : Opens M)
    (h₁ : ⇑g₁ '' (O₁ : Set N₁) ⊆ V) (h₂ : ⇑g₂ '' (O₂ : Set N₂) ⊆ V) :
    IsFibreProduct (AnalyticMap.restrictMap g₁ O₁ V h₁) (AnalyticMap.restrictMap g₂ O₂ V h₂)
      (AnalyticMap.restrictMap p₁ (restrictOpens p₁ p₂ O₁ O₂) O₁ (image_fst_restrictOpens O₁ O₂))
      (AnalyticMap.restrictMap p₂ (restrictOpens p₁ p₂ O₁ O₂) O₂
        (image_snd_restrictOpens O₁ O₂)) := by
  refine ⟨AnalyticMap.isLocalDiffeomorph_restrictMap hp.1 _ _ _,
    AnalyticMap.isLocalDiffeomorph_restrictMap hp.2.1 _ _ _, fun z => ?_, fun x y hxy => ?_⟩
  · exact Subtype.ext (hp.2.2.1 z.1)
  · have hxy' : g₁ x.1 = g₂ y.1 := congrArg Subtype.val hxy
    obtain ⟨z, ⟨hz₁, hz₂⟩, huniq⟩ := hp.2.2.2 x.1 y.1 hxy'
    refine ⟨⟨z, ⟨by rw [mem_preimage, hz₁]; exact x.2, by rw [mem_preimage, hz₂]; exact y.2⟩⟩,
      ⟨Subtype.ext hz₁, Subtype.ext hz₂⟩, ?_⟩
    rintro ⟨w, hw⟩ ⟨hw₁, hw₂⟩
    exact Subtype.ext (huniq w ⟨congrArg Subtype.val hw₁, congrArg Subtype.val hw₂⟩)

/-- Relative compactness descends to the fibre product: the closure of `p₁⁻¹(O₁) ∩ p₂⁻¹(O₂)` lies
in the preimage of the compact `closure O₁ × closure O₂` under the closed embedding `(p₁, p₂)`. -/
theorem isCompact_closure_restrictOpens (hg₂ : IsCoprodOfOpenEmbeddings g₂) {O₁ : Opens N₁}
    (hO₁ : IsCompact (closure (O₁ : Set N₁))) {O₂ : Opens N₂}
    (hO₂ : IsCompact (closure (O₂ : Set N₂))) :
    IsCompact (closure (restrictOpens p₁ p₂ O₁ O₂ : Set P)) := by
  have hce := hp.isClosedEmbedding_prodMk hg₂
  have hK : IsCompact ((fun z : P => (p₁ z, p₂ z)) ⁻¹'
      (closure (O₁ : Set N₁) ×ˢ closure (O₂ : Set N₂))) := hce.isCompact_preimage (hO₁.prod hO₂)
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_
    ((isClosed_closure.prod isClosed_closure).preimage hce.continuous))
  rintro z ⟨hz₁, hz₂⟩
  exact ⟨subset_closure hz₁, subset_closure hz₂⟩

end IsFibreProduct

end Manifold

end
