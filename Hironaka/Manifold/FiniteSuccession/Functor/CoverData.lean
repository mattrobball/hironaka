/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Basic
public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
public import Hironaka.Manifold.SigmaManifold
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.LocalTriples
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackInj
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
public import Hironaka.Manifold.FiniteSuccession.Functor.SigmaDesc
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaLocalDiffeo
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Local covers, coproducts of open embeddings and fibre products

The covering and fibre-product steps of the proof of [Kol07, Theorem 105] on manifolds. (i) From
clause (2) of the theorem (every point has a local triple over it along an open embedding, and the
local triples are closed under countable disjoint unions), every global triple has a local cover
(`exists_isLocalCover_of_globalizationData`): choose `𝓜`-morphisms `gₓᵢ : Uₓᵢ → X` whose images
cover `X` (countably many by second countability), and let `g : X' := ∐ᵢ Uₓᵢ → X` be the induced
map (`sigmaManifold`). (ii) The two projections `τ₁, τ₂ : X'' → X'` of the fibre product
`X'' := X' ×_X X'` are again surjections in `𝓜`: with a coproduct of open embeddings they are
coproducts of open embeddings (pieces the preimages of the other factor's pieces) and surjective
(`IsFibreProduct.isCoprodOfOpenEmbeddings_fst/_snd`, `surjective_fst/_snd`), the pull-back data
along the two projections agree (`isPullbackOf_pullback_fst_snd`), and coproducts of open
embeddings compose (`IsCoprodOfOpenEmbeddings.comp`). (iii) The convention of [Kol07, 32] for the
descended list: a list whose pull-back along a surjective local analytic isomorphism has no empty
centre has none (`noEmptyCenters_of_pullback_of_surjective`).
-/

@[expose] public section

noncomputable section

open Set Topology Function
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N N₁ N₂ P : AnalyticManifold.{u} 𝕜 E}

/-! ### [Kol07, 32] for the descended list -/

/-- A list whose pull-back along a surjective local analytic isomorphism has no empty centre has
none (the centres pull back to their preimages, empty only if empty). -/
theorem _root_.AnalyticManifold.BlowUpSequence.noEmptyCenters_of_pullback_of_surjective : ∀
    {M N : AnalyticManifold.{u} 𝕜 E}
    (L : AnalyticManifold.BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜,
        E) 𝓘(𝕜, E) ω h),
    Function.Surjective h → (L.pullback h hh).NoEmptyCenters → L.NoEmptyCenters
  | _, _, AnalyticManifold.BlowUpSequence.nil _, _, _, _, _ =>
      AnalyticManifold.BlowUpSequence.noEmptyCenters_nil
  | _, _, AnalyticManifold.BlowUpSequence.cons hY rest, h, hh, hs, hL => by
    rw [AnalyticManifold.BlowUpSequence.pullback_cons,
        AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff] at hL
    rw [AnalyticManifold.BlowUpSequence.noEmptyCenters_cons_iff]
    obtain ⟨hne, hrest⟩ := hL
    refine ⟨fun h0 => hne ?_,
        AnalyticManifold.BlowUpSequence.noEmptyCenters_of_pullback_of_surjective rest _ _
      (AnalyticManifold.BlowUpSequence.surjective_liftStep h hh hY hs) hrest⟩
    rw [h0]
    exact Set.preimage_empty

/-! ### Coproducts of open embeddings -/

/-- Coproducts of open embeddings compose (pieces `Vⱼ ∩ k⁻¹(Uᵢ)`). -/
theorem IsCoprodOfOpenEmbeddings.comp {h : AnalyticMap N M} {k : AnalyticMap P N}
    (hh : IsCoprodOfOpenEmbeddings h) (hk : IsCoprodOfOpenEmbeddings k) :
    IsCoprodOfOpenEmbeddings (h.comp k) := by
  obtain ⟨hh₁, σ, U, hUclo, hUd, hUcov, hUi⟩ := hh
  obtain ⟨hk₁, τ, V, hVclo, hVd, hVcov, hVi⟩ := hk
  refine ⟨AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hh₁ hk₁, σ × τ, fun ij =>
      k ⁻¹' U ij.1 ∩ V ij.2,
    fun ij => ((hUclo _).preimage k.contMDiff.continuous).inter (hVclo _), ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hjj : j ≠ j' := fun e => hne (e ▸ rfl)
      have hd : Disjoint (V j) (V j') := hVd hjj
      exact hd.mono inter_subset_right inter_subset_right
    · have hd : Disjoint (U i) (U i') := hUd hii
      exact (hd.preimage k).mono inter_subset_left inter_subset_left
  · refine eq_univ_of_forall fun x => ?_
    have h1 : k x ∈ ⋃ i, U i := hUcov ▸ mem_univ _
    have h2 : x ∈ ⋃ j, V j := hVcov ▸ mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp h1
    obtain ⟨j, hj⟩ := mem_iUnion.mp h2
    exact mem_iUnion.mpr ⟨(i, j), hi, hj⟩
  · rintro ⟨i, j⟩ x hx x' hx' heq
    exact hVi j hx.2 hx'.2 (hUi i hx.1 hx'.1 heq)

/-- A functor commuting with all surjective local analytic isomorphisms commutes with the
surjections of any class. -/
theorem AnalyticBlowUpSequenceAssignment.CommutesWithSurjectiveLocalIsos.commutesWithSurjectionsIn
    {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    {B : AnalyticBlowUpSequenceAssignment ψ₀ Dom} (hB : B.CommutesWithSurjectiveLocalIsos)
    (𝓜 : ∀ {M N : AnalyticManifold.{u} 𝕜 E}, AnalyticMap N M → Prop) :
    B.CommutesWithSurjectionsIn 𝓜 :=
  fun T T' h hh _ hs hT' => hB T T' h hh hs hT'

/-! ### The projections of a fibre product -/

namespace IsFibreProduct

variable {g₁ : AnalyticMap N₁ M} {g₂ : AnalyticMap N₂ M} {p₁ : AnalyticMap P N₁}
  {p₂ : AnalyticMap P N₂} (hp : IsFibreProduct g₁ g₂ p₁ p₂)
include hp

theorem comp_eq : g₁.comp p₁ = g₂.comp p₂ := ContMDiffMap.ext hp.2.2.1

theorem surjective_fst (hs : Function.Surjective g₂) : Function.Surjective p₁ := fun x => by
  obtain ⟨y, hy⟩ := hs (g₁ x)
  obtain ⟨z, ⟨hz₁, -⟩, -⟩ := hp.2.2.2 x y hy.symm
  exact ⟨z, hz₁⟩

theorem surjective_snd (hs : Function.Surjective g₁) : Function.Surjective p₂ := fun y => by
  obtain ⟨x, hx⟩ := hs (g₂ y)
  obtain ⟨z, ⟨-, hz₂⟩, -⟩ := hp.2.2.2 x y hx
  exact ⟨z, hz₂⟩

theorem injOn_fst {V : Set N₂} (hV : InjOn g₂ V) : InjOn p₁ (p₂ ⁻¹' V) := by
  intro w hw w' hw' heq
  have hg : g₂ (p₂ w) = g₂ (p₂ w') := by
    rw [← hp.2.2.1, ← hp.2.2.1, heq]
  have h2 : p₂ w = p₂ w' := hV hw hw' hg
  obtain ⟨z, -, hz⟩ := hp.2.2.2 (p₁ w) (p₂ w) (hp.2.2.1 w)
  exact (hz w ⟨rfl, rfl⟩).trans (hz w' ⟨heq.symm, h2.symm⟩).symm

theorem injOn_snd {U : Set N₁} (hU : InjOn g₁ U) : InjOn p₂ (p₁ ⁻¹' U) := by
  intro w hw w' hw' heq
  have hg : g₁ (p₁ w) = g₁ (p₁ w') := by
    rw [hp.2.2.1, hp.2.2.1, heq]
  have h1 : p₁ w = p₁ w' := hU hw hw' hg
  obtain ⟨z, -, hz⟩ := hp.2.2.2 (p₁ w) (p₂ w) (hp.2.2.1 w)
  exact (hz w ⟨rfl, rfl⟩).trans (hz w' ⟨h1.symm, heq.symm⟩).symm

/-- The proof of [Kol07, Theorem 105] (the two projections `τ₁, τ₂ : X'' → X'` are surjective and
in `𝓜`): the first projection of a fibre product with a coproduct of open embeddings is one — its
pieces the preimages under `p₂` of the pieces of `g₂`. -/
theorem isCoprodOfOpenEmbeddings_fst (h₂ : IsCoprodOfOpenEmbeddings g₂) :
    IsCoprodOfOpenEmbeddings p₁ := by
  obtain ⟨-, σ, V, hVclo, hVd, hVcov, hVi⟩ := h₂
  refine ⟨hp.1, σ, fun k => p₂ ⁻¹' V k, fun k => (hVclo k).preimage p₂.contMDiff.continuous,
    fun k k' hne => ?_, ?_, fun k => hp.injOn_fst (hVi k)⟩
  · have hd : Disjoint (V k) (V k') := hVd hne
    exact hd.preimage p₂
  · rw [← preimage_iUnion, hVcov, preimage_univ]

theorem isCoprodOfOpenEmbeddings_snd (h₁ : IsCoprodOfOpenEmbeddings g₁) :
    IsCoprodOfOpenEmbeddings p₂ := by
  obtain ⟨-, σ, U, hUclo, hUd, hUcov, hUi⟩ := h₁
  refine ⟨hp.2.1, σ, fun k => p₁ ⁻¹' U k, fun k => (hUclo k).preimage p₁.contMDiff.continuous,
    fun k k' hne => ?_, ?_, fun k => hp.injOn_snd (hUi k)⟩
  · have hd : Disjoint (U k) (U k') := hUd hne
    exact hd.preimage p₁
  · rw [← preimage_iUnion, hUcov, preimage_univ]

/-- The pull-back data of `T₁` along `p₁` are the pull-back data of `T₂` along `p₂` when `T₁`, `T₂`
carry the pull-back data of `T` along `g₁`, `g₂`. -/
theorem isPullbackOf_pullback_fst_snd {T : AnalyticTriple ψ₀ M} {T₁ : AnalyticTriple ψ₀ N₁}
    {T₂ : AnalyticTriple ψ₀ N₂} (h₁ : T₁.IsPullbackOf T g₁) (h₂ : T₂.IsPullbackOf T g₂) :
    (T₁.pullback p₁ hp.1).IsPullbackOf T₂ p₂ := by
  refine ⟨?_, ?_⟩
  · change T₁.I.pullback p₁ p₁.contMDiff = T₂.I.pullback p₂ p₂.contMDiff
    rw
        [h₁.1, h₂.1, AnalyticManifold.IdealSheaf.pullback_comp,
            AnalyticManifold.IdealSheaf.pullback_comp,
      hp.comp_eq]
  · change T₁.F.comap p₁ = T₂.F.comap p₂
    rw [h₁.2, h₂.2, HypersurfaceFamily.comap_comap, HypersurfaceFamily.comap_comap]
    exact congrArg (fun f => HypersurfaceFamily.comap f T.F) (funext hp.2.2.1)

end IsFibreProduct

/-! ### The disjoint union of a family of open embeddings -/

section SigmaCover

variable {σ : Type u} [Countable σ] {N : σ → AnalyticManifold.{u} 𝕜 E}
  (ι : ∀ i, AnalyticMap (N i) M)

/-- The proof of [Kol07, Theorem 105]: the map `∐ᵢ Uₓᵢ → X` induced by a family. -/
def sigmaDescMap : AnalyticMap (sigmaManifold N) M :=
  ⟨fun p => ι p.1 p.2, ContMDiff.sigmaDesc (M := fun i => (N i : Type u)) fun i => (ι i).contMDiff⟩

theorem sigmaDescMap_apply (p : sigmaManifold N) : sigmaDescMap ι p = ι p.1 p.2 := rfl

theorem sigmaDescMap_comp_sigmaMk (i : σ) : (sigmaDescMap ι).comp (sigmaMk N i) = ι i :=
  ContMDiffMap.ext fun _ => rfl

theorem isLocalDiffeomorph_sigmaDescMap (hι : ∀ i, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ι i)) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sigmaDescMap ι) :=
  IsLocalDiffeomorph.sigmaDesc (M := fun i => (N i : Type u)) hι

/-- The induced map of a family of analytic open embeddings is a coproduct of open embeddings. -/
theorem isCoprodOfOpenEmbeddings_sigmaDescMap (hι : ∀ i, IsAnalyticOpenEmbedding (ι i)) :
    IsCoprodOfOpenEmbeddings (sigmaDescMap ι) := by
  refine ⟨isLocalDiffeomorph_sigmaDescMap ι fun i => (hι i).1, σ, fun i => range (sigmaMk N i),
    fun i => ?_, pairwise_disjoint_range_sigmaMk N, iUnion_range_sigmaMk N, fun i => ?_⟩
  · exact isClopen_range_of_cover (sigmaMk N) (isAnalyticOpenEmbedding_sigmaMk N)
      (pairwise_disjoint_range_sigmaMk N) (iUnion_range_sigmaMk N) i
  · rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ h
    exact congrArg (sigmaMk N i) ((hι i).2 h)

theorem surjective_sigmaDescMap (hcov : (⋃ i, range (ι i)) = univ) :
    Function.Surjective (sigmaDescMap ι) :=
  (surjective_sigmaDesc_iff (M := fun i => (N i : Type u)) fun i => ⇑(ι i)).mpr hcov

/-- The pull-back data along the induced map are the disjoint union of the pull-back data along
the members of the family. -/
theorem isSigmaOf_pullback_sigmaDescMap (T : AnalyticTriple ψ₀ M)
    (hι : ∀ i, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (ι i)) (Ts : ∀ i, AnalyticTriple ψ₀ (N i))
    (hTs : ∀ i, (Ts i).IsPullbackOf T (ι i)) :
    (T.pullback (sigmaDescMap ι) (isLocalDiffeomorph_sigmaDescMap ι hι)).IsSigmaOf Ts
      (sigmaMk N) := by
  refine AnalyticTriple.isSigmaOf_sigma N _ Ts fun i => ⟨?_, ?_⟩
  · change (Ts i).I = (T.I.pullback _ (sigmaDescMap ι).contMDiff).pullback _ (sigmaMk N i).contMDiff
    rw [AnalyticManifold.IdealSheaf.pullback_comp, sigmaDescMap_comp_sigmaMk]
    exact (hTs i).1
  · change (Ts i).F = (T.F.comap (sigmaDescMap ι)).comap (sigmaMk N i)
    rw [HypersurfaceFamily.comap_comap]
    exact (hTs i).2

end SigmaCover

/-- The first step of the proof of [Kol07, Theorem 105]: under clause (2), every global triple has
a local cover by a local triple — the disjoint union of countably many of the local triples over
its points (second countability), with the induced map. -/
theorem AnalyticTriple.exists_isLocalCover_of_globalizationData
    {GT LT : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    (D : AnalyticTriple.GlobalizationData GT LT) (T : AnalyticTriple ψ₀ M) (hG : GT T) :
    ∃ (N : AnalyticManifold.{u} 𝕜 E) (T' : AnalyticTriple ψ₀ N) (g : AnalyticMap N M),
      AnalyticTriple.IsLocalCover GT LT T T' g := by
  choose N T' g hg hx hT' hL using D.exists_isPullbackOf T hG
  obtain ⟨t, ht, hcov⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x : M => range (g x))
    fun x => (hg x).isOpen_range
  have := ht.to_subtype
  let ι : ∀ i : t, AnalyticMap (N i.1) M := fun i => g i.1
  have hι : ∀ i, IsAnalyticOpenEmbedding (ι i) := fun i => hg i.1
  have hcov' : (⋃ i : t, range (ι i)) = univ := by
    refine eq_univ_of_forall fun y => ?_
    have hy : y ∈ ⋃ x ∈ t, range (g x) := by
      rw [hcov]
      exact mem_iUnion.mpr ⟨y, hx y⟩
    obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion.mpr ⟨⟨x, hxt⟩, hyx⟩
  refine ⟨sigmaManifold fun i : t => N i.1,
    T.pullback (sigmaDescMap ι) (isLocalDiffeomorph_sigmaDescMap ι fun i => (hι i).1),
    sigmaDescMap ι, hG, ?_, isCoprodOfOpenEmbeddings_sigmaDescMap ι hι,
    surjective_sigmaDescMap ι hcov', T.isPullbackOf_pullback _ _⟩
  exact D.closedUnderSigma (fun i : t => T' i.1) _ (sigmaMk _)
    (isSigmaOf_pullback_sigmaDescMap ι T (fun i => (hι i).1) _ fun i => hT' i.1) fun i => hL i.1

/-! ### Local cover data (generalisation, in place) -/

/-- The single hypothesis the construction of [Kol07, Theorem 105] uses: **every global triple has a
local cover** by a local triple.
`GlobalizationData` supplies it through `exists_isLocalCover_of_globalizationData`
(`toLocalCoverData`); the classes of the global case of the proof of [Kol07, Theorem 103]
(`BOClass`, not closed under countable disjoint unions) supply it directly
(`localCoverData_localMCClass`). -/
structure AnalyticTriple.LocalCoverData
    (GT LT : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop) : Prop where
  /-- Every global triple has a local cover. -/
  exists_isLocalCover : ∀ {M : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M), GT T →
    ∃ (N : AnalyticManifold.{u} 𝕜 E) (T' : AnalyticTriple ψ₀ N) (g : AnalyticMap N M),
      AnalyticTriple.IsLocalCover GT LT T T' g

/-- Clause (2) of [Kol07, Theorem 105] provides the local cover data (step (i) of its proof). -/
theorem AnalyticTriple.GlobalizationData.toLocalCoverData
    {GT LT : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
    (D : AnalyticTriple.GlobalizationData GT LT) : AnalyticTriple.LocalCoverData GT LT :=
  ⟨fun T hG => AnalyticTriple.exists_isLocalCover_of_globalizationData D T hG⟩

end Manifold

end
