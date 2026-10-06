/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
public import Hironaka.Resolution.Analytic.OrderReduction.Basic
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.Submanifold.DisjointUnion
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Hypersurfaces of maximal contact on disjoint unions

Step 2 of the proof of [Kol07, Theorem 103] notes that the existence of a hypersurface of maximal
contact "is also preserved under disjoint unions", and Step 3 uses it: the disjoint union
`H^* := ∐_j H^{(j)} ⊂ ∐_j X^{(j)} =: X^*` "is a smooth hypersurface of maximal contact". On
manifolds: a triple which is the disjoint union of triples each carrying a global hypersurface of
maximal contact carries one, namely the union `H := ⋃ᵢ ιᵢ(Hᵢ)` of the images of the pieces'
hypersurfaces along the open embeddings `ιᵢ` with pairwise disjoint ranges covering `M`. `H` is
closed (its complement is the open union of the images `ιᵢ(Hᵢᶜ)`), it is a closed submanifold of
codimension one (the adapted charts of `Hᵢ` transported along `ιᵢ`), and its ideal sheaf lies in
`MC(𝓘)`: at a point `ιᵢ y` both stalks are read on the piece, the pull-back of the ideal sheaf of
`H` along `ιᵢ` being the ideal sheaf of `Hᵢ`, the pull-back of `MC(𝓘)` being `MC(ιᵢ^* 𝓘)`, and the
germ map of a local isomorphism being bijective.

* `AnalyticTriple.closedUnderSigma_hasMaximalContact` — the class of triples with a global
  hypersurface of maximal contact is closed under countable disjoint unions (Kollár's disjoint
  unions of triples, [Kol07, Warning 38]);
* `AnalyticTriple.localMCClass_pullback_sigmaDescMap` — the pull-back of a triple of `BOClass m`
  along the coproduct `∐ᵢ ιᵢ` of countably many open embeddings whose pulled-back triples have
  maximal contact lies in `LocalMCClass m`; this is the class statement of Step 3 of the proof of
  Theorem 103, that `BO_{n,m}` "is defined on `(X^*, g^* I, g^{-1} E)`" by Step 2.
-/

public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

-- The finite-dimensionality `[FiniteDimensional 𝕜 E]` of the model space belongs to every statement
-- here, as to Kollár's varieties; a proof that does not need it names it (`have _hfd := hfd`) so
-- that it remains part of the statement.

section Union

variable {M : AnalyticManifold.{u} 𝕜 E} {σ : Type u} {N : σ → AnalyticManifold.{u} 𝕜 E}
  (ι : ∀ i, AnalyticMap (N i) M) (hι : ∀ i, IsAnalyticOpenEmbedding (ι i))
  (hdisj : Pairwise fun i j => Disjoint (Set.range (ι i)) (Set.range (ι j)))
  (hcov : (⋃ i, Set.range (ι i)) = Set.univ) (Y : ∀ i, Set (N i))

end Union

section Stalks

variable {M N : AnalyticManifold.{u} 𝕜 E}

end Stalks

/-- "This condition is also preserved under disjoint unions" (Step 2 of the proof of
[Kol07, Theorem 103]; Step 3: the disjoint union `H^* := ∐_j H^{(j)}` "is a smooth hypersurface
of maximal contact"): the class of triples with a global hypersurface of maximal contact is closed
under countable disjoint unions. `H := ⋃ᵢ ιᵢ(Hᵢ)` is a closed hypersurface
(`IsClosedSubmanifold.iUnion_image`) and its ideal sheaf lies in `MC(𝓘)` stalkwise at `ιᵢ y`, both
stalks read on the `i`-th piece through the bijective germ map of `ιᵢ`. -/
theorem AnalyticTriple.closedUnderSigma_hasMaximalContact (m : ℕ) :
    AnalyticTriple.ClosedUnderSigma (AnalyticTriple.HasMaximalContact (ψ₀ := ψ₀) m) := by
  have _hfd := hfd
  intro σ _ N Ts M T ι hσ hmc
  obtain ⟨hι, hdisj, hcov, hTs⟩ := hσ
  choose H hH hle using hmc
  refine ⟨⋃ i, ⇑(ι i) '' H i, IsClosedSubmanifold.iUnion_image ι hι hdisj hcov H hH, ?_⟩
  rw [IdealSheaf.le_def]
  intro x
  have hx : x ∈ ⋃ i, Set.range (ι i) := hcov ▸ Set.mem_univ x
  obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp hx
  refine IdealSheaf.stalkIdeal_le_of_comap_le (hι i).1 y ?_
  -- the pull-back of `𝓘_H` along `ιᵢ` is `𝓘_{Hᵢ}`, that of `MC(𝓘)` is `MC(ιᵢ^*𝓘)`
  have h1 : (IsClosedSubmanifold.iUnion_image ι hι hdisj hcov H hH).idealSheaf.pullback _ (ι
      i).contMDiff = (hH i).idealSheaf := by
    rw [comap_idealSheaf_of_isLocalDiffeomorph ψ₀ (ι i) (hι i).1]
    refine IsClosedSubmanifold.idealSheaf_congr _ _ ?_
    rw [← Set.preimage_inter_range, iUnion_image_inter_range ι hι hdisj H i,
      Set.preimage_image_eq (H i) (hι i).2]
  have h2 : (T.I.iteratedDeriv (m - 1)).pullback _ (ι i).contMDiff =
      ((Ts i).I).iteratedDeriv (m - 1) := by
    rw [(hTs i).1]
    exact (iteratedDeriv_pullback_of_isLocalDiffeomorph (⇑(ι i)) (ι i).contMDiff T.I (hι i).1
      (m - 1)).symm
  rw [h1, h2]
  exact IdealSheaf.le_def.mp (hle i) y

/-- Step 3 of the proof of [Kol07, Theorem 103] (`H^*` is a hypersurface of maximal contact, so
`BO_{n,m}` "is defined on `(X^*, g^* I, g^{-1} E)`" by Step 2): the pull-back of a triple
of the class `BOClass m` along the coproduct `∐ᵢ ιᵢ` of countably many open embeddings whose
pulled-back triples have maximal contact lies in `LocalMCClass m`; it is in `BOClass m` by
pull-back along a local isomorphism, and has maximal contact by the closure under disjoint unions
applied to the disjoint-union decomposition of the pull-back (`isSigmaOf_pullback_sigmaDescMap`). -/
theorem AnalyticTriple.localMCClass_pullback_sigmaDescMap {m : ℕ} {M : AnalyticManifold.{u} 𝕜 E}
    {T : AnalyticTriple ψ₀ M} (hT : AnalyticTriple.BOClass m T) {σ : Type u} [Countable σ]
    {N : σ → AnalyticManifold.{u} 𝕜 E} (ι : ∀ i, AnalyticMap (N i) M)
    (hι : ∀ i, IsAnalyticOpenEmbedding (ι i))
    (hmc : ∀ i, AnalyticTriple.HasMaximalContact m (T.pullback (ι i) (hι i).1)) :
    AnalyticTriple.LocalMCClass m
      (T.pullback (sigmaDescMap ι) (isLocalDiffeomorph_sigmaDescMap ι fun i => (hι i).1)) := by
  have _hfd := hfd
  refine ⟨AnalyticTriple.boClass_of_isPullbackOf hT
    (isLocalDiffeomorph_sigmaDescMap ι fun i => (hι i).1) (T.isPullbackOf_pullback _ _), ?_⟩
  exact AnalyticTriple.closedUnderSigma_hasMaximalContact m _ _ _
    (isSigmaOf_pullback_sigmaDescMap ι T (fun i => (hι i).1) _ fun i =>
      T.isPullbackOf_pullback _ _) hmc

end Manifold

end
