/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
public import Hironaka.Resolution.Analytic.OrderReduction.Basic
import Hironaka.Manifold.FiniteSuccession.Functor.LocalTriples
import Hironaka.Resolution.Analytic.OrderReduction.ClassPullback
import Hironaka.Resolution.Analytic.OrderReduction.LocalMaximalContact
import Hironaka.Resolution.Analytic.OrderReduction.SigmaContact
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Theorem 103, Step 3: the local cover by triples with maximal contact

Step 3 of the proof of [Kol07, Theorem 103] (the global case) covers `X` by open subsets `X^{(j)}`
each carrying a smooth hypersurface of maximal contact `H^{(j)}`; the disjoint union
`H^* := ∐_j H^{(j)} ⊂ ∐_j X^{(j)} =: X^*` is then a smooth hypersurface of maximal contact, and for
`g : X^* → X` the coproduct of the inclusions, Step 2 defines `BO_{n,m}` on
`(X^*, g^* I, g^{-1} E)`. On manifolds this is the local
cover data of the globalization theorem [Kol07, Theorem 105] (`OrderReduction/GlobalizeFam.lean`,
`AnalyticTriple.LocalCoverData`) for the pair of classes `(BOClass m, LocalMCClass m)`: every
triple of `BOClass m` is covered by a triple with a global hypersurface of maximal contact, the
disjoint union of countably many of the neighbourhoods with maximal contact given by
[Kol07, Theorem 80 (2)] (`exists_isPullbackOf_localMCClass`; countably many by second
countability), which lies in `LocalMCClass m` (`localMCClass_pullback_sigmaDescMap`).

The hypothesis (2)(ii) of Theorem 105, that the local class is closed under disjoint unions, is
not available here: a countable disjoint union of triples of `BOClass m` need not have finitely
many nonempty boundary members. The construction is therefore run from the cover data directly.
The class `LocalMCClass m` is closed under pull-back along every local analytic isomorphism
(`localMCClass_of_isPullbackOf`), hence under fibre products of local covers
(`localCoversFibreClosed_localMCClass`), the form in which Theorem 105's proof applies the functor
to `X' ×_X X'`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold.AnalyticTriple

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {m : ℕ}

/-- Step 3 of the proof of [Kol07, Theorem 103] (the cover of `X` by open subsets `X^{(j)}`, the
coproduct `g : X^* → X` of the inclusions, and `BO_{n,m}` "defined on `(X^*, g^* I, g^{-1} E)`"):
every triple of `BOClass m` has a local cover by a triple of `LocalMCClass m`, the disjoint union
of countably many of the neighbourhoods with a hypersurface of maximal contact of
[Kol07, Theorem 80 (2)] (second countability), which lies in `LocalMCClass m`. -/
theorem localCoverData_localMCClass (m : ℕ) :
    AnalyticTriple.LocalCoverData (AnalyticTriple.BOClass (ψ₀ := ψ₀) m)
      (AnalyticTriple.LocalMCClass m) := by
  have := Manifold.finiteDimensional_of_chartIso ψ₀
  refine ⟨fun {M} T hG => ?_⟩
  choose N T' g hg hx hT' hL using AnalyticTriple.exists_isPullbackOf_localMCClass hG
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
  refine AnalyticTriple.localMCClass_pullback_sigmaDescMap hG ι hι fun i => ?_
  have e : T' i.1 = T.pullback (ι i) (hι i).1 :=
    AnalyticTriple.IsPullbackOf.eq (hT' i.1) (T.isPullbackOf_pullback _ _)
  rw [← e]
  exact (hL i.1).2

/-- The class `LocalMCClass m` is closed under pull-back along every local analytic isomorphism:
`BOClass m` is (`boClass_of_isPullbackOf`) and a hypersurface of maximal contact pulls back
(`hasMaximalContact_of_isPullbackOf`). Kollár remarks in Step 2 of the proof of
[Kol07, Theorem 103] that the condition "is also preserved under disjoint unions"; the closure
under pull-backs is the library's form, used without statement in his Step 3. -/
theorem localMCClass_of_isPullbackOf {M N : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
    (hT : AnalyticTriple.LocalMCClass m T) {T' : AnalyticTriple ψ₀ N} {g : AnalyticMap N M}
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hT' : T'.IsPullbackOf T g) :
    AnalyticTriple.LocalMCClass m T' :=
  have := Manifold.finiteDimensional_of_chartIso ψ₀
  ⟨AnalyticTriple.boClass_of_isPullbackOf hT.1 hg hT',
    AnalyticTriple.hasMaximalContact_of_isPullbackOf hT.2 hg hT'⟩

/-- `LocalMCClass m` is closed under fibre products of local covers, the hypothesis under which the
proof of [Kol07, Theorem 105] applies the functor to `X' ×_X X'`: a triple carrying the pull-back
data of a member along the first projection, a local analytic isomorphism, is a member. -/
theorem localCoversFibreClosed_localMCClass (m : ℕ) :
    AnalyticTriple.LocalCoversFibreClosed (AnalyticTriple.BOClass (ψ₀ := ψ₀) m)
      (AnalyticTriple.LocalMCClass m) := by
  intro M N₁ N₂ P T T₁ T₂ g₁ g₂ hc₁ _ p₁ p₂ T₁₂ hp hT₁₂
  exact localMCClass_of_isPullbackOf hc₁.2.1 hp.1 hT₁₂

end Manifold.AnalyticTriple

end
