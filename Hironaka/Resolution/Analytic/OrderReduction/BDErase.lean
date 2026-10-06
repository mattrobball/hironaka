/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BDOf
import Hironaka.Manifold.FiniteSuccession.Functor.PushforwardPullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102 (2): commutation with surjective local analytic isomorphisms

Clause (2) of [Kol07, Lemma 102], commutation with smooth morphisms, has two parts in [Kol07, 34.1]:
the functor commutes with smooth surjections, and along an arbitrary smooth morphism its value at
the pull-back is the pull-back of its value with the empty blow-ups deleted. This module completes
the first for `BDan`, the analytic `BD_{n,m,j}`, once the identification
`BlowUpSequence.pushforward_pullback` of the pull-back of a pushed-forward list with the
push-forward of the pulled-back list is available
(`Hironaka/Manifold/FiniteSuccession/Functor/PushforwardPullback.lean`); both parts in the
compatible-family form are `BDanFam_commutesWithLocalIsos` (`BDFamComm.lean`).

* `pushforwardPullback` — the identification, so that `BDan_pullback_of_surjective` (the first
  bullet, `BDOf.lean`) holds outright.
* `AnalyticTriple.bmoClass_pullback` — the marked class is closed under pull-back along local
  analytic isomorphisms (a nonempty pulled-back member comes from a nonempty member).
-/

public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The pull-back along a local analytic isomorphism of the push-forward of a list of centres on a
closed hypersurface is the push-forward of the pull-back along the restricted map:
`BlowUpSequence.pushforward_pullback` at codimension one (which proof of local analyticity is given
for the restricted map does not matter). -/
theorem pushforwardPullback [FiniteDimensional 𝕜 E] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) :
    PushforwardPullback.{u} ψ :=
  fun hS g hg L => AnalyticManifold.BlowUpSequence.pushforward_pullback hS g hg L

/-- The marked class `BMOClass s` is closed under pull-back along local analytic isomorphisms: a
member of the pulled-back boundary is nonempty only if the member it comes from is. -/
theorem _root_.Manifold.AnalyticTriple.bmoClass_pullback {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
    {M N : AnalyticManifold.{u} 𝕜 E} {s : ℕ} {T : AnalyticTriple ψ M}
    (hT : AnalyticTriple.BMOClass s T) (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    AnalyticTriple.BMOClass s (T.pullback g hg) := by
  refine ⟨hT.1, ?_⟩
  have := hT.2
  refine Finite.of_injective
    (fun j : {j // (T.pullback g hg).F.hyp j ≠ ∅} =>
      (⟨j.1, fun h0 => j.2 ?_⟩ : {j // T.F.hyp j ≠ ∅})) ?_
  · change ⇑g ⁻¹' T.F.hyp j.1 = ∅
    rw [h0, Set.preimage_empty]
  · intro a b hab
    exact Subtype.ext (congrArg Subtype.val hab :)

section Assembly

variable [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {m : ℕ} (inp : BMOanData 𝕜 (n - 1) (tuningParam m))

/-- [Kol07, Lemma 102 (2)], the first bullet of [Kol07, 34.1]: **`BD_{n,m,j}` commutes with
surjective local analytic isomorphisms** — `BDan_pullback_of_surjective_of_pushforwardPullback`
with the identification `pushforwardPullback` supplied. -/
theorem BDan_pullback_of_surjective {N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) (hT : AnalyticTriple.BOClass m T)
    (hT' : AnalyticTriple.BOClass m (T.pullback h hh)) (j : T.F.ι) :
    BDan m inp (T.pullback h hh) hT' j = (BDan m inp T hT j).pullback h hh :=
  BDan_pullback_of_surjective_of_pushforwardPullback (pushforwardPullback ψ₀) inp T h hh hs hT hT' j

end Assembly

end Hironaka.Manifold

end
