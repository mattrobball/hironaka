/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A nonzero ideal sheaf stays nonzero along a blow-up sequence

The disjoined triple of [Kol07, 72] carries the pull-back `π^* I` of the ideal sheaf along the
composite of the disjoining blow-ups, and the domain of the order-reduction functor
(`AnalyticTriple`) asks it to be nonzero at every point, as Hironaka's "coherent sheaf of non-zero
ideals" [Hir64, Main Theorem II(N), p. 176]. Along one blowing-up the germ map is injective
(`IsBlowUp.germMap_injective`), so the stalk of the pull-back — the image of the stalk under the
germ map — is nonzero; along the succession, by induction on the stage through the functoriality
of `comap`. Used for the disjoined input of the order reduction (`DisjoinInput.lean`).
-/

public section

universe u

open AnalyticManifold
open scoped Manifold ContDiff

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}

section BlowUp

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {Y : Set M} {c : ℕ} {π : M' → M}

/-- The pull-back of a nonzero-everywhere ideal sheaf along a blowing-up is nonzero everywhere:
its stalk is the image of a nonzero stalk under the injective germ map. -/
theorem IsBlowUp.isNonzeroEverywhere_pullback (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) {I : IdealSheaf (structureSheaf 𝕜 E M)} (hI : I.IsNonzeroEverywhere) :
    (I.pullback π h.contMDiff).IsNonzeroEverywhere := by
  intro b hb
  rw [IdealSheaf.stalkIdeal_pullback] at hb
  exact hI (π b) ((Ideal.map_eq_bot_iff_of_injective (h.germMap_injective hY b)).mp hb)

end BlowUp

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- Along a blow-up sequence the pull-back of a nonzero-everywhere ideal sheaf to every stage is
nonzero everywhere (induction on the stage; `comap` is functorial). -/
theorem _root_.Hironaka.Manifold.isNonzeroEverywhere_comap_stageMap [FiniteDimensional 𝕜 E]
    {S : FiniteSuccession M}
    {I : AnalyticManifold.IdealSheaf M} (hI : I.IsNonzeroEverywhere) (i : Fin (S.length + 1)) :
    (I.pullback _ (S.stageMap i).contMDiff).IsNonzeroEverywhere := by
  induction i using Fin.induction with
  | zero =>
    rw [FiniteSuccession.stageMap_zero]
    -- the identity is a local analytic isomorphism
    have hid : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ⇑(ContMDiffMap.id : AnalyticMap M M) := by
      have h := (Diffeomorph.refl 𝓘(𝕜, E) M ω).isLocalDiffeomorph
      rw [Diffeomorph.coe_refl] at h
      exact h
    exact IdealSheaf.isNonzeroEverywhere_comap hI ContMDiffMap.id hid
  | succ i ih =>
    rw [FiniteSuccession.stageMap_succ, ← IdealSheaf.pullback_comp]
    exact (S.isBlowUp_map i).isNonzeroEverywhere_pullback (S.isClosedSubmanifold_center i) ih

end Manifold
