/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
public import Hironaka.Manifold.Chart.Transport
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The pull-back of a hypersurface of maximal contact

[Kol07, Theorem 103 (2)] for the local functor of Steps 1 and 2 uses that the hypersurface of
maximal contact chosen from the class for the pulled-back triple may be replaced by the pull-back
of the one chosen for the original triple (Step 2.3 of the proof; a hypersurface of maximal contact
pulls back along a local analytic isomorphism, as Kollár uses in [Kol07, 104, Step 2.3]).

* `AnalyticTriple.idealSheaf_preimage_le_iteratedDeriv_pullback` — the pull-back of a hypersurface
  of maximal contact has maximal contact for the pulled-back ideal sheaf.

It enters the commutation of the local functor in the compatible-family form
(`LocalFunctorFam.lean`).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- A hypersurface of maximal contact pulls back along a local analytic isomorphism: if the ideal
sheaf of `H` lies in the `r`-th derivative ideal sheaf of `𝓘`, then the ideal sheaf of `h⁻¹(H)`
lies in the `r`-th derivative ideal sheaf of the pull-back of `𝓘` (the inequality behind
`hasMaximalContact_of_isPullbackOf`, for the explicit preimage). Not in the sources as a separate
statement. -/
theorem AnalyticTriple.idealSheaf_preimage_le_iteratedDeriv_pullback
    {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {H : Set M} (hH : IsClosedSubmanifold ψ₀ H 1)
    {r : ℕ} (hle : hH.idealSheaf ≤ T.I.iteratedDeriv r) :
    (hH.preimage_of_isLocalDiffeomorph hh).idealSheaf ≤ (T.pullback h hh).I.iteratedDeriv r :=
  (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh hH).symm.trans_le
    ((IdealSheaf.pullback_le_pullback (φ := ⇑h) (hφ := h.contMDiff) hle).trans_eq
      (iteratedDeriv_pullback_of_isLocalDiffeomorph (⇑h) h.contMDiff T.I hh r).symm)

end Manifold

end
