/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
import Hironaka.Manifold.BlowUp.Transform.GermIso
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Functoriality of the pullback data of triples

The inverse image ideal sheaf is functorial (`IdealSheaf.pullback_pullback` of
`Hironaka.Manifold.BlowUp.Transform.GermIso`: pulling back twice is pulling back along the
composite), so the pullback data of triples compose (`AnalyticTriple.IsPullbackOf.comp`, the
analogue of `IsPullbackOf.comp` for schemes), and the pulled-back triples compose
(`AnalyticTriple.pullback_pullback`). This is the functoriality behind the pull-back of blow-up
sequences [Kol07, Definition 30, 30.1] and [Kol07, 34.1].
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold


variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N P : AnalyticManifold.{u} 𝕜 E}

/-- The pullback along analytic maps is functorial (`IdealSheaf.pullback_pullback`, with the
composite as an analytic map). -/
@[simp]
theorem _root_.AnalyticManifold.IdealSheaf.pullback_comp (J : AnalyticManifold.IdealSheaf M)
    (h : AnalyticMap N M) (k : AnalyticMap P N) :
    (J.pullback h h.contMDiff).pullback k k.contMDiff =
      J.pullback (h.comp k) (h.comp k).contMDiff :=
  IdealSheaf.pullback_pullback J h h.contMDiff k k.contMDiff

@[simp]
theorem HypersurfaceFamily.comap_comap {M N P : Type u} (F : HypersurfaceFamily M) (h : N → M)
    (k : P → N) : (F.comap h).comap k = F.comap (h ∘ k) := rfl

namespace AnalyticTriple

/-- [Kol07, 34.1] (`IsPullbackOf.comp`): pullback data compose along composites. -/
theorem IsPullbackOf.comp {T : AnalyticTriple ψ₀ M} {T' : AnalyticTriple ψ₀ N}
    {T'' : AnalyticTriple ψ₀ P} {h : AnalyticMap N M} {k : AnalyticMap P N}
    (h₁ : T'.IsPullbackOf T h) (h₂ : T''.IsPullbackOf T' k) : T''.IsPullbackOf T (h.comp k) := by
  refine ⟨?_, ?_⟩
  · rw [h₂.1, h₁.1, AnalyticManifold.IdealSheaf.pullback_comp]
  · rw [h₂.2, h₁.2]
    rfl

/-- The pulled-back triples compose. -/
theorem pullback_pullback (T : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (k : AnalyticMap P N)
    (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k) :
    (T.pullback h hh).pullback k hk =
      T.pullback (h.comp k) (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hh hk) :=
  IsPullbackOf.eq
    ((T.isPullbackOf_pullback h hh).comp ((T.pullback h hh).isPullbackOf_pullback k hk))
    (T.isPullbackOf_pullback (h.comp k) _)

end AnalyticTriple

end Manifold

end
