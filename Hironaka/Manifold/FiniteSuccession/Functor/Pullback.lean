/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
import Hironaka.Manifold.Chart.Transport
import Hironaka.Manifold.IdealSheaf.Order
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.LocalDiffeomorph
import Hironaka.Manifold.Snc.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The pulled-back triple `(N, h^* 𝓘, h⁻¹(E))` along a local analytic isomorphism

The pullback data of a triple `(X, I, E)` along a smooth morphism `h : Y → X` form a triple
([Kol07, Definition 30, 30.1]; [Kol07, 34.1], "`B(Y, h^* I, h⁻¹(E))`"). On manifolds, for a
local analytic isomorphism `h : N → M`: the inverse image ideal sheaf `h^* 𝓘` (`comap`) has
nonzero stalks because the stalk map of a local isomorphism is a ring isomorphism
(`ord_pullback_of_isLocalDiffeomorphAt`: `ν_b(h^* 𝓘) = ν_{h b}(𝓘)`, and `ν = ⊤` iff the stalk
is zero); the inverse image family `h⁻¹(E)` is a simple normal crossings divisor because its
components are the preimages of closed hypersurfaces
(`IsClosedSubmanifold.preimage_of_isLocalDiffeomorph`), local finiteness pulls back along
continuous maps, and a simple normal crossings chart at `h a` transported along a local inverse of
`h` (`transportChart`) is such a chart at `a`.

* `IdealSheaf.isNonzeroEverywhere_comap`, `HypersurfaceFamily.isSnc_comap`;
* `AnalyticTriple.pullback T h hh : AnalyticTriple ψ₀ N`, `isPullbackOf_pullback`, `ext'`,
  `IsPullbackOf.eq` (the pullback data determine the triple).

The arguments are routine and not in the source.
-/

@[expose] public section

noncomputable section

open Set Topology Function
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The model chart iso `ψ₀ : E ≃L[𝕜] 𝕜ⁿ` makes `E` finite-dimensional (the standing hypothesis of
order theory, `IdealSheaf.ord_eq_top_iff`). -/
theorem finiteDimensional_of_chartIso (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) : FiniteDimensional 𝕜 E :=
  ψ₀.symm.toLinearEquiv.finiteDimensional

/-- Nonzero stalks pull back along a local analytic isomorphism: the stalk map at `b` is an
isomorphism onto the stalk at `h b` (`ord_pullback_of_isLocalDiffeomorphAt`, read
through `ν = ⊤ ↔ stalk = 0`). -/
theorem IdealSheaf.isNonzeroEverywhere_comap [FiniteDimensional 𝕜 E]
    {I : AnalyticManifold.IdealSheaf M}
    (hI : I.IsNonzeroEverywhere) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) : (I.pullback h h.contMDiff).IsNonzeroEverywhere
        := by
  intro b hb
  have h1 : (I.pullback h h.contMDiff).ord b = ⊤ := (IdealSheaf.ord_eq_top_iff (J := I.pullback h
      h.contMDiff) b).mpr hb
  have h2 : I.ord (h b) = ⊤ :=
    (IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt (φ := h) (hφ := h.contMDiff) I
      (hh b)).symm.trans h1
  exact hI (h b) ((IdealSheaf.ord_eq_top_iff (J := I) (h b)).mp h2)

/-- The simple normal crossings property pulls back along a local analytic isomorphism: the
components are the preimages of closed hypersurfaces, local finiteness pulls back, and an snc chart
at `h a` transported along a local inverse of `h` is an snc chart at `a`. -/
theorem HypersurfaceFamily.isSnc_comap {F : HypersurfaceFamily M} (hF : F.IsSnc ψ₀)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (F.comap h).IsSnc ψ₀ := by
  refine ⟨fun j => (hF.isClosedSubmanifold j).preimage_of_isLocalDiffeomorph hh,
    hF.locallyFinite.preimage_continuous h.contMDiff.continuous, fun a => ?_⟩
  obtain ⟨Φ, haΦ, hΦ⟩ := (hh a).exists_partialDiffeomorph
  obtain ⟨φ, c, hφ⟩ := hF.exists_isSncChartAt (h a)
  refine ⟨transportChart Φ.symm φ, fun j => c ⟨j.1, j.2⟩,
    transportChart_mem_maximalAtlas _ hφ.1, ?_, ?_, ?_⟩
  · rw [transportChart_source]
    refine ⟨haΦ, ?_⟩
    change Φ a ∈ φ.source
    rw [← hΦ haΦ]
    exact hφ.2.1
  · intro j x hx
    rw [transportChart_source] at hx
    obtain ⟨hxΦ, hxφ⟩ := hx
    have hx' : h x ∈ φ.source := by
      rw [hΦ hxΦ]
      exact hxφ
    rw [transportChart_apply]
    change h x ∈ F.hyp j.1 ↔ ψ₀ (φ (Φ x)) (c ⟨j.1, j.2⟩) = 0
    rw [← hΦ hxΦ]
    exact hφ.2.2.1 ⟨j.1, j.2⟩ (h x) hx'
  · intro j j' hjj'
    exact Subtype.ext (congrArg Subtype.val (hφ.2.2.2 hjj'))

namespace AnalyticTriple

/-- [Kol07, Definition 30, 30.1], 34.1: **the pulled-back triple** `(N, h^* 𝓘, h⁻¹(E))`
of `T = (M, 𝓘, E)` along a local analytic isomorphism `h : N → M`. -/
def pullback (T : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) : AnalyticTriple ψ₀ N where
  I := T.I.pullback h h.contMDiff
  isNonzeroEverywhere :=
    haveI := finiteDimensional_of_chartIso ψ₀
    IdealSheaf.isNonzeroEverywhere_comap T.isNonzeroEverywhere h hh
  F := T.F.comap h
  isSnc := HypersurfaceFamily.isSnc_comap T.isSnc h hh

/-- The pulled-back triple carries the pullback data (`isPullbackOf_pullback`). -/
theorem isPullbackOf_pullback (T : AnalyticTriple ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) : (T.pullback h hh).IsPullbackOf T h :=
  ⟨rfl, rfl⟩

/-- A triple is its ideal sheaf and its divisor (the other fields are proofs). -/
theorem ext' {T₁ T₂ : AnalyticTriple ψ₀ M} (hI : T₁.I = T₂.I) (hF : T₁.F = T₂.F) : T₁ = T₂ := by
  cases T₁
  cases T₂
  cases hI
  cases hF
  rfl

/-- The pullback data determine the triple. -/
theorem IsPullbackOf.eq {T₁ T₂ : AnalyticTriple ψ₀ N} {T : AnalyticTriple ψ₀ M}
    {h : AnalyticMap N M} (h₁ : T₁.IsPullbackOf T h) (h₂ : T₂.IsPullbackOf T h) : T₁ = T₂ :=
  ext' (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)

end AnalyticTriple

end Manifold

end
