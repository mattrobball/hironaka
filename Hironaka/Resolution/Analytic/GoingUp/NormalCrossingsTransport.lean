/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport of normal crossings along a diffeomorphism

Hironaka's normal crossings [Hir64, Definition 2] at the stalk level
(`AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith`) is stated through a regular system
of parameters of the stalk, the minimal primes of the divisor's stalk and generators of the
centre's stalk. All three transport along a ring isomorphism of the stalks, here the germ map of a
diffeomorphism `g : M₁ ≃ M₂` at a point (`germMap`, bijective by
`germMap_bijective_of_isLocalDiffeomorphAt`): the pull-backs `g^* E`, `g^* D` have only normal
crossings when `E`, `D` have. This is the piece of the normal-crossings clause of the push-forward
that concerns the identification `T_i ≃ S_i` of the stages of a sequence with those of the
restricted push-forward ([Kol07, 30.2–30.3]).

* `Ideal.comap_mem_minimalPrimes_of_bijective`: minimal primes over `J S` pull back to minimal
  primes over `J` along a bijective ring map.
* `AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith.pullback_diffeomorph`: the transport
  itself.
-/

public section

noncomputable section

open TopologicalSpace IsLocalRing
open scoped Manifold ContDiff Topology

universe u

/-- A minimal prime over the extension `J S` of an ideal along a bijective ring map pulls back to a
minimal prime over `J`. -/
theorem Ideal.comap_mem_minimalPrimes_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    (e : R →+* S) (he : Function.Bijective e) {J : Ideal R} {P : Ideal S}
    (hP : P ∈ (J.map e).minimalPrimes) : P.comap e ∈ J.minimalPrimes := by
  obtain ⟨⟨hPp, hJP⟩, hmin⟩ := hP
  refine ⟨⟨Ideal.comap_isPrime e P, Ideal.map_le_iff_le_comap.mp hJP⟩, ?_⟩
  intro Q hQ hQle
  have := hQ.1
  have hmapQ : (Q.map e).IsPrime := Ideal.map_isPrime_of_equiv (RingEquiv.ofBijective e he)
  have h1 : P ≤ Q.map e := hmin ⟨hmapQ, Ideal.map_mono hQ.2⟩ (Ideal.map_le_iff_le_comap.mpr hQle)
  calc P.comap e ≤ (Q.map e).comap e := Ideal.comap_mono h1
    _ = Q := Ideal.comap_map_of_bijective e he

namespace AnalyticManifold.IdealSheaf

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M₁ M₂ : AnalyticManifold.{u} 𝕜 E}

/-- Hironaka's normal crossings [Hir64, Definition 2] at the stalk level transport along a
diffeomorphism: for `g : M₁ ≃ M₂` and ideal sheaves `E'`, `D` on `M₂` with `E'` having only normal
crossings with `D`, the pull-backs have only normal crossings; the regular system of parameters,
the minimal primes and the generators of the centre are carried by the (bijective, local) germ map
of `g` at the point. -/
theorem HasOnlyNormalCrossingsWith.pullback_diffeomorph (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M₁ M₂ ω)
    {E' D : IdealSheaf M₂} (h : E'.HasOnlyNormalCrossingsWith D) :
    HasOnlyNormalCrossingsWith (E'.pullback ⇑g g.contMDiff)
      (D.pullback ⇑g g.contMDiff) := by
  intro x hx
  have hgx : g x ∈ D.support := by
    have hx' : x ∈ (D.pullback ⇑g g.contMDiff).support := hx
    rwa [IdealSheaf.support_pullback] at hx'
  obtain ⟨n, z, ⟨hspan, hdim⟩, hmin, s, hD⟩ := h (g x) hgx
  have hbij : Function.Bijective (germMap ⇑g g.contMDiff x) :=
    germMap_bijective_of_isLocalDiffeomorphAt ⇑g g.contMDiff (g.isLocalDiffeomorph x)
  refine ⟨n, fun i => germMap ⇑g g.contMDiff x (z i), ⟨?_, ?_⟩, ?_, s, ?_⟩
  · rw [show (fun i => germMap ⇑g g.contMDiff x (z i)) = germMap ⇑g g.contMDiff x ∘ z from rfl,
      Set.range_comp, ← Ideal.map_span, hspan]
    exact map_maximalIdeal_of_surjective _ hbij.2
  · exact hdim.trans (ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _ hbij))
  · intro P hP
    rw [IdealSheaf.stalkIdeal_pullback] at hP
    obtain ⟨i, hi⟩ := hmin (P.comap (germMap ⇑g g.contMDiff x))
      (Ideal.comap_mem_minimalPrimes_of_bijective _ hbij hP)
    refine ⟨i, ?_⟩
    rw [← Ideal.map_comap_of_surjective _ hbij.2 P, hi, Ideal.map_span, Set.image_singleton]
  · rw [IdealSheaf.stalkIdeal_pullback, hD, Ideal.map_span, ← Set.image_comp]
    rfl

end AnalyticManifold.IdealSheaf

end
