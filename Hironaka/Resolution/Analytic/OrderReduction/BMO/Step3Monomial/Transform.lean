/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.TransformStalk
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The marked transform of the monomial ideal under the blow-up of a centre

The marked transform `π_*^{-1}(M(𝓘), m)` of the monomial ideal along a centre of the monomial
procedure is the monomial ideal of the transformed piece family
(`Realizes.birationalTransform_monomialIdeal`): the old pieces keep their exponents on their strict
transforms, and the new piece of each face `P` carries `total P − m`, as in [Kol07, 111, Step 3].
Stalk by stalk, the marked transform is the exact quotient of the total transform by the `m`-th
power of the exceptional ideal ([Kol07, Definition 60, (60.1)]): off the exceptional divisor both
ideals agree with the total transform; over the locus of `P` the total transform is `𝓘_F^{total P}`
times the strict transforms (`BMO/Step3Monomial/TransformStalk.lean`), so dividing by `𝓘_F^m` leaves
`𝓘_F^{total P − m}`, the colon of a principal power in the regular analytic stalk, a domain. The
identification uses the uniqueness of the exact quotient.
-/

public section

open Set Topology Hironaka.Monomial IsLocalRing
open scoped Manifold ContDiff

universe u

/-- In a domain, the colon of a principal power out of a product with a larger principal power:
`(J · (u^t)) : (u^m) = J · (u^{t−m})` for `m ≤ t` and `u ≠ 0`. -/
theorem Ideal.colon_mul_span_singleton_pow {R : Type*} [CommRing R] [IsDomain R] (J : Ideal R)
    {u : R} (hu : u ≠ 0) {m t : ℕ} (hmt : m ≤ t) :
    (J * Ideal.span {u ^ t}).colon ↑(Ideal.span {u ^ m}) = J * Ideal.span {u ^ (t - m)} := by
  ext r
  rw [Submodule.mem_colon, mul_comm J, mul_comm J]
  constructor
  · intro h
    have hr := h (u ^ m) (Ideal.mem_span_singleton_self _)
    rw [smul_eq_mul, Ideal.mem_span_singleton_mul] at hr
    obtain ⟨z, hz, hzr⟩ := hr
    rw [Ideal.mem_span_singleton_mul]
    refine ⟨z, hz, ?_⟩
    have hum : u ^ m ≠ 0 := pow_ne_zero _ hu
    apply mul_left_cancel₀ hum
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmt, hzr, mul_comm]
  · intro h s hs
    rw [Ideal.mem_span_singleton_mul] at h
    obtain ⟨z, hz, hzr⟩ := h
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hs
    rw [smul_eq_mul, Ideal.mem_span_singleton_mul]
    refine ⟨z * a, J.mul_mem_right a hz, ?_⟩
    rw [← hzr]
    have hpow : u ^ t = u ^ (t - m) * u ^ m := by rw [← pow_add, Nat.sub_add_cancel hmt]
    rw [hpow]
    ring

namespace Hironaka.Manifold.BMO.PieceFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E} {Φ : PieceFamily N}
  {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι} {m : ℕ} {hV : Φ.IsValid n m}
  {S : Finset (Finset ℕ)}

/-- The marked transform of the monomial ideal along the locus of a centre is the monomial ideal of
the transformed family ([Kol07, 111, Step 3], [Kol07, Definition 60]): the old pieces keep their
exponents on their strict transforms, and the new piece of each face `P` carries `total P − m`. -/
theorem Realizes.birationalTransform_monomialIdeal (hF : F.IsSnc ψ₀) (hΦ : Φ.Realizes F e)
    (hS : (Φ.toState n m hV).IsCenter S) (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) (faceCard S))
    (hge : ∀ P ∈ S, m ≤ Φ.total P) :
    (MarkedIdealSheaf.birationalTransform hZ (isBlowUp_blowUpπ ψ₀ hZ)
        ⟨Φ.monomialIdeal hF hΦ, m⟩).I =
      (Φ.blowUpPieces S m hZ).monomialIdeal (Φ.isSnc_totalTransform_centerOf hF hΦ hS hZ)
        (hΦ.realizes_blowUpPieces hS hZ) := by
  classical
  set π := Manifold.blowUpπ ψ₀ hZ with hπdef
  have h := isBlowUp_blowUpπ ψ₀ hZ
  have hm : ∀ a ∈ Φ.centerOf S,
      ((m : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hZ.idealSheaf (Φ.monomialIdeal hF hΦ) a :=
    fun a ha => hΦ.le_ordAlongIdeal_monomialIdeal_centerOf hF hS hZ hge ha
  refine IsDivExceptional.unique (isDivExceptional_birationalTransform hZ h _ hm) fun p => ?_
  rw [IsBlowUp.stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk hZ h]
  by_cases hp : π p ∈ Φ.centerOf S
  · -- over the locus of the face `P` through `π p`
    obtain ⟨P, hP, hxP⟩ := Φ.mem_centerOf.mp hp
    rw [Φ.stalkIdeal_monomialIdeal_blowUpPieces_of_mem_faceSet hF hΦ hS hZ hP hxP,
      Φ.stalkIdeal_totalTransform_monomialIdeal_of_mem_faceSet hF hΦ hS hZ hP hxP]
    -- the exceptional divisor's vanishing stalk is principal, generated by an element of order one
    obtain ⟨u, hu, hu1⟩ :=
      (h.isClosedSubmanifold_preimage hZ).exists_generator_stalkIdeal_idealSheaf (x := p) hp
    rw [(h.isClosedSubmanifold_preimage hZ).stalkIdeal_idealSheaf_eq_vanishingStalk] at hu
    have := finiteDimensional_of_chartIso ψ₀
    have hu0 : u ≠ 0 := fun h0 => by
      rw [h0, ordElem_eq_top_iff.mpr rfl] at hu1
      exact ENat.top_ne_one hu1
    have := isDomain_stalk ψ₀ (IsManifold.chart_mem_maximalAtlas p) (mem_chart_source E p)
    rw [hu, Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.colon_mul_span_singleton_pow _ hu0 (hge P hP)]
  · -- off the exceptional divisor: the marked and total transforms agree
    rw [Φ.stalkIdeal_monomialIdeal_blowUpPieces_of_notMem hF hΦ hS hZ hp,
      Φ.stalkIdeal_totalTransform_monomialIdeal_of_notMem hF hΦ hZ hp,
      vanishingStalk_eq_top_of_notMem (hZ.isClosed.preimage h.contMDiff.continuous) hp,
      Ideal.top_pow, Submodule.top_coe]
    ext r
    rw [Submodule.mem_colon]
    constructor
    · intro hr s _
      exact Ideal.mul_mem_right s _ hr
    · intro hr
      simpa using hr 1 (Set.mem_univ 1)

end Hironaka.Manifold.BMO.PieceFamily
