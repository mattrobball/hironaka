/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.TotalTransform
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1BlowUp
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1ExistsComap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Measure
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nonmonomial part of a marked transform, one blow-up at a time

Step 1 of the proof of [Kol07, Theorem 107] (item 111) applies order reduction to the nonmonomial
part `N(𝓘)` and observes that the transform of `N(𝓘)` and the marked transform of `(𝓘, m)` differ
by a product of powers of the exceptional divisors, hence only in their monomial part, so that along
the whole sequence `Π` one has `N(Π_*^{-1}(𝓘, m)) = Π_*^{-1} N(𝓘)`. This file proves the
blow-up-by-blow-up content of that remark, in the form `N(π_*^{-1}(𝓘, m)) = N(π^* N(𝓘))` with the
total transform on the right, for a blow-up `π` with centre `Y` having simple normal crossings with
the boundary family
`F` and for the transformed family `F' = F.totalTransform π Y` (the strict transforms of the members
followed by the exceptional divisor):

* the total transform `π^* 𝓘` and the marked transform `π_*^{-1}(𝓘, m)` have the same nonmonomial
  part with respect to `F'`, because they differ by a power of the exceptional ideal
  (`BMO/Step1BlowUp.lean`), which the nonmonomial part ignores;
* the total transform of `𝓘 = M(𝓘) · N(𝓘)` is `π^*(M(𝓘)) · π^*(N(𝓘))`, and the factor `π^*(M(𝓘))`
  is a monomial in the components of `F'` (`BMO/Step1ExistsComap.lean`), so `π^* 𝓘` and `π^* N(𝓘)`
  have the same nonmonomial part;
* hence `N_{F'}(π_*^{-1}(𝓘, m)) = N_{F'}(π^* N(𝓘))`, the one-step form of Kollár's remark.

The file also records that the nonmonomial part and the total transform of an ideal sheaf that is
nonzero at every point are nonzero at every point, and that the monomial part is the unit ideal when
every component exponent vanishes.
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M}
  {c : ℕ} {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M} (hY : IsClosedSubmanifold ψ Y c)
  (h : IsBlowUp ψ Y c π) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- For `m ≤ ord_Y J` along the centre, the total transform `π^* J` and the marked transform
`π_*^{-1}(J, m)` have the same nonmonomial part with respect to the transformed boundary family
`F'`: the total transform is the `m`-th power
of the exceptional ideal times the marked transform
(`totalTransform_eq_exc_pow_mul_birationalTransform`), and the nonmonomial part ignores powers of
the exceptional ideal (`nonmonomialPart_exceptionalIdealSheaf_pow_mul`), the marked transform being
nonzero at every point. -/
theorem nonmonomialPart_totalTransform_eq_nonmonomialPart_birationalTransform (m : ℕ)
    {J : IdealSheaf (structureSheaf 𝕜 E M)}
    (hk : ∀ x ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J x)
    (hJmt : (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.IsNonzeroEverywhere) :
    nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (J.pullback π h.contMDiff) =
      nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I := by
  rw [totalTransform_eq_exc_pow_mul_birationalTransform hY h hk,
    nonmonomialPart_exceptionalIdealSheaf_pow_mul hY h F hF hsnc m _ hJmt]

/-- The total transform of `𝓘` is the product of the total transforms of its monomial and
nonmonomial parts, `π^* 𝓘 = π^*(M(𝓘)) · π^*(N(𝓘))`: from `𝓘 = M(𝓘) · N(𝓘)` and the multiplicativity
of the total transform. -/
theorem totalTransform_eq_totalTransform_monomialPart_mul_nonmonomialPart
    (I : IdealSheaf (structureSheaf 𝕜 E M)) :
    I.pullback π h.contMDiff =
      (monomialPart F hF I).pullback π h.contMDiff *
        (nonmonomialPart F hF I).pullback π h.contMDiff := by
  conv_lhs => rw [← monomialPart_mul_nonmonomialPart F hF I]
  rw [IdealSheaf.pullback_mul]

/-- The total transforms of `𝓘` and of its nonmonomial part `N(𝓘)` have the same nonmonomial part
with respect to the transformed boundary family `F'`: writing `π^* 𝓘 = π^*(M(𝓘)) · π^*(N(𝓘))`, the
factor `π^*(M(𝓘))` is a locally finite product of powers of the component ideals of `F'`
(`exists_comap_monomialPart_eq_monomial`), which the nonmonomial part ignores
(`nonmonomialPart_locallyFiniteProduct_pow_mul`) as long as the other factor is nonzero at every
point. -/
theorem nonmonomialPart_totalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart
    (I : IdealSheaf (structureSheaf 𝕜 E M))
    (hNnz : ((nonmonomialPart F hF I).pullback π h.contMDiff).IsNonzeroEverywhere) :
    nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (I.pullback π h.contMDiff) =
      nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        ((nonmonomialPart F hF I).pullback π h.contMDiff) := by
  obtain ⟨a, ha⟩ := exists_comap_monomialPart_eq_monomial hY h F hF hsnc I
  rw [totalTransform_eq_totalTransform_monomialPart_mul_nonmonomialPart h F hF I, ha]
  exact nonmonomialPart_locallyFiniteProduct_pow_mul (F.totalTransform π Y)
    (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc) a
    ((nonmonomialPart F hF I).pullback π h.contMDiff) hNnz

/-- For `m ≤ ord_Y J` along the centre, the nonmonomial part of the marked transform of `(J, m)`
equals the nonmonomial part of the total transform of `N(J)`, both with respect to the transformed
boundary family:
`N_{F'}(π_*^{-1}(J, m)) = N_{F'}(π^* N(J))`. This is the one-blow-up form of the remark in [Kol07,
111, Step 1] that the two transforms differ only in their monomial part, obtained by composing
`nonmonomialPart_totalTransform_eq_nonmonomialPart_birationalTransform` with
`nonmonomialPart_totalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart`. -/
theorem nonmonomialPart_birationalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart
    (m : ℕ) {J : IdealSheaf (structureSheaf 𝕜 E M)}
    (hk : ∀ x ∈ Y, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J x)
    (hJmt : (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I.IsNonzeroEverywhere)
    (hNnz : ((nonmonomialPart F hF J).pullback π h.contMDiff).IsNonzeroEverywhere) :
    nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        (MarkedIdealSheaf.birationalTransform hY h ⟨J, m⟩).I =
      nonmonomialPart (F.totalTransform π Y) (HypersurfaceFamily.isSnc_totalTransform hY h hF hsnc)
        ((nonmonomialPart F hF J).pullback π h.contMDiff) :=
  (nonmonomialPart_totalTransform_eq_nonmonomialPart_birationalTransform hY h F hF hsnc m hk
    hJmt).symm.trans
    (nonmonomialPart_totalTransform_eq_nonmonomialPart_totalTransform_nonmonomialPart hY h F hF hsnc
      J hNnz)

include hY in
/-- The total transform along a blow-up of an ideal sheaf that is nonzero at every point is nonzero
at every point: its stalk is the image of a nonzero stalk under the injective germ map of the
blow-up. -/
theorem isNonzeroEverywhere_totalTransform {J : IdealSheaf (structureSheaf 𝕜 E M)}
    (hJ : J.IsNonzeroEverywhere) : (J.pullback π h.contMDiff).IsNonzeroEverywhere := by
  intro a' hbot
  rw [IdealSheaf.stalkIdeal_pullback] at hbot
  exact hJ (π a')
    ((Ideal.map_eq_bot_iff_of_injective (IsBlowUp.germMap_injective hY h a')).mp hbot)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The monomial part is the unit ideal when every component exponent vanishes: each factor is then
`𝓘_D ^ 0 = 1`. -/
theorem monomialPart_eq_top_of_forall_componentExponent_eq_zero
    (I : IdealSheaf (structureSheaf 𝕜 E M))
    (hzero : ∀ i : ComponentIndex F, componentExponent F hF I i = 0) :
    monomialPart F hF I = ⊤ := by
  refine IdealSheaf.ext fun x => ?_
  rw [stalkIdeal_monomialPart, IdealSheaf.stalkIdeal_top, ← Ideal.one_eq_top]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [componentFactor, hzero i, IdealSheaf.stalkIdeal_pow, pow_zero]

end Hironaka.Manifold.BMO
