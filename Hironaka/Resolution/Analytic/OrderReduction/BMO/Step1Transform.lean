/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Monoid
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Measure
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1MeasureOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nonmonomial part ignores a finite product of component factors

Step 1 of the proof of [Kol07, Theorem 107] (item 111) rests on the remark that the transform of
`N(𝓘)` and the marked transform of `(𝓘, m)` differ by a product of powers of the exceptional
divisors, hence only in their monomial part. The one-component form of that remark,
`N(𝓘_D^a · J) = N(J)` for a component `D` of the boundary (`nonmonomialPart_componentIdeal_pow_mul`,
`BMO/Step1MeasureOrder.lean`), is extended here to a finite product of component factors:
`N((∏_D 𝓘_D^{a_D}) · J) = N(J)`, by induction on the finite set of components, the product staying
nonzero at every point because a factor of a nonzero product is nonzero
(`isNonzeroEverywhere_of_mul_right`).
-/

public section

open Set
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

/-- The nonmonomial part ignores a finite product of component factors:
`N((∏_{i ∈ s} 𝓘_i^{a_i}) · J) = N(J)` whenever the product is nonzero at every point
([Kol07, 111, Step 1]: multiplying by an ideal of boundary divisors changes only the monomial part).
By induction on `s`, peeling off one factor with `nonmonomialPart_componentIdeal_pow_mul`; the
remaining product is nonzero because it is a factor of a nonzero product. -/
theorem nonmonomialPart_finprod_componentIdeal_pow_mul (F : HypersurfaceFamily M) (hF : F.IsSnc ψ)
    (J : IdealSheaf (structureSheaf 𝕜 E M)) (a : ComponentIndex F → ℕ) :
    ∀ (s : Finset (ComponentIndex F)),
      ((∏ i ∈ s, componentIdeal F hF i ^ a i) * J).IsNonzeroEverywhere →
      nonmonomialPart F hF ((∏ i ∈ s, componentIdeal F hF i ^ a i) * J)
        = nonmonomialPart F hF J := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _; rw [Finset.prod_empty, one_mul]
  | @insert j s' hj ih =>
    intro hprod
    rw [Finset.prod_insert hj, mul_assoc] at hprod ⊢
    rw [nonmonomialPart_componentIdeal_pow_mul F hF _
      (isNonzeroEverywhere_of_mul_right hprod) j (a j)]
    exact ih (isNonzeroEverywhere_of_mul_right hprod)

end Hironaka.Manifold.BMO
