/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Balanced
public import Hironaka.Algebra.Local.MaximalContact
import Hironaka.Algebra.Local.Marked
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Algebra.Local.PowerSeriesRegular

/-!
# D-balance and MC-invariance of `⟨x₀^m⟩` and `⟨x₀ x₁⟩` in `ℚ⟦x₀, x₁⟧`

The two examples of `Hironaka/Algebra/Local/Balanced.lean` and `MaximalContact.lean` on the
coordinate structure `RegularCoords.mvPowerSeries` of `ℚ⟦x₀, x₁⟧`, whose regularity and
dimension inputs are `Hironaka/Algebra/Local/PowerSeriesRegular.lean`: `⟨x₀^m⟩` is D-balanced
with respect to `m` and MC-invariant with respect to `m ≥ 1`, and `⟨x₀ x₁⟩` is neither with
respect to `2`.
-/

-- The module consists of `example`s only, so it declares nothing public.
set_option linter.privateModule false

namespace IsLocalRing

/-- The coordinate structure `x = X`, `∂ᵢ = pderiv ℚ i` on `ℚ⟦x₀, x₁⟧`. -/
private noncomputable def 𝒞 : RegularCoords (MvPowerSeries (Fin 2) ℚ) 2 :=
  RegularCoords.stdMvPowerSeries ℚ 2

example (m : ℕ) : 𝒞.IsDBalanced (Ideal.span {MvPowerSeries.X 0 ^ m}) m :=
  RegularCoords.isDBalanced_span_singleton_x_pow _ 0 m

example : ¬ 𝒞.IsDBalanced (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}) 2 :=
  RegularCoords.not_isDBalanced_span_singleton_x_mul_x _ (by decide)
    (X_sq_notMem_span_X_mul_X (by decide))

example {m : ℕ} (hm : 1 ≤ m) : 𝒞.IsMCInvariant (Ideal.span {MvPowerSeries.X 0 ^ m}) m :=
  RegularCoords.isMCInvariant_span_singleton_x_pow _ 0 hm

example : ¬ 𝒞.IsMCInvariant (Ideal.span {MvPowerSeries.X 0 * MvPowerSeries.X 1}) 2 :=
  RegularCoords.not_isMCInvariant_span_singleton_x_mul_x _ (by decide)
    (X_sq_notMem_span_X_mul_X (by decide))

end IsLocalRing
