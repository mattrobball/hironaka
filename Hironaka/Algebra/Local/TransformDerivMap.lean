/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.TransformDeriv
public import Hironaka.Algebra.Derivative.Basic
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The chart derivative ideal under a ring map carrying the transformed derivations

Kollár's item 75 ends with the observation that "the right-hand sides of these equations are in
`D(π⁻¹_*(f, m))`" [Kol07, 75]: the transported derivations `∂'ⱼ` of the chart ring
(`chartDerivRing`, `Hironaka/Algebra/Local/Chart.lean`) are the partial derivatives of the blow-up
chart, so the chart derivative ideal `D'(K) = K + ∑ⱼ ∂'ⱼ(K)` (`chartD`,
`Hironaka/Algebra/Local/TransformDeriv.lean`) maps into Kollár's derivative ideal of the image. This
module proves that observation abstractly (`map_chartD_le_derivative`): for a ring map `χ` out of
the chart ring and `k`-derivations `δⱼ` of the target with `χ ∘ ∂'ⱼ = δⱼ ∘ χ`, `χ(D'(K)) ⊆ D(χ(K))`,
where `D` is `Ideal.derivative k` of `Hironaka/Algebra/Derivative/Basic.lean` (the ideal generated
by `J` and all `δ f`, `f ∈ J`, `δ` a `k`-derivation).

Used for Theorem 76 on manifolds (`Hironaka/Manifold/BlowUp/Transform/DerivTransform.lean`); the
logarithmic version and a converse are `Hironaka/Algebra/Local/TransformLogDerivMap.lean`.
-/

public section

namespace IsLocalRing.RegularCoords

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (c : RegularCoords R n) (r : Fin n) {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]

/-- For a ring map `χ` out of the chart ring carrying the transported derivations `∂'ⱼ` to
`k`-derivations `δⱼ` of the target, the image of the chart derivative ideal `D'(K)` lies in the
derivative ideal of the image, `χ(D'(K)) ⊆ D(χ(K))` (Kollár's observation in [Kol07, 75]). -/
theorem map_chartD_le_derivative (χ : chartRing c.x r →+* S) (δ : Fin n → Derivation k S S)
    (hδ : ∀ (j : Fin n) (g : chartRing c.x r), χ (c.chartDerivRing r j g) = δ j (χ g))
    (K : Ideal (chartRing c.x r)) :
    Ideal.map χ (c.chartD r K) ≤ Ideal.derivative k (Ideal.map χ K) := by
  rw [Ideal.map_le_iff_le_comap]
  unfold chartD
  refine sup_le ?_ (iSup_le fun j => Ideal.span_le.mpr ?_)
  · exact Ideal.le_comap_map.trans (Ideal.comap_mono (Ideal.le_derivative _))
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, hδ]
    exact Ideal.derivation_apply_mem_derivative (δ j) (Ideal.mem_map_of_mem χ hg)

end IsLocalRing.RegularCoords
