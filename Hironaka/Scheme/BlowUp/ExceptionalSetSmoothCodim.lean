/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.ExceptionalSet
public import Hironaka.Scheme.BlowUp.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUp.ExceptionalSetSupport
import Hironaka.Scheme.Smooth.ExceptionalDivisorSmooth
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# The exceptional set of a blow-up along a smooth centre of codimension at least two

For `X` smooth of relative dimension `n` over a field `k` and a closed subscheme `Z` smooth of
relative dimension `n − r` over `k`, `2 ≤ r ≤ n`, the exceptional set of the monoidal
transformation `Z.blowUpπ` is exactly the exceptional divisor `|F|`: the single-blow-up case of
Kollár's remark that for nontrivial blow-ups the exceptional set is the total exceptional divisor
[Kol07, Definition 25].  The two inclusions are `exceptionalSet_blowUpπ_subset_support`
(`Hironaka.Scheme.BlowUp.ExceptionalSetSupport`; the blow-up map is an isomorphism off the centre)
and `support_comap_subset_exceptionalSet` (`Hironaka.Scheme.BlowUp.ExceptionalSetSmooth`) applied
with the smoothness of `F → Z` of relative dimension `r − 1`,
`smoothOfRelativeDimension_exceptionalMap` of `Hironaka.Scheme.Smooth.ExceptionalDivisorSmooth`.

The mathematics.  `Ex(π) ⊆ |F|` because `π` is an isomorphism over `X ∖ Z`.  For `|F| ⊆ Ex(π)`,
let `x' ∈ F` and suppose `π` is an open immersion on an open `U' ∋ x'`.  Then `F ∩ U' → Z`, the
base change of `π|_{U'}` along `Z → X`, is an open immersion, hence smooth of relative dimension
`0`; it is also the restriction of `F → Z` to the open `F ∩ U'` of `F`, hence smooth of relative
dimension `r − 1`; its source is nonempty; and a morphism with nonempty source has one relative
dimension (`SmoothOfRelativeDimension.eq_of_nonempty`, from the rank of the Kähler differentials
on an affine piece).  So `r − 1 = 0`, contradicting `r ≥ 2`.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

universe u

/-- **The exceptional set of the blow-up along a smooth centre of codimension `r ≥ 2` is the
exceptional divisor** [Kol07, Definition 25]: for `X` smooth of relative dimension `n` over `k` and
`Z ⊆ X` smooth of relative dimension `n − r` over `k` with `2 ≤ r ≤ n`,
`Ex(Z.blowUpπ) = |Z.exceptionalDivisor|`. -/
theorem exceptionalSet_eq_support {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (n r : ℕ) [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hr : 2 ≤ r) (hrn : r ≤ n) :
    Z.blowUpπ.exceptionalSet =
        (Z.exceptionalDivisor.support : Set Z.blowUp) := by
  refine Set.Subset.antisymm
    (exceptionalSet_blowUpπ_subset_support Z) ?_
  have hsm := smoothOfRelativeDimension_exceptionalMap f n r Z
    (by omega) hrn
  have : SmoothOfRelativeDimension (r - 1)
      (Scheme.IdealSheafData.subschemeMap (Z.comap Z.blowUpπ) Z
          Z.blowUpπ
        (Scheme.IdealSheafData.le_map_comap Z Z.blowUpπ)) := hsm
  exact support_comap_subset_exceptionalSet Z.blowUpπ Z (m := r - 1)
    (by omega)

end AlgebraicGeometry

