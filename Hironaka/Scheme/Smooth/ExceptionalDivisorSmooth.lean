/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Hironaka.Scheme.BlowUp.Defs
import Hironaka.Scheme.Smooth.DescentRelativeDimension
import Hironaka.Scheme.Smooth.ExceptionalBaseChange
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# The exceptional divisor of a smooth blow-up is smooth over the center, over any field

For a smooth blow-up over an arbitrary field `k` (`X` smooth of relative dimension `n` over `k`,
the center `Z` smooth of relative dimension `n − r`, `1 ≤ r ≤ n`), the exceptional divisor
`F = π⁻¹(Z)` is smooth over the center `Z` of relative dimension `r − 1`
(`smoothOfRelativeDimension_exceptionalMap`): Kollár's "if `π_{Z,X}` is a smooth blow-up, then
`F` … [is] smooth" [Kol07, Notation 19], relative to `Z`, in the vocabulary `exceptionalDivisor`,
`blowUpπ` of the main theorems.

The perfect-field form is `smoothOfRelativeDimension_subschemeMap_exceptional`
(`Hironaka/Scheme/Smooth/ExceptionalDivisor.lean`), proved over the charts of adapted étale
coordinates, which exist only over a perfect field. The general statement follows by descent: with
`K` the algebraic closure of `k` (perfect), `X_K → Spec K` and `Z_K → Spec K` are smooth of relative
dimensions `n` and `n − r` (base change), so `F_K → Z_K` is smooth of relative dimension `r − 1`
over `K`; blowing up commutes with the flat base change `X_K → X` ([Sta, Tag 0805]), so `F_K → Z_K`
is the base change of `F → Z` along `Z_K → Z`, which is surjective, flat and quasi-compact as the
base change of `Spec K → Spec k`; and smoothness of relative dimension `m` descends along such
morphisms ([Sta, Tag 02VL] for smoothness; `descendsAlong_smoothOfRelativeDimension` of
`Hironaka/Scheme/Smooth/DescentRelativeDimension.lean`). The bookkeeping is
`smoothOfRelativeDimension_subschemeMap_exceptional_of_descendsAlong`
(`Hironaka/Scheme/Smooth/ExceptionalBaseChange.lean`). The hypothesis `1 ≤ r` is part of the
statement so that it reads as Kollár's smooth blow-up, whose center has codimension `r ≥ 1` and
whose exceptional divisor has relative dimension `r − 1` over the center ([Kol07, Notation 19]); the
module that uses it, `Hironaka/Scheme/BlowUp/ExceptionalSetSmoothCodim.lean`, supplies it from its
own `2 ≤ r`. The proof does not need it, because it descends from the perfect-field form, whose
chart computation (`ExceptionalModel.lean`) is uniform in `r`, with `r − 1` the truncated
difference.

Used for the codimension of the exceptional set
(`Hironaka/Scheme/BlowUp/ExceptionalSetSmoothCodim.lean`).
-/

public section

open AlgebraicGeometry CategoryTheory Algebra Scheme.IdealSheafData

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- For a smooth blow-up over any field `k` (`X` smooth of relative dimension `n`, the center `Z`
smooth of relative dimension `n − r`, `1 ≤ r ≤ n`), the exceptional divisor is smooth over the
center of relative dimension `r − 1` ([Kol07, Notation 19], relative to `Z`; the projective bundle
of [Hau14, Definition 4.8]). Proved by descent from the perfect-field form. -/
theorem smoothOfRelativeDimension_exceptionalMap
    (f : X ⟶ Spec (.of k)) (n r : ℕ)
    [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (_hr : 1 ≤ r) (hrn : r ≤ n) :
    SmoothOfRelativeDimension (r - 1)
      (Scheme.IdealSheafData.subschemeMap Z.exceptionalDivisor Z Z.blowUpπ
        (Scheme.IdealSheafData.le_map_comap Z Z.blowUpπ)) :=
  smoothOfRelativeDimension_subschemeMap_exceptional_of_descendsAlong f n r Z hrn
    (descendsAlong_smoothOfRelativeDimension (r - 1))

end AlgebraicGeometry

