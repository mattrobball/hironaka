/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.ExceptionalSet
public import Hironaka.Scheme.BlowUp.Defs
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# The exceptional set of the monoidal transformation lies in the exceptional divisor

`exceptionalSet_subset_support_comap` of `Hironaka.Scheme.BlowUp.ExceptionalSet`, stated for the
monoidal transformation of the vocabulary of the main theorems, `I.blowUpπ`: the hypothesis that
the map is an isomorphism over the complement of the centre is
`blowUp.isIso_π_restrict_compl_support` of `Hironaka.Scheme.BlowUp.Glue.Trivial`.
`Hironaka.Scheme.BlowUp.ExceptionalSetSmoothCodim` combines it with the reverse inclusion for a
smooth centre of codimension at least two.

The mathematics ([Kol07, Definition 25]; [Sta, Tag 02OS]).  The exceptional set of `g` is by
definition the set of points with no open neighbourhood on which `g` is an open immersion, so it is
empty exactly when every point has one, which is Mathlib's `IsLocalIso g`.  For the blow-up map
`π`, a point `x'` outside the exceptional divisor has `π x' ∉ Z`, so `x'` lies in the open
`π⁻¹(X ∖ Z)`, on which `π` is the isomorphism `π ∣_ (X ∖ Z)` followed by the open immersion of
`X ∖ Z` — an open immersion; hence `x' ∉ Ex(π)`, i.e. `Ex(π) ⊆ |F|`, where `|F|` is the support of
`I·𝒪_B = I.comap π`, the preimage of `|Z|` (Mathlib's `support_comap`).
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

universe u

/-- The exceptional set of the monoidal transformation lies in the exceptional divisor,
`Ex(π) ⊆ |F|` ([Sta, Tag 02OS]; [Kol07, Definition 25]), because `π` is an isomorphism off the
centre. -/
theorem exceptionalSet_blowUpπ_subset_support
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    I.blowUpπ.exceptionalSet ⊆
        (I.exceptionalDivisor.support : Set I.blowUp) := by
  have := blowUp.isIso_π_restrict_compl_support I
  exact Scheme.Hom.exceptionalSet_subset_support_comap I.blowUpπ I

end AlgebraicGeometry
