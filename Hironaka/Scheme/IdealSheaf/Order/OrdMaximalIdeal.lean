/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Algebra.Local.Defs
public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Algebra.Local.Order
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.RingTheory.Nakayama

/-!
# The maximal ideal has order one

[Kol07, Definition 47]: the order of an ideal `I` of a local ring is the largest `r` with
`I ⊆ 𝔪^r`. For the maximal ideal itself of a Noetherian local ring that is not a field the order
is exactly `1`: `𝔪 ⊆ 𝔪` and, by Nakayama, `𝔪 ⊆ 𝔪²` would force `𝔪 = 0`. On a locally Noetherian
scheme, an ideal sheaf whose stalk at `x` is the maximal ideal has order `1` at `x`: the order of
the ideal of a reduced component at its generic point, as in the Claim in the proof of
[Wlo05, Theorem 4.7.1], "the order of the controlled transform `σ^c(I)` of `I` is `1` along the
strict transform of `Y₁`".

Used for the embedded resolution (`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedClaimTools.lean`,
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedGenericOrder.lean`).
-/

public section

universe u

open IsLocalRing

namespace AlgebraicGeometry

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The order ([Kol07, Definition 47]) of the maximal ideal of a Noetherian local ring that is not
a field is `1` (Nakayama: `𝔪 ⊆ 𝔪²` forces `𝔪 = 0`). -/
theorem ord_maximalIdeal_eq_one (h : maximalIdeal R ≠ ⊥) : ord (maximalIdeal R) = 1 := by
  refine le_antisymm (iSup_le fun r => iSup_le fun hr => ?_) ?_
  · rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · exact_mod_cast Nat.lt_succ_iff.mp hr2
    · exfalso
      have hsq : maximalIdeal R ≤ maximalIdeal R ^ 2 := hr.trans (Ideal.pow_le_pow_right hr2)
      refine h (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
        (IsNoetherian.noetherian _) ?_ ?_)
      · rw [Ideal.smul_eq_mul, ← pow_two]
        exact hsq
      · rw [jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top]
  · have := le_ord_of_le (I := maximalIdeal R) (r := 1) (by rw [pow_one])
    simpa using this

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

open AlgebraicGeometry

/-- An ideal sheaf whose stalk at `x` is the maximal ideal of a stalk that is not a field has order
`1` at `x`. -/
theorem ord_eq_one_of_stalkIdeal_eq_maximalIdeal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) {x : X} (h : I.stalkIdeal x = maximalIdeal (X.presheaf.stalk x))
    (hne : maximalIdeal (X.presheaf.stalk x) ≠ ⊥) : I.ord x = 1 := by
  rw [ord_eq_ord_stalkIdeal, h]
  exact ord_maximalIdeal_eq_one hne

end AlgebraicGeometry.Scheme.IdealSheafData
