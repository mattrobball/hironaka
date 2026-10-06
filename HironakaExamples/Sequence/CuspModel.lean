/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The cusp in the affine plane: a model for Kollár's warning on restriction

"The restriction of a smooth blow-up sequence need not be a smooth blow-up sequence" [Kol07, 30.2].
The example behind this sentence: with `X = 𝔸²`, `Z` the origin and `S` the cuspidal cubic
`(y² = x³)`, blowing up the origin of the plane is a smooth blow-up sequence (its one center is the
reduced point `Spec k`, smooth over `k`), but its restriction to `S = V(y² − x³)` is a blow-up
sequence starting at a scheme that is not smooth over `k`, whereas a smooth blow-up sequence in
Kollár's sense has a smooth ambient scheme at every stage [Kol07, Notation 19].

This module defines the model as named terms, in the pattern of
`HironakaExamples/Sequence/Remark33Model.lean`:

* `affine2 k = Spec k[x, y]` with `x = X 0`, `y = X 1`;
* `originCenter k = V(x, y)` and `cusp k = V(y² − x³)` as ideal sheaves (`specIdealSheaf`);
* `seqOrigin k : BlowUpSequence (affine2 k)`, the blow-up of the origin, of length `1`.

The statements about them are proved in `HironakaExamples/Sequence/CuspWitness.lean` and
`HironakaExamples/Sequence/RestrictClosedImmersion.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial Scheme BlowUpSequence

namespace Hironaka.Sequence.Cusp

variable (k : Type u) [Field k]

/-- The affine plane `𝔸²_k = Spec k[x, y]`, with `x = X 0`, `y = X 1`. -/
noncomputable abbrev affine2 : Scheme.{u} := Spec (.of (MvPolynomial (Fin 2) k))

/-- The ideal `(x, y)` of the origin `0 ∈ 𝔸²_k`. -/
noncomputable abbrev originCenterIdeal : Ideal (MvPolynomial (Fin 2) k) := Ideal.span (Set.range X)

/-- The ideal `(y² − x³)` of the cuspidal cubic. -/
noncomputable abbrev cuspIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {X 1 ^ 2 - X 0 ^ 3}

/-- The origin `Z = V(x, y) ⊂ 𝔸²_k` as an ideal sheaf: the center of the blow-up. -/
noncomputable abbrev originCenter : (affine2 k).IdealSheafData :=
  specIdealSheaf (originCenterIdeal k)

/-- The cuspidal cubic `S = V(y² − x³) ⊂ 𝔸²_k` as an ideal sheaf: the closed subscheme to which
the sequence is restricted. -/
noncomputable abbrev cusp : (affine2 k).IdealSheafData := specIdealSheaf (cuspIdeal k)

/-- The blow-up sequence of length one blowing up the origin of the plane; the sequence of the
example illustrating [Kol07, 30.2]. -/
noncomputable def seqOrigin : BlowUpSequence (affine2 k) := cons _ (originCenter k) (nil _)

/-- The sequence has one blow-up. -/
theorem length_seqOrigin : (seqOrigin k).length = 1 := rfl

end Hironaka.Sequence.Cusp
