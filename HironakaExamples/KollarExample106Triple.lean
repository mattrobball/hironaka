/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.Balanced.Example106
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Hironaka.Scheme.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Hironaka.Scheme.Snc.Defs
import Hironaka.Scheme.IdealSheaf.Defs
/-!
# Kollár's Example 106: the triple `(𝔸⁴_ℚ, I, ∅)`

[Kol07, Example 106] follows the principalization of the ideal `I = (x³ − y², x⁴ + xz² − w³)` of a
subvariety `X ⊂ 𝔸⁴`: `I` has order `2`, the hyperplane `H = (y = 0)` is a hypersurface of maximal
contact, the restriction `I|_H = (x³, xz² − w³)` has order `3` with `MC(I|_H) = (x, z, w)`, so the
first step blows up the origin of `𝔸⁴`. On the chart `x₁ = x`, `y₁ = y/x`, `z₁ = z/x`, `w₁ = w/x`
the birational transform is `I₁ = (x₁ − y₁², x₁(x₁ + z₁² − w₁³))` with exceptional divisor
`E₁ = (x₁ = 0)`, and Kollár concludes that "the order has dropped to 1", so that the run continues
with `(I₁, 1, E₁)`; his closing sentences contrast this with the birational transform `X₁` of `X`
on the same chart, which meets the plane `(x₁ = y₁ = 0)` in the cuspidal curve
`(x₁ = y₁ = z₁² − w₁³ = 0)`. The sentence "the order has dropped to 1" holds on the `x`-chart
only: on the chart `x = x₁z₁`, `y = y₁z₁`, `z = z₁`, `w = w₁z₁` the point
`q = [0:0:1:0] ∈ E₁` has `ord_q I₁ = 2` (`I₁ = (x₁³z₁ − y₁², z₁(x₁⁴z₁ + x₁ − w₁³))`), so the
order-reduction functor `BO_{4,2}` continues by blowing up `q` (and further points of order `2`)
before the order-`1` phase begins. The chart computations are in
`HironakaExamples/MaximalContact/Example106Charts.lean` and `Example106Stages.lean`, and in
`HironakaExamples/Balanced/Example106.lean` (`I106`, `m0`, `D(I) = (x², y, z², xz, w²)`,
`cosupp(I, 2) = {0}`).

This file builds the triple `(𝔸⁴_ℚ, I, ∅)` on which the functor is run in
`HironakaExamples/KollarExample106Run.lean`: the coordinate ring `Poly4 = ℚ[x, y, z, w]`, the
affine space `A4 = 𝔸⁴_ℚ`, the ideal sheaf `idealSheafOf I` of an ideal `I ⊆ ℚ[x, y, z, w]`
(`ofIdealTop` of `I` transported along `Γ(𝔸⁴, ⊤) ≅ ℚ[x, y, z, w]`), the `z`-axis
`zAxis = (x, y, w)`, whose strict transform meets `E₁` at `q`, the structure morphism
`𝔸⁴_ℚ → Spec ℚ` (`Spec` of the algebra map `ℚ → ℚ[x, y, z, w]`, the only ring map out of `ℚ`), and
the triple itself.

## Conventions

* **The triple is built from a witness.** `Triple ℚ` demands the structure morphism together with
  its finiteness, separatedness and smoothness instances, the equidimensionality witness, `I ≠ 0`
  on every component and the simple-normal-crossing condition on the (empty) boundary. These facts
  about `𝔸⁴_ℚ` are packaged as the `Prop`-valued structure `WellFormed`, and
  `triple (h : WellFormed)` is built from a witness `h`; by proof irrelevance the triple does not
  depend on the witness. The witness `wellFormed` is proved in the run module, and every statement
  about the functor there takes it and the class membership `hT : BOClass 4 2 (triple h)` as
  hypotheses.
* **Orders and transforms.** `ord` is the order `ord_x J` of [Kol07, Definition 47] on the ideal
  sheaf; the transform `I₁ = π⁻¹_*(I, 2)` at stage `1` is the weak transform `weakTransform m₀ I`,
  the birational transform of the marked ideal `(I, 2)` ([Kol07, Definition 60 and Warning 63]).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial Hironaka Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData Hironaka.Local Hironaka.Examples.Example106

namespace Hironaka.Examples.KollarExample106

/-! ### The triple `(𝔸⁴_ℚ, I, ∅)` -/

section Triple

/-- `x = X 0` in `ℚ[x, y, z, w]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y = X 1` in `ℚ[x, y, z, w]`. -/
local notation "y" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `w = X 3` in `ℚ[x, y, z, w]`. -/
local notation "w" => (X 3 : MvPolynomial (Fin 4) ℚ)

/-- The coordinate ring `ℚ[x, y, z, w]` of Example 106, `x = X 0`, `y = X 1`, `z = X 2`,
`w = X 3`. -/
abbrev Poly4 : Type := MvPolynomial (Fin 4) ℚ

/-- The affine space `𝔸⁴_ℚ` of Example 106. -/
noncomputable abbrev A4 : Scheme := Spec (CommRingCat.of Poly4)

/-- The ideal sheaf of `V(I) ⊆ 𝔸⁴_ℚ` for an ideal `I ⊆ ℚ[x, y, z, w]`: `ofIdealTop` of `I`
transported along `Γ(𝔸⁴, ⊤) ≅ ℚ[x, y, z, w]` (as in `HironakaExamples/KollarExample28_1.lean`). -/
noncomputable def idealSheafOf (I : Ideal Poly4) : A4.IdealSheafData :=
  ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of Poly4)).inv.hom)

/-- The `z`-axis `(x = y = w = 0) ⊆ 𝔸⁴`, whose strict transform meets `E₁` at the point
`q = [0:0:1:0]` of order `2`. -/
noncomputable abbrev zAxis : Ideal Poly4 := Ideal.span {x, y, w}

/-- The structure morphism `𝔸⁴_ℚ → Spec ℚ`: `Spec` of the algebra map `ℚ → ℚ[x, y, z, w]`. -/
noncomputable def structureMap : A4 ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ Poly4))

/-- The well-formedness of the triple `(𝔸⁴_ℚ, I, ∅)` of Example 106 as a triple in the sense of
`AlgebraicGeometry.Triple` ([Kol07, Notation 64]): the structure morphism is locally of finite
type, quasi-compact, separated and smooth, of some relative dimension; `I` is nonzero on every
component; the empty boundary is a simple normal crossing divisor. These are facts about `𝔸⁴_ℚ`,
proved as `wellFormed` in `HironakaExamples/KollarExample106Run.lean`; they are packaged so that
the triple is built from a witness. -/
structure WellFormed : Prop where
  /-- `𝔸⁴_ℚ → Spec ℚ` is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType structureMap
  /-- `𝔸⁴_ℚ → Spec ℚ` is quasi-compact. -/
  quasiCompact : QuasiCompact structureMap
  /-- `𝔸⁴_ℚ → Spec ℚ` is separated. -/
  isSeparated : IsSeparated structureMap
  /-- `𝔸⁴_ℚ → Spec ℚ` is smooth. -/
  smooth : Smooth structureMap
  /-- `𝔸⁴_ℚ → Spec ℚ` is smooth of one relative dimension (Notation 64 (1); it is `4`). -/
  equidim : ∃ n : ℕ, SmoothOfRelativeDimension n structureMap
  /-- `I` is nonzero on every irreducible component (Notation 64 (2)). -/
  isNonzeroEverywhere : IsNonzeroEverywhere (idealSheafOf I106)
  /-- The empty boundary is a simple normal crossing divisor (Notation 64 (3)). -/
  isSnc : (DivisorFamily.empty A4).IsSnc

/-- The triple `(𝔸⁴_ℚ, I, ∅)` of [Kol07, Example 106], from a well-formedness witness. -/
noncomputable def triple (h : WellFormed) : Triple ℚ where
  X := .ofHom structureMap (@FiniteType.mk _ _ _ h.locallyOfFiniteType h.quasiCompact)
    h.isSeparated
  smoothOfRelativeDimension := h.equidim
  I := idealSheafOf I106
  isNonzeroEverywhere := h.isNonzeroEverywhere
  E := DivisorFamily.empty A4
  isSnc := h.isSnc

end Triple

/-! ### The run of `BO_{4,2}`

The functor is run on the triple in `HironakaExamples/KollarExample106Run.lean`. -/

section Test

end Test

/-! ### The `x`-chart coordinates of Kollár's last sentences -/

section Cuspidal

/-- `x₁ = X 0` in the `x`-chart ring `ℚ[x₁, y₁, z₁, w₁]`. -/
local notation "x₁" => (X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y₁ = X 1`. -/
local notation "y₁" => (X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z₁ = X 2`. -/
local notation "z₁" => (X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w₁ = X 3`. -/
local notation "w₁" => (X 3 : MvPolynomial (Fin 4) ℚ)

end Cuspidal

end Hironaka.Examples.KollarExample106
