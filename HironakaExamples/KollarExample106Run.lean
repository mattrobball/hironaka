/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import HironakaExamples.KollarExample106Triple
public import Hironaka.Resolution.Algebraic.OrderReduction.Step3Data
import Hironaka.Scheme.Snc.EmptyFamily
import HironakaExamples.OrderReduction.Example106
import HironakaExamples.OrderReduction.Example106Length
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Kollár's Example 106 run through the order-reduction functor `BO_{4,2}`

[Kol07, Example 106] follows the principalization of `I = (x³ − y², x⁴ + xz² − w³)` on `𝔸⁴`.
This file checks the beginning of the run against the functor `BO_{4,2}` of [Kol07, Theorem 103]
(`Hironaka.BO.data`, assembled from arbitrary inductive data `BMO_{≤ 3}`) on the triple
`(𝔸⁴_ℚ, I, ∅)` of `HironakaExamples/KollarExample106Triple.lean`. The chart computations it
relies on are those of `HironakaExamples/OrderReduction/Example106.lean`, `Example106BlowUp.lean`
and `Example106Length.lean`, together with the general cosupport forcing of
`HironakaExamples/Sequence/CosuppForcing.lean` and the comparison of the blow-up of `Spec R` with
the affine blow-up in `HironakaExamples/BlowUp/Glue/SpecIso.lean`.

*How the check is run.* Nothing of the inductive input `B` is unfolded: `BO_{4,2}` is tested
through its three properties alone. Its sequence is a smooth blow-up sequence of order `2`
(`isOrderSeq`), has no empty centre (`noEmptyCenters`, the convention [Kol07, 32]) and ends with
maximal order `< 2` (`maxOrd_lt`, [Kol07, Theorem 103 (1)]). Under these the centres are forced:
the cosupport `{ord ≥ 2}` of the current ideal is a single closed point, every generic point of
the next centre has order `2` ([Kol07, Definition 66 (4)]), so the centre is supported at that
point; being smooth it is the reduced point. At stage `0` the cosupport of `I` is the origin
(`HironakaExamples/Balanced/Example106.lean`, at every scheme point); at stage `1` the transform
`I₁ = π_*^{-1}(I, 2)` of the marked ideal ([Kol07, Definition 60]), which is the weak transform
since `ord_0 I = 2`, is read on the four charts of the blow-up of the origin, where it is
`(σ_j I : x_j²)`: on the `x`-chart `∂_{x₁}(x₁ − y₁²) = 1`, so the order has dropped to `1` there,
as Kollár says; the `y`- and `w`-charts have no point of order `2`; but on the `z`-chart the
cosupport is the origin `q = [0:0:1:0] ∈ E₁`, the intersection of `E₁` with the strict transform
of the `z`-axis. At stages `2` and `3` the same computation on `K_z = (x³z − y², z(x⁴z + x − w³))`
and `K_zw` finds further points `q'`, `q''` of order `2`
(`HironakaExamples/MaximalContact/Example106Stages.lean`), so the order-`2` run has at least four
blow-ups.

*Kollár's text, corrected.* "The order has dropped to 1" holds on the `x`-chart but not on the
`z`-chart, so `BO_{4,2}` does not yet continue with `(I₁, 1, E₁)` as printed: it first blows up
`q` (`secondCenter`, `four_le_length`). The cuspidal curve `(x₁ = y₁ = z₁² − w₁³ = 0)` of Kollár's
last sentences is `strictTransform_meets_plane_ideal` in
`HironakaExamples/OrderReduction/Example106.lean`, an instance of [Kol07, Warning 23] (the strict
transform of a smooth `X` need not meet the exceptional divisor in a simple normal crossing
divisor).

-/

public section

open AlgebraicGeometry CategoryTheory Hironaka Scheme IdealSheafData BlowUpSequence
  Hironaka.Examples.KollarExample106 Hironaka.Examples.Example106 Hironaka.Examples.Example106BO
  Hironaka.Sequence Hironaka.BlowUp IsLocalRing

namespace Hironaka.Examples.KollarExample106Run

/-- The triple `(𝔸⁴_ℚ, I, ∅)` of [Kol07, Example 106] is well formed in the sense of
[Kol07, Notation 64]: `𝔸⁴_ℚ → Spec ℚ` is affine (quasi-compact, separated), smooth of relative
dimension `4`, hence locally of finite type; `I ≠ 0` on the domain `ℚ[x, y, z, w]`
(`isNonzeroEverywhere_I106`); the empty boundary is a simple normal crossing divisor
(`isSnc_empty_of_smooth`). -/
theorem wellFormed : WellFormed where
  locallyOfFiniteType := by
    have : Smooth (affineSpaceToSpec ℚ 4) := smooth_affineSpaceToSpec
    change LocallyOfFiniteType (affineSpaceToSpec ℚ 4)
    infer_instance
  quasiCompact := by
    change QuasiCompact (affineSpaceToSpec ℚ 4)
    infer_instance
  isSeparated := by
    change IsSeparated (affineSpaceToSpec ℚ 4)
    infer_instance
  smooth := smooth_affineSpaceToSpec
  equidim := ⟨4, smoothOfRelativeDimension_affineSpaceToSpec⟩
  isNonzeroEverywhere := isNonzeroEverywhere_I106
  isSnc := by
    have : Smooth structureMap := smooth_affineSpaceToSpec
    exact isSnc_empty_of_smooth structureMap

/-- Kollár's "`ord I = 2`": the triple lies in the class `BOClass 4 2` of Theorem 103: `1 ≤ 2`,
`dim 𝔸⁴ = 4 ≤ 4`, `max-ord I ≤ 2` (`maxOrd_le_two`, at every scheme point). -/
theorem boClass (h : WellFormed) : Triple.BOClass 4 2 (triple h) :=
  ⟨one_le_two, ⟨4, le_rfl, smoothOfRelativeDimension_affineSpaceToSpec⟩, maxOrd_le_two⟩

/-- "Thus the first step is to blow up the origin in `𝔸⁴`" ([Kol07, Example 106]):
`BO_{4,2}(𝔸⁴_ℚ, I, ∅)` begins with the blow-up of the origin `m₀ = (x, y, z, w)`, by the cosupport
forcing at stage `0` (`exists_eq_cons_specIdealSheaf_m0`) applied to the three properties of the
functor. -/
theorem firstCenter (h : WellFormed) (hT : Triple.BOClass 4 2 (triple h))
    (Dom : ∀ (k : Type) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (4 - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers) :
    ∃ rest : BlowUpSequence (idealSheafOf m0).blowUp,
      ((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).seq (triple h) hT =
        cons A4 (idealSheafOf m0) rest :=
  exists_eq_cons_specIdealSheaf_m0 _ _
    (((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).isOrderSeq (triple h) hT)
    (((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).noEmptyCenters (triple h) hT)
    ((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).maxOrd_lt ℚ (triple h) hT)

/-- The correction to Kollár's continuation: the second blow-up of `BO_{4,2}(𝔸⁴_ℚ, I, ∅)` has a
centre supported at `q = [0:0:1:0]`, the point where the strict transform of the `z`-axis meets
`E₁`, at which `I₁` has order exactly `2` (`secondCenter_of_axioms` applied to the three
properties of the functor, rewritten along the first-stage identity). -/
theorem secondCenter (h : WellFormed) (hT : Triple.BOClass 4 2 (triple h))
    (Dom : ∀ (k : Type) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (4 - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers)
    (rest : BlowUpSequence (idealSheafOf m0).blowUp)
    (hS : ((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).seq (triple h) hT =
      cons A4 (idealSheafOf m0) rest) :
    ∃ (Z₁ : (idealSheafOf m0).blowUp.IdealSheafData)
      (rest' : BlowUpSequence Z₁.blowUp),
      rest = cons (idealSheafOf m0).blowUp Z₁ rest' ∧
      Z₁.support = ((idealSheafOf zAxis).strictTransform (idealSheafOf m0)).support ⊓
        (idealSheafOf m0).exceptionalDivisor.support ∧
      ∀ q ∈ Z₁.support, ((idealSheafOf I106).weakTransform (idealSheafOf m0)).ord q = 2 := by
  have h1 :=
    ((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).isOrderSeq (triple h) hT
  have h2 :=
    ((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).noEmptyCenters (triple h) hT
  have h3 := (Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).maxOrd_lt ℚ (triple h) hT
  rw [hS] at h1 h2 h3
  exact secondCenter_of_axioms m0 centerIdeal_eq_m0.symm _ rest h1 h2 h3

/-- The order-`2` run of `BO_{4,2}(𝔸⁴_ℚ, I, ∅)` has at least four blow-ups, forced by the points
`q`, `q'`, `q''` of order `2` at the stages `1`, `2`, `3`
(`HironakaExamples/MaximalContact/Example106Stages.lean`; `four_le_length_of_axioms` applied to the
three properties of the functor). -/
theorem four_le_length (h : WellFormed) (hT : Triple.BOClass 4 2 (triple h))
    (Dom : ∀ (k : Type) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (4 - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers) :
    4 ≤ (((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).seq (triple h) hT).length :=
  four_le_length_of_axioms _ _
    (((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).isOrderSeq (triple h) hT)
    (((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).functor ℚ).noEmptyCenters (triple h) hT)
    ((Hironaka.BO.data 4 2 Dom B hDom hB hsm hbc hBind).maxOrd_lt ℚ (triple h) hT)

/-- `x₁ = X 0` in the `x`-chart ring `ℚ[x₁, y₁, z₁, w₁]`. -/
local notation "x₁" => (MvPolynomial.X 0 : MvPolynomial (Fin 4) ℚ)
/-- `y₁ = X 1`. -/
local notation "y₁" => (MvPolynomial.X 1 : MvPolynomial (Fin 4) ℚ)
/-- `z₁ = X 2`. -/
local notation "z₁" => (MvPolynomial.X 2 : MvPolynomial (Fin 4) ℚ)
/-- `w₁ = X 3`. -/
local notation "w₁" => (MvPolynomial.X 3 : MvPolynomial (Fin 4) ℚ)

end Hironaka.Examples.KollarExample106Run

