/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A centre of order at least two never contains a reduced component

Włodarczyk's Claim in the proof of [Wlo05, Theorem 4.7.1] is about the FIRST stage of the run of
`BMO_1` whose centre contains the strict transform `c̃` of a component `c` of `V(I)` along which
`I` is reduced. The rounds of Step 1 of the proof of [Kol07, Theorem 107] at an order `d ≥ 2`
blow up centres along which the nonmonomial part has order `≥ d`; such a centre cannot contain
`c̃`: at the generic point `η̃` of `c̃` the nonmonomial part is the maximal ideal, of order `1`
(`ord_maximalIdeal_eq_one`), and the order at `η̃` is at least the order at a generic point of the
centre specializing to it (upper semicontinuity of the order, [Hau03, p. 392]). So the first
containing stage lies in the round of order `1`. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimStep1`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedGenericOrder` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  IsLocalRing

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
  (n : ℕ) [SmoothOfRelativeDimension n f]

include f n in
/-- A point at which an ideal sheaf has order `1` lies on no closed set along which the ideal sheaf
has order `≥ 2` (the order at a specialization is at least the order at the generic point); the
order at the point may be `≤ 1`. -/
theorem notMem_of_leOrdAlong_two (I : X.IdealSheafData) (D : Closeds X)
    (hD : I.LeOrdAlong D ((2 : ℕ) : ℕ∞)) {η : X} (hη : I.ord η ≤ 1) : η ∉ D := fun hηD => by
  obtain ⟨ζ, hζ, hsp⟩ := Closeds.exists_mem_genericPoints_specializes D hηD
  have h2 : ((2 : ℕ) : ℕ∞) ≤ I.ord η := (hD ζ hζ).trans (IdealSheafData.ord_le_ord_of_specializes I
      f n hsp)
  have h21 : ((2 : ℕ) : ℕ∞) ≤ 1 := h2.trans hη
  exact absurd (by exact_mod_cast h21 : (2 : ℕ) ≤ 1) (by norm_num)

include f n in
/-- Step 1 of the proof of [Kol07, Theorem 107] read against the Claim: a centre along which the
marked ideal has order `≥ 2` does not contain the strict transform of a component whose generic
point carries order `≤ 1`. The run is smooth (`S.IsSmooth f`), so its stages are smooth of relative
dimension `n` over `k` and the semicontinuity applies at stage `i`. -/
theorem not_centerContains_of_leOrdAlong_two (S : BlowUpSequence X) (hS : S.IsSmooth f)
    (c : X.IdealSheafData) (i : Fin S.length) (N : (S.stage i.castSucc).IdealSheafData)
    (hN : N.LeOrdAlong (S.center i).support ((2 : ℕ) : ℕ∞)) {η : S.stage i.castSucc}
    (hη : η ∈ (S.strictTransformSeq c i.castSucc).support) (hord : N.ord η ≤ 1) :
    ¬ CenterContains S c i := fun ⟨_, hle⟩ => by
  have := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) hS i.castSucc
  exact notMem_of_leOrdAlong_two (S.stageMap i.castSucc ≫ f) n N _ hN hord
    (IdealSheafData.support_antitone hle hη)

end Hironaka.Resolution
