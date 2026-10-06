/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Reduced
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Sequence
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Step
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The centers of the disjoining sequence are the reduced meet loci

Kollár blows up first `Z_0 ⊂ X`, "the subset where all the `E^i` intersect", then `Z_1 ⊂ X_1`,
the subset where `k − 1` of the birational transforms intersect, and so on [Kol07, 72]. The
center at multiplicity
`m` is defined here as the product ideal sheaf `disjoinCenter G m = ∏_{|s| = m} ∑_{i ∈ s} G_i` (the
scheme structure `∑_{i∈s} G_i` on each `m`-fold intersection), and `Disjoin/Reduced.lean` shows
that at each step this is the reduced subscheme on the meet locus once no `(m+1)`-fold
intersections remain (`disjoinCenter_eq_vanishingIdeal`). This module iterates that fact along the
sequence: the invariant "no `(m+1)`-fold intersections" is carried by
`meetLocus_strictTransform_disjoinCenter` (`Disjoin/Step.lean`), the running family stays inside an
snc family by `isSnc_totalTransform_disjoinCenter`, so that every center `Z_t` of `disjoinSeq E`
is Kollár's subset with its reduced structure.

* `center_disjoinSeqAux_eq_vanishingIdeal`: the invariant along `disjoinSeqAux`;
* `center_disjoinSeq_eq_vanishingIdeal`: for `disjoinSeq E`, the center at step `t` is the reduced
  subscheme on the locus where `card E.ι − t` of the current birational transforms meet.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {k : Type u} [Field k] [PerfectField k]

section Aux

variable {ι : Type*} [Fintype ι]

/-- The invariant along the disjoining steps [Kol07, 72]: with no `(m+1)`-fold intersections among
the current transforms, the center at step `i` is the reduced subscheme on the locus where `m − i`
of the current birational transforms meet. -/
theorem center_disjoinSeqAux_eq_vanishingIdeal : ∀ (m : ℕ) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : DivisorFamily X} (_ : F.IsSnc) (G : ι → X.IdealSheafData)
    (_ : ∀ i, G i ∈ Set.range F.component) (_ : meetLocus G (m + 1) = ⊥)
    (i : Fin (disjoinSeqAux m G).length),
    (disjoinSeqAux m G).center i = IdealSheafData.vanishingIdeal (meetLocus
      (fun a => (disjoinSeqAux m G).strictTransformSeq (G a) i.castSucc) (m - i))
  | 0, _, _, _, _, _, _, _, _, i => i.elim0
  | 1, _, _, _, _, _, _, _, _, i => i.elim0
  | m + 2, _, f, _, _, hF, G, hG, hm, ⟨0, _⟩ =>
    disjoinCenter_eq_vanishingIdeal f hF G hG (m + 1) hm
  | m + 2, X, f, _, F, hF, G, hG, hm, ⟨j + 1, h⟩ => by
    have hsm := smooth_disjoinCenter f hF G hG (m + 1) hm
    have : Smooth ((disjoinCenter G (m + 2)).blowUpπ ≫ f) :=
      smooth_blowUpπ_comp_of_smooth' f _
    have ih := center_disjoinSeqAux_eq_vanishingIdeal (m + 1)
      ((disjoinCenter G (m + 2)).blowUpπ ≫ f)
      (isSnc_totalTransform_disjoinCenter f hF G hG (m + 1) hm) _
      (strictTransform_mem_range_totalTransform hG _)
      (meetLocus_strictTransform_disjoinCenter f hF G hG (m + 1) hm)
      ⟨j, Nat.lt_of_succ_lt_succ h⟩
    have hidx : m + 2 - ((⟨j + 1, h⟩ : Fin (disjoinSeqAux (m + 2) G).length) : ℕ) = m + 1 - j :=
      Nat.succ_sub_succ _ _
    rw [hidx]
    exact ih

end Aux

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X) (hE : E.IsSnc)
include f hE

/-- The center of the `t`-th disjoining blow-up is the reduced subscheme on Kollár's subset
[Kol07, 72]: the locus where `card E.ι − t` of the current birational transforms of the components
meet. -/
theorem center_disjoinSeq_eq_vanishingIdeal (i : Fin (disjoinSeq E).length) :
    (disjoinSeq E).center i = IdealSheafData.vanishingIdeal (meetLocus
      (fun a => (disjoinSeq E).strictTransformSeq (E.component a) i.castSucc)
      (Fintype.card E.ι - i)) :=
  center_disjoinSeqAux_eq_vanishingIdeal _ f hE E.component (fun i => ⟨i, rfl⟩)
    (meetLocus_component_card_succ E) i

end Hironaka.Sequence
