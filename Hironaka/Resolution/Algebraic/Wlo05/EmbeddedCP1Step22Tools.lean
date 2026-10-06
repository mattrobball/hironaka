/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.EraseFamily
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Mathlib.Data.Fintype.Sort
public import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Hironaka.Scheme.Snc.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Hironaka.Scheme.BlowUpSequence.Defs

/-!
# Tools for the maximal-contact step of CP1

Elementary bookkeeping for the step of the proof of CP1 (the statement of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) that descends to the hypersurface of
maximal contact (Step 2.2 of the proof of [Kol07, Theorem 103], the proof of [Kol07, Lemma 102]):
snc with a closed subscheme restricts along an injection of families with equal members
(`HasSncWith.of_embeds`)
and depends on the subscheme only through its stalks at its points (`HasSncWith.of_stalkIdeal_eq`);
generic points and the reducedness of `I` at them descend along a closed immersion
(`mem_genericPoints_comap_of_isClosedImmersion`,
`stalkIdeal_comap_eq_vanishingIdeal_closure_of_eq`); removing a member keeps a family snc
(`isSnc_erase`); in `E + J` with `J` appended last, every index other than `J`'s is an original
index (`exists_eq_inl_of_erase_append_last`); and along a smooth order-`1` sequence without empty
blow-ups from a triple with `max-ord I ≤ 1`, a point on the marked transform's support forces
`max-ord I = 1` (`maxOrd_eq_one_of_mem_support_markedTransformSeq`; below the mark the sequence is
empty, [Kol07, Theorem 68]). The coordinates are those of [Kol07, Definition 24]. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Core` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData
  Hironaka.Sequence Hironaka.Snc

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-- Snc with `Z` restricts along an injection of families with equal members — the coordinates are
the same, the members of `E₁` through `x` corresponding to members of `E₂` through `x`. -/
theorem HasSncWith.of_embeds {E₁ E₂ : DivisorFamily X} (e : E₁.ι → E₂.ι)
    (he : Function.Injective e) (hcomp : ∀ a, E₂.component (e a) = E₁.component a)
    {Z : X.IdealSheafData} (h : E₂.HasSncWith Z) : E₁.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, ⟨hrs, c, hcinj, hc⟩, s, hs⟩ := h x hx
  refine ⟨n, z, ⟨hrs, fun i => c ⟨e i.1, by rw [hcomp]; exact i.2⟩, ?_, fun i => ?_⟩, s, hs⟩
  · intro i₁ i₂ h12
    exact Subtype.ext (he (Subtype.mk.inj (hcinj h12)))
  · exact (congrArg (fun D => D.stalkIdeal x) (hcomp i.1).symm).trans
      (hc ⟨e i.1, by rw [hcomp]; exact i.2⟩)

/-- Snc with `Z` depends on `Z` only through its stalks at its points — a closed subscheme `Z'`
inside `Z` with the same stalks at its points has snc with `E` when `Z` does. -/
theorem HasSncWith.of_stalkIdeal_eq {E : DivisorFamily X} {Z Z' : X.IdealSheafData}
    (h : E.HasSncWith Z) (hsupp : Z'.support ≤ Z.support)
    (hst : ∀ x ∈ Z'.support, Z'.stalkIdeal x = Z.stalkIdeal x) : E.HasSncWith Z' := by
  intro x hx
  obtain ⟨n, z, hz, s, hs⟩ := h x (hsupp hx)
  refine ⟨n, z, hz, s, ?_⟩
  rw [hst x hx]
  exact hs

/-- Generic points descend along a closed immersion — a point over a generic point of `V(I)` is a
generic point of `V(I|_Y)` (the closed immersion is injective, so a generization in `V(I|_Y)` maps
to a generization in `V(I)`). -/
theorem mem_genericPoints_comap_of_isClosedImmersion (g : Y ⟶ X) [IsClosedImmersion g]
    (I : X.IdealSheafData) {η' : Y} (hη : g η' ∈ I.support.genericPoints) :
    η' ∈ (I.comap g).support.genericPoints := by
  refine ⟨?_, fun ξ hξ hsp => ?_⟩
  · rw [mem_support_comap_iff_apply]
    exact hη.1
  · rw [mem_support_comap_iff_apply] at hξ
    exact (Scheme.Hom.isClosedEmbedding g).injective (hη.2 hξ (hsp.map g.continuous))

/-- The reducedness of `I` at a point descends along a closed immersion — if `I_{g η'}` is the
reduced ideal of the closure of `g η'`, then `(I|_Y)_{η'}` is the reduced ideal of the closure of
`η'`. -/
theorem stalkIdeal_comap_eq_vanishingIdeal_closure_of_eq (g : Y ⟶ X) [IsClosedImmersion g]
    (I : X.IdealSheafData) (η' : Y)
    (hIc : I.stalkIdeal (g η') = (IdealSheafData.vanishingIdeal (Closeds.closure
        {g η'})).stalkIdeal (g η')) :
    (I.comap g).stalkIdeal η' = (IdealSheafData.vanishingIdeal (Closeds.closure
        {η'})).stalkIdeal η' := by
  rw [IdealSheafData.stalkIdeal_comap, hIc, ← IdealSheafData.stalkIdeal_comap,
      comap_vanishingIdeal_closure_of_isClosedImmersion]

/-- Removing a member keeps a family snc — the regularity of the members and the coordinates at
every point are inherited. -/
theorem isSnc_erase (E : DivisorFamily X) (j : E.ι) (hE : E.IsSnc) : (E.erase j).IsSnc := by
  refine ⟨fun i => hE.1 i.1, fun x => ?_⟩
  obtain ⟨n, z, hrs, c, hcinj, hc⟩ := hE.2 x
  exact ⟨n, z, hrs, fun i => c ⟨i.1.1, i.2⟩,
    fun i₁ i₂ h => Subtype.ext (Subtype.ext (Subtype.mk.inj (hcinj h))), fun i => hc ⟨i.1.1, i.2⟩⟩

/-- In `E + J` with `J` appended last (position `card E.ι`, `nth_append_last`), every index other
than `J`'s is an original index. -/
theorem exists_eq_inl_of_erase_append_last (E : DivisorFamily X) (J : X.IdealSheafData)
    (h : Fintype.card E.ι < Fintype.card (E.append J).ι)
    (b : ((E.append J).erase (monoEquivOfFin (E.append J).ι rfl ⟨Fintype.card E.ι, h⟩)).ι) :
    ∃ a : E.ι, b.1 = toLex (Sum.inl a) := by
  have hj : monoEquivOfFin (E.append J).ι rfl ⟨Fintype.card E.ι, h⟩ =
      toLex (Sum.inr PUnit.unit) :=
    monoEquivOfFin_lex_inr_last h
  rcases hb : ofLex b.1 with a | u
  · exact ⟨a, (toLex_ofLex b.1).symm.trans (congrArg toLex hb)⟩
  · exfalso
    apply b.2
    cases u
    exact ((toLex_ofLex b.1).symm.trans (congrArg toLex hb)).trans hj.symm

/-- Along a smooth order-`1` sequence without empty blow-ups from a triple with `max-ord I ≤ 1`, a
point on the marked transform's support forces `max-ord I = 1` — below the mark the sequence is
empty (the remark after [Kol07, Theorem 68]: the case `max-ord I < m` is trivial) and the marked
transform is `I` itself, which then has no point of order `≥ 1`. -/
theorem maxOrd_eq_one_of_mem_support_markedTransformSeq {k : Type u} [Field k]
    (f : X ⟶ Spec (CommRingCat.of k)) (_n : ℕ)
    {S : BlowUpSequence X} {I : X.IdealSheafData} {E : DivisorFamily X}
    (hS : S.IsOrderSeq f I E 1) (hne : S.NoEmptyCenters) (hmax : I.maxOrd ≤ 1)
    {i : Fin (S.length + 1)} {η : S.stage i} (hη : η ∈ (S.markedTransformSeq I 1 i).support) :
    I.maxOrd = ((1 : ℕ) : ℕ∞) := by
  rw [Nat.cast_one]
  rcases lt_or_eq_of_le hmax with hlt | heq
  · exfalso
    have hlt' : I.maxOrd < ((1 : ℕ) : ℕ∞) := by rwa [Nat.cast_one]
    have hnil := Hironaka.BO.eq_nil_of_isOrderSeq_of_maxOrd_lt f hS hne hlt'
    subst hnil
    change η ∈ I.support at hη
    have h1 := (IdealSheafData.one_le_ord_iff I η).mpr hη
    exact absurd (h1.trans (IdealSheafData.le_maxOrd I η)) (not_le.mpr hlt)
  · exact heq

end Hironaka.Resolution
