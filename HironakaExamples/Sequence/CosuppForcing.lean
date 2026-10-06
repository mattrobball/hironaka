/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Cosupport forcing: the first center of an order sequence with a one-point cosupport

Condition (4) of [Kol07, Definition 66] (`ord_{Z_i} I_i = m`) places every center of a smooth
blow-up sequence of order `m` inside the cosupport `cosupp(I_i, m) = {x : ord_x I_i ≥ m}`
([Kol07, Definition 59]; the order along a center is read at its generic points,
[Kol07, Definition 47]), the empty blow-up convention [Kol07, 32] forbids empty centers, and the
conclusion `max-ord I_r < m` of [Kol07, Theorem 103 (1)] makes the final maximal order drop below
`m`. When the cosupport of `(I, m)` is a single closed point `x`, these three clauses force the
first center: the sequence is not empty (else `max-ord I ≥ ord_x I ≥ m`), its first center `Z₀`
has every generic point of order `m`, hence equal to `x`, so `Z₀` is supported at `x` and, being
smooth over `k` (a center with simple normal crossings has a regular, hence reduced, subscheme), is
the reduced point `vanishingIdeal {x}`.

This is the mechanism by which the worked example [Kol07, Example 106] reads "the first step is to
blow up the origin" from the properties of the order reduction functor alone (the fields of
`OrderSeqFunctor` and the bound on the final maximal order), without its construction. Nothing of
`𝔸⁴`, of the ideal of the example or of the origin appears here; the identification of the reduced
point with the ideal of the origin is in `HironakaExamples/OrderReduction/Example106.lean`. The
point `x` is any point with `IsClosed {x}` (a scheme point, not a rational point: the later stages
of the example need the lemma at points of the blown-up scheme), and the hypothesis is `IsOrderSeq`.

The topological input is `Closeds.exists_mem_genericPoints_specializes`
(`Hironaka/Scheme/IdealSheaf/Order/Specialization.lean`): in a sober `T₀` space every point of a
closed set `Z` is a specialization of a generic point of `Z`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Sequence


variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Cosupport forcing, support form** (condition (4) of [Kol07, Definition 66], the empty
blow-up convention [Kol07, 32], and the conclusion of [Kol07, Theorem 103 (1)]). Let `S` be a
smooth blow-up sequence of order `m` for `(X, I, E)` with no empty center whose final weak
transform has maximal order `< m`, and let the cosupport `{y : ord_y I ≥ m}` be a single closed
point `x`. Then `S` begins with a blow-up, of a center supported exactly at `x`: the sequence is
not empty (`max-ord I ≥ ord_x I ≥ m`), every generic point of the first center has order `m`, so
is `x`, and the center is nonempty. -/
theorem exists_eq_cons_of_ord_le_iff (S : BlowUpSequence X)
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)
    (hS : S.IsOrderSeq f I E m) (hne : S.NoEmptyCenters)
    (hend : (S.weakTransformSeq I (Fin.last _)).maxOrd < (m : ℕ∞)) {x : X}
    (hx : IsClosed ({x} : Set X)) (hcos : ∀ y, (m : ℕ∞) ≤ I.ord y ↔ y = x) :
    ∃ (Z : X.IdealSheafData) (rest : BlowUpSequence Z.blowUp),
      S = cons X Z rest ∧ Z.support = ⟨{x}, hx⟩ := by
  cases S with
  | nil _ =>
    exfalso
    change I.maxOrd < (m : ℕ∞) at hend
    have h1 : (m : ℕ∞) ≤ I.ord x := (hcos x).mpr rfl
    have h2 : I.ord x ≤ I.maxOrd := IdealSheafData.le_maxOrdAlong I (Set.mem_univ x)
    exact absurd (h1.trans h2) (not_le.mpr hend)
  | cons X Z rest =>
    refine ⟨Z, rest, rfl, ?_⟩
    have h0 := hS.2 ⟨0, Nat.succ_pos _⟩
    change E.HasSncWith Z ∧ I.OrdAlongEq Z.support (m : ℕ∞) at h0
    have hZ : Z ≠ ⊤ := hne ⟨0, Nat.succ_pos _⟩
    have hsub : ∀ z ∈ Z.support, z = x := by
      intro z hz
      obtain ⟨η, hη, hηz⟩ := Closeds.exists_mem_genericPoints_specializes Z.support hz
      have hηx : η = x := (hcos η).mp (h0.2 η hη).ge
      subst hηx
      have := specializes_iff_mem_closure.mp hηz
      rwa [hx.closure_eq, Set.mem_singleton_iff] at this
    have hne' : ∃ z, z ∈ Z.support := by
      by_contra h
      refine hZ ((IdealSheafData.support_eq_bot_iff (I := Z)).mp (Closeds.ext ?_))
      rw [Closeds.coe_bot]
      exact Set.ext fun z => ⟨fun hz => (h ⟨z, hz⟩).elim, fun hz => hz.elim⟩
    obtain ⟨z, hz⟩ := hne'
    have hxZ : x ∈ Z.support := hsub z hz ▸ hz
    ext y
    simp only [SetLike.mem_coe, Closeds.coe_mk, Set.mem_singleton_iff]
    exact ⟨hsub y, fun hy => hy ▸ hxZ⟩

/-- The first center of a smooth blow-up sequence of order `m` over a smooth `k`-scheme is a
reduced closed subscheme: it has simple normal crossings with the boundary (condition (3) of
[Kol07, Definition 66]), so its subscheme is regular, its stalks are domains, and its ideal sheaf
is the vanishing ideal of its support. -/
theorem center_eq_vanishingIdeal_support_of_isOrderSeq (f : X ⟶ Spec (.of k)) [Smooth f]
    (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ) (Z : X.IdealSheafData)
    (rest : BlowUpSequence Z.blowUp) (hS : (cons X Z rest).IsOrderSeq f I E m) :
    Z = IdealSheafData.vanishingIdeal Z.support := by
  have h0 := hS.2 ⟨0, Nat.succ_pos _⟩
  change E.HasSncWith Z ∧ I.OrdAlongEq Z.support (m : ℕ∞) at h0
  have hreg : IsRegular Z.subscheme := isRegular_subscheme_of_hasSncWith f h0.1
  have : IsReduced Z.subscheme := by
    have : ∀ w, _root_.IsReduced (Z.subscheme.presheaf.stalk w) := fun w =>
      have : IsRegularLocalRing (Z.subscheme.presheaf.stalk w) := hreg.isRegularAt w
      have := IsLocalRing.isDomain_of_isRegularLocalRing (Z.subscheme.presheaf.stalk w)
      inferInstance
    exact isReduced_of_isReduced_stalk _
  rw [IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]

/-- **Cosupport forcing, reduced-point form**: under the hypotheses of
`exists_eq_cons_of_ord_le_iff` over a smooth `k`-scheme, `S` begins with the blow-up of the reduced
point `x`, `vanishingIdeal {x}`, given here through any ideal sheaf `Z₀` equal to it (the worked
example supplies the ideal of the origin). -/
theorem exists_eq_cons_of_ord_le_iff_of_eq_vanishingIdeal
    (S : BlowUpSequence X) (f : X ⟶ Spec (.of k)) [Smooth f] (I : X.IdealSheafData)
    (E : DivisorFamily X) (m : ℕ) (hS : S.IsOrderSeq f I E m) (hne : S.NoEmptyCenters)
    (hend : (S.weakTransformSeq I (Fin.last _)).maxOrd < (m : ℕ∞)) {x : X}
    (hx : IsClosed ({x} : Set X)) (hcos : ∀ y, (m : ℕ∞) ≤ I.ord y ↔ y = x)
    {Z₀ : X.IdealSheafData} (hZ₀ : IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ = Z₀) :
    ∃ rest : BlowUpSequence Z₀.blowUp, S = cons X Z₀ rest := by
  obtain ⟨Z, rest, hS', hsupp⟩ := exists_eq_cons_of_ord_le_iff S f I E m hS hne hend hx hcos
  subst hS'
  have hZ := center_eq_vanishingIdeal_support_of_isOrderSeq f I E m Z rest hS
  rw [hsupp, hZ₀] at hZ
  subst hZ
  exact ⟨rest, rfl⟩

end Hironaka.Sequence
