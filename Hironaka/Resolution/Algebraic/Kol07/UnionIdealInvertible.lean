/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SncOn
public import Hironaka.Scheme.Snc.Dictionary
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.PrimeProducts
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Reduced
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.IdealSheaf.Invertible
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.Family
import Hironaka.Scheme.Snc.ParameterAlgebra
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The reduced union of a simple normal crossing family is a Cartier divisor

Hironaka's definition of a reduced subscheme `E` with only normal crossings [Hir64, Definition 2]
presupposes that the ideal sheaf of `E` is invertible; Kollár's principalization theorem produces
the pull-back of an ideal as a monomial ideal `∏ F_j^{a_j}` on a simple normal crossing family `F`
[Kol07, Theorem 35 (2)]. Clause (iii) of [Hir64, Corollary 3] needs the reduced inverse image, that
is the radical of that monomial ideal, to be invertible with only normal crossings. This module
supplies the two facts, beside `unionIdeal_eq_radical_prod` and
`IsSnc.isSncBoundary_unionIdeal`:

* `isInvertible_unionIdeal_of_isSnc`: the reduced union `unionIdeal F` of a simple normal
  crossing family on a locally Noetherian scheme smooth over `k` is defined by an invertible sheaf
  of ideals, checked at the stalks (`isInvertible_of_forall_stalkIdeal_eq_span`). At a point `x`
  its stalk is the radical of
  `span {∏ z_{c(i)}}`, the product of the pairwise distinct transversal coordinates of the members
  through `x`, which is its own radical since the coordinates are prime and pairwise non-dividing
  (`IsLocalRing.isRadical_span_prod`), and a product of nonzero elements of the regular local
  ring is a non-zero-divisor.
* `radical_prod_pow_eq_unionIdeal_subfamily`: the radical of `∏ F_j^{a_j}` is the reduced union of
  the sub-family of members with positive multiplicity (both are the vanishing ideal of the same
  closed set).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {k : Type u} [Field k]

/-- The reduced union of a simple normal crossing family [Kol07, Definition 24] on a locally
Noetherian scheme smooth over `k` is defined by an invertible sheaf of ideals, as
[Hir64, Definition 2] presupposes (checked at the stalks,
`isInvertible_of_forall_stalkIdeal_eq_span`): at a point `x` its stalk is the radical of the
product of the stalks of the members,
`span {∏ z_{c(i)}}` over the members through `x` (`prod_stalkIdeal_eq_span`), which is its own
radical since the `z_{c(i)}` are pairwise distinct members of a regular system of parameters,
prime and pairwise non-divisible (`isRadical_span_prod`), and a product of nonzero elements of the
regular local ring is a non-zero-divisor. -/
theorem isInvertible_unionIdeal_of_isSnc {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth f] {F : DivisorFamily X} (hF : F.IsSnc) :
    F.unionIdeal.IsInvertible := by
  classical
  have := LocallyOfFiniteType.isLocallyNoetherian f
  refine isInvertible_of_forall_stalkIdeal_eq_span _ fun x => ?_
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk f x
  obtain ⟨n, z, hrs, c, hcinj, hc⟩ := hF.2 x
  have h1 : F.unionIdeal.stalkIdeal x = (Ideal.span {∏ i, z (c i)}).radical := by
    rw [unionIdeal_eq_radical_prod, stalkIdeal_radical, stalkIdeal_finset_prod,
      prod_stalkIdeal_eq_span c hc]
  have hrad : (Ideal.span {∏ i, z (c i)}).radical = Ideal.span {∏ i, z (c i)} :=
    Ideal.radical_eq_iff.mpr (IsLocalRing.isRadical_span_prod (s := Finset.univ)
      (p := fun i => z (c i)) (fun i _ => prime_of_stalkIdeal_eq_span hrs (hc i))
      (fun i _ j _ hij => not_dvd_of_ne hrs.1.symm hrs.2 fun h => hij (hcinj h)))
  refine ⟨∏ i, z (c i), ?_, ?_⟩
  swap
  · rw [h1, hrad]
  have : IsDomain (X.presheaf.stalk x) := IsLocalRing.isDomain_of_isRegularLocalRing _
  exact mem_nonZeroDivisors_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ =>
    (prime_of_stalkIdeal_eq_span hrs (hc i)).ne_zero)

/-- The radical of the monomial ideal `∏ F_j^{a_j}` of a family (the shape of the pull-back in
[Kol07, Theorem 35 (2)]) is the reduced union of the sub-family of members with positive
multiplicity: both are the vanishing ideal of the same closed set (`vanishingIdeal_support`,
`support_finset_prod`, `support_pow`). -/
theorem radical_prod_pow_eq_unionIdeal_subfamily {X : Scheme.{u}} (F : DivisorFamily X)
    (a : F.ι → ℕ) :
    (∏ j, F.component j ^ a j).radical = (F.subfamily fun j => a j ≠ 0).unionIdeal := by
  classical
  rw [← vanishingIdeal_support]
  unfold DivisorFamily.unionIdeal
  congr 1
  rw [support_finset_prod]
  apply le_antisymm
  · refine iSup₂_le fun j _ => ?_
    by_cases hj : a j = 0
    · rw [hj, pow_zero]
      change (⊤ : X.IdealSheafData).support ≤ _
      rw [support_top]
      exact bot_le
    · rw [support_pow _ _ hj]
      exact le_iSup (fun i : {j : F.ι // a j ≠ 0} => (F.component i.1).support) ⟨j, hj⟩
  · refine iSup_le fun i => ?_
    change (F.component i.1).support ≤ _
    rw [← support_pow (F.component i.1) (a i.1) i.2]
    exact le_iSup₂ (f := fun j (_ : j ∈ Finset.univ) => (F.component j ^ a j).support) i.1
      (Finset.mem_univ _)

end Hironaka.Sequence
