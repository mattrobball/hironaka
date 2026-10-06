/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Order
public import Hironaka.Algebra.RegularSmooth.Defs
public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Algebra.Local.CohenIso
import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
import Hironaka.Resolution.Algebraic.Tuning.Transform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.OrderAlongCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENat.BigOperators
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Orders of products, the weak transform of a product, the factors along an irreducible center

Hironaka's Corollary 1 applies Main Theorem II to the product `J = ∏ J_j` of finitely many ideal
sheaves and reads off its condition (1) for the factors: for every pair `(i, j)`, the order
`ν(J_j(i)_y)` "is a positive constant for the points `y` of `D(i)`" [Hir64, Corollary 1,
pp. 143–144]. The three
lemmas behind that sentence, which the source does not state:

* `ord_mul`, `ord_prod`: at every point of a smooth scheme over a field of characteristic zero the
  order of a product is the sum of the orders. The stalk is a regular local ring containing `ℚ`
  (`isRegularLocalRing_stalk`, `stalkAlgebraRat`), on which the order of elements is additive
  (`ordElem_mul_of_algebraRat`, through the Cohen structure theorem); the order of an ideal is the
  least order of an element (`ord_eq_iInf`), attained on a finite generating set
  (`exists_ord_span_eq_ordElem`), which gives `ord_mul_of_ordElem_mul` for ideals; the stalk of a
  product is the product of the stalks (`stalkIdeal_mul`). Compare the properties of the
  cosupport in [Kol07, Definition 59].
* `weakTransform_prod`: along a regular center `D` on which every factor has constant order `c_j`,
  the weak transform of the product is the product of the weak transforms. Each weak transform is
  the marked transform with mark `c_j` (`weakTransform_eq_markedTransform_of_smooth`),
  `π^* J_j = F^{c_j} · W_j` [Kol07, Definition 60, (60.1)], so `π^* (∏ J_j) = F^{∑ c_j} · ∏ W_j`,
  and the colon by the invertible `F^{∑ c_j}` recovers `∏ W_j` (`colon_pow_eq_of_mul_eq`).
* `ord_factors_const_on_center`: on an irreducible center on which the order of the product is
  the constant `d`, every factor has constant order: each `ν(J_j)` is upper semicontinuous with
  its least value at the generic point `η`, the sum of the `e` values at any `y ∈ D` and at `η` is
  the same `d`, so the termwise inequalities are equalities.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme.BlowUpSequence
  TopologicalSpace IsLocalRing

/-! ### The local lemma: the order of a product of ideals -/

namespace Hironaka.Local

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- `ord I ≤ ordElem f` for `f ∈ I`. -/
theorem ord_le_ordElem_of_mem {I : Ideal R} {f : R} (hf : f ∈ I) : IsLocalRing.ord I ≤ ordElem f :=
    by
  rw [ord_eq_iInf]
  exact iInf₂_le f hf

/-- The order of a nonzero ideal of a Noetherian local ring is attained on an element. -/
theorem exists_mem_ordElem_eq_ord (I : Ideal R) (hI : I ≠ ⊥) : ∃ f ∈ I,
    ordElem f = IsLocalRing.ord I := by
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp (IsNoetherian.noetherian I)
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · exact absurd (hS.symm.trans (by rw [h, Submodule.span_empty])) hI
    · exact h
  obtain ⟨f, hf, hord⟩ := exists_ord_span_eq_ordElem hSfin hne
  exact ⟨f, hS ▸ Ideal.subset_span hf, by rw [← hS, hord]⟩

/-- When the order of elements is additive, the order of a product of ideals is the sum of the
orders. -/
theorem ord_mul_of_ordElem_mul (hmul : ∀ f g : R, ordElem (f * g) = ordElem f + ordElem g)
    (I J : Ideal R) : IsLocalRing.ord (I * J) = IsLocalRing.ord I + IsLocalRing.ord J := by
  refine le_antisymm ?_ (le_ord_mul I J)
  by_cases hI : I = ⊥
  · subst hI
    rw [Ideal.bot_mul, IsLocalRing.ord_bot, top_add]
  by_cases hJ : J = ⊥
  · subst hJ
    rw [Ideal.mul_bot, IsLocalRing.ord_bot, add_top]
  obtain ⟨f, hf, hfo⟩ := exists_mem_ordElem_eq_ord I hI
  obtain ⟨g, hg, hgo⟩ := exists_mem_ordElem_eq_ord J hJ
  calc IsLocalRing.ord (I * J) ≤ ordElem (f * g) := ord_le_ordElem_of_mem (Ideal.mul_mem_mul hf hg)
    _ = IsLocalRing.ord I + IsLocalRing.ord J := by rw [hmul, hfo, hgo]

end Hironaka.Local

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-! ### The order of a product on a smooth scheme -/

/-! ### The Corollary's setting -/

section Setting

variable (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]

include f n in
/-- On a smooth scheme over a field of characteristic zero the order of a product is the sum of
the orders at every point: the stalk is a regular local ring containing `ℚ`, where the order of
elements is additive (`ordElem_mul_of_algebraRat`). -/
theorem ord_mul_of_smooth (I J : X.IdealSheafData) (x : X) :
    (I * J).ord x = I.ord x + J.ord x := by
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n f
  have := isRegularLocalRing_stalk f x
  let _ := f.stalkAlgebraRat x
  change (I * J).ord x = I.ord x + J.ord x
  rw [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, Scheme.IdealSheafData.ord_eq_ord_stalkIdeal,
    Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, Scheme.IdealSheafData.stalkIdeal_mul]
  exact Hironaka.Local.ord_mul_of_ordElem_mul
    (ordElem_mul_of_algebraRat (X.presheaf.stalk x)) _ _

include f n in
/-- `ord_mul_of_smooth` for finite products. -/
theorem ord_prod_of_smooth {ι : Type*} (s : Finset ι) (J : ι → X.IdealSheafData) (x : X) :
    (∏ j ∈ s, J j).ord x = ∑ j ∈ s, (J j).ord x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact Scheme.IdealSheafData.ord_top (X := X) (x := x)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ord_mul_of_smooth f n, ih]

include f n in
/-- The weak transform of a product along a smooth center on which every factor has constant
order is the product of the weak transforms (general form over the structure morphism `f`): each
inverse image is `F^{c_j}` times the weak transform (the marked transform with mark `c_j`,
[Kol07, Definition 60, (60.1)]), so the inverse image of the product is `F^{Σ c_j}` times the
product of the weak transforms, and the colon by the invertible `F^{Σ c_j}` recovers it. Not
stated in [Hir64, Corollary 1], whose proof uses it. -/
theorem weakTransform_prod_of_smooth (D : X.IdealSheafData) [Smooth (D.subschemeι ≫ f)] {e : ℕ}
    (J : Fin e → X.IdealSheafData) (c : Fin e → ℕ)
    (hc : ∀ j, ∀ y ∈ D.support, (J j).ord y = c j) :
    (∏ j, J j).weakTransform D = ∏ j, (J j).weakTransform D := by
  -- the orders along the centre
  have hcj : ∀ j, (J j).OrdAlongEq D.support ((c j : ℕ) : ℕ∞) := fun j η hη => hc j η hη.1
  have hsum : (∏ j, J j).OrdAlongEq D.support ((∑ j, c j : ℕ) : ℕ∞) := fun η hη => by
    rw [ord_prod_of_smooth f n Finset.univ J η, Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => hc j η hη.1
  -- the factors' inverse images
  have hfac : ∀ j, (J j).comap D.blowUpπ =
      D.exceptionalDivisor ^ c j * (J j).weakTransform D := fun j => by
    rw [weakTransform_eq_markedTransform_of_smooth f n D (J j) (hcj j)]
    exact (pow_mul_markedTransform D (J j) (c j) (pow_dvd_comap_of_leOrdAlong f n D (J j)
      (fun η hη => (hcj j η hη).ge))).symm
  -- the product
  have hprod : (∏ j, J j).comap D.blowUpπ =
      D.exceptionalDivisor ^ (∑ j, c j) * ∏ j, (J j).weakTransform D := by
    rw [Scheme.IdealSheafData.comap_finset_prod, ← Finset.prod_pow_eq_pow_sum,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hfac j
  rw [weakTransform_eq_markedTransform_of_smooth f n D (∏ j, J j) hsum, markedTransform_eq_colon]
  exact Scheme.IdealSheafData.colon_pow_eq_of_mul_eq _
    (blowUp.isInvertible_comap_π D) _ _ hprod.symm

include f n in
/-- On an irreducible closed subscheme on which the order of the product is constant, the order of
every factor is constant (general form over `f`): each order is upper semicontinuous with its
least value at the generic point, the sums agree, and termwise `≤` with equal finite sums forces
equality. This is condition (1) of [Hir64, Corollary 1] for the factors. -/
theorem ord_factors_const_on_center_of_smooth (D : X.IdealSheafData)
    (hD : IrreducibleSpace D.subscheme) {e : ℕ} (J : Fin e → X.IdealSheafData) (d : ℕ)
    (hd : ∀ y ∈ D.support, (∏ j, J j).ord y = d) (j : Fin e) :
    ∃ c : ℕ, ∀ y ∈ D.support, (J j).ord y = c := by
  -- the generic point of the centre
  have hirr : IsIrreducible (D.support : Set X) := by
    have hemb : Topology.IsEmbedding D.subschemeι.base := D.subschemeι.isClosedEmbedding.isEmbedding
    rw [← Scheme.IdealSheafData.range_subschemeι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ D.subscheme).image _ hemb.continuous.continuousOn
  let Z : IrreducibleCloseds X := ⟨D.support, hirr, D.support.isClosed⟩
  have hη : IsGenericPoint Z.genericPoint (Z : Set X) := Z.isGenericPoint_genericPoint
  have hηD : Z.genericPoint ∈ D.support := hη.mem
  -- pointwise inequalities and the two equal sums
  have husc : ∀ j', UpperSemicontinuous fun x => (J j').ord x := fun j' =>
    Scheme.IdealSheafData.upperSemicontinuous_ord f n (J j')
  have hle : ∀ y ∈ D.support, ∀ j', (J j').ord Z.genericPoint ≤ (J j').ord y := fun y hy j' =>
    Scheme.IdealSheafData.ord_le_ord_of_specializes_of_upperSemicontinuous (J j') (husc j')
      (hη.specializes hy)
  have hsumy : ∀ y ∈ D.support, ∑ j', (J j').ord y = (d : ℕ∞) := fun y hy => by
    rw [← ord_prod_of_smooth f n Finset.univ J y]
    exact hd y hy
  -- the orders are finite
  have hfin : ∀ y ∈ D.support, ∀ j', (J j').ord y ≠ ⊤ := fun y hy j' => by
    intro htop
    have : ∑ j', (J j').ord y = ⊤ := by
      refine ENat.sum_eq_top.mpr ⟨j', Finset.mem_univ _, htop⟩
    rw [hsumy y hy] at this
    exact ENat.natCast_ne_top d this
  refine ⟨((J j).ord Z.genericPoint).toNat, fun y hy => ?_⟩
  -- in `ℕ`: termwise `≤` with equal sums forces equality
  have key : ∀ j', ((J j').ord Z.genericPoint).toNat = ((J j').ord y).toNat := by
    have h1 : ∀ j' ∈ (Finset.univ : Finset (Fin e)),
        ((J j').ord Z.genericPoint).toNat ≤ ((J j').ord y).toNat := fun j' _ =>
      ENat.toNat_le_toNat (hle y hy j') (hfin y hy j')
    have h2 : ∑ j', ((J j').ord Z.genericPoint).toNat = ∑ j', ((J j').ord y).toNat := by
      apply ENat.natCast_inj.mp
      rw [Nat.cast_sum, Nat.cast_sum]
      simp_rw [ENat.natCast_toNat (hfin _ hηD _), ENat.natCast_toNat (hfin y hy _)]
      rw [hsumy _ hηD, hsumy y hy]
    exact fun j' => (Finset.sum_eq_sum_iff_of_le h1).mp h2 j' (Finset.mem_univ _)
  rw [← ENat.natCast_toNat (hfin y hy j), key j]

end Setting

section Corollary

variable (X) [X.Over (Spec (CommRingCat.of k))]

/-- The order of a product is the sum of the orders at every point of a smooth `k`-scheme; used
without comment in the proof of [Hir64, Corollary 1]. -/
theorem ord_mul
    (hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    (I J : X.IdealSheafData) (x : X) : (I * J).ord x = I.ord x + J.ord x := by
  obtain ⟨N, hN⟩ := hN
  exact ord_mul_of_smooth (X ↘ Spec (CommRingCat.of k)) N I J x

/-- The weak transform of a product along a regular center on which every factor has constant
order is the product of the weak transforms (`weakTransform_prod_of_smooth` at the structure
morphism; a regular closed subscheme of a smooth `k`-scheme is smooth over `k`). -/
theorem weakTransform_prod
    (hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    (D : X.IdealSheafData) (hD : IsRegular D.subscheme) {e : ℕ}
    (J : Fin e → X.IdealSheafData) (c : Fin e → ℕ)
    (hc : ∀ j, ∀ y ∈ D.support, (J j).ord y = c j) :
    (∏ j, J j).weakTransform D = ∏ j, (J j).weakTransform D := by
  obtain ⟨N, hN⟩ := hN
  have := SmoothOfRelativeDimension.smooth N (X ↘ Spec (CommRingCat.of k))
  have hDs : Smooth (D.subschemeι ≫ (X ↘ Spec (CommRingCat.of k))) :=
    (Scheme.smooth_iff_isRegular (D.subschemeι ≫ (X ↘ Spec (CommRingCat.of k)))).mpr hD
  exact weakTransform_prod_of_smooth (X ↘ Spec (CommRingCat.of k)) N D J c hc

/-- On an irreducible center on which the order of the product is constant, the order of every
factor is constant (`ord_factors_const_on_center_of_smooth` at the structure morphism); condition
(1) of [Hir64, Corollary 1] for the factors. -/
theorem ord_factors_const_on_center
    (hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    (D : X.IdealSheafData) (hD : IrreducibleSpace D.subscheme)
    {e : ℕ} (J : Fin e → X.IdealSheafData) (d : ℕ) (hd : ∀ y ∈ D.support, (∏ j, J j).ord y = d)
    (j : Fin e) : ∃ c : ℕ, ∀ y ∈ D.support, (J j).ord y = c := by
  obtain ⟨N, hN⟩ := hN
  exact ord_factors_const_on_center_of_smooth (X ↘ Spec (CommRingCat.of k)) N D hD J d hd j

end Corollary

end Hironaka.Sequence
