/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
public import Hironaka.Scheme.BlowUpSequence.Concat
import Hironaka.Scheme.BlowUpSequence.ConcatTotalTransform
import Hironaka.Scheme.BlowUpSequence.ConcatTransforms
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Heterogeneous equalities for the truncation and the concatenation of blow-up sequences

The embedded desingularization sequence (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) reads the
absorbing stage through the truncation `run.take n` at its last index, whose end result is only
propositionally the run's stage `n`, and glues the truncation to the restarted run by `concat`,
whose end result is only propositionally the restarted run's. The facts about the loop are proved in
the index form of the run's stages and at the restarted run's end. This module holds the bookkeeping
that carries data across the two casts: an ideal sheaf equal to the pullback of another along
`eqToHom h` is heterogeneously equal to it (`heq_of_eq_comap_eqToHom`), and heterogeneous equality
is compatible with the constructions the loop uses (colon, product, the vanishing ideal of a union
of supports, the image of a finite set, composition with a morphism, the strict, marked and total
transforms along a concatenation). Nothing here is mathematics; every proof is `subst` and a
rewrite. The lemmas are used by the analysis of the loop
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep`).
-/

public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

/-- An ideal sheaf equal to the pull-back of another along the cast `eqToHom h` is heterogeneously
equal to it. -/
theorem heq_of_eq_comap_eqToHom {Y Y' : Scheme.{u}} (h : Y = Y') {a : Y.IdealSheafData}
    {b : Y'.IdealSheafData} (hab : a = b.comap (eqToHom h)) : HEq a b := by
  subst h
  rw [eqToHom_refl, IdealSheafData.comap_id] at hab
  exact heq_of_eq hab

/-- `heq_of_eq_comap_eqToHom` for divisor families. -/
theorem heq_of_eq_comap_eqToHom_divisorFamily {Y Y' : Scheme.{u}} (h : Y = Y')
    {E : DivisorFamily Y} {E' : DivisorFamily Y'} (hE : E = E'.comap (eqToHom h)) : HEq E E' := by
  subst h
  rw [eqToHom_refl, DivisorFamily.comap_id] at hE
  exact heq_of_eq hE

/-- Heterogeneous equality is compatible with the colon. -/
theorem heq_colon {Y Y' : Scheme.{u}} (h : Y = Y') {a b : Y.IdealSheafData}
    {a' b' : Y'.IdealSheafData} (ha : HEq a a') (hb : HEq b b') :
    HEq (a.colon b) (a'.colon b') := by
  subst h
  rw [eq_of_heq ha, eq_of_heq hb]

/-- Heterogeneous equality is compatible with the product. -/
theorem heq_mul {Y Y' : Scheme.{u}} (h : Y = Y') {a b : Y.IdealSheafData}
    {a' b' : Y'.IdealSheafData} (ha : HEq a a') (hb : HEq b b') : HEq (a * b) (a' * b') := by
  subst h
  rw [eq_of_heq ha, eq_of_heq hb]

/-- Heterogeneous equality is compatible with the vanishing ideal of a finite union of supports. -/
theorem heq_vanishingIdeal_biSup_support {Y Y' : Scheme.{u}} (h : Y = Y') {ι : Type v}
    (A : Finset ι) {g : ι → Y.IdealSheafData} {g' : ι → Y'.IdealSheafData}
    (hg : ∀ c, HEq (g c) (g' c)) :
    HEq (IdealSheafData.vanishingIdeal (⨆ c ∈ A, (g c).support)) (IdealSheafData.vanishingIdeal
        (⨆ c ∈ A, (g' c).support)) := by
  subst h
  rw [funext fun c => eq_of_heq (hg c)]

open Classical in
/-- Heterogeneous equality is compatible with the image of a finite set. -/
theorem heq_finset_image {Y Y' : Scheme.{u}} (h : Y = Y') {ι : Type v} (A : Finset ι)
    {g : ι → Y.IdealSheafData} {g' : ι → Y'.IdealSheafData} (hg : ∀ c, HEq (g c) (g' c)) :
    HEq (A.image g) (A.image g') := by
  subst h
  rw [funext fun c => eq_of_heq (hg c)]

/-- Heterogeneous equality is compatible with the pull-back of an ideal sheaf. -/
theorem heq_comap {Y Y' Z : Scheme.{u}} (h : Y = Y') {f : Y ⟶ Z} {f' : Y' ⟶ Z} (hf : HEq f f')
    (I : Z.IdealSheafData) : HEq (I.comap f) (I.comap f') := by
  subst h
  rw [eq_of_heq hf]

/-- Heterogeneous equality is compatible with a finite product. -/
theorem heq_finset_prod {Y Y' : Scheme.{u}} (h : Y = Y') {ι : Type v} (A : Finset ι)
    {g : ι → Y.IdealSheafData} {g' : ι → Y'.IdealSheafData} (hg : ∀ c, HEq (g c) (g' c)) :
    HEq (∏ c ∈ A, g c) (∏ c ∈ A, g' c) := by
  subst h
  rw [funext fun c => eq_of_heq (hg c)]

/-- Pointwise heterogeneously equal families of ideal sheaves are heterogeneously equal. -/
theorem heq_pi {Y Y' : Scheme.{u}} (h : Y = Y') {α : Sort v} {f : α → Y.IdealSheafData}
    {g : α → Y'.IdealSheafData} (hfg : ∀ a, HEq (f a) (g a)) : HEq f g := by
  subst h
  exact heq_of_eq (funext fun a => eq_of_heq (hfg a))

/-- An equation of ideal sheaves transports across a cast. -/
theorem eq_of_heq_of_heq {Y Y' : Scheme.{u}} (h : Y = Y') {a b : Y.IdealSheafData}
    {a' b' : Y'.IdealSheafData} (ha : HEq a a') (hb : HEq b b') (hab : a' = b') : a = b := by
  subst h
  rw [eq_of_heq ha, eq_of_heq hb, hab]

section Concat

variable {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last)

/-- The strict transform along a concatenation, heterogeneously: the iterated strict transform. -/
theorem strictTransformSeq_concat_last_heq (D : X.IdealSheafData) :
    HEq ((S.concat T).strictTransformSeq D (Fin.last _))
      (T.strictTransformSeq (S.strictTransformSeq D (Fin.last _)) (Fin.last _)) :=
  heq_of_eq_comap_eqToHom (last_concat S T)
    (strictTransformSeq_concat_last S T D)

/-- The marked transform along a concatenation, heterogeneously. -/
theorem markedTransformSeq_concat_last_heq (I : X.IdealSheafData) (m : ℕ) :
    HEq ((S.concat T).markedTransformSeq I m (Fin.last _))
      (T.markedTransformSeq (S.markedTransformSeq I m (Fin.last _)) m (Fin.last _)) :=
  heq_of_eq_comap_eqToHom (last_concat S T) (markedTransformSeq_concat_last S T I m)

/-- The total transform along a concatenation, heterogeneously. -/
theorem totalTransformSeq_concat_last_heq (E : DivisorFamily X) :
    HEq ((S.concat T).totalTransformSeq E (Fin.last _))
      (T.totalTransformSeq (S.totalTransformSeq E (Fin.last _)) (Fin.last _)) :=
  heq_of_eq_comap_eqToHom_divisorFamily (last_concat S T) (totalTransformSeq_concat_last S T E)

/-- The pull-back along the composite of a concatenation, heterogeneously. -/
theorem comap_composite_concat_heq (I : X.IdealSheafData) :
    HEq (I.comap (S.concat T).composite) ((I.comap S.composite).comap T.composite) :=
  heq_of_eq_comap_eqToHom (last_concat S T) (comap_composite_concat S T I)

end Concat

end Hironaka.Resolution
