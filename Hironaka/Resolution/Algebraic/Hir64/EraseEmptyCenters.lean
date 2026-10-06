/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Hironaka.Resolution.Algebraic.Hir64.SingleCenterTools
import Hironaka.Resolution.Algebraic.Kol07.Thm36.IsoOverSmoothLocus
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Points of the centers under pull-back and under the deletion of empty blow-ups

The set of points of the base over which some center of a blow-up sequence has a point is
unchanged by the deletion of the empty blow-ups (the empty blow-up convention of [Kol07, 32]:
empty blow-ups "are then ignored"), and it moves along a flat pull-back as
`restrictedCenterHasPointOver_pullback_iff` of
`Hironaka/Scheme/BlowUpSequence/RestrictedCenters.lean` says. These are the facts about the centers
that the resolution of an affine scheme needs when its sequence is compared with the sequence of an
open piece.

The predicate is `RestrictedCenterHasPointOver S J i x` at the zero ideal `J = ⊥`: the strict
transform of `⊥` is `⊥` (`strictTransformSeq_bot`), whose support is everything, so the predicate
reads "the center `Z_i` has a point over `x`" (`restrictedCenterHasPointOver_bot_iff`). Along
`cons X D rest` the base points are those of `D` and the images under `D.blowUpπ` of the base
points of `rest` (`exists_restrictedCenterHasPointOver_bot_cons_iff`); the deletion keeps a
nonempty first center and, for an empty one (`D = ⊤`, no base point), carries the tail back along
the isomorphism `inv (blowUpπ X ⊤)`, which is a flat pull-back
(`exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence
open AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- At the zero ideal the restricted-center predicate reads "the center `Z_i` has a point over
`x`": the strict transform of `⊥` is `⊥` (`strictTransformSeq_bot`), whose support is the whole
stage. -/
theorem restrictedCenterHasPointOver_bot_iff (S : BlowUpSequence X) (i : Fin S.length) (x : X) :
    RestrictedCenterHasPointOver S ⊥ i x ↔
      ∃ p : S.stage i.castSucc, p ∈ (S.center i).support ∧ S.stageMap i.castSucc p = x := by
  unfold RestrictedCenterHasPointOver
  constructor
  · rintro ⟨p, hZ, -, hp⟩
    exact ⟨p, hZ, hp⟩
  · rintro ⟨p, hZ, hp⟩
    refine ⟨p, hZ, ?_, hp⟩
    rw [Hironaka.Resolution.strictTransformSeq_bot, support_bot]
    exact Set.mem_univ p

/-- Some restricted center of the pull-back along a flat `h` has a point over `y` iff some
restricted center of `S` has a point over `h y` (`restrictedCenterHasPointOver_pullback_iff` with
the index bijection `pullbackCenterIdx`). -/
theorem exists_restrictedCenterHasPointOver_pullback_iff (S : BlowUpSequence X) (h : Y ⟶ X)
    [Flat h] (J : X.IdealSheafData) (y : Y) :
    (∃ i, RestrictedCenterHasPointOver (S.pullback h) (J.comap h) i y) ↔
      ∃ i, RestrictedCenterHasPointOver S J i (h y) := by
  constructor
  · rintro ⟨i', hi'⟩
    refine ⟨Fin.cast (length_pullback S h) i', ?_⟩
    refine (restrictedCenterHasPointOver_pullback_iff S h J _ y).1 ?_
    exact (Hironaka.Resolution.restrictedCenterHasPointOver_congr rfl rfl rfl y).1 hi'
  · rintro ⟨i, hi⟩
    exact ⟨_, (restrictedCenterHasPointOver_pullback_iff S h J i y).2 hi⟩

/-- The base points under some center of `cons X D rest` are the points of `D` and the images
under `D.blowUpπ` of the base points under some center of `rest`. -/
theorem exists_restrictedCenterHasPointOver_bot_cons_iff (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (x : X) :
    (∃ i, RestrictedCenterHasPointOver (cons X D rest) ⊥ i x) ↔
      x ∈ D.support ∨ ∃ q : D.blowUp, D.blowUpπ q = x ∧
        ∃ j, RestrictedCenterHasPointOver rest ⊥ j q := by
  constructor
  · rintro ⟨⟨_ | j, hj⟩, hi⟩
    · rw [restrictedCenterHasPointOver_bot_iff] at hi
      obtain ⟨p, hZ, hp⟩ := hi
      left
      have hp' : p = x := hp
      exact hp' ▸ hZ
    · rw [restrictedCenterHasPointOver_bot_iff] at hi
      obtain ⟨p, hZ, hp⟩ := hi
      right
      have hj' : j < rest.length := Nat.lt_of_succ_lt_succ hj
      refine ⟨rest.stageMap (⟨j, hj'⟩ : Fin rest.length).castSucc p, hp, ⟨j, hj'⟩, ?_⟩
      rw [restrictedCenterHasPointOver_bot_iff]
      exact ⟨p, hZ, rfl⟩
  · rintro (hx | ⟨q, hq, j, hj⟩)
    · refine ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
      rw [restrictedCenterHasPointOver_bot_iff]
      exact ⟨x, hx, rfl⟩
    · rw [restrictedCenterHasPointOver_bot_iff] at hj
      obtain ⟨p, hZ, hp⟩ := hj
      refine ⟨⟨j.val + 1, Nat.succ_lt_succ j.2⟩, ?_⟩
      rw [restrictedCenterHasPointOver_bot_iff]
      refine ⟨p, hZ, ?_⟩
      change D.blowUpπ (rest.stageMap j.castSucc p) = x
      rw [hp, hq]

/-- Deleting the empty blow-ups [Kol07, 32] leaves the set of base points under some center
unchanged: an empty first center (`D = ⊤`) has no base point and its tail is carried back along
the isomorphism `inv (blowUpπ X ⊤)`, a flat pull-back; a nonempty first center is kept. -/
theorem exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (x : X),
      (∃ i, RestrictedCenterHasPointOver S.eraseEmpty ⊥ i x) ↔
        ∃ i, RestrictedCenterHasPointOver S ⊥ i x
  | _, nil X, x => Iff.rfl
  | _, cons X D rest, x => by
    classical
    by_cases hD : D = ⊤
    · have hiso : IsIso D.blowUpπ := isIso_blowUpπ_of_eq_top hD
      rw [eraseEmpty_cons_of_eq_top rest hD, exists_restrictedCenterHasPointOver_bot_cons_iff]
      have key := exists_restrictedCenterHasPointOver_pullback_iff rest.eraseEmpty
        (inv D.blowUpπ) ⊥ x
      rw [comap_bot] at key
      rw [key, exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff rest]
      have hsupp : x ∉ D.support := by
        rw [hD, support_top]
        exact fun h => h
      constructor
      · intro h
        exact Or.inr ⟨inv D.blowUpπ x, by
          rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl, h⟩
      · rintro (hx | ⟨q, hq, h⟩)
        · exact (hsupp hx).elim
        · have hq' : inv D.blowUpπ x = q := by
            rw [← hq, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
          rw [hq']
          exact h
    · rw [eraseEmpty_cons_of_ne_top rest hD, exists_restrictedCenterHasPointOver_bot_cons_iff,
        exists_restrictedCenterHasPointOver_bot_cons_iff]
      exact or_congr_right (exists_congr fun q => and_congr_right fun _ =>
        exists_restrictedCenterHasPointOver_bot_eraseEmpty_iff rest q)

end Hironaka.Sequence
