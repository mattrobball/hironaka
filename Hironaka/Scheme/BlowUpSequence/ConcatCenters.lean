/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The centers of a concatenation lie over a given set

The centers of `S.concat T` lie over a set `Z ⊆ X` when those of `S` do and those of `T` do after
`S.composite`. This is the form of `forall_center_concat`
(`Hironaka/Scheme/BlowUpSequence/ConcatApi.lean`) that involves the stage maps rather than the
center ideals alone; it is used when the composite of a blow-up sequence whose centers lie over the
singular locus is rewritten as a single blow-up with a suitably chosen center, as in the remark
following Main Theorem I in [Hir64, pp. 132–133].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry

/-- The centers of a concatenation lie over `Z` when those of `S` do and those of `T` do after
`S.composite` (structural recursion on `S`: the first center of `cons X D rest` is `D` under
`𝟙 X`, the others are those of `rest.concat T` followed by `D.blowUpπ`). -/
theorem forall_center_concat_mem :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last) (Z : Set X),
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ Z) →
      (∀ (i : Fin T.length) (z : T.stage i.castSucc), z ∈ (T.center i).support →
        S.composite (T.stageMap i.castSucc z) ∈ Z) →
      ∀ (i : Fin (S.concat T).length) (z : (S.concat T).stage i.castSucc),
        z ∈ ((S.concat T).center i).support → (S.concat T).stageMap i.castSucc z ∈ Z
  | _, nil X, T, Z, _, hT, i, z, hz => by
    have h := hT i z hz
    change T.stageMap i.castSucc z ∈ Z
    exact h
  | _, cons X D rest, T, Z, hS, hT, ⟨0, _⟩, z, hz => hS ⟨0, Nat.succ_pos _⟩ z hz
  | _, cons X D rest, T, Z, hS, hT, ⟨j + 1, hj⟩, z, hz => by
    have hS' : ∀ (i : Fin rest.length) (z : rest.stage i.castSucc), z ∈ (rest.center i).support →
        rest.stageMap i.castSucc z ∈ D.blowUpπ ⁻¹' Z :=
      fun i z hz => hS ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ z hz
    have hT' : ∀ (i : Fin T.length) (z : T.stage i.castSucc), z ∈ (T.center i).support →
        rest.composite (T.stageMap i.castSucc z) ∈ D.blowUpπ ⁻¹' Z := by
      intro i z hz
      let y : rest.last := T.stageMap i.castSucc z
      have h : (rest.composite ≫ D.blowUpπ) y ∈ Z := hT i z hz
      rw [Scheme.Hom.comp_apply] at h
      exact h
    have hj' : j < (rest.concat T).length := Nat.lt_of_succ_lt_succ hj
    have ih := forall_center_concat_mem rest T (D.blowUpπ ⁻¹' Z) hS' hT'
      (⟨j, hj'⟩ : Fin (rest.concat T).length) z hz
    let w : (rest.concat T).stage (⟨j, hj'⟩ : Fin (rest.concat T).length).castSucc := z
    have h2 :
        ((rest.concat T).stageMap (⟨j, hj'⟩ : Fin (rest.concat T).length).castSucc ≫
          D.blowUpπ) w ∈ Z := by
      rw [Scheme.Hom.comp_apply]
      exact ih
    exact h2

end AlgebraicGeometry
