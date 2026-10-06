/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Totient

/-!
# The stalk of a product of ideal sheaves with disjoint supports

A stalk computation used by the embedded desingularization at a point of an isolated strict
transform, where the ideal to be resolved further is the colon `I : I_Γ` by the reduced ideal
`I_Γ` of the union of the strict transforms already isolated, the product of the pairwise disjoint
strict transforms (the isolation of the components in the proof of [Wlo05, Theorem 4.7.1];
compare the factorization `I = M(I) · N(I)` of [Kol07, Definition–Lemma 110]). The lemma
`stalkIdeal_finset_prod_eq_of_mem_of_pairwise_disjoint` says that the stalk of a product of ideal
sheaves with pairwise disjoint supports at a point of one member's support is that member's stalk
(the other factors are the unit ideal there); it is the indexed form, on any scheme, of
`Hironaka.Resolution.stalkIdeal_prod_eq_of_mem`. The stalk of the colon itself is
`stalkIdeal_colon_of_isLocallyNoetherian` (`Hironaka/Scheme/BlowUp/FlatColon.lean`), imported here
for the modules of the embedded desingularization.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The stalk of a product of ideal sheaves with pairwise disjoint supports at a point of one
member's support is that member's stalk; the other factors have the unit stalk there (the indexed
form of `Hironaka.Resolution.stalkIdeal_prod_eq_of_mem`, on any scheme). -/
theorem stalkIdeal_finset_prod_eq_of_mem_of_pairwise_disjoint {ι : Type*} (A : Finset ι)
    (I : ι → X.IdealSheafData)
    (hdisj : (A : Set ι).Pairwise fun a b => Disjoint (I a).support (I b).support)
    {a : ι} (ha : a ∈ A) {x : X} (hx : x ∈ (I a).support) :
    (∏ b ∈ A, I b).stalkIdeal x = (I a).stalkIdeal x := by
  classical
  rw [stalkIdeal_finset_prod, Finset.prod_eq_single a]
  · intro b hb hba
    rw [Ideal.one_eq_top]
    refine stalkIdeal_eq_top_of_notMem_support _ fun hxb => ?_
    have hmem : x ∈ (((I b).support ⊓ (I a).support : Closeds X) : Set X) := by
      rw [Closeds.coe_inf]
      exact ⟨hxb, hx⟩
    have hbot : x ∈ ((⊥ : Closeds X) : Set X) := (hdisj hb ha hba).le_bot hmem
    rw [Closeds.coe_bot] at hbot
    exact hbot
  · exact fun habs => (habs ha).elim

end AlgebraicGeometry.Scheme.IdealSheafData
