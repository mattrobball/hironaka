/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Finite sums and products of locally finitely generated ideal sheaves

Sums, products and powers of locally finitely generated ideal sheaves are locally finitely
generated; the binary `+` and `*`, `⊤` and `⊥` are built from their stalks by `IdealSheaf.ofStalks`,
and the power `pow` by recursion. To write finite sums `∑ i ∈ F, G i` and finite products
`∏ i ∈ F, G i` of ideal sheaves — Kollár's maximal coefficient ideal
`W_s(I) = ∑_{wt(e) ≥ s} ∏_j (D^j I)^{e_j}` [Kol07, Definition 98] is one — this module records the
`AddCommMonoid` and `CommMonoid` structures of `IdealSheaf 𝒪` on those operations: `0 = ⊥`, `1 = ⊤`,
`+` and `*` the existing sum and product, and the monoid power `npow n J` the existing `pow`
(definitionally; five `rfl` examples check that no second power, unit or zero appears). Every law
holds stalkwise (`IdealSheaf.ext` and the stalk simp lemmas), and taking the stalk at a point is
additive and multiplicative on finite families (`stalkIdeal_finset_sum`, `stalkIdeal_finset_prod`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory

universe u

namespace Manifold

namespace IdealSheaf

section Monoid

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

instance : Zero (IdealSheaf 𝒪) := ⟨⊥⟩

instance : One (IdealSheaf 𝒪) := ⟨⊤⟩

@[simp] theorem stalkIdeal_zero (x : X) : (0 : IdealSheaf 𝒪).stalkIdeal x = ⊥ := stalkIdeal_bot x

@[simp] theorem stalkIdeal_one (x : X) : (1 : IdealSheaf 𝒪).stalkIdeal x = ⊤ := stalkIdeal_top x

/-- The additive monoid of ideal sheaves, `0 = ⊥` and `+` the sum (stalkwise sup). -/
instance : AddCommMonoid (IdealSheaf 𝒪) where
  add := (· + ·)
  zero := 0
  add_assoc a b c := ext fun x => by simp [sup_assoc]
  zero_add a := ext fun x => by simp
  add_zero a := ext fun x => by simp
  add_comm a b := ext fun x => by simp [sup_comm]
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

/-- The sum of ideal sheaves is monotone: `IdealSheaf 𝒪` is an ordered additive monoid, so that
Mathlib's `Finset.single_le_sum` and `Finset.sum_le_sum` apply to finite sums of ideal sheaves. -/
instance : IsOrderedAddMonoid (IdealSheaf 𝒪) where
  add_le_add_left _ _ h _ := fun x => by
    simp only [stalkIdeal_add]
    exact sup_le_sup_right (h x) _

/-- The multiplicative monoid of ideal sheaves, `1 = ⊤`, `*` the product and `J ^ n` the existing
`pow`. -/
instance : CommMonoid (IdealSheaf 𝒪) where
  mul := (· * ·)
  one := 1
  mul_assoc a b c := ext fun x => by simp [mul_assoc]
  one_mul a := ext fun x => by simp
  mul_one a := ext fun x => by simp
  mul_comm a b := ext fun x => by simp [mul_comm]
  npow n J := J ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl

/-- The monoid structures sit on the existing operations: no second power, unit or zero. -/
example (J : IdealSheaf 𝒪) (n : ℕ) : NPow.npow n J = J ^ n := rfl
example (J : IdealSheaf 𝒪) (n : ℕ) : NPow.npow n J = J.pow n := rfl
example : (1 : IdealSheaf 𝒪) = ⊤ := rfl
example : (0 : IdealSheaf 𝒪) = ⊥ := rfl
example (I J : IdealSheaf 𝒪) : I * J = Mul.mul I J := rfl

theorem stalkIdeal_finset_sum {ι : Type*} (F : Finset ι) (G : ι → IdealSheaf 𝒪) (x : X) :
    (∑ i ∈ F, G i).stalkIdeal x = ∑ i ∈ F, (G i).stalkIdeal x := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, stalkIdeal_add, ih]; rfl

@[simp]
theorem stalkIdeal_finset_prod {ι : Type*} (F : Finset ι) (G : ι → IdealSheaf 𝒪) (x : X) :
    (∏ i ∈ F, G i).stalkIdeal x = ∏ i ∈ F, (G i).stalkIdeal x := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, stalkIdeal_mul, ih]

/-- The stalks of an ideal sheaf have local generators (its `locallyFG` field). -/
theorem hasLocalGenerators_stalkIdeal (J : IdealSheaf 𝒪) : HasLocalGenerators J.stalkIdeal :=
  fun a => by
    obtain ⟨U, ha, k, f, -, hf⟩ := J.exists_generators a
    exact ⟨U, ha, Fin k, inferInstance, f, hf⟩

end Monoid

end IdealSheaf

end Manifold

end
