/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.FieldTheory.PrimitiveElement

/-!
# A primitive element that is a linear combination of given generators

A field-theoretic tool for the local parametrization theorem ([GR84, Chapter 3, §1]; the second
alternative of [Fre17, Ch. I, 8.2]). The classical primitive element theorem (Mathlib's
`Field.exists_primitive_element`) returns some generator of a finite separable extension; the
parametrization needs the generator to be a linear combination `∑ c_j • β_j` of the given
generators `β_j` (the classes of the fibre coordinates) with constant coefficients `c_j ∈ ℂ`, not
elements of the function field `Frac 𝒪_d`, and coefficient `1` on a chosen one, because it is
realised as a coordinate after a linear change of coordinates of `ℂⁿ`. The coefficients are
therefore drawn from an infinite subfield `C` given by a ring map `ϕ : C →+* F`.

The argument is the one Mathlib uses for extensions with finitely many intermediate fields
(`Field.primitive_element_inf_aux_of_finite_intermediateField`, private): over an infinite field
`F`, among the fields `F⟮α + x • β⟯` (`x : F`) two coincide, and then `β`, hence `α`, lies in that
field. Finitely many intermediate fields is Artin's theorem for a finite separable extension
(`Field.finite_intermediateField_of_exists_primitive_element`), applied to the subfield generated
by the `β_j`. Routine field theory, recorded so that the parametrization theorem rests only on
Mathlib and the Weierstrass theory.
-/

public section

open IntermediateField

namespace Analytic

section Pair

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The argument of Mathlib's private `Field.primitive_element_inf_aux_of_finite_intermediateField`,
with the generator `α + ϕ x • β` exposed and the coefficient drawn from a subfield: if `E / F`
has finitely many intermediate fields and `ϕ : C →+* F` is a ring map from an infinite field `C`
(the constants `ℂ` inside the function field `Frac 𝒪_d`), then for all `α β : E` some `x : C`
has `F⟮α, β⟯ = F⟮α + ϕ x • β⟯`. -/
theorem exists_adjoin_pair_eq_adjoin_add_smul {C : Type*} [Field C] [Infinite C] (ϕ : C →+* F)
    [Finite (IntermediateField F E)] (α β : E) : ∃ x : C, F⟮α, β⟯ = F⟮α + ϕ x • β⟯ := by
  let f : C → IntermediateField F E := fun x ↦ F⟮α + ϕ x • β⟯
  obtain ⟨x, y, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨x, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    have αxβ_in_K : α + ϕ x • β ∈ F⟮α + ϕ x • β⟯ := mem_adjoin_simple_self F _
    have αyβ_in_K : α + ϕ y • β ∈ F⟮α + ϕ y • β⟯ := mem_adjoin_simple_self F _
    have heq' : F⟮α + ϕ y • β⟯ = F⟮α + ϕ x • β⟯ := heq.symm
    rw [heq'] at αyβ_in_K
    have β_in_K := sub_mem αxβ_in_K αyβ_in_K
    rw [show (α + ϕ x • β) - (α + ϕ y • β) = (ϕ x - ϕ y) • β by rw [sub_smul]; abel1] at β_in_K
    have hxy : ϕ x - ϕ y ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hneq (ϕ.injective h)
    replace β_in_K := smul_mem _ β_in_K (x := (ϕ x - ϕ y)⁻¹)
    rw [smul_smul, inv_mul_eq_div, div_self hxy, one_smul] at β_in_K
    have α_in_K : α ∈ F⟮α + ϕ x • β⟯ := by
      convert! ← sub_mem αxβ_in_K (smul_mem _ β_in_K)
      apply add_sub_cancel_right
    rintro z (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert α {β})
    have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (Set.mem_insert_of_mem α rfl)
    exact F⟮α, β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ)

/-- Iterating `exists_adjoin_pair_eq_adjoin_add_smul` over a finite family `β` indexed by
`insert i₀ t` (`i₀ ∉ t`): a linear combination `∑ ϕ (c j) • β_j` with coefficients `c` in the
subfield `C`, `c i₀ = 1` and `c = 0` off the index set, generates a field containing every
`β_i`, `i ∈ insert i₀ t`. -/
theorem exists_linear_primitive_aux {C : Type*} [Field C] [Infinite C] (ϕ : C →+* F)
    [Finite (IntermediateField F E)] {ι : Type*} [DecidableEq ι] (β : ι → E) (i₀ : ι)
    (t : Finset ι) (hi₀ : i₀ ∉ t) :
    ∃ c : ι → C, c i₀ = 1 ∧ (∀ i, i ∉ insert i₀ t → c i = 0) ∧
      ∀ i ∈ insert i₀ t, β i ∈ F⟮∑ j ∈ insert i₀ t, ϕ (c j) • β j⟯ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨fun i => if i = i₀ then 1 else 0, by simp, fun i hi => ?_, fun i hi => ?_⟩
    · have : i ≠ i₀ := by simpa using hi
      simp [this]
    · have hi' : i = i₀ := by simpa using hi
      subst hi'
      simpa using mem_adjoin_simple_self F (β i)
  | insert a t hat ih =>
    have hi₀' : i₀ ∉ t := fun h => hi₀ (Finset.mem_insert_of_mem h)
    have hai₀ : a ≠ i₀ := fun h => hi₀ (h ▸ Finset.mem_insert_self a t)
    obtain ⟨c, hc₀, hcz, hcmem⟩ := ih hi₀'
    set γ := ∑ j ∈ insert i₀ t, ϕ (c j) • β j with hγ
    obtain ⟨x, hx⟩ := exists_adjoin_pair_eq_adjoin_add_smul (F := F) ϕ γ (β a)
    have hanot : a ∉ insert i₀ t := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hai₀, hat⟩
    have hcomm : insert i₀ (insert a t) = insert a (insert i₀ t) := Finset.insert_comm i₀ a t
    refine ⟨Function.update c a x, ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [Function.update_of_ne (Ne.symm hai₀), hc₀]
    · rw [hcomm] at hi
      have hia : i ≠ a := fun h => hi (by rw [h]; exact Finset.mem_insert_self a _)
      have hi' : i ∉ insert i₀ t := fun h => hi (Finset.mem_insert_of_mem h)
      rw [Function.update_of_ne hia]
      exact hcz i hi'
    · rw [hcomm] at hi ⊢
      have hsum : ∑ j ∈ insert a (insert i₀ t), ϕ (Function.update c a x j) • β j =
          γ + ϕ x • β a := by
        rw [Finset.sum_insert hanot, Function.update_self, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hja : j ≠ a := fun h => hanot (h ▸ hj)
        rw [Function.update_of_ne hja]
      rw [hsum, ← hx]
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact subset_adjoin F {γ, β i} (Set.mem_insert_of_mem γ rfl)
      · have hγmem : F⟮γ⟯ ≤ F⟮γ, β a⟯ :=
          adjoin_simple_le_iff.mpr (subset_adjoin F {γ, β a} (Set.mem_insert γ {β a}))
        exact hγmem (hcmem i hi')

end Pair

section Integral

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- In characteristic zero, a finite family `β` of elements of `E` integral over `F`, indexed by a
finset `s` with a distinguished `i₀ ∈ s`, admits coefficients `c : ι → C` in a subfield
`C` (given by `ϕ : C →+* F`) with `c i₀ = 1`, `c = 0` off `s`, such that every `β_i` (`i ∈ s`)
lies in `F⟮∑ j ∈ s, ϕ (c j) • β j⟯`: a primitive element of `F(β_i : i ∈ s)` that is a
`C`-linear combination of the generators. The primitive element theorem (Artin) gives finitely
many intermediate fields of `F(β_i : i ∈ s) / F`, and the pair lemma is iterated inside that
field. -/
theorem exists_linear_primitive_of_isIntegral [CharZero F] {C : Type*} [Field C]
    (ϕ : C →+* F) {ι : Type*} (s : Finset ι) (β : ι → E) (hβ : ∀ i ∈ s, IsIntegral F (β i))
    {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ∃ c : ι → C, c i₀ = 1 ∧ (∀ i, i ∉ s → c i = 0) ∧
      ∀ i ∈ s, β i ∈ F⟮∑ j ∈ s, ϕ (c j) • β j⟯ := by
  classical
  have : CharZero C := ϕ.charZero
  -- the subfield generated by the family
  set M : IntermediateField F E := IntermediateField.adjoin F (β '' (s : Set ι)) with hM
  have : Finite ↑(β '' (s : Set ι)) := (s.finite_toSet.image β).to_subtype
  have : FiniteDimensional F M :=
    IntermediateField.finiteDimensional_adjoin fun x hx => by
      obtain ⟨i, hi, rfl⟩ := hx
      exact hβ i hi
  have : Algebra.IsSeparable F M := Algebra.IsSeparable.of_integral F M
  have : Finite (IntermediateField F M) :=
    Field.finite_intermediateField_of_exists_primitive_element F M
      (Field.exists_primitive_element F M)
  -- the family inside `M`
  have hmem : ∀ i ∈ s, β i ∈ M := fun i hi =>
    IntermediateField.subset_adjoin F _ ⟨i, hi, rfl⟩
  let β' : ι → M := fun i => if h : i ∈ s then ⟨β i, hmem i h⟩ else 0
  have hβ' : ∀ i ∈ s, (β' i : E) = β i := fun i hi => by simp [β', hi]
  have hs : s = insert i₀ (s.erase i₀) := (Finset.insert_erase hi₀).symm
  obtain ⟨c, hc₀, hcz, hcmem⟩ :=
    exists_linear_primitive_aux (F := F) ϕ β' i₀ (s.erase i₀) (Finset.notMem_erase i₀ s)
  rw [← hs] at hcz hcmem
  refine ⟨c, hc₀, hcz, fun i hi => ?_⟩
  -- transport the membership from `M` to `E` along `M.val`
  have hval : (M.val : M →ₐ[F] E) (∑ j ∈ s, ϕ (c j) • β' j) = ∑ j ∈ s, ϕ (c j) • β j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, IntermediateField.coe_val, hβ' j hj]
  have h1 := hcmem i hi
  have h2 : (M.val : M →ₐ[F] E) (β' i) ∈
      (F⟮∑ j ∈ s, ϕ (c j) • β' j⟯).map (M.val : M →ₐ[F] E) :=
    (IntermediateField.mem_map _).mpr ⟨_, h1, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton, hval, IntermediateField.coe_val,
    hβ' i hi] at h2
  exact h2

end Integral

end Analytic
