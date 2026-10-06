/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Hironaka.Analytic.Rueckert.PrimitiveLinear
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Localization.Integral

/-!
# The algebraic core of the primitive normalization

The abstract form of the primitive normalization ([GR84, Chapter 3, §1]; the second alternative
of [Fre17, Ch. I, 8.2]): let `R` be a domain of characteristic zero (the base `𝒪_d`; integral
closedness enters only in the division argument, through `minpoly.isIntegrallyClosed_dvd`), `S` a
domain which is finite over `R` through an injective ring map `f` (the quotient `𝒪_n / P` with
the Noether normalization), both algebras over an infinite field `C` (the constants `ℂ`)
compatibly with `f`. Given finitely many elements `ξ_i` of `S` (the classes of the fibre
coordinates) with a distinguished `ξ_{i₀}`:

* there are constants `c_j ∈ C`, `c_{i₀} = 1`, such that `γ := ∑ c_j ξ_j` is a primitive element:
  the field `Frac S` is generated over `Frac R` by `γ` (`PrimitiveLinear.lean`,
  `exists_linear_primitive_of_isIntegral`, applied in `Frac S / Frac R`);
* the minimal polynomial `Q := minpoly R γ` is monic and irreducible in `R[T]` (Mathlib's
  `minpoly.irreducible` for domains) and `Q(γ) = 0`;
* every `ξ_i` lies in `Frac R (γ) = Frac R [γ]` (`γ` is algebraic), so clearing denominators
  gives `A ∈ R ∖ 0` and `B_i ∈ R[T]` with `A · ξ_i = B_i(γ)` in `S`
  (`IsLocalization.integerNormalization`, the injectivity of `S → Frac S`, a common denominator).

The statement is in ring-map form (`Polynomial.eval₂ f`), with no `Algebra R S` instance,
because it is applied to a quotient of `𝒪_n` whose ring structure is not reducibly the one an
`R`-algebra instance built from `f` would carry (the algebra structure is introduced locally
inside the proof by `RingHom.toAlgebra`).
-/

public section

open Polynomial IntermediateField

namespace Analytic

variable {R S : Type*} [CommRing R] [IsDomain R] [CharZero R] [CommRing S] [IsDomain S] {C :
Type*} [Field C] [Algebra C R] [Algebra C S]

/-- The algebraic core of the primitive normalization (the second alternative of
[Fre17, Ch. I, 8.2], over a `d`-dimensional base): for a domain `S` finite over the domain `R`
(characteristic `0`) through an injective `f : R →+* S`, both `C`-algebras compatibly (`C` an
field), and a finite family `ξ_i ∈ S` (`i ∈ s`, `i₀ ∈ s`), there are constants
`c : ι → C` with `c i₀ = 1`, `c = 0` off `s`, such that with `γ := ∑ c_j ξ_j`: the minimal
polynomial `Q` of `γ` over `R` is monic irreducible with `Q(γ) = 0`, and some `A ∈ R ∖ 0` has
`A · ξ_i = B_i(γ)` for polynomials `B_i ∈ R[T]`, every `i ∈ s`. -/
theorem exists_linear_primitive_relations (f : R →+* S) (hf : f.Finite)
    (hinj : Function.Injective f) (hC : ∀ c, f (algebraMap C R c) = algebraMap C S c)
    {ι : Type*} (s : Finset ι) (ξ : ι → S) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ∃ c : ι → C, c i₀ = 1 ∧ (∀ i, i ∉ s → c i = 0) ∧
      ∃ Q : R[X], Q.Monic ∧ Irreducible Q ∧
        eval₂ f (∑ j ∈ s, algebraMap C S (c j) * ξ j) Q = 0 ∧
        ∃ A : R, A ≠ 0 ∧ ∀ i ∈ s, ∃ B : R[X],
          f A * ξ i = eval₂ f (∑ j ∈ s, algebraMap C S (c j) * ξ j) B := by
  classical
  have : CharZero C := (algebraMap C R).charZero
  let _ := f.toAlgebra
  have halg : algebraMap R S = f := rfl
  have hint : Algebra.IsIntegral R S := ⟨fun x => hf.to_isIntegral x⟩
  -- the fraction fields
  let K := FractionRing R
  let Lf := FractionRing S
  have hfs : FaithfulSMul R Lf := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R S Lf]
    exact (IsFractionRing.injective S Lf).comp hinj
  let _ : Algebra K Lf := FractionRing.liftAlgebra R Lf
  have : IsScalarTower R K Lf := FractionRing.isScalarTower_liftAlgebra R Lf
  -- the fibre classes in `Lf`, integral over `K`
  let β : ι → Lf := fun i => algebraMap S Lf (ξ i)
  have hβint : ∀ i ∈ s, IsIntegral K (β i) := fun i _ =>
    ((hint.isIntegral (ξ i)).map (IsScalarTower.toAlgHom R S Lf)).tower_top
  -- the linear primitive element
  obtain ⟨c, hc₀, hcz, hcmem⟩ :=
    exists_linear_primitive_of_isIntegral (F := K) (algebraMap C K) s β hβint hi₀
  set γS : S := ∑ j ∈ s, algebraMap C S (c j) * ξ j with hγS
  have hγ : algebraMap S Lf γS = ∑ j ∈ s, algebraMap C K (c j) • β j := by
    simp only [γS, map_sum, map_mul, β, Algebra.smul_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← hC, IsScalarTower.algebraMap_apply C R K, ← IsScalarTower.algebraMap_apply R K Lf]
    exact (IsScalarTower.algebraMap_apply R S Lf _).symm
  have hγint : IsIntegral R γS := hint.isIntegral γS
  have hγLint : IsIntegral K (algebraMap S Lf γS) :=
    (hγint.map (IsScalarTower.toAlgHom R S Lf)).tower_top
  -- every fibre class is a polynomial in `γ` over `K`
  have hmem : ∀ i ∈ s, ∃ p : K[X], aeval (algebraMap S Lf γS) p = β i := fun i hi => by
    have h := hcmem i hi
    rw [← hγ] at h
    have h2 : β i ∈ (IntermediateField.adjoin K {algebraMap S Lf γS}).toSubalgebra := h
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hγLint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at h2
    exact h2
  -- clearing denominators, one class at a time
  have hclear : ∀ i ∈ s, ∃ (b : R) (B : R[X]), b ≠ 0 ∧ f b * ξ i = eval₂ f γS B := fun i hi => by
    obtain ⟨p, hp⟩ := hmem i hi
    obtain ⟨b, hb, hbp⟩ :=
      IsLocalization.integerNormalization_spec (nonZeroDivisors R) (S := K) p
    refine ⟨b, IsLocalization.integerNormalization (nonZeroDivisors R) p,
      nonZeroDivisors.ne_zero hb, ?_⟩
    apply IsFractionRing.injective S Lf
    have h1 : aeval (algebraMap S Lf γS)
        (IsLocalization.integerNormalization (nonZeroDivisors R) p) = algebraMap R Lf b * β i := by
      rw [← aeval_map_algebraMap K, hbp, ← algebraMap_smul K b p, map_smul, hp, Algebra.smul_def,
        ← IsScalarTower.algebraMap_apply]
    rw [map_mul]
    change algebraMap S Lf (algebraMap R S b) * algebraMap S Lf (ξ i) =
      algebraMap S Lf (aeval γS (IsLocalization.integerNormalization (nonZeroDivisors R) p))
    have h2 : aeval (algebraMap S Lf γS)
        (IsLocalization.integerNormalization (nonZeroDivisors R) p) =
        algebraMap S Lf (aeval γS (IsLocalization.integerNormalization (nonZeroDivisors R) p)) :=
      aeval_algebraMap_apply Lf γS _
    rw [← h2, h1, IsScalarTower.algebraMap_apply R S Lf]
  choose! b B hb hB using hclear
  -- the common denominator
  refine ⟨c, hc₀, hcz, minpoly R γS, minpoly.monic hγint, minpoly.irreducible hγint,
    minpoly.aeval R γS, ∏ j ∈ s, b j, Finset.prod_ne_zero_iff.mpr fun j hj => hb j hj,
    fun i hi => ⟨Polynomial.C (∏ j ∈ s.erase i, b j) * B i, ?_⟩⟩
  rw [eval₂_mul, eval₂_C, ← hB i hi, ← Finset.mul_prod_erase s b hi, map_mul]
  ring

end Analytic
