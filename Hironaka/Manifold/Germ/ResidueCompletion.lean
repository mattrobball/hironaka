/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.StructureSheaf
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Hironaka.Manifold.Germ.TaylorCompletion
import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue field in the completion

Bierstone–Milman's second condition on the local rings of their category of spaces: "the residue
field `F_a := 𝒪_{X,a}/𝔪_{X,a}` is included in `𝒪̂_{X,a}`" [BM97, (0.1)(2)]; and Kollár's
description of the completion, "`𝒪̂_{p,X} ≅ k(p)[[x_1, …, x_n]]`, where `x_1, …, x_n` are local
coordinates" [Kol07, Definition 55]. For the analytic stalk `𝒪_{M,a}` the constants
`const 𝕜 E M a : 𝕜 →+* 𝒪_{M,a}` are a field of representatives, so Kollár's Hensel-lemma
construction of a coefficient field (loc. cit.) is not needed:

* `residue_eq_residue_const`: a germ and the constant `f(a)` have the same residue;
  `bijective_residue_comp_const`: `𝕜 → 𝒪_{M,a} → 𝒪_{M,a}/𝔪_a` is an isomorphism;
* `injective_algebraMap_comp_const`, `exists_evalₐ_one_eq_const`: the constants embed in the
  completion `𝒪̂_{M,a}` and represent every class at its first level `𝒪̂_{M,a} → 𝒪_{M,a}/𝔪_a`
  (Bierstone–Milman's "`F_a` is included in `𝒪̂`", without forming the residue field of `𝒪̂_{M,a}`,
  which Mathlib only provides for Noetherian rings);
* `IsTaylorHom.map_const`, `IsTaylorHom.map_coord_sub_const`,
  `IsTaylorHom.exists_adicCompletion_equiv_const_coord`: under the Taylor homomorphism the
  constants go to the constant series and the centred chart coordinates `x_i − x_i(a)` to the
  variables `X_i`, so the isomorphism `𝒪̂_{M,a} ≅ 𝕜[[X]]` of
  `Hironaka/Manifold/Germ/TaylorCompletion.lean` is Kollár's `𝒪̂ ≅ k(p)[[x]]` with `k(p) = k` the
  constants and `x` the coordinates centred at `a`. Everything rests on `taylorHom_const`,
  `taylorHom_coord_sub`, the uniqueness `IsTaylorHom.eq` and
  `IsTaylorHom.exists_adicCompletion_equiv'`.
-/

public section

noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology IsLocalRing MvPowerSeries
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {a : M}

section ResidueField

/-- A germ and the constant germ of its value at `a` have the same residue: their difference
vanishes at `a`, hence lies in `𝔪_a`. -/
theorem residue_eq_residue_const (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    residue _ s = residue _ (const 𝕜 E M a (eval 𝕜 E M a s)) :=
  Ideal.Quotient.eq.mpr
    ((mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self]))

/-- The composite `𝕜 → 𝒪_{M,a} → 𝒪_{M,a}/𝔪_a` of the constants with the residue map is an
isomorphism ([BM97, (0.1)(2)]; [Kol07, Definition 55]): the constants are a field of
representatives, and the residue field is `𝕜`. Injective as a ring homomorphism out of a field
into a nontrivial ring; surjective because every residue class is that of a constant. -/
theorem bijective_residue_comp_const :
    Function.Bijective
      ((residue ((structureSheaf 𝕜 E M).presheaf.stalk a)).comp (const 𝕜 E M a)) :=
  ⟨((residue _).comp (const 𝕜 E M a)).injective, fun x => by
    obtain ⟨s, rfl⟩ := residue_surjective x
    exact ⟨eval 𝕜 E M a s, (residue_eq_residue_const E s).symm⟩⟩

/-- The first level `𝒪_{M,a} ⧸ 𝔪_a ^ 1` of the completion is a nontrivial ring (`𝔪_a ≠ ⊤`). -/
theorem nontrivial_quotient_maximalIdeal_pow_one :
    Nontrivial ((structureSheaf 𝕜 E M).presheaf.stalk a ⧸
      maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ 1) := by
  rw [pow_one]
  exact inferInstanceAs (Nontrivial (ResidueField ((structureSheaf 𝕜 E M).presheaf.stalk a)))

/-- The completion `Ô_{M,a}` is a nontrivial ring: it projects onto `𝒪_{M,a}/𝔪_a`. -/
theorem nontrivial_adicCompletion :
    Nontrivial (AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a)) :=
  have := nontrivial_quotient_maximalIdeal_pow_one (𝕜 := 𝕜) E (a := a)
  (AdicCompletion.surjective_evalₐ (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
    1).nontrivial

/-- "The residue field `F_a` is included in `𝒪̂`" [BM97, (0.1)(2)]: the constants embed into the
completion `𝒪̂_{M,a}`. -/
theorem injective_algebraMap_comp_const :
    Function.Injective
      ((algebraMap ((structureSheaf 𝕜 E M).presheaf.stalk a)
        (AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
          ((structureSheaf 𝕜 E M).presheaf.stalk a))).comp (const 𝕜 E M a)) :=
  have := nontrivial_adicCompletion (𝕜 := 𝕜) E (a := a)
  RingHom.injective _

/-- Every element of `𝒪̂_{M,a}` agrees with a constant at the first level `𝒪̂_{M,a} → 𝒪_{M,a}/𝔪_a`
of the completion: the constants represent the residue field inside `𝒪̂_{M,a}` [BM97, (0.1)(2)]. -/
theorem exists_evalₐ_one_eq_const
    (x : AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    ∃ c : 𝕜, AdicCompletion.evalₐ (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) 1 x =
      AdicCompletion.evalₐ (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) 1
        (algebraMap _ _ (const 𝕜 E M a c)) := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) 1 x)
  refine ⟨eval 𝕜 E M a s, ?_⟩
  have h2 : AdicCompletion.evalₐ (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) 1
      (algebraMap _ _ (const 𝕜 E M a (eval 𝕜 E M a s))) =
        Ideal.Quotient.mk _ (const 𝕜 E M a (eval 𝕜 E M a s)) :=
    AdicCompletion.evalₐ_of _ 1 _
  rw [h2, ← hs]
  refine Ideal.Quotient.eq.mpr ?_
  rw [pow_one]
  exact (mem_maximalIdeal_iff_eval E _).mpr (by rw [map_sub, eval_const, sub_self])

end ResidueField

section Taylor

variable {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (φ : OpenPartialHomeomorph M E)
  (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M) (ha : a ∈ φ.source)

include hφ ha in
/-- The Taylor homomorphism sends the constant `c` to the constant series `C c` (`taylorHom_const`,
transported to any `T` satisfying the specification by its uniqueness): Kollár's "`k(p) = k`"
[Kol07, Definition 55]. -/
theorem IsTaylorHom.map_const
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (c : 𝕜) : T (const 𝕜 E M a c) = C c := by
  rw [IsTaylorHom.eq E ψ φ hT (isTaylorHom_taylorHom E ψ φ ha hφ), taylorHom_const]

/-- The Taylor homomorphism sends the centred coordinate germ `x_i − x_i(a)` to the variable `X_i`
(`taylorHom_coord_sub`): Kollár's "`x_1, …, x_n` local coordinates" [Kol07, Definition 55]. -/
theorem IsTaylorHom.map_coord_sub_const
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) (i : Fin n) :
    T (coord E ψ φ hφ ha i - const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i))) = X i := by
  rw [IsTaylorHom.eq E ψ φ hT (isTaylorHom_taylorHom E ψ φ ha hφ), taylorHom_coord_sub]

/-- `𝒪̂_{M,a} ≅ 𝕜[[X]]` through the Taylor homomorphism ([BM97, (0.1)(2), (0.3)];
[Kol07, Definition 55]), with the constants going to the constants and the centred chart
coordinates to the variables. -/
theorem IsTaylorHom.exists_adicCompletion_equiv_const_coord
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) :
    ∃ e : AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
        ((structureSheaf 𝕜 E M).presheaf.stalk a) ≃+* MvPowerSeries (Fin n) 𝕜,
      (∀ s, e (algebraMap _ _ s) = T s) ∧
        (∀ c : 𝕜, e (algebraMap _ _ (const 𝕜 E M a c)) = C c) ∧
        ∀ i, e (algebraMap _ _ (coord E ψ φ hφ ha i -
          const 𝕜 E M a (eval 𝕜 E M a (coord E ψ φ hφ ha i)))) = X i := by
  obtain ⟨e, he⟩ := IsTaylorHom.exists_adicCompletion_equiv' E ψ φ ha hφ hT
  exact ⟨e, he, fun c => by rw [he, IsTaylorHom.map_const E ψ φ hφ ha hT],
    fun i => by rw [he, IsTaylorHom.map_coord_sub_const E ψ φ hφ ha hT]⟩

end Taylor

end Manifold

end
