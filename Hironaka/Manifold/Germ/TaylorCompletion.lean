/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Hironaka.Analytic.Weierstrass.AdicComplete
public import Hironaka.Manifold.Germ.TaylorHom
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Hironaka.Manifold.Germ.TaylorIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The completion of a stalk of the structure sheaf

Bierstone–Milman's Taylor series homomorphism "induces an isomorphism `𝒪̂_{M,a} ≅ F_a[[X]]`"
[BM97, (0.3)]. Since the Taylor homomorphism `T_a` reflects the powers of the maximal ideal
(`taylorHom_mem_maximalIdeal_pow_iff`, `Hironaka/Manifold/Germ/TaylorIdeal.lean`) and its
range, the convergent series, contains the polynomials, `T_a` induces isomorphisms
`𝒪_{M,a}/𝔪_a^k ≅ 𝕜[[X]]/(X)^k` for every `k` (`taylorQuot`); `𝕜[[X]]` being `(X)`-adically complete
(`isAdicComplete_maximalIdeal` of `Hironaka/Analytic/Weierstrass/AdicComplete.lean`),
Mathlib's universal property `IsAdicComplete.liftRingHom` assembles them into a ring homomorphism
`taylorCompletion : AdicCompletion 𝔪_a 𝒪_{M,a} →+* 𝕜[[X]]`, which is injective (the quotient maps
are) and surjective (a series is the limit of the images of the lifts of its truncations), and
restricts to `T_a` on `𝒪_{M,a}` (`taylorCompletionEquiv`,
`IsTaylorHom.exists_adicCompletion_equiv'`). The isomorphism gives the Krull dimension of the
stalk (`Hironaka/Manifold/Germ/StalkNoetherian.lean`) and, with the constants and coordinates,
Kollár's `𝒪̂_{p,X} ≅ k(p)[[x_1, …, x_n]]` (`Hironaka/Manifold/Germ/ResidueCompletion.lean`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Analytic IsLocalRing MvPowerSeries
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜))
  (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source) (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

/-- The map `𝒪_{M,a}/𝔪_a^k →+* 𝕜[[X]]/(X)^k` induced by `T_a`. -/
def taylorQuot (k : ℕ) :
    (structureSheaf 𝕜 E M).presheaf.stalk a ⧸
        (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k) →+*
      MvPowerSeries (Fin n) 𝕜 ⧸ (maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k) :=
  Ideal.quotientMap _ (taylorHom E ψ φ ha hφ) fun s hs =>
    Ideal.mem_comap.mpr ((taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s k).mpr hs)

theorem taylorQuot_mk (k : ℕ) (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    taylorQuot E ψ φ ha hφ k (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ (taylorHom E ψ φ ha hφ s) :=
  Ideal.quotientMap_mk

theorem taylorQuot_injective (k : ℕ) : Function.Injective (taylorQuot E ψ φ ha hφ k) :=
  Ideal.quotientMap_injective' fun s hs =>
    (taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ s k).mp (Ideal.mem_comap.mp hs)

/-- `𝒪_{M,a}/𝔪_a^k → 𝕜[[X]]/(X)^k` is onto: the truncation of a series is a polynomial, hence the
Taylor series of a germ. -/
theorem taylorQuot_surjective (k : ℕ) : Function.Surjective (taylorQuot E ψ φ ha hφ k) := by
  intro c
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨s, hs⟩ := Set.mem_range.mp ((range_taylorHom E ψ φ ha hφ).ge (truncDeg_mem_conv k c))
  refine ⟨Ideal.Quotient.mk _ s, ?_⟩
  rw [taylorQuot_mk, hs, Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
  exact sub_truncDeg_mem_maximalIdeal_pow k c

/-- The compatible family `AdicCompletion 𝔪_a 𝒪_{M,a} →+* 𝕜[[X]]/(X)^k`. -/
def taylorCompletionFamily (k : ℕ) :
    AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
        ((structureSheaf 𝕜 E M).presheaf.stalk a) →+*
      MvPowerSeries (Fin n) 𝕜 ⧸ (maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k) :=
  (taylorQuot E ψ φ ha hφ k).comp
    (AdicCompletion.evalₐ (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a)) k).toRingHom

theorem taylorCompletionFamily_mk (k : ℕ)
    (f : AdicCompletion.AdicCauchySequence
      (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    taylorCompletionFamily E ψ φ ha hφ k (AdicCompletion.mk _ _ f) =
      Ideal.Quotient.mk _ (taylorHom E ψ φ ha hφ (f.val k)) := by
  simp only [taylorCompletionFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AdicCompletion.evalₐ_mk, taylorQuot_mk]

theorem taylorCompletionFamily_compat {m k : ℕ} (hle : m ≤ k) :
    (Ideal.Quotient.factorPow (maximalIdeal (MvPowerSeries (Fin n) 𝕜)) hle).comp
        (taylorCompletionFamily E ψ φ ha hφ k) =
      taylorCompletionFamily E ψ φ ha hφ m := by
  ext x
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective _ _ x
  rw [RingHom.comp_apply, taylorCompletionFamily_mk, taylorCompletionFamily_mk]
  refine (Ideal.Quotient.factor_mk _ _).trans (Ideal.Quotient.eq.mpr ?_)
  rw [← map_sub, taylorHom_mem_maximalIdeal_pow_iff, ← neg_sub, neg_mem_iff]
  have h1 := SModEq.sub_mem.mp (f.property hle)
  simpa using h1

/-- The ring homomorphism `𝒪̂_{M,a} →+* 𝕜[[X]]` induced by `T_a` on the `𝔪_a`-adic completion, by
the universal property of the complete ring `𝕜[[X]]`. -/
def taylorCompletion :
    AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a) →+* MvPowerSeries (Fin n) 𝕜 :=
  IsAdicComplete.liftRingHom (maximalIdeal (MvPowerSeries (Fin n) 𝕜))
    (taylorCompletionFamily E ψ φ ha hφ) fun hle => taylorCompletionFamily_compat E ψ φ ha hφ hle

theorem mk_taylorCompletion (k : ℕ)
    (x : AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a)) :
    Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k)
        (taylorCompletion E ψ φ ha hφ x) = taylorCompletionFamily E ψ φ ha hφ k x :=
  IsAdicComplete.mk_liftRingHom _ _ _ k x

/-- Two series equal modulo every `(X)^k` are equal (`𝕜[[X]]` is `(X)`-adically separated). -/
theorem eq_of_forall_mk_eq {c c' : MvPowerSeries (Fin n) 𝕜}
    (h : ∀ k, Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k) c =
      Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k) c') : c = c' :=
  congrFun (IsHausdorff.funext' (maximalIdeal (MvPowerSeries (Fin n) 𝕜)) (f := fun _ : Unit => c)
    (g := fun _ => c') fun k _ => h k) ()

theorem taylorCompletion_of (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    taylorCompletion E ψ φ ha hφ (AdicCompletion.of _ _ s) = taylorHom E ψ φ ha hφ s := by
  refine eq_of_forall_mk_eq fun k => ?_
  rw [mk_taylorCompletion]
  simp only [taylorCompletionFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AdicCompletion.evalₐ_of, taylorQuot_mk]

theorem taylorCompletion_injective : Function.Injective (taylorCompletion E ψ φ ha hφ) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  refine AdicCompletion.ext_evalₐ fun k => ?_
  apply taylorQuot_injective E ψ φ ha hφ k
  have h1 := mk_taylorCompletion E ψ φ ha hφ k x
  rw [hx, map_zero] at h1
  simp only [taylorCompletionFamily, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] at h1
  rw [← h1, map_zero, map_zero]

/-- `𝒪̂_{M,a} → 𝕜[[X]]` is onto: a series is the limit of the Taylor series of the lifts of its
truncations, an `𝔪_a`-adic Cauchy sequence. -/
theorem taylorCompletion_surjective : Function.Surjective (taylorCompletion E ψ φ ha hφ) := by
  intro c
  have h1 : ∀ k, ∃ s : (structureSheaf 𝕜 E M).presheaf.stalk a,
      taylorHom E ψ φ ha hφ s - c ∈ maximalIdeal (MvPowerSeries (Fin n) 𝕜) ^ k := by
    intro k
    obtain ⟨q, hq⟩ := taylorQuot_surjective E ψ φ ha hφ k (Ideal.Quotient.mk _ c)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [taylorQuot_mk, Ideal.Quotient.eq] at hq
    exact ⟨s, hq⟩
  choose s hs using h1
  have hcauchy : AdicCompletion.IsAdicCauchy
      (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a) s := by
    intro m k hmk
    rw [SModEq.sub_mem]
    have h2 : s m - s k ∈ maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ m := by
      rw [← taylorHom_mem_maximalIdeal_pow_iff E ψ φ ha hφ, map_sub]
      have := Ideal.sub_mem _ (hs m) (Ideal.pow_le_pow_right hmk (hs k))
      rwa [sub_sub_sub_cancel_right] at this
    simpa using h2
  refine ⟨AdicCompletion.mk _ _ ⟨s, hcauchy⟩, eq_of_forall_mk_eq fun k => ?_⟩
  rw [mk_taylorCompletion]
  exact (taylorCompletionFamily_mk E ψ φ ha hφ k ⟨s, hcauchy⟩).trans (Ideal.Quotient.eq.mpr (hs k))

/-- **`𝒪̂_{M,a} ≅ 𝕜[[X₁, …, Xₙ]]`** through the Taylor homomorphism [BM97, (0.3)]. -/
def taylorCompletionEquiv :
    AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a) ≃+* MvPowerSeries (Fin n) 𝕜 :=
  RingEquiv.ofBijective _
    ⟨taylorCompletion_injective E ψ φ ha hφ, taylorCompletion_surjective E ψ φ ha hφ⟩

theorem taylorCompletionEquiv_algebraMap (s : (structureSheaf 𝕜 E M).presheaf.stalk a) :
    taylorCompletionEquiv E ψ φ ha hφ (algebraMap _ _ s) = taylorHom E ψ φ ha hφ s :=
  taylorCompletion_of E ψ φ ha hφ s

include ha hφ in
/-- For any map satisfying the specification `IsTaylorHom`: the `𝔪_a`-adic completion of
`𝒪_{M,a}` is `𝕜[[X₁, …, Xₙ]]`, through `T_a`. -/
theorem IsTaylorHom.exists_adicCompletion_equiv'
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) :
    ∃ e : AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
        ((structureSheaf 𝕜 E M).presheaf.stalk a) ≃+* MvPowerSeries (Fin n) 𝕜,
      ∀ s, e (algebraMap _ _ s) = T s := by
  obtain rfl := IsTaylorHom.eq E ψ φ hT (isTaylorHom_taylorHom E ψ φ ha hφ)
  exact ⟨taylorCompletionEquiv E ψ φ ha hφ, taylorCompletionEquiv_algebraMap E ψ φ ha hφ⟩

end Manifold
