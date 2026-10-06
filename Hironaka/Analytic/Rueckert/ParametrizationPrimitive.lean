/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.NoetherNormalization
public import Mathlib.Analysis.Complex.Basic
import Hironaka.Analytic.Rueckert.Hypersurface
import Hironaka.Analytic.Rueckert.LinearMix
import Hironaka.Analytic.Rueckert.PrimitiveRelations
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The primitive normalization of a prime germ

The first step of the local parametrization theorem [GR84, Chapter 3, §1] (the second
alternative of [Fre17, Ch. I, 8.2] together with the Noether normalization 7.2, generalized to a
`d`-dimensional base): a nonzero prime `P ⊆ 𝒪_n = Conv ℂ n` has a Noether normalization
`normMap ℂ P e L` (`NoetherNormalization.lean`, finite and injective) with a fibre coordinate
`X_{i₀}` (`i₀ ∉ range e`) that is a primitive element of `Frac(𝒪_n/P)` over `Frac(𝒪_d)`; in the
coordinates of `σ = substEquiv L`, for the ideal `P' = comap σ P`, its minimal polynomial
`Q ∈ 𝒪_d[T]` is monic irreducible with `Q(X_{i₀}) ∈ P'`, and some `A ∈ 𝒪_d ∖ 0`, `B_i ∈ 𝒪_d[T]`
have `A · X_i − B_i(X_{i₀}) ∈ P'` for every fibre coordinate `i`.

The proof assembles three pieces. (1) Noether normalization
`exists_noetherNormalization_analytic` gives `d`, `e`, `L₀`; since `P ≠ ⊥`, `e` is not onto
(`exists_notMem_range_of_ne_bot`: were every coordinate a base coordinate, `convEmbed e` would be
onto `𝒪_n` and the injectivity of the normalization would force `P = ⊥`), so a fibre index `i₁`
exists. (2) The algebraic core `PrimitiveRelations.lean` (`exists_linear_primitive_relations`),
applied to `R = 𝒪_d`, `S = 𝒪_n / P` with `f = normMap ℂ P e L₀` and the fibre classes
`ξ_i = [σ₀ X_i]`, returns constants `c ∈ ℂ` with `c_{i₁} = 1`, the primitive element
`γ = ∑ c_j ξ_j`, its minimal polynomial `Q`, and the denominators `A`, `B_i`. (3) The coordinate
mix `L₁ = mixLinear i₁ c` (`LinearMix.lean`) turns the linear form into the coordinate `X_{i₁}`:
with `L = L₀.trans L₁`, `substEquiv L = σ₀ ∘ σ₁`, `σ₁` fixes the base and the other fibre
coordinates and sends `X_{i₁}` to `∑ c_j X_j`, so the normalization is unchanged and the
relations of (2) read exactly as the statement demands.
-/

public section

open Polynomial Filter Topology

namespace Analytic

variable {n d : ℕ}

/-- If the injection `e : Fin d ↪ Fin n` is onto, the base embedding `convEmbed ℂ e : 𝒪_d → 𝒪_n`
is onto (rename along the inverse bijection stays convergent). -/
theorem convEmbed_surjective_of_surjective (e : Fin d ↪ Fin n) (hsurj : Function.Surjective e) :
    Function.Surjective (convEmbed ℂ e) := by
  have hbij : Function.Bijective e := ⟨e.injective, hsurj⟩
  let ε : Fin d ≃ Fin n := Equiv.ofBijective e hbij
  intro g
  have hmem : MvPowerSeries.rename (⇑ε.symm.toEmbedding) g.1 ∈ Conv ℂ d :=
    rename_mem_conv ε.symm.toEmbedding g.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  rw [coe_convEmbed]
  change MvPowerSeries.rename ⇑e (MvPowerSeries.rename ⇑ε.symm.toEmbedding g.1) = g.1
  rw [MvPowerSeries.rename_rename]
  have key : ∀ (φ : Fin n → Fin n) [Filter.TendstoCofinite φ], φ = id →
      MvPowerSeries.rename φ g.1 = g.1 := by
    intro φ _ hφ
    subst hφ
    rw [MvPowerSeries.rename_id]
    rfl
  exact key _ (by funext x; change ε (ε.symm x) = x; exact ε.apply_symm_apply x)

/-- A Noether normalization `normMap ℂ P e L` of a nonzero prime `P` has a fibre coordinate: some
index is outside the range of `e`. Otherwise `convEmbed ℂ e` is onto `𝒪_n`, and the injectivity of
`mk_P ∘ σ ∘ convEmbed e` makes `mk_P` injective, i.e. `P = ⊥`. -/
theorem exists_notMem_range_of_ne_bot (P : Ideal (Conv ℂ n)) (hP : P ≠ ⊥) (e : Fin d ↪ Fin n)
    (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)) (hinj : Function.Injective (normMap ℂ P e L)) :
    ∃ i, i ∉ Set.range e := by
  by_contra hall
  have hsurj : Function.Surjective e := fun i => by
    by_contra hi
    exact hall ⟨i, hi⟩
  have hsurjC := convEmbed_surjective_of_surjective e hsurj
  apply hP
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := hsurjC ((substEquiv L).symm g)
  have hgc : substEquiv L (convEmbed ℂ e c) = g := by rw [hc, AlgEquiv.apply_symm_apply]
  have h1 : normMap ℂ P e L c = 0 := by
    rw [normMap_apply, hgc, Ideal.Quotient.eq_zero_iff_mem]; exact hg
  have h2 : c = 0 := hinj (by rw [h1, map_zero])
  rw [← hgc, h2, map_zero, map_zero]; exact Ideal.zero_mem _

/-- The class in `𝒪_n / P` of a polynomial in `X_{i₀}` with coefficients embedded from the base,
read in the coordinates of `σ`, is the polynomial evaluated through `mk_P ∘ σ ∘ convEmbed e` at
the class of `σ X_{i₀}`. -/
theorem mk_substEquiv_eval_map (P : Ideal (Conv ℂ n)) (e : Fin d ↪ Fin n)
    (σ : Conv ℂ n ≃ₐ[ℂ] Conv ℂ n) (Q : (Conv ℂ d)[X]) (x : Conv ℂ n) :
    Ideal.Quotient.mk P (σ ((Q.map (convEmbed ℂ e).toRingHom).eval x)) =
      eval₂ ((Ideal.Quotient.mk P).comp ((σ : Conv ℂ n →+* Conv ℂ n).comp
        (convEmbed ℂ e).toRingHom)) (Ideal.Quotient.mk P (σ x)) Q := by
  rw [eval_map]
  have h := hom_eval₂ Q (convEmbed ℂ e).toRingHom
    ((Ideal.Quotient.mk P).comp (σ : Conv ℂ n →+* Conv ℂ n)) x
  rw [RingHom.comp_assoc] at h
  exact h

/-- The primitive normalization of a nonzero prime germ ([GR84, Chapter 3, §1]; the second
alternative of [Fre17, Ch. I, 8.2] with the Noether normalization 7.2, over a `d`-dimensional
base): a Noether normalization with a fibre coordinate `X_{i₀}` whose class is a primitive
element, its monic irreducible minimal polynomial `Q` with `Q(X_{i₀}) ∈ comap σ P`, and
denominators `A ≠ 0`, `B_i` with `A · X_i − B_i(X_{i₀}) ∈ comap σ P` for every fibre
coordinate. -/
theorem exists_primitive_normalization (P : Ideal (Conv ℂ n)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ (d : ℕ) (e : Fin d ↪ Fin n) (L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ)),
      Function.Injective (normMap ℂ P e L) ∧
      RingHom.Finite (A := Conv ℂ d) (B := Conv ℂ n ⧸ P)
        (normMap ℂ P e L : Conv ℂ d →+* Conv ℂ n ⧸ P) ∧
      ∃ (i₀ : Fin n) (_ : i₀ ∉ Set.range e) (Q : Polynomial (Conv ℂ d)) (A : Conv ℂ d),
        Q.Monic ∧ Irreducible Q ∧ A ≠ 0 ∧
        (Q.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈ Ideal.comap (substEquiv L) P ∧
        ∀ i, i ∉ Set.range e → ∃ B : Polynomial (Conv ℂ d),
          convEmbed ℂ e A * convX ℂ i - (B.map (convEmbed ℂ e).toRingHom).eval (convX ℂ i₀) ∈
            Ideal.comap (substEquiv L) P := by
  classical
  -- (1) Noether normalization and a fibre index
  obtain ⟨d, e, L₀, hinj₀, hfin₀⟩ :=
    exists_noetherNormalization_analytic P (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨i₁, hi₁⟩ := exists_notMem_range_of_ne_bot P hP e L₀ hinj₀
  -- (2) the algebraic core in `S = 𝒪_n / P`
  have hdom : IsDomain (Conv ℂ n ⧸ P) := Ideal.Quotient.isDomain P
  set f : Conv ℂ d →+* Conv ℂ n ⧸ P := (normMap ℂ P e L₀ : Conv ℂ d →+* Conv ℂ n ⧸ P) with hf
  have hC : ∀ c : ℂ, f (algebraMap ℂ (Conv ℂ d) c) = algebraMap ℂ (Conv ℂ n ⧸ P) c := fun c => by
    rw [hf, AlgHom.coe_toRingHom, AlgHom.commutes]
  set s : Finset (Fin n) := Finset.univ.filter (fun i => i ∉ Set.range e) with hs
  have hmem_s : ∀ i, i ∈ s ↔ i ∉ Set.range e := fun i =>
    Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))
  have hi₁s : i₁ ∈ s := (hmem_s i₁).mpr hi₁
  set ξ : Fin n → Conv ℂ n ⧸ P := fun i => Ideal.Quotient.mk P (substEquiv L₀ (convX ℂ i)) with hξ
  obtain ⟨c, hc₁, hcz, Q, hQm, hQi, hQ0, A, hA, hB⟩ :=
    exists_linear_primitive_relations (R := Conv ℂ d) (S := Conv ℂ n ⧸ P) (C := ℂ) f hfin₀ hinj₀
      hC s ξ hi₁s
  set γ : Conv ℂ n ⧸ P := ∑ j ∈ s, algebraMap ℂ (Conv ℂ n ⧸ P) (c j) * ξ j with hγ
  -- (3) the coordinate mix
  set L := L₀.trans (mixLinear i₁ c hc₁) with hL
  have hσ : ∀ g, substEquiv L g = substEquiv L₀ (substEquiv (mixLinear i₁ c hc₁) g) := fun g => by
    rw [hL]
    simp only [substEquiv_apply]
    rw [substConv_substConv]
    congr 1
  have hσ₁base : ∀ a, substEquiv (mixLinear i₁ c hc₁) (convEmbed ℂ e a) = convEmbed ℂ e a :=
    fun a => by rw [substEquiv_apply]; exact substConv_mixLinear_convEmbed i₁ c hc₁ e hi₁ a
  have hσ₁self : substEquiv (mixLinear i₁ c hc₁) (convX ℂ i₁) =
      ∑ j, algebraMap ℂ (Conv ℂ n) (c j) * convX ℂ j := by
    rw [substEquiv_apply]; exact substConv_mixLinear_convX_self i₁ c hc₁
  have hσ₁ne : ∀ i, i ≠ i₁ → substEquiv (mixLinear i₁ c hc₁) (convX ℂ i) = convX ℂ i :=
    fun i hi => by rw [substEquiv_apply]; exact substConv_mixLinear_convX_of_ne i₁ c hc₁ hi
  have hσbase : ∀ a, substEquiv L (convEmbed ℂ e a) = substEquiv L₀ (convEmbed ℂ e a) := fun a => by
    rw [hσ, hσ₁base]
  -- the normalization is unchanged
  have hnm : (normMap ℂ P e L : Conv ℂ d →+* Conv ℂ n ⧸ P) = f := by
    ext a
    simp only [hf, AlgHom.coe_toRingHom, normMap_apply, hσbase]
  have hnm' : normMap ℂ P e L = normMap ℂ P e L₀ := AlgHom.ext fun a =>
    congrArg (fun φ : Conv ℂ d →+* Conv ℂ n ⧸ P => φ a) hnm
  -- the composite `mk ∘ σ ∘ convEmbed e` is the normalization
  have hcomp : (Ideal.Quotient.mk P).comp (((substEquiv L : Conv ℂ n ≃ₐ[ℂ] Conv ℂ n) :
      Conv ℂ n →+* Conv ℂ n).comp (convEmbed ℂ e).toRingHom) = f := by
    rw [← hnm]
    rfl
  -- the class of `σ X_{i₁}` is the primitive element `γ`
  have hXi₁ : Ideal.Quotient.mk P (substEquiv L (convX ℂ i₁)) = γ := by
    rw [hσ, hσ₁self, map_sum, map_sum, hγ]
    rw [← Finset.sum_subset (Finset.subset_univ s)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul, AlgEquiv.commutes, hξ]
      rfl
    · intro j _ hj
      have : c j = 0 := hcz j hj
      rw [this, map_zero, zero_mul, map_zero, map_zero]
  -- the class of `σ X_i`, `i ≠ i₁`, is the old class
  have hXi : ∀ i, i ≠ i₁ → Ideal.Quotient.mk P (substEquiv L (convX ℂ i)) = ξ i := fun i hi => by
    rw [hσ, hσ₁ne i hi, hξ]
  -- membership in `comap σ P` through the quotient
  have hmemP : ∀ g : Conv ℂ n, g ∈ Ideal.comap (substEquiv L) P ↔
      Ideal.Quotient.mk P (substEquiv L g) = 0 := fun g => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨d, e, L, ?_, ?_, i₁, hi₁, Q, A, hQm, hQi, hA, ?_, fun i hi => ?_⟩
  · rw [hnm']; exact hinj₀
  · rw [hnm]; exact hfin₀
  · rw [hmemP, mk_substEquiv_eval_map, hcomp, hXi₁]
    exact hQ0
  · by_cases hii : i = i₁
    · subst hii
      refine ⟨Polynomial.C A * X, ?_⟩
      rw [hmemP, map_sub, map_sub, map_mul, map_mul, mk_substEquiv_eval_map, hcomp, hXi₁,
        eval₂_mul, eval₂_C, eval₂_X]
      have : Ideal.Quotient.mk P (substEquiv L (convEmbed ℂ e A)) = f A := by
        rw [hσbase]; rfl
      rw [this, sub_self]
    · obtain ⟨B, hBi⟩ := hB i ((hmem_s i).mpr hi)
      refine ⟨B, ?_⟩
      rw [hmemP, map_sub, map_sub, map_mul, map_mul, mk_substEquiv_eval_map, hcomp, hXi₁,
        hXi i hii]
      have : Ideal.Quotient.mk P (substEquiv L (convEmbed ℂ e A)) = f A := by
        rw [hσbase]; rfl
      rw [this, hBi, sub_self]

end Analytic
