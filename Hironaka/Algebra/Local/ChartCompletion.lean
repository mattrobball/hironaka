/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.Lemma61
import Hironaka.Algebra.Local.ChartSubstTrunc
import Mathlib.Combinatorics.Matroid.Init

/-!
# The completed chart map is the chart substitution

[Kol07, (60.3)] writes the chart map `R → R'_{𝔪'}` in the coordinates `x` of `R` and `y` of the
chart as the substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`). This module proves that
statement for the completions (`hasCohenChart`): the map `R̂ → (R'_{𝔪'})^` induced by `R → R'_{𝔪'}`
is the substitution `chartSubst r` of `Hironaka/Algebra/Local/ChartSubst.lean` under the Cohen
isomorphism `R̂ ≅ K⟦x⟧` (`cohenEquiv`, `Hironaka/Algebra/Local/CohenIso.lean`) and the Cohen
isomorphism `(R'_{𝔪'})^ ≅ K⟦y⟧` built on the coefficient field transported from `R̂`
(`chartCoefficientField`, `Hironaka/Algebra/Local/Lemma61.lean`) and on the regular system of
parameters `y` of `R'_{𝔪'}` (`Hironaka/Algebra/Local/ChartLocal.lean`). This is the predicate
`HasCohenChart` of `Hironaka/Algebra/Local/Lemma61.lean`, whose order bounds thereby become
unconditional.

The identification is proved level by level (`completionMap_cohenMap`) for an abstract target: a
Noetherian local ring `B` with a local homomorphism `φ : R → B`, a family `y` in `B` satisfying the
chart relations `φ(xᵢ) = y_r yᵢ` (`i < r`), `φ(xⱼ) = yⱼ`, and a coefficient field on `B̂` compatible
with that of `R̂` through a ring map `e` of residue fields. Modulo `𝔪_B̂ᴺ`, both `φ̂(Φ_R(F))` and
`Φ_B(subst (F.map e))`, where `Φ_R = cohenMap R x` and `Φ_B = cohenMap B y`, are the evaluation of
the truncation `truncTotal N F` at the images of the variables (`mk_completionMap_cohenMap`).
Keeping `B` abstract keeps every unification away from the concrete chart ring, whose definition
as an `Algebra.adjoin` Lean would otherwise unfold.

Elementary inputs collected here: the chart relations in `R'_{𝔪'}` (`algebraMap_x_atPrime`); the
chart substitution as a polynomial substitution (`chartSubstPoly`, `subst_chartSubst_coe`), so
that on truncations it is a polynomial evaluation; its compatibility with a change of
coefficients (`map_subst_chartSubst`); and the isomorphism of residue fields `K ≃ K_B`
(`chartResidueEquiv`).

Used in `Hironaka/Resolution/Analytic/GoingUp/MaxOrder.lean`;
`Hironaka/Algebra/Local/ChartCompletionHom.lean` and `Hironaka/Algebra/Local/ChartHom.lean` build on
it.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

section Relations

variable {R : Type*} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n) [(chartOrigin x r).IsPrime]

/-- `φ(xᵢ) = y_r yᵢ` in `R'_{𝔪'}` for `i < r`. -/
theorem algebraMap_x_atPrime_of_lt {i : Fin n} (hi : i < r) :
    algebraMap R (Localization.AtPrime (chartOrigin x r)) (x i) =
      algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r)) (chartYR x r r) *
        algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r)) (chartYR x r i) := by
  rw [IsScalarTower.algebraMap_apply R (chartRing x r), algebraMap_x_eq_mul_chartYR x r hi, map_mul]
  congr 2
  apply Subtype.ext
  rw [coe_chartYROf, chartYOf_self]
  rfl

/-- `φ(xⱼ) = yⱼ` in `R'_{𝔪'}` for `j ≥ r`. -/
theorem algebraMap_x_atPrime_of_not_lt {j : Fin n} (hj : ¬ j < r) :
    algebraMap R (Localization.AtPrime (chartOrigin x r)) (x j) =
      algebraMap (chartRing x r) (Localization.AtPrime (chartOrigin x r)) (chartYR x r j) := by
  rw [IsScalarTower.algebraMap_apply R (chartRing x r)]
  congr 1
  apply Subtype.ext
  rw [coe_chartYROf, chartYOf_of_not_lt _ _ _ hj]
  rfl

end Relations

section Poly

variable {n : ℕ} (r : Fin n) {K : Type*} [CommRing K]

/-- The chart substitution as a polynomial substitution: `Xᵢ ↦ Xᵢ X_r` (`i < r`), `Xⱼ ↦ Xⱼ`. -/
noncomputable def chartSubstPoly : Fin n → MvPolynomial (Fin n) K :=
  fun i => if i < r then MvPolynomial.X i * MvPolynomial.X r else MvPolynomial.X i

theorem coe_chartSubstPoly (i : Fin n) :
    ((chartSubstPoly (K := K) r i : MvPolynomial (Fin n) K) : MvPowerSeries (Fin n) K) =
      chartSubst r i := by
  unfold chartSubstPoly chartSubst
  split_ifs
  · rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, MvPolynomial.coe_X]
  · rw [MvPolynomial.coe_X]

/-- On polynomials the chart substitution is the polynomial substitution `chartSubstPoly`. -/
theorem subst_chartSubst_coe (P : MvPolynomial (Fin n) K) :
    subst (chartSubst (K := K) r) (P : MvPowerSeries (Fin n) K) =
      ((MvPolynomial.aeval (chartSubstPoly r) P : MvPolynomial (Fin n) K) :
        MvPowerSeries (Fin n) K) := by
  rw [subst_coe]
  induction P using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      MvPolynomial.coe_C]; rfl
  | add p q hp hq => rw [map_add, map_add, MvPolynomial.coe_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.coe_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      coe_chartSubstPoly]

variable {L : Type*} [CommRing L]

theorem map_chartSubst (e : K →+* L) (i : Fin n) :
    (chartSubst (K := K) r i).map e = chartSubst (K := L) r i := by
  unfold chartSubst
  split_ifs
  · rw [map_mul, map_X, map_X]
  · rw [map_X]

/-- The chart substitution commutes with a change of coefficients. -/
theorem map_subst_chartSubst (e : K →+* L) (F : MvPowerSeries (Fin n) K) :
    (subst (chartSubst (K := K) r) F).map e = subst (chartSubst (K := L) r) (F.map e) := by
  rw [map_subst (hasSubst_chartSubst r)]
  congr 1
  funext i
  exact map_chartSubst r e i

end Poly

section Trunc

variable {n : ℕ} {K L : Type*} [CommRing K] [CommRing L]

/-- Truncation commutes with a change of coefficients. -/
theorem truncTotal_map (e : K →+* L) (N : ℕ) (F : MvPowerSeries (Fin n) K) :
    truncTotal N (F.map e) = (truncTotal N F).map e := by
  ext β
  rw [MvPolynomial.coeff_map, coeff_truncTotal_eq_ite, coeff_truncTotal_eq_ite, coeff_map]
  split_ifs <;> simp

end Trunc

section

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (r : Fin n)
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
  [(chartOrigin x r).IsPrime]

/-- The isomorphism `e : K ≃ K_B` of residue fields induced by `R → R'_{𝔪'}`. -/
noncomputable def chartResidueEquiv :
    ResidueField R ≃+* ResidueField (Localization.AtPrime (chartOrigin x r)) :=
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  RingEquiv.ofBijective _ (residueField_map_bijective_chartOrigin x r hx hn)

/-- The transported coefficient field on `e k` is `φ̂` of the coefficient field of `R̂` on `k`. -/
theorem chartCoefficientField_chartResidueEquiv (k : ResidueField R) :
    chartCoefficientField x r hx hn (chartResidueEquiv x r hx hn k) =
      @completionMap _ _ _ _ _ _ (algebraMap R (Localization.AtPrime (chartOrigin x r)))
        (isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn)
        (coefficientField R k) := by
  have := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  change completionMap _ (coefficientField R
    ((chartResidueEquiv x r hx hn).symm (chartResidueEquiv x r hx hn k))) = _
  rw [RingEquiv.symm_apply_apply]

omit [Algebra ℚ R] in
/-- The chart's local ring is Noetherian, being a localization of the Noetherian chart ring. -/
instance isNoetherianRing_atPrime_chartOrigin :
    IsNoetherianRing (Localization.AtPrime (chartOrigin x r)) :=
  IsLocalization.isNoetherianRing (chartOrigin x r).primeCompl _ (isNoetherianRing_chartRing x r)

/-- The regular system of parameters `y` of the chart's local ring
(`maximalIdeal_localization_chartOrigin`). -/
noncomputable abbrev chartY' : Fin n → Localization.AtPrime (chartOrigin x r) :=
  fun i => algebraMap (chartRing x r) _ (chartYR x r i)

end

/-! ### The completed chart map for an abstract target

The level-by-level identification is proved for an arbitrary Noetherian local ring `B` with a local
homomorphism `φ : R → B`, a family `y` in `B` satisfying the chart relations `φ(xᵢ) = y_r yᵢ`
(`i < r`), `φ(xⱼ) = yⱼ`, and a coefficient-field datum on `B̂` compatible with that of `R̂`
through a ring map `e` of residue fields.  Keeping `B` abstract keeps every unification away
from the concrete chart ring (whose definition as an `adjoin` Lean would otherwise unfold). -/

section Abstract

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (r : Fin n)
  {B : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (φ : R →+* B) [IsLocalHom φ]
  [Algebra (ResidueField B) (AdicCompletion (maximalIdeal B) B)]

omit [Algebra ℚ R] [Algebra (ResidueField B) (AdicCompletion (maximalIdeal B) B)] in
theorem maximalIdeal_pow_le_comap_completionMap (N : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ N ≤
      (maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N).comap (completionMap φ) :=
  fun _ hz => Ideal.mem_comap.mpr (completionMap_mem_maximalIdeal_pow φ hz)

/-- The level-`N` map `R̂/𝔪̂ᴺ → B̂/𝔪_B̂ᴺ` induced by `φ̂`. -/
noncomputable def levelMap (N : ℕ) :
    AdicCompletion (maximalIdeal R) R ⧸ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ N →+*
      AdicCompletion (maximalIdeal B) B ⧸ maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N :=
  Ideal.quotientMap _ (completionMap φ) (maximalIdeal_pow_le_comap_completionMap φ N)

omit [Algebra ℚ R] [Algebra (ResidueField B) (AdicCompletion (maximalIdeal B) B)] in
theorem levelMap_mk (N : ℕ) (z : AdicCompletion (maximalIdeal R) R) :
    levelMap φ N (Ideal.Quotient.mk _ z) = Ideal.Quotient.mk _ (completionMap φ z) :=
  Ideal.quotientMap_mk

variable (e : ResidueField R →+* ResidueField B)
  (he : ∀ k, algebraMap (ResidueField B) (AdicCompletion (maximalIdeal B) B) (e k) =
    completionMap φ (coefficientField R k))

include he in
/-- Constants: the level map carries the coefficient field of `R̂` to the datum on `B̂`. -/
theorem levelMap_algebraMap (N : ℕ) (k : ResidueField R) :
    levelMap φ N (algebraMap (ResidueField R)
        (AdicCompletion (maximalIdeal R) R ⧸ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ N)
        k) =
      algebraMap (ResidueField B)
        (AdicCompletion (maximalIdeal B) B ⧸ maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N)
        (e k) := by
  rw [IsScalarTower.algebraMap_apply (ResidueField R) (AdicCompletion (maximalIdeal R) R),
    IsScalarTower.algebraMap_apply (ResidueField B) (AdicCompletion (maximalIdeal B) B),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, levelMap_mk, he]
  rfl

variable (y : Fin n → B) (hyx : ∀ i, φ (x i) = if i < r then y r * y i else y i)

omit [Algebra ℚ R] in
include hyx in
/-- Variables: `φ̂(ι xᵢ)` at level `N` is the chart substitution evaluated at the `levelVar` of
`y`. -/
theorem levelMap_levelVar (N : ℕ) (i : Fin n) :
    levelMap φ N (levelVar R x N i) =
      MvPolynomial.aeval (levelVar B y N) (chartSubstPoly (K := ResidueField B) r i) := by
  unfold levelVar chartSubstPoly
  rw [levelMap_mk, completionMap_algebraMap φ (x i), hyx i]
  split_ifs
  · simp only [map_mul, MvPolynomial.aeval_X, mul_comm]
  · simp only [MvPolynomial.aeval_X]

include he hyx in
/-- Polynomials: the level map of an evaluation at the `levelVar` of `x` is the evaluation, at the
`levelVar` of `y`, of the chart substitution of the polynomial with coefficients moved by `e`. -/
theorem levelMap_aeval (N : ℕ) (P : MvPolynomial (Fin n) (ResidueField R)) :
    levelMap φ N (MvPolynomial.aeval (levelVar R x N) P) =
      MvPolynomial.aeval (levelVar B y N)
        (MvPolynomial.aeval (chartSubstPoly (K := ResidueField B) r) (P.map e)) := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  have hc : (levelMap φ N).comp (algebraMap (ResidueField R) _) =
      (algebraMap (ResidueField B) _).comp e :=
    RingHom.ext fun k => levelMap_algebraMap φ e he N k
  rw [hc]
  exact congrArg (fun v => MvPolynomial.eval₂ _ v P)
    (funext fun i => levelMap_levelVar x r φ y hyx N i)

variable (hxm : ∀ i, x i ∈ maximalIdeal R) (hym : ∀ i, y i ∈ maximalIdeal B)

include he hyx in
/-- Level `N` of the identification: modulo `𝔪_B̂ᴺ`, `φ̂(Φ_R(F))` is the Cohen map of `B` applied
to the chart substitution of `F` (coefficients moved by `e`). -/
theorem mk_completionMap_cohenMap (N : ℕ) (F : MvPowerSeries (Fin n) (ResidueField R)) :
    Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N)
        (completionMap φ (cohenMap R x hxm F)) =
      Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N)
        (cohenMap B y hym (subst (chartSubst r) (F.map e))) := by
  rw [← levelMap_mk, mk_cohenMap, mk_cohenMap, levelEval_apply, levelEval_apply,
    levelMap_aeval x r φ e he y hyx, ← truncTotal_map]
  refine aeval_eq_of_coeff_eq (levelVar_mem B y hym N) (map_maximalIdeal_pow_eq_bot B N)
    fun α hα => ?_
  rw [coeff_truncTotal _ hα, ← coeff_subst_chartSubst_truncTotal r _ hα, subst_chartSubst_coe,
    MvPolynomial.coeff_coe]

include he hyx in
/-- The completed chart map for an abstract target: `φ̂ ∘ Φ_R = Φ_B ∘ subst ∘ map e`. -/
theorem completionMap_cohenMap (F : MvPowerSeries (Fin n) (ResidueField R)) :
    completionMap φ (cohenMap R x hxm F) = cohenMap B y hym (subst (chartSubst r) (F.map e)) :=
  eq_of_forall_mk_pow_eq (maximalIdeal _) fun N =>
    mk_completionMap_cohenMap x r φ e he y hyx hxm hym N F

end Abstract

section

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [Algebra ℚ R] {n : ℕ}
  (x : Fin n → R) (r : Fin n)
  (hx : maximalIdeal R = Ideal.span (Set.range x)) (hn : (n : WithBot ℕ∞) = ringKrullDim R)
  [(chartOrigin x r).IsPrime]

/-- The transported coefficient field as an algebra structure on `(R'_{𝔪'})^`. -/
noncomputable abbrev chartCompletionAlgebra :
    Algebra (ResidueField (Localization.AtPrime (chartOrigin x r)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
        (Localization.AtPrime (chartOrigin x r))) :=
  (chartCoefficientField x r hx hn).toAlgebra

omit [IsRegularLocalRing R] [Algebra ℚ R] in
/-- The chart relations in the local ring: `φ(xᵢ) = y_r yᵢ` (`i < r`), `φ(xⱼ) = yⱼ`. -/
theorem algebraMap_x_atPrime (i : Fin n) :
    algebraMap R (Localization.AtPrime (chartOrigin x r)) (x i) =
      if i < r then chartY' x r r * chartY' x r i else chartY' x r i := by
  split_ifs with hi
  · exact algebraMap_x_atPrime_of_lt x r hi
  · exact algebraMap_x_atPrime_of_not_lt x r hi

/-- **The completed chart map is the chart substitution** ([Kol07, (60.3)]): the map induced on
completions by `R → R'_{𝔪'}` is the chart substitution `xᵢ ↦ yᵢ y_r` (`i < r`), `xⱼ ↦ yⱼ` (`j ≥ r`)
under the Cohen isomorphism of `R̂` and the Cohen isomorphism of `(R'_{𝔪'})^` built on the
transported coefficient field `chartCoefficientField` and the regular system of parameters `y` of
`R'_{𝔪'}`, by the level-by-level identification `completionMap_cohenMap`. -/
theorem hasCohenChart : HasCohenChart x r hx hn := by
  have hloc := isLocalHom_algebraMap_atPrime_chartOrigin x r hx hn
  let _ := chartCompletionAlgebra x r hx hn
  have hι : IsCoefficientAlgebra (Localization.AtPrime (chartOrigin x r)) :=
    fun k => residue_chartCoefficientField x r hx hn k
  have hy : maximalIdeal (Localization.AtPrime (chartOrigin x r)) =
      Ideal.span (Set.range (chartY' x r)) :=
    maximalIdeal_localization_chartOrigin x r
  have hd : (n : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime (chartOrigin x r)) :=
    (ringKrullDim_localization_chartOrigin x r hx hn).symm
  have he : ∀ k, algebraMap (ResidueField (Localization.AtPrime (chartOrigin x r)))
      (AdicCompletion (maximalIdeal (Localization.AtPrime (chartOrigin x r)))
        (Localization.AtPrime (chartOrigin x r))) (chartResidueEquiv x r hx hn k) =
      completionMap (algebraMap R (Localization.AtPrime (chartOrigin x r)))
        (coefficientField R k) :=
    fun k => chartCoefficientField_chartResidueEquiv x r hx hn k
  have hee : ((chartResidueEquiv x r hx hn :
      ResidueField R →+* ResidueField (Localization.AtPrime (chartOrigin x r))).comp
      ((chartResidueEquiv x r hx hn).symm :
        ResidueField (Localization.AtPrime (chartOrigin x r)) →+* ResidueField R)) =
      RingHom.id _ :=
    RingHom.ext fun k => (chartResidueEquiv x r hx hn).apply_symm_apply k
  have hee' : (((chartResidueEquiv x r hx hn).symm :
      ResidueField (Localization.AtPrime (chartOrigin x r)) →+* ResidueField R).comp
      (chartResidueEquiv x r hx hn :
        ResidueField R →+* ResidueField (Localization.AtPrime (chartOrigin x r)))) =
      RingHom.id _ :=
    RingHom.ext fun k => (chartResidueEquiv x r hx hn).symm_apply_apply k
  have hm1 : (MvPowerSeries.map (σ := Fin n) (chartResidueEquiv x r hx hn :
      ResidueField R →+* ResidueField (Localization.AtPrime (chartOrigin x r)))).comp
      (MvPowerSeries.map ((chartResidueEquiv x r hx hn).symm :
        ResidueField (Localization.AtPrime (chartOrigin x r)) →+* ResidueField R)) =
      RingHom.id _ := RingHom.ext fun p => by
    rw [RingHom.comp_apply, MvPowerSeries.map_map, hee, MvPowerSeries.map_id, RingHom.id_apply]
  have hm2 : (MvPowerSeries.map (σ := Fin n) ((chartResidueEquiv x r hx hn).symm :
      ResidueField (Localization.AtPrime (chartOrigin x r)) →+* ResidueField R)).comp
      (MvPowerSeries.map (chartResidueEquiv x r hx hn :
        ResidueField R →+* ResidueField (Localization.AtPrime (chartOrigin x r)))) =
      RingHom.id _ := RingHom.ext fun p => by
    rw [RingHom.comp_apply, MvPowerSeries.map_map, hee', MvPowerSeries.map_id, RingHom.id_apply]
  refine ⟨(RingEquiv.ofRingHom
    (MvPowerSeries.map (chartResidueEquiv x r hx hn :
      ResidueField R →+* ResidueField (Localization.AtPrime (chartOrigin x r))))
    (MvPowerSeries.map ((chartResidueEquiv x r hx hn).symm :
      ResidueField (Localization.AtPrime (chartOrigin x r)) →+* ResidueField R)) hm1 hm2).trans
      (cohenEquivOfResidue _ (chartY' x r) hι hy hd), fun F => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.ofRingHom_apply, cohenEquiv_apply,
    cohenEquivOfResidue_apply, map_subst_chartSubst]
  exact completionMap_cohenMap x r (algebraMap R (Localization.AtPrime (chartOrigin x r)))
    (chartResidueEquiv x r hx hn :
      ResidueField R →+* ResidueField (Localization.AtPrime (chartOrigin x r))) he (chartY' x r)
    (algebraMap_x_atPrime x r) (x_mem_maximalIdeal_of_eq_span R x hx)
    (x_mem_maximalIdeal_of_eq_span _ _ hy) F

end


end IsLocalRing
