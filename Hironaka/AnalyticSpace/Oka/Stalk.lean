/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Oka.PolySection
import Hironaka.Analytic.Weierstrass.Tail
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init

/-!
# The polynomial map from the base stalk into the stalk of the model

Freitag's subring `𝒪_{n−1}[z_n] ⊆ 𝒪_n` at a point `a` of the product `V × D` [Fre17, Ch. I, 10.3 and
10.4], as the ring homomorphism `Ψ_a : 𝒪_{Kᵐ, π a}[X] →+* 𝒪_{Kᵐ⁺¹, a}` (`psi ψ a x₀`) evaluating a
polynomial with coefficients in the base stalk, pulled back along the projection `π` by the map of
germs `germMapProj`, at the shifted coordinate `x_0 − x₀`:

* `TKn_germMap`: the Taylor series of a pulled-back stalk element is the lift of its Taylor series;
* `psi` and `TKn_psi`: `T_a (Ψ_a Q) = ofPoly ((Q.map T_{π a}).comp (X − C (x₀ − a_0)))` (two ring
  homomorphisms agreeing on constants and on `X`), hence `psi_injective`;
* the germs of the polynomial sections of `Hironaka.AnalyticSpace.Oka.PolySection` are `Ψ_a` of the
  polynomials with the germs of their coefficients (`germ_polyComb_eq_psi`,
  `germ_polyMonic_eq_psi`);
* `exists_psi_eq_of_degLt`: for `0 < N`, every stalk element whose Taylor series has `x_0`-degree
  `< N` is `Ψ_a Q` for a polynomial `Q` of degree `< N`, the identification
  `K_N = 𝒪_{n−1}[z_n : N]^p ∩ K` in the statement of Oka's lemma [Fre17, Ch. I, 10.4].

Every statement is bookkeeping for the induction of Oka's theorem
(`Hironaka.AnalyticSpace.Oka.Core`).
-/

@[expose] public noncomputable section

open TopologicalSpace Opposite CategoryTheory Filter Topology Manifold
open Analytic
open scoped Manifold ContDiff

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K] {m : ℕ} (ψ : Kn.{u} K (m + 1) ≃L[K] (Fin (m + 1) → K))

/-- The stalk map `𝒪_{Kᵐ, π a} →+* 𝒪_{Kᵐ⁺¹, a}` of the projection. -/
abbrev germMapProj (a : Kn.{u} K (m + 1)) :
    (sheafKn K m).presheaf.stalk (projKn ψ a) →+* (sheafKn K (m + 1)).presheaf.stalk a :=
  germMap (projKn ψ) (contMDiff_projKn ψ) a

/-- The Taylor series of a pulled-back stalk element is the lift of its Taylor series. -/
theorem TKn_germMap (a : Kn.{u} K (m + 1)) (x : (sheafKn K m).presheaf.stalk (projKn ψ a)) :
    TKn ψ a (germMapProj ψ a x) = liftTail (TKn (knCoord K m) (projKn ψ a) x) := by
  obtain ⟨U, hU, g, rfl⟩ := (sheafKn K m).presheaf.exists_germ_eq x
  rw [germMapProj, germMap_germ, TKn_germ_comapSection ψ a hU g]

/-- The shifted coordinate germ `x_0 − x₀` at `a`. -/
def shiftGerm (a : Kn.{u} K (m + 1)) (x0 : K) : (sheafKn K (m + 1)).presheaf.stalk a :=
  coordKn ψ a 0 - const K (Kn.{u} K (m + 1)) (Kn.{u} K (m + 1)) a x0

theorem TKn_shiftGerm (a : Kn.{u} K (m + 1)) (x0 : K) :
    TKn ψ a (shiftGerm ψ a x0) = MvPowerSeries.X 0 - MvPowerSeries.C (x0 - ψ a 0) := by
  unfold shiftGerm
  have := TKn_coord_sub_const ψ a 0
  rw [map_sub, TKn_const, sub_eq_iff_eq_add] at this
  rw [map_sub, this, TKn_const, map_sub]
  ring

theorem germ_shiftSec {V : Opens (Kn.{u} K m)} {a : Kn.{u} K (m + 1)} (ha : a ∈ baseOpens ψ V)
    (x0 : K) :
    (sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (shiftSec ψ V x0) =
      shiftGerm ψ a x0 := by
  unfold shiftSec shiftGerm
  rw [map_sub, germ_x0Sec, germ_cSec]

theorem germ_pullSec {V : Opens (Kn.{u} K m)} {a : Kn.{u} K (m + 1)} (ha : a ∈ baseOpens ψ V)
    (w : (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (pullSec ψ V w) =
      germMapProj ψ a ((sheafKn K m).presheaf.germ V (projKn ψ a) ha w) :=
  (germMap_germ (projKn ψ) (contMDiff_projKn ψ) ha w).symm

/-- Freitag's `𝒪_{n−1}[z_n] → 𝒪_n` at `a` [Fre17, Ch. I, 10.3]: evaluate a polynomial with
coefficients in the base stalk (pulled back along `π`) at the shifted coordinate `x_0 − x₀`. -/
def psi (a : Kn.{u} K (m + 1)) (x0 : K) :
    Polynomial ((sheafKn K m).presheaf.stalk (projKn ψ a)) →+*
      (sheafKn K (m + 1)).presheaf.stalk a :=
  Polynomial.eval₂RingHom (germMapProj ψ a) (shiftGerm ψ a x0)

theorem psi_C (a : Kn.{u} K (m + 1)) (x0 : K)
    (x : (sheafKn K m).presheaf.stalk (projKn ψ a)) :
    psi ψ a x0 (Polynomial.C x) = germMapProj ψ a x := by
  simp [psi]

theorem psi_X (a : Kn.{u} K (m + 1)) (x0 : K) : psi ψ a x0 Polynomial.X = shiftGerm ψ a x0 := by
  simp [psi]

theorem ofPoly_X_sub_C (s : K) :
    ofPoly (Polynomial.X - Polynomial.C (MvPowerSeries.C s) :
        Polynomial (MvPowerSeries (Fin m) K)) =
      MvPowerSeries.X 0 - MvPowerSeries.C s := by
  rw [sub_eq_add_neg, ofPoly_add, ofPoly_neg, ofPoly_X, ofPoly_C, liftTail, MvPowerSeries.rename_C,
    sub_eq_add_neg]

/-- The Taylor series of `Ψ_a Q`: the polynomial with the Taylor series of the coefficients,
composed with the shift `X − C (x₀ − a_0)`. -/
theorem TKn_psi (a : Kn.{u} K (m + 1)) (x0 : K)
    (Q : Polynomial ((sheafKn K m).presheaf.stalk (projKn ψ a))) :
    TKn ψ a (psi ψ a x0 Q) = ofPoly ((Q.map (TKn (knCoord K m) (projKn ψ a))).comp
      (Polynomial.X - Polynomial.C (MvPowerSeries.C (x0 - ψ a 0)))) := by
  have key : (TKn ψ a).comp (psi ψ a x0) =
      (ofPolyHom.comp (Polynomial.compRingHom
        (Polynomial.X - Polynomial.C (MvPowerSeries.C (x0 - ψ a 0))))).comp
        (Polynomial.mapRingHom (TKn (knCoord K m) (projKn ψ a))) := by
    refine Polynomial.ringHom_ext (fun x => ?_) ?_
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_compRingHom_apply, Polynomial.C_comp]
      rw [psi_C, TKn_germMap]
      exact (ofPoly_C _).symm
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coe_compRingHom_apply, Polynomial.X_comp]
      rw [psi_X, TKn_shiftGerm]
      exact (ofPoly_X_sub_C _).symm
  have := congrArg (fun f => f Q) key
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_compRingHom_apply]
    at this
  exact this

theorem psi_injective (a : Kn.{u} K (m + 1)) (x0 : K) : Function.Injective (psi ψ a x0) := by
  intro Q Q' h
  have h1 := congrArg (TKn ψ a) h
  rw [TKn_psi, TKn_psi, ofPoly_injective.eq_iff] at h1
  have h2 := congrArg
    (fun P => P.comp (Polynomial.X + Polynomial.C (MvPowerSeries.C (x0 - ψ a 0)))) h1
  simp only [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    add_sub_cancel_right, Polynomial.comp_X] at h2
  exact Polynomial.map_injective _ (TKn_injective (knCoord K m) _) h2

/-- The germ of a polynomial combination is `Ψ_a` of the polynomial with the germs of the
coefficients. -/
theorem germ_polyComb_eq_psi {V : Opens (Kn.{u} K m)} {a : Kn.{u} K (m + 1)}
    (ha : a ∈ baseOpens ψ V) (x0 : K) {N : ℕ} (w : Fin N → (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (polyComb ψ V x0 w) =
      psi ψ a x0 (∑ k, Polynomial.C ((sheafKn K m).presheaf.germ V (projKn ψ a) ha (w k)) *
        Polynomial.X ^ (k : ℕ)) := by
  rw [polyComb, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, map_mul, map_pow, psi_C, psi_X, germ_pullSec ψ ha, germ_shiftSec ψ ha]

/-- The germ of a monic polynomial section is `Ψ_a` of the Weierstrass-shaped polynomial with the
germs of the coefficients. -/
theorem germ_polyMonic_eq_psi {V : Opens (Kn.{u} K m)} {a : Kn.{u} K (m + 1)}
    (ha : a ∈ baseOpens ψ V) (x0 : K) (e : ℕ) (c : Fin e → (sheafKn K m).presheaf.obj (op V)) :
    (sheafKn K (m + 1)).presheaf.germ (baseOpens ψ V) a ha (polyMonic ψ V x0 e c) =
      psi ψ a x0 (weierstrassPolynomial e fun j =>
        (sheafKn K m).presheaf.germ V (projKn ψ a) ha (c j)) := by
  rw [polyMonic, weierstrassPolynomial, map_add, map_pow, map_sum, map_add, map_pow, map_sum,
    psi_X, germ_shiftSec ψ ha]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, map_mul, map_pow, psi_C, psi_X, germ_pullSec ψ ha, germ_shiftSec ψ ha]

/-- Freitag's identification `K_N = 𝒪_{n−1}[z_n : N] ∩ K` [Fre17, Ch. I, 10.4]: for `0 < N`, a stalk
element whose Taylor series has `x_0`-degree `< N` is `Ψ_a Q` for a polynomial `Q` over the base
stalk of degree `< N`. -/
theorem exists_psi_eq_of_degLt (a : Kn.{u} K (m + 1)) (x0 : K) {N : ℕ} (hN : 0 < N)
    (b : (sheafKn K (m + 1)).presheaf.stalk a) (hb : DegLt N (TKn ψ a b)) :
    ∃ Q : Polynomial ((sheafKn K m).presheaf.stalk (projKn ψ a)),
      Q.natDegree < N ∧ psi ψ a x0 Q = b := by
  set P := toPoly N (TKn ψ a b) with hP
  have hPdeg : P.natDegree < N := natDegree_toPoly_lt N _ hN
  have hPconv : ∀ k, P.coeff k ∈ Analytic.Conv K m := fun k => by
    rw [hP, toPoly, PowerSeries.coeff_trunc]
    split_ifs
    · exact coeff_splitFirst_mem_conv (TKn_mem_conv ψ a b) k
    · exact Subalgebra.zero_mem _
  -- lift the coefficients of `P` through the Taylor isomorphism of the base stalk
  choose q hq using fun k => exists_TKn_eq (knCoord K m) (projKn ψ a) (hPconv k)
  set Q0 : Polynomial ((sheafKn K m).presheaf.stalk (projKn ψ a)) :=
    ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (q k) * Polynomial.X ^ k with hQ0
  have hQ0map : Q0.map (TKn (knCoord K m) (projKn ψ a)) = P := by
    rw [hQ0, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, hq]
    exact (Polynomial.as_sum_range_C_mul_X_pow P).symm
  have hQ0deg : Q0.natDegree ≤ P.natDegree := by
    rw [hQ0]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  -- the constant of the inverse shift, lifted to the base stalk
  obtain ⟨t, ht⟩ := exists_TKn_eq (knCoord K m) (projKn ψ a)
    (show MvPowerSeries.C (x0 - ψ a 0) ∈ Analytic.Conv K m from monomial_mem_conv 0 _)
  refine ⟨Q0.comp (Polynomial.X + Polynomial.C t), ?_, ?_⟩
  · calc (Q0.comp (Polynomial.X + Polynomial.C t)).natDegree
        ≤ Q0.natDegree * (Polynomial.X + Polynomial.C t).natDegree := Polynomial.natDegree_comp_le
      _ = Q0.natDegree := by rw [Polynomial.natDegree_X_add_C, mul_one]
      _ < N := lt_of_le_of_lt hQ0deg hPdeg
  · apply TKn_injective ψ a
    rw [TKn_psi, Polynomial.map_comp, hQ0map, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_C, ht, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
      Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X, hP, ofPoly_toPoly hb]

end AnalyticSpace
