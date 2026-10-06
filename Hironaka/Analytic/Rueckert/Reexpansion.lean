/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Basic
import Hironaka.Analytic.ConvSeries.Bridge
import Hironaka.Analytic.ConvSeries.Rescale
import Hironaka.Analytic.Germ.CoordDiv
import Hironaka.Analytic.Rueckert.EvalRename
import Hironaka.Analytic.Rueckert.EvalTools
import Hironaka.Analytic.Rueckert.Parameters
import Hironaka.Analytic.Rueckert.ZeroSet
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Monic relations under translation of the centre

The analytic half of the upper semicontinuity of the dimension of an analytic germ
[Fre17, Ch. II, 5.4], on `Conv K n`. A Noether normalization `𝒪_d → 𝒪_n/I`
(`NoetherNormalization.lean`: embed along `e : Fin d ↪ Fin n`, substitute the linear change
`σ = substEquiv L`, reduce mod `I`) is module-finite, so every coordinate `σ (X i)` is integral
over `𝒪_d`: it satisfies a monic relation `σ (X_i^D + ∑_k c_k(X ∘ e) X_i^k) ∈ I`
(`exists_monic_relation_of_finite`; the module-finiteness of the normalization in the proof of
[Fre17, Ch. II, 5.4]). The relation is a convergent series; its function near a nearby centre `w`
is again of the same shape, with the coefficient series `c_k` re-expanded at the projected point
`(L w) ∘ e` (`exists_reexpansion`, from `AnalyticAt.exists_eventuallyEq_evalSeries`) and the fibre
coordinate translated by `(L w) i` (`exists_substEquiv_shapeSeries_translate`; the polynomial
`Q(a₁, …, a_{n−1}, z_n − a_n)`, general in `z_n − a_n` with coefficients converging on a common
polydisc, of the same proof). Modulo the base coordinates `σ X_{e j}` such a shape is a monic
polynomial with constant coefficients in `σ X_i + a` (`substEquiv_shapeSeries_sub_mem`, by
`convEmbed_sub_algebraMap_mem`), which is what the parameter bound
`ringKrullDim_quotient_le_of_parameters` (`Parameters.lean`, Krull's height theorem) needs:
`ringKrullDim_quotient_le_of_forall_exists_shape_mem`. The semicontinuity theorem for analytic
spaces (`Hironaka/AnalyticSpace/Semicontinuity.lean`) realizes the relations as sections near the
point, spreads their membership in the ideal to a neighbourhood and reads their germs at nearby
points through the Taylor isomorphism.

Two steps differ from the printed proof: the translation lemma
`eventually_eventually_add_of_eventuallyEq` (a formal filter statement) and the re-expansion of
the coefficients replace the Weierstrass polynomial whose coefficients converge on a polydisc, and
the parameter bound replaces the appeal to Cohen–Seidenberg for `dim 𝒪_{Y,f(a)} ≥ dim 𝒪_{X,a}`
([Fre17, Ch. II, 5.4] with [Fre17, Ch. VII, 5.6–5.7]).
-/

@[expose] public section

open MvPowerSeries Filter Topology

namespace Analytic

variable {K : Type*} [RCLike K] {n d : ℕ}

/-- The function of a series embedded along `e` is the function of the series in the base
coordinates `x ∘ e` (`convEmbed` is `rename e`). -/
theorem evalSeries_convEmbed (e : Fin d ↪ Fin n) (c : Conv K d) (x : Fin n → K) :
    evalSeries (convEmbed K e c : MvPowerSeries (Fin n) K) x =
      evalSeries (c : MvPowerSeries (Fin d) K) (x ∘ e) := by
  rw [coe_convEmbed, evalSeries_rename]

/-- The function of a constant series is the constant. -/
theorem evalSeries_algebraMap_conv (a : K) (x : Fin n → K) :
    evalSeries ((algebraMap K (Conv K n) a : Conv K n) : MvPowerSeries (Fin n) K) x = a := by
  rw [Subalgebra.coe_algebraMap, MvPowerSeries.algebraMap_apply]
  rw [Algebra.algebraMap_self, RingHom.id_apply, evalSeries_C']

/-- The function of the coordinate series `X i` is the coordinate `x i`. -/
theorem evalSeries_convX (i : Fin n) (x : Fin n → K) :
    evalSeries (convX K i : MvPowerSeries (Fin n) K) x = x i := by
  have := evalSeries_X_pow i 1 x
  rwa [pow_one, pow_one, ← coe_convX] at this

/-- `Conv`-level form of `evalSeries_add_eventually`. -/
theorem evalSeries_conv_add_eventually (f g : Conv K n) :
    evalSeries ((f + g : Conv K n) : MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)] fun x =>
      evalSeries (f : MvPowerSeries (Fin n) K) x + evalSeries (g : MvPowerSeries (Fin n) K) x := by
  rw [Subalgebra.coe_add]
  exact evalSeries_add_eventually f.2 g.2

/-- `Conv`-level form of `evalSeries_mul_eventually`. -/
theorem evalSeries_conv_mul_eventually (f g : Conv K n) :
    evalSeries ((f * g : Conv K n) : MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)] fun x =>
      evalSeries (f : MvPowerSeries (Fin n) K) x * evalSeries (g : MvPowerSeries (Fin n) K) x := by
  rw [Subalgebra.coe_mul]
  exact evalSeries_mul_eventually f.2 g.2

/-- `Conv`-level form of `evalSeries_pow_eventually`. -/
theorem evalSeries_conv_pow_eventually (f : Conv K n) (k : ℕ) :
    evalSeries ((f ^ k : Conv K n) : MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)] fun x =>
      evalSeries (f : MvPowerSeries (Fin n) K) x ^ k := by
  rw [Subalgebra.coe_pow]
  exact evalSeries_pow_eventually f.2 k

/-- `Conv`-level form of `evalSeries_finsetSum_eventually`. -/
theorem evalSeries_conv_sum_eventually {ι : Type*} (s : Finset ι) (F : ι → Conv K n) :
    evalSeries ((∑ i ∈ s, F i : Conv K n) : MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)] fun x =>
      ∑ i ∈ s, evalSeries (F i : MvPowerSeries (Fin n) K) x := by
  rw [AddSubmonoidClass.coe_finsetSum]
  exact evalSeries_finsetSum_eventually s F

variable (K) in
/-- The shape `(X_i + a)^D + ∑_k c_k(X ∘ e) (X_i + a)^k` of a monic relation for `X_i` over the
base coordinates `X ∘ e`, translated by `a` in the fibre coordinate. -/
noncomputable def shapeSeries (i : Fin n) (e : Fin d ↪ Fin n) {D : ℕ} (a : K)
    (c : Fin D → Conv K d) : Conv K n :=
  (convX K i + algebraMap K (Conv K n) a) ^ D +
    ∑ k : Fin D, convEmbed K e (c k) * (convX K i + algebraMap K (Conv K n) a) ^ (k : ℕ)

/-- The function of the shape near `0`. -/
theorem evalSeries_shapeSeries (i : Fin n) (e : Fin d ↪ Fin n) {D : ℕ} (a : K)
    (c : Fin D → Conv K d) :
    evalSeries (shapeSeries K i e a c : MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)] fun x =>
      (x i + a) ^ D + ∑ k : Fin D, evalSeries (c k : MvPowerSeries (Fin d) K) (x ∘ e) *
        (x i + a) ^ (k : ℕ) := by
  set A : Conv K n := convX K i + algebraMap K (Conv K n) a with hA
  have h3 : evalSeries (A : MvPowerSeries (Fin n) K) =ᶠ[𝓝 (0 : Fin n → K)] fun x => x i + a := by
    refine (evalSeries_conv_add_eventually _ _).trans (Eventually.of_forall fun x => ?_)
    simp only [evalSeries_convX, evalSeries_algebraMap_conv]
  have h1 := evalSeries_conv_add_eventually (A ^ D)
    (∑ k : Fin D, convEmbed K e (c k) * A ^ (k : ℕ))
  have h2 := evalSeries_conv_pow_eventually A D
  have h4 := evalSeries_conv_sum_eventually Finset.univ fun k : Fin D =>
    convEmbed K e (c k) * A ^ (k : ℕ)
  have h5 : ∀ᶠ x in 𝓝 (0 : Fin n → K), ∀ k : Fin D,
      evalSeries ((convEmbed K e (c k) * A ^ (k : ℕ) : Conv K n) : MvPowerSeries (Fin n) K) x =
        evalSeries (convEmbed K e (c k) : MvPowerSeries (Fin n) K) x *
          evalSeries ((A ^ (k : ℕ) : Conv K n) : MvPowerSeries (Fin n) K) x :=
    eventually_all.mpr fun k => evalSeries_conv_mul_eventually _ _
  have h6 : ∀ᶠ x in 𝓝 (0 : Fin n → K), ∀ k : Fin D,
      evalSeries ((A ^ (k : ℕ) : Conv K n) : MvPowerSeries (Fin n) K) x =
        evalSeries (A : MvPowerSeries (Fin n) K) x ^ (k : ℕ) :=
    eventually_all.mpr fun k => evalSeries_conv_pow_eventually A k
  filter_upwards [h1, h2, h3, h4, h5, h6] with x h1 h2 h3 h4 h5 h6
  change evalSeries ((A ^ D + ∑ k : Fin D, convEmbed K e (c k) * A ^ (k : ℕ) : Conv K n) :
    MvPowerSeries (Fin n) K) x = _
  rw [h1, h2, h3, h4]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h5 k, h6 k, h3, evalSeries_convEmbed]

/-- Modulo the base coordinates `σ X_{e j}`, `σ (shapeSeries a c)` is the polynomial expression
with the constant coefficients of the `c_k` in `σ X_i + a`. -/
theorem substEquiv_shapeSeries_sub_mem (L : (Fin n → K) ≃L[K] (Fin n → K)) (i : Fin n)
    (e : Fin d ↪ Fin n) {D : ℕ} (a : K) (c : Fin D → Conv K d) :
    substEquiv L (shapeSeries K i e a c) -
      ((substEquiv L (convX K i) + algebraMap K (Conv K n) a) ^ D +
        ∑ k : Fin D, algebraMap K (Conv K n) (constantCoeff (c k : MvPowerSeries (Fin d) K)) *
          (substEquiv L (convX K i) + algebraMap K (Conv K n) a) ^ (k : ℕ)) ∈
      Ideal.span (Set.range fun j => substEquiv L (convX K (e j))) := by
  unfold shapeSeries
  simp only [map_add, map_pow, map_sum, map_mul, AlgEquiv.commutes]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [← sub_mul]
  refine Ideal.mul_mem_right _ _ ?_
  have h2 := Ideal.mem_map_of_mem (substEquiv L) (convEmbed_sub_algebraMap_mem e (c k))
  rw [map_sub, AlgEquiv.commutes, Ideal.map_span, ← Set.range_comp] at h2
  exact h2

/-- Re-expansion of a convergent series at a point near `0` (the coefficients are re-expanded at
the projected point; the coefficients converging on a common polydisc in the proof of
[Fre17, Ch. II, 5.4]). -/
theorem exists_reexpansion (c : Conv K d) :
    ∀ᶠ u₀ in 𝓝 (0 : Fin d → K), ∃ c' : Conv K d,
      ∀ᶠ u in 𝓝 u₀, evalSeries (c : MvPowerSeries (Fin d) K) u =
        evalSeries (c' : MvPowerSeries (Fin d) K) (u - u₀) := by
  obtain ⟨ρ, hρ⟩ := c.2
  have h0 : polydisc K ρ ∈ 𝓝 (0 : Fin d → K) :=
    (isOpen_polydisc ρ).mem_nhds fun k => by simpa using ρ.pos k
  filter_upwards [h0] with u₀ hu₀
  obtain ⟨ρ', c'', hc'', h⟩ :=
    AnalyticAt.exists_eventuallyEq_evalSeries (analyticOnNhd_evalSeries hρ u₀ hu₀)
  exact ⟨⟨c'', ρ', hc''⟩, h⟩

/-- Translation of an eventual equality at `0`: if `F` and `G` agree near `0`, then for `v` near
`0`, `F (z + v) = G (z + v)` for `z` near `0`. -/
theorem eventually_eventually_add_of_eventuallyEq {F G : (Fin n → K) → K}
    (h : F =ᶠ[𝓝 (0 : Fin n → K)] G) :
    ∀ᶠ v in 𝓝 (0 : Fin n → K), ∀ᶠ z in 𝓝 (0 : Fin n → K), F (z + v) = G (z + v) := by
  filter_upwards [h.eventually_nhds] with v hv
  have ht : Tendsto (fun z : Fin n → K => z + v) (𝓝 0) (𝓝 v) := by
    have := (continuous_add_const v).tendsto (0 : Fin n → K)
    rwa [zero_add] at this
  exact ht.eventually hv

/-- Composition with `∘ e` tends to `0` at `0`. -/
theorem tendsto_comp_embedding (e : Fin d ↪ Fin n) :
    Tendsto (fun v : Fin n → K => v ∘ e) (𝓝 0) (𝓝 0) := by
  have : Continuous fun v : Fin n → K => v ∘ e := continuous_pi fun j => continuous_apply (e j)
  simpa using this.tendsto (0 : Fin n → K)

/-- A continuous linear equivalence tends to `0` at `0`. -/
theorem tendsto_clequiv_zero (L : (Fin n → K) ≃L[K] (Fin n → K)) :
    Tendsto (fun z : Fin n → K => L z) (𝓝 0) (𝓝 0) :=
  L.continuous.tendsto' 0 0 (map_zero L)

/-- Translation of a monic relation: for `w` near `0`, the function `z ↦ σ(shape 0 c)(z + w)` is
near `z = 0` the function of `σ (shape ((L w) i) c')` for re-expanded coefficients `c'`. -/
theorem exists_substEquiv_shapeSeries_translate (L : (Fin n → K) ≃L[K] (Fin n → K)) (i : Fin n)
    (e : Fin d ↪ Fin n) {D : ℕ} (c : Fin D → Conv K d) :
    ∀ᶠ w in 𝓝 (0 : Fin n → K), ∃ c' : Fin D → Conv K d,
      ∀ᶠ z in 𝓝 (0 : Fin n → K),
        evalSeries (substEquiv L (shapeSeries K i e 0 c) : MvPowerSeries (Fin n) K) (z + w) =
          evalSeries (substEquiv L (shapeSeries K i e (L w i) c') : MvPowerSeries (Fin n) K) z := by
  have hL := tendsto_clequiv_zero L
  have hE1 := eventually_eventually_add_of_eventuallyEq
    (evalSeries_substConv (L : (Fin n → K) →L[K] (Fin n → K)) (shapeSeries K i e 0 c))
  have hE3 := hL.eventually
    (eventually_eventually_add_of_eventuallyEq (evalSeries_shapeSeries i e 0 c))
  have hE2 : ∀ᶠ w in 𝓝 (0 : Fin n → K), ∀ k : Fin D, ∃ c' : Conv K d,
      ∀ᶠ u in 𝓝 ((L w) ∘ e), evalSeries (c k : MvPowerSeries (Fin d) K) u =
        evalSeries (c' : MvPowerSeries (Fin d) K) (u - (L w) ∘ e) :=
    ((tendsto_comp_embedding e).comp hL).eventually
      (eventually_all.mpr fun k => exists_reexpansion (c k))
  filter_upwards [hE1, hE3, hE2] with w hw1 hw3 hw2
  choose c' hc' using hw2
  refine ⟨c', ?_⟩
  have hw3' := hL.eventually hw3
  have hu : ∀ᶠ z in 𝓝 (0 : Fin n → K), ∀ k : Fin D,
      evalSeries (c k : MvPowerSeries (Fin d) K) ((L z + L w) ∘ e) =
        evalSeries (c' k : MvPowerSeries (Fin d) K) ((L z) ∘ e) := by
    have hc : Continuous fun z : Fin n → K => (L z + L w) ∘ e :=
      continuous_pi fun j => (continuous_apply (e j)).comp (L.continuous.add continuous_const)
    have ht : Tendsto (fun z : Fin n → K => (L z + L w) ∘ e) (𝓝 0) (𝓝 ((L w) ∘ e)) :=
      hc.tendsto' 0 _ (by rw [map_zero, zero_add])
    refine (eventually_all.mpr fun k => ht.eventually (hc' k)).mono fun z hz k => ?_
    rw [hz k]
    congr 1
    funext j
    simp
  have hE0' := hL.eventually (evalSeries_shapeSeries i e (L w i) c')
  have hsub := evalSeries_substConv (L : (Fin n → K) →L[K] (Fin n → K))
    (shapeSeries K i e (L w i) c')
  filter_upwards [hw1, hw3', hu, hE0', hsub] with z h1 h3 hu h0 hs
  rw [substEquiv_apply, h1, Function.comp_apply, map_add, substEquiv_apply, hs,
    Function.comp_apply]
  change evalSeries (↑(shapeSeries K i e 0 c)) (L z + L w) = evalSeries _ (L z)
  rw [h3, h0]
  simp only [Pi.add_apply, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hu k]

/-- A finite normalization map makes every coordinate `σ (X i)` integral over `𝒪_d`: a monic
relation of the shape `σ (X_i^D + ∑_k c_k(X ∘ e) X_i^k) ∈ I` (`shapeSeries` with `a = 0`); the
module-finiteness of the normalization in the proof of [Fre17, Ch. II, 5.4]. -/
theorem exists_monic_relation_of_finite (I : Ideal (Conv K n)) (e : Fin d ↪ Fin n)
    (L : (Fin n → K) ≃L[K] (Fin n → K))
    (hfin : RingHom.Finite (A := Conv K d) (B := Conv K n ⧸ I)
      (normMap K I e L : Conv K d →+* Conv K n ⧸ I)) (i : Fin n) :
    ∃ (D : ℕ) (c : Fin D → Conv K d), substEquiv L (shapeSeries K i e 0 c) ∈ I := by
  obtain ⟨p, hp, hp0⟩ := hfin.to_isIntegral (Ideal.Quotient.mk I (substEquiv L (convX K i)))
  refine ⟨p.natDegree, fun k => p.coeff k, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hp0]
  conv_rhs => rw [hp.as_sum]
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, Finset.sum_range]
  simp only [shapeSeries, map_zero, add_zero, map_add, map_pow, map_sum, map_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_monomial]
  rfl

/-- If every coordinate `σ (X i)` satisfies a relation of the shape `σ (shapeSeries i e a c) ∈ I`,
then `dim 𝒪_n / I ≤ d`: the relation is monic with constant coefficients modulo the base
coordinates, and the parameter bound applies ([Fre17, Ch. II, 5.4] with [Fre17, Ch. VII, 5.6]). -/
theorem ringKrullDim_quotient_le_of_forall_exists_shape_mem (I : Ideal (Conv K n))
    (L : (Fin n → K) ≃L[K] (Fin n → K)) (e : Fin d ↪ Fin n)
    (h : ∀ i : Fin n, ∃ (D : ℕ) (a : K) (c : Fin D → Conv K d),
      substEquiv L (shapeSeries K i e a c) ∈ I) :
    ringKrullDim (Conv K n ⧸ I) ≤ (d : WithBot ℕ∞) := by
  refine ringKrullDim_quotient_le_of_parameters I (substEquiv L) e fun i _ => ?_
  obtain ⟨D, a, c, hmem⟩ := h i
  have h1 := substEquiv_shapeSeries_sub_mem L i e a c
  have h2 := Ideal.sub_mem _ (Ideal.mem_sup_left hmem) (Ideal.mem_sup_right h1)
  rw [sub_sub_cancel] at h2
  exact exists_monic_aeval_mem_of_pow_add_sum
    (fun k => constantCoeff (c k : MvPowerSeries (Fin d) K)) a h2

end Analytic
