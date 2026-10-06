/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CompletionMap
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Valuation.ValuationRing
import Hironaka.Algebra.Local.ChartCompletion
import Hironaka.Algebra.Local.Taylor
import Mathlib.Combinatorics.Matroid.Init

/-!
# A local homomorphism inducing an isomorphism of completions

A bijectivity criterion for the map of completions `Â → B̂` induced by a local homomorphism
`f : A → B` of Noetherian local rings, through the Cohen structure theorem
(`completionMap_bijective_of_cohen`). Given a coefficient field on `Â` and a regular system of
parameters `y` of `A`, so that `Ψ : K_A⟦X⟧ ≃ Â` (`cohenEquivOfResidue`,
`Hironaka/Algebra/Local/CohenIso.lean`), and an isomorphism `Θ : B̂ ≃ K⟦X⟧` with `Θ(f(yᵢ)) = Xᵢ`
such that `Θ ∘ f̂` carries the coefficient field to the constants through a bijection `e : K_A → K`,
the composite `Θ ∘ f̂ ∘ Ψ : K_A⟦X⟧ → K⟦X⟧` is the coefficient map `F ↦ F.map e`: both sides agree,
level by level, with the evaluation of the truncation `truncTotal N F` modulo `𝔪ᴺ` (`mk_cohenMap`).
Hence `f̂` is bijective.

Also here: a ring map `c : K → A` from a field with a local retraction `ev : A → K` identifies `K`
with the residue field of `A`, and `K → A → Â` is then a coefficient field of `Â`, a section of the
residue map in the sense of [Kol07, Definition 55] (`isCoefficientAlgebra_of_section`); this is the
situation of [BM97, (0.1)(2)], where the residue field is contained in the completion. Coefficient
maps of power series along a bijection are bijections (`mvPowerSeries_map_bijective`).

Applied in `Hironaka/Manifold/BlowUp/Transform/StrictSubspaceCompletion.lean`, an input to the
proof there of [BM97, Proposition 3.13] on the strict transform, to the map `R'_{𝔪'} → 𝒪_{M',a'}`
from the local ring of the chart ring to the ring of germs of analytic functions at a point of the
exceptional divisor, with the constants as the coefficient field and the Taylor isomorphism
`𝒪̂_{M',a'} ≅ 𝕜⟦X⟧` as `Θ`. The criterion itself is not stated in the sources.
-/

public section

open IsLocalRing MvPowerSeries

namespace IsLocalRing

/-- Coefficient maps of power series along a bijection are bijections. -/
theorem mvPowerSeries_map_bijective {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    {e : K →+* L} (he : Function.Bijective e) :
    Function.Bijective (MvPowerSeries.map (σ := Fin n) e) := by
  let e' := RingEquiv.ofBijective e he
  have h1 : ∀ F : MvPowerSeries (Fin n) K,
      MvPowerSeries.map (σ := Fin n) (e'.symm : L →+* K) (MvPowerSeries.map (σ := Fin n) e F) = F :=
    fun F => by
      rw [MvPowerSeries.map_map]
      have : (e'.symm : L →+* K).comp e = RingHom.id K :=
        RingHom.ext fun k => e'.symm_apply_apply k
      rw [this, MvPowerSeries.map_id, RingHom.id_apply]
  have h2 : ∀ G : MvPowerSeries (Fin n) L,
      MvPowerSeries.map (σ := Fin n) e (MvPowerSeries.map (σ := Fin n) (e'.symm : L →+* K) G) = G :=
    fun G => by
      rw [MvPowerSeries.map_map]
      have : e.comp (e'.symm : L →+* K) = RingHom.id L :=
        RingHom.ext fun l => e'.apply_symm_apply l
      rw [this, MvPowerSeries.map_id, RingHom.id_apply]
  exact ⟨fun F G h => by rw [← h1 F, h, h1], fun G => ⟨_, h2 G⟩⟩

variable {A B : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [CommRing B]
  [IsNoetherianRing B] [IsLocalRing B] {K : Type*} [Field K] {n : ℕ}

omit [IsNoetherianRing B] [IsLocalRing B] in
/-- **Constants as a coefficient field** ([Kol07, Definition 55]): a ring map `c : K → A` from a
field with a local retraction `ev : A → K` (`ev ∘ c = id`) identifies `K` with the residue field of
`A`, and `K → A → Â` is a coefficient field of `Â`, a section of the residue map. -/
theorem isCoefficientAlgebra_of_section (ev : A →+* K) [IsLocalHom ev] (cA : K →+* A)
    (hevc : ∀ b, ev (cA b) = b) [Algebra (ResidueField A) (AdicCompletion (maximalIdeal A) A)]
    (hσ : ∀ k, algebraMap (ResidueField A) (AdicCompletion (maximalIdeal A) A) k =
      algebraMap A (AdicCompletion (maximalIdeal A) A) (cA (ResidueField.lift ev k))) :
    IsCoefficientAlgebra A := by
  intro k
  obtain ⟨a, rfl⟩ := residue_surjective k
  rw [hσ]
  change residue _ (algebraMap A (AdicCompletion (maximalIdeal A) A)
    (cA (ResidueField.lift ev (residue A a)))) =
      ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) (residue A a)
  rw [ResidueField.map_residue]
  refine Ideal.Quotient.eq.mpr ?_
  rw [← map_sub, AdicCompletion.maximalIdeal_eq_map]
  refine Ideal.mem_map_of_mem _ ?_
  rw [← maximalIdeal_comap ev, Ideal.mem_comap, map_sub, hevc, ResidueField.lift_residue_apply,
    sub_self]
  exact Ideal.zero_mem _

/-- **Bijectivity of the induced map of completions through Cohen structure**: for a local
homomorphism `f : A → B`, a regular system of parameters `y` of `A`, a coefficient field on `Â`,
and an isomorphism `Θ : B̂ ≃ K⟦X⟧` with `Θ(f(yᵢ)) = Xᵢ` and `Θ(f̂(k)) = e(k)` for a bijection
`e : K_A → K` of the coefficient fields, `f̂ : Â → B̂` is bijective: `Θ ∘ f̂ ∘ Ψ` is the coefficient
map `F ↦ F.map e`. -/
theorem completionMap_bijective_of_cohen (f : A →+* B) [IsLocalHom f] (y : Fin n → A)
    (hy : maximalIdeal A = Ideal.span (Set.range y)) (hd : (n : WithBot ℕ∞) = ringKrullDim A)
    [Algebra (ResidueField A) (AdicCompletion (maximalIdeal A) A)] (hι : IsCoefficientAlgebra A)
    (Θ : AdicCompletion (maximalIdeal B) B ≃+* MvPowerSeries (Fin n) K)
    (e : ResidueField A →+* K) (he : Function.Bijective e)
    (hΘy : ∀ i, Θ (algebraMap B _ (f (y i))) = X i)
    (hΘk : ∀ k, Θ (completionMap f (algebraMap (ResidueField A) _ k)) = C (e k)) :
    Function.Bijective (completionMap f) := by
  classical
  set Ψ := cohenEquivOfResidue A y hι hy hd with hΨdef
  let g : AdicCompletion (maximalIdeal A) A →+* MvPowerSeries (Fin n) K :=
    (Θ : AdicCompletion (maximalIdeal B) B →+* MvPowerSeries (Fin n) K).comp (completionMap f)
  have hg : ∀ (N : ℕ) (z : AdicCompletion (maximalIdeal A) A),
      z ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ N →
        g z ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
    intro N z hz
    have h1 := completionMap_mem_maximalIdeal_pow f hz
    have h2 : (maximalIdeal (AdicCompletion (maximalIdeal B) B) ^ N).map
        (Θ : AdicCompletion (maximalIdeal B) B →+* MvPowerSeries (Fin n) K) ≤
          maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (map_maximalIdeal_le _) N
    exact h2 (Ideal.mem_map_of_mem _ h1)
  -- the polynomial part: `g (P(ι y)) = P.map e`
  have hpoly : g.comp (MvPolynomial.aeval fun i => algebraMap A (AdicCompletion (maximalIdeal A) A)
      (y i)).toRingHom = MvPolynomial.coeToMvPowerSeries.ringHom.comp (MvPolynomial.map e) := by
    refine MvPolynomial.ringHom_ext (fun k => ?_) (fun i => ?_)
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_C]
      exact hΘk k
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
        MvPolynomial.coe_X]
      change Θ (completionMap f (algebraMap A _ (y i))) = X i
      rw [completionMap_algebraMap]
      exact hΘy i
  -- the key identity, level by level
  have hkey : ∀ F, g (Ψ F) = MvPowerSeries.map e F := by
    intro F
    refine eq_of_forall_mk_pow_eq (maximalIdeal (MvPowerSeries (Fin n) K)) fun N => ?_
    have hΨ : Ideal.Quotient.mk (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ N) (Ψ F) =
        Ideal.Quotient.mk _ (MvPolynomial.aeval
          (fun i => algebraMap A (AdicCompletion (maximalIdeal A) A) (y i)) (truncTotal N F)) := by
      rw [hΨdef, cohenEquivOfResidue_apply, mk_cohenMap, levelEval_apply]
      have : (Ideal.Quotient.mkₐ (ResidueField A)
          (maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ N)).comp
            (MvPolynomial.aeval fun i => algebraMap A (AdicCompletion (maximalIdeal A) A) (y i)) =
          MvPolynomial.aeval (levelVar A y N) := by
        rw [MvPolynomial.comp_aeval]
        rfl
      exact (congrArg (fun φ => φ (truncTotal N F)) this).symm
    have hz := hg N _ (Ideal.Quotient.eq.mp hΨ)
    rw [map_sub] at hz
    have hmk : Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin n) K) ^ N) (g (Ψ F)) =
        Ideal.Quotient.mk _ (g (MvPolynomial.aeval
          (fun i => algebraMap A (AdicCompletion (maximalIdeal A) A) (y i)) (truncTotal N F))) :=
      Ideal.Quotient.eq.mpr hz
    have hp := RingHom.congr_fun hpoly (truncTotal N F)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply] at hp
    rw [hmk, hp, ← truncTotal_map]
    rcases N with _ | N
    · exact eq_of_pow_zero _ _ _
    · exact (Ideal.Quotient.eq.mpr (sub_truncTotal_mem (MvPowerSeries.map e F) N)).symm
  have hfun : ⇑(completionMap f) =
      (Θ.symm : MvPowerSeries (Fin n) K → AdicCompletion (maximalIdeal B) B) ∘
        MvPowerSeries.map e ∘ (Ψ.symm : AdicCompletion (maximalIdeal A) A →
          MvPowerSeries (Fin n) (ResidueField A)) := by
    funext z
    simp only [Function.comp_apply]
    rw [← hkey, RingEquiv.apply_symm_apply]
    exact (Θ.symm_apply_apply (completionMap f z)).symm
  rw [hfun]
  exact Θ.symm.bijective.comp ((mvPowerSeries_map_bijective he).comp Ψ.symm.bijective)

end IsLocalRing
