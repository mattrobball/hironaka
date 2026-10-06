/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.CoherentAnalytic
import Hironaka.AnalyticSpace.CoherentLemmas
import Hironaka.AnalyticSpace.CoherentQuotient
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Colon ideals of ideal sheaves have local generators

For ideal sheaves `J`, `I` of finite type on an analytic `K`-space, the stalkwise colon
`(J_x : I_x)` has local generators (in the spirit of [Fre17, Ch. I, 10.6 and 10.8]). With
`I_x = (h₁, …, h_l)` and `J_x = (f₁, …, f_m)` near `x`, `r ∈ (J_x : I_x)` iff `r h_j ∈ J_x` for
every `j`, iff `r` extends to a relation `(r, b)` of the augmented matrix with rows
`(h_j | −f in block j)`; by coherence the relations are generated near `x` by finitely many
sections `R_n`, and the first components `R_{n,0}` generate the colon at every point near `x`
(`hasLocalGenerators_colon_idealSheaf`). This is the bookkeeping for the saturation
`⋃_k (J : I^k)`, which describes the strict transform of a closed subspace under a blow-up
([BM97, Proposition 3.13] and the sentence after it, `𝓘_{X'} = ⋃_k [𝓘 : y_exc^k]`): the colon
ideal sheaves `(J : I^k)` form an increasing chain of ideal sheaves of finite type, whose local
stationarity is the Noether lemma (`Hironaka/AnalyticSpace/NoetherDerived.lean`,
`Hironaka/AnalyticSpace/ModelTransport.lean`).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open AnalyticSpace.QuotientSpace (augCol augMat augVec augVec_inl augVec_inr sum_map_augMat_mul)

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- The stalkwise colon `(J_x : I_x)` of two ideal sheaves of finite type on an analytic
`K`-space has local generators. -/
theorem hasLocalGenerators_colon_idealSheaf (X : AnalyticSpace.{u} K)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x)) := by
  intro a
  obtain ⟨U₁, haU₁, l, h, -, hh⟩ := I.exists_generators a
  obtain ⟨U₂, haU₂, m, f, -, hf⟩ := J.exists_generators a
  obtain ⟨U, hU⟩ : ∃ U, U = U₁ ⊓ U₂ := ⟨_, rfl⟩
  have hUU₁ : U ≤ U₁ := hU ▸ inf_le_left
  have hUU₂ : U ≤ U₂ := hU ▸ inf_le_right
  have haU : a ∈ U := by
    rw [hU, ← SetLike.mem_coe, Opens.coe_inf]
    exact ⟨haU₁, haU₂⟩
  -- the augmented matrix: row `j` is `(h_j | −f in block j)`
  obtain ⟨A, hA⟩ : ∃ A : Fin l → Fin 1 → X.toLocallyRingedSpace.𝒪.presheaf.obj (op U),
      A = fun j _ => X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU₁).op (h j) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin m → X.toLocallyRingedSpace.𝒪.presheaf.obj (op U),
      g = fun i => -X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU₂).op (f i) := ⟨_, rfl⟩
  obtain ⟨V, hVU, haV, k, R, hR⟩ :=
    isCoherent_analyticSpace X U (1 + l * m) l (augMat A g) a haU
  have hVU₁ : V ≤ U₁ := hVU.trans hUU₁
  have hVU₂ : V ≤ U₂ := hVU.trans hUU₂
  refine ⟨V, haV, Fin k, inferInstance, fun n => R n (augCol 1 l m (Sum.inl 0)), fun b hb => ?_⟩
  -- the germs of the matrix entries at `b`
  have hgA : ∀ j (t : Fin 1), X.toLocallyRingedSpace.𝒪.presheaf.germ U b (hVU hb) (A j t) =
      X.toLocallyRingedSpace.𝒪.presheaf.germ U₁ b (hVU₁ hb) (h j) := fun j t => by
    subst hA
    exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hgg : ∀ i, X.toLocallyRingedSpace.𝒪.presheaf.germ U b (hVU hb) (g i) =
      -X.toLocallyRingedSpace.𝒪.presheaf.germ U₂ b (hVU₂ hb) (f i) := fun i => by
    subst hg
    rw [map_neg, TopCat.Presheaf.germ_res_apply]
  -- the relations of the augmented matrix at `b`, in components
  have hrel : ∀ v : Fin (1 + l * m) → X.toLocallyRingedSpace.𝒪.presheaf.stalk b,
      v ∈ relationSubmodule X.toLocallyRingedSpace.𝒪 (augMat A g) b (hVU hb) ↔ ∀ j,
        X.toLocallyRingedSpace.𝒪.presheaf.germ U₁ b (hVU₁ hb) (h j) * v (augCol 1 l m (Sum.inl 0)) -
          ∑ i, X.toLocallyRingedSpace.𝒪.presheaf.germ U₂ b (hVU₂ hb) (f i) *
            v (augCol 1 l m (Sum.inr (j, i))) = 0 := by
    intro v
    rw [mem_relationSubmodule_iff]
    refine forall_congr' fun j => ?_
    rw [sum_map_augMat_mul (X.toLocallyRingedSpace.𝒪.presheaf.germ U b (hVU hb)).hom A g v j,
      Fin.sum_univ_one, hgA]
    simp only [hgg, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  have hRw : relationSubmodule X.toLocallyRingedSpace.𝒪 (augMat A g) b (hVU hb) =
      Submodule.span _ (Set.range fun n c =>
        X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb (R n c)) := hR b hb
  -- the colon at `b`, in components
  ext r
  dsimp only
  rw [hh b (hVU₁ hb), hf b (hVU₂ hb), Ideal.colon_span, Submodule.mem_colon,
    Ideal.mem_span_range_iff_exists_fun]
  constructor
  · intro hr
    have hc : ∀ j, ∃ c : Fin m → X.toLocallyRingedSpace.𝒪.presheaf.stalk b,
        ∑ i, c i * X.toLocallyRingedSpace.𝒪.presheaf.germ U₂ b (hVU₂ hb) (f i) =
          X.toLocallyRingedSpace.𝒪.presheaf.germ U₁ b (hVU₁ hb) (h j) * r := fun j => by
      have := hr _ ⟨j, rfl⟩
      rw [smul_eq_mul, Ideal.mem_span_range_iff_exists_fun] at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by rw [hc, mul_comm]⟩
    choose c hc using hc
    have hv : augVec (fun _ : Fin 1 => r) c ∈
        relationSubmodule X.toLocallyRingedSpace.𝒪 (augMat A g) b (hVU hb) := by
      rw [hrel]
      intro j
      simp only [augVec_inl, augVec_inr]
      rw [sub_eq_zero, ← hc j]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hRw, Submodule.mem_span_range_iff_exists_fun] at hv
    obtain ⟨lam, hlam⟩ := hv
    refine ⟨lam, ?_⟩
    have := congrFun hlam (augCol 1 l m (Sum.inl 0))
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, augVec_inl] using this
  · rintro ⟨lam, rfl⟩ s ⟨j, rfl⟩
    rw [smul_eq_mul, Finset.sum_mul]
    refine Ideal.sum_mem _ fun n _ => ?_
    rw [mul_assoc]
    refine Ideal.mul_mem_left _ _ ?_
    have hRn : (fun x => X.toLocallyRingedSpace.𝒪.presheaf.germ V b hb (R n x)) ∈
        relationSubmodule X.toLocallyRingedSpace.𝒪 (augMat A g) b (hVU hb) := by
      rw [hRw]
      exact Submodule.subset_span ⟨n, rfl⟩
    rw [hrel] at hRn
    have h1 := sub_eq_zero.mp (hRn j)
    rw [mul_comm, h1]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

end AnalyticSpace
