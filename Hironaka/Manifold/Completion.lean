/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Hironaka.Manifold.IdealSheaf.Defs
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Algebra.Local.CompletionCoords
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.IdealSheaf.Order
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The completion map of the analytic stalk is injective

Bierstone–Milman's first condition on the local rings of their category of spaces
[BM97, (0.1)(1)]: "the natural homomorphism `𝒪_{X,a} → 𝒪̂_{X,a}` into the completion is
injective"; and Krull's intersection theorem in the geometric form Kollár uses
[Kol07, Definition 55]: "if `Ẑ_x = Ŵ_x` then `Z ∩ U = W ∩ U`" on a neighbourhood `U` of `x`.

* `⋂_k 𝔪_a^k = 0` in the analytic stalk `𝒪_{M,a}` (`iInf_maximalIdeal_pow_eq_bot`): a germ in every
  `𝔪_a^k` has Taylor series in every `(X)^k` (`IsTaylorHom.mem_maximalIdeal_pow_iff`), hence of
  infinite order, hence zero, hence the germ is zero (`IsTaylorHom.injective'`); so the stalk is
  `𝔪_a`-adically Hausdorff (`isHausdorff_stalk`) and the completion map is injective
  (`injective_algebraMap_adicCompletion`, Mathlib's `AdicCompletion.of_injective`).
* Ideals of a Noetherian local ring with the same extension to the completion are equal
  (`Ideal.eq_of_map_adicCompletion_eq`: Krull, in the form `I R̂ ∩ R = I`), and two locally finitely
  generated ideal sheaves with equal stalks at `a` have equal stalks near `a`
  (`IdealSheaf.exists_opens_forall_stalkIdeal_eq`): the generators of one near `a` are combinations
  of the generators of the other at `a`, hence, as sections, on a neighbourhood
  (`TopCat.Presheaf.germ_eq`). The propagation is stated for ideal sheaves over any sheaf of
  commutative rings; the geometric form for the analytic stalk
  (`exists_opens_forall_stalkIdeal_eq_of_map_adicCompletion_eq`) carries Kollár's Noetherian
  hypothesis explicitly (the Noetherian instance for the analytic stalk is
  `Hironaka/Manifold/Germ/StalkNoetherian.lean`).

These results compare ideal sheaves through their completions; they are used in the
maximal-contact arguments (`Hironaka/Manifold/MaximalContact/`).
-/

public section

open TopologicalSpace Opposite CategoryTheory Filter IsLocalRing
open scoped Manifold ContDiff Topology
open IsManifold (maximalAtlas)

namespace Manifold

universe u

/-! ### Krull's intersection theorem in a chart -/

section Taylor

variable {𝕜 : Type} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (φ : OpenPartialHomeomorph M E) {a : M} (ha : a ∈ φ.source)
  (hφ : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M)

include ha hφ in
/-- In a chart: `⋂_k 𝔪_a^k = 0` — a germ in every `𝔪_a^k` has Taylor series in every `(X)^k`,
hence zero Taylor series, hence is zero (the Taylor homomorphism is injective). -/
theorem IsTaylorHom.iInf_maximalIdeal_pow_eq_bot
    {T : (structureSheaf 𝕜 E M).presheaf.stalk a →+* MvPowerSeries (Fin n) 𝕜}
    (hT : IsTaylorHom E ψ φ a T) :
    ⨅ k : ℕ, maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k = ⊥ := by
  refine eq_bot_iff.mpr fun s hs => ?_
  rw [Ideal.mem_iInf] at hs
  have hk : ∀ k : ℕ, (k : ℕ∞) ≤ (T s).order := fun k => by
    have := (hT.mem_maximalIdeal_pow_iff E ψ φ ha hφ s k).mpr (hs k)
    rwa [MvPowerSeries.maximalIdeal_eq_span_range_X,
      MvPowerSeries.mem_span_range_X_pow_iff_le_order] at this
  have hT0 : T s = 0 := MvPowerSeries.order_eq_top_iff.mp (ENat.eq_top_iff_forall_ge.mpr hk)
  exact Ideal.mem_bot.mpr (IsTaylorHom.injective' E ψ φ ha hT (hT0.trans (map_zero T).symm))

end Taylor

/-! ### Krull's intersection theorem for the stalk -/

section Stalk

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] (a : M)

/-- Krull's intersection theorem for the analytic stalk, `⋂_k 𝔪_a^k = 0`, through the Taylor
homomorphism of the chart at `a` ([BM97, (0.1)(1)]; [Kol07, Definition 55]). -/
theorem iInf_maximalIdeal_pow_eq_bot :
    ⨅ k : ℕ, maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k = ⊥ :=
  IsTaylorHom.iInf_maximalIdeal_pow_eq_bot E (IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E))
    (chartAt E a) (mem_chart_source E a)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) a)
    (isTaylorHom_taylorHom E (IdealSheaf.modelCoord (𝕜 := 𝕜) (E := E)) (chartAt E a)
      (mem_chart_source E a) (IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, E)) (n := ω) a))

/-- The analytic stalk is `𝔪_a`-adically Hausdorff. -/
theorem isHausdorff_stalk :
    IsHausdorff (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
      ((structureSheaf 𝕜 E M).presheaf.stalk a) := by
  refine ⟨fun x hx => ?_⟩
  have h : x ∈ ⨅ k : ℕ, maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a) ^ k := by
    rw [Ideal.mem_iInf]
    intro k
    have := SModEq.zero.mp (hx k)
    rwa [Ideal.smul_eq_mul, Ideal.mul_top] at this
  rw [iInf_maximalIdeal_pow_eq_bot (𝕜 := 𝕜) (E := E) a] at h
  exact Ideal.mem_bot.mp h

/-- Bierstone–Milman's condition (0.1)(1) [BM97, (0.1)]: the completion map `𝒪_{M,a} → 𝒪̂_{M,a}`
is injective. -/
theorem injective_algebraMap_adicCompletion :
    Function.Injective (algebraMap ((structureSheaf 𝕜 E M).presheaf.stalk a)
      (AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
        ((structureSheaf 𝕜 E M).presheaf.stalk a))) := by
  have := isHausdorff_stalk (𝕜 := 𝕜) (E := E) a
  intro x y hxy
  refine AdicCompletion.of_injective (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
    ((structureSheaf 𝕜 E M).presheaf.stalk a) ?_
  simpa [AdicCompletion.algebraMap_apply] using hxy

end Stalk

/-! ### Krull's theorem for ideals of a Noetherian local ring -/

/-- Krull's intersection theorem `I = ⋂_s (I + 𝔪^s)` [Kol07, Definition 55] in the form
`I R̂ ∩ R = I`: ideals of a Noetherian local ring with the same extension to the completion are
equal. -/
theorem _root_.Ideal.eq_of_map_adicCompletion_eq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {I J : Ideal R}
    (h : I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
      J.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) : I = J :=
  calc I = (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comap
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
        (comap_map_adicCompletion I).symm
    _ = (J.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).comap
        (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by rw [h]
    _ = J := comap_map_adicCompletion J

/-! ### Equal stalks propagate to a neighbourhood -/

section IdealSheaf

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} X}

/-- One inclusion: if the stalk of `J` at `a` lies in that of `I`, the generators of `J` near `a`
are combinations of the generators of `I` at `a`, hence on a neighbourhood, so `J_b ⊆ I_b` for `b`
near `a`. -/
theorem IdealSheaf.eventually_stalkIdeal_le {I J : IdealSheaf 𝒪} {a : X}
    (h : J.stalkIdeal a ≤ I.stalkIdeal a) : ∀ᶠ b in 𝓝 a, J.stalkIdeal b ≤ I.stalkIdeal b := by
  classical
  obtain ⟨U, haU, k, f, hfI, hfgen⟩ := I.exists_generators a
  obtain ⟨V, haV, l, g, hgJ, hggen⟩ := J.exists_generators a
  have key : ∀ j : Fin l, ∀ᶠ b in 𝓝 a,
      ∀ hb : b ∈ V, 𝒪.presheaf.germ V b hb (g j) ∈ I.stalkIdeal b := by
    intro j
    have hj : 𝒪.presheaf.germ V a haV (g j) ∈
        Ideal.span (Set.range fun i => 𝒪.presheaf.germ U a haU (f i)) := by
      rw [← hfgen a haU]
      exact h (J.germ_mem_stalkIdeal haV (hgJ j))
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hj
    choose W hW cs hcs using fun i => 𝒪.presheaf.exists_germ_eq (c i)
    -- the common open `W₀ ∋ a` on which the coefficients, the `fᵢ` and the `gⱼ` all live
    let W₀ : Opens X := ⟨(⋂ i, (W i : Set X)) ∩ U ∩ V,
      ((isOpen_iInter_of_finite fun i => (W i).2).inter U.2).inter V.2⟩
    have haW₀ : a ∈ W₀ := ⟨⟨Set.mem_iInter.mpr hW, haU⟩, haV⟩
    have hW₀W : ∀ i, W₀ ≤ W i := fun i x hx => Set.mem_iInter.mp hx.1.1 i
    have hW₀U : W₀ ≤ U := fun x hx => hx.1.2
    have hW₀V : W₀ ≤ V := fun x hx => hx.2
    -- the section `t = ∑ cᵢ fᵢ` on `W₀` has the germ of `gⱼ` at `a`
    let t : 𝒪.presheaf.obj (op W₀) := ∑ i, 𝒪.presheaf.map (homOfLE (hW₀W i)).op (cs i) *
      𝒪.presheaf.map (homOfLE hW₀U).op (f i)
    have ht : 𝒪.presheaf.germ W₀ a haW₀ t =
        𝒪.presheaf.germ W₀ a haW₀ (𝒪.presheaf.map (homOfLE hW₀V).op (g j)) := by
      simp only [t, map_sum, map_mul, TopCat.Presheaf.germ_res_apply, hcs]
      exact hc
    obtain ⟨W', haW', iW', iW'', hW'⟩ := 𝒪.presheaf.germ_eq a haW₀ haW₀ _ _ ht
    refine Filter.eventually_of_mem (W'.2.mem_nhds haW') fun b hb hbV => ?_
    have hbW₀ : b ∈ W₀ := iW'.le hb
    have e1 : 𝒪.presheaf.germ V b hbV (g j) = 𝒪.presheaf.germ W' b hb
        (𝒪.presheaf.map iW''.op (𝒪.presheaf.map (homOfLE hW₀V).op (g j))) := by
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [e1, ← hW', TopCat.Presheaf.germ_res_apply]
    simp only [t, map_sum, map_mul, TopCat.Presheaf.germ_res_apply]
    exact Ideal.sum_mem _ fun i _ =>
      Ideal.mul_mem_left _ _ (I.germ_mem_stalkIdeal (hW₀U hbW₀) (hfI i))
  filter_upwards [V.2.mem_nhds haV, Filter.eventually_all.mpr key] with b hbV hb
  rw [hggen b hbV, Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  exact hb j hbV

/-- Two locally finitely generated ideal sheaves with equal stalks at `a` have equal stalks near
`a` (filter form). -/
theorem IdealSheaf.eventuallyEq_stalkIdeal_of_eq {I J : IdealSheaf 𝒪} {a : X}
    (h : I.stalkIdeal a = J.stalkIdeal a) : ∀ᶠ b in 𝓝 a, I.stalkIdeal b = J.stalkIdeal b := by
  filter_upwards [IdealSheaf.eventually_stalkIdeal_le h.le,
    IdealSheaf.eventually_stalkIdeal_le h.ge] with b h1 h2
  exact le_antisymm h1 h2

/-- Two locally finitely generated ideal sheaves with equal stalks at `a` agree on an open
neighbourhood of `a`. -/
theorem IdealSheaf.exists_opens_forall_stalkIdeal_eq {I J : IdealSheaf 𝒪} {a : X}
    (h : I.stalkIdeal a = J.stalkIdeal a) :
    ∃ U : Opens X, a ∈ U ∧ ∀ b ∈ U, I.stalkIdeal b = J.stalkIdeal b := by
  obtain ⟨t, hts, hto, hat⟩ := mem_nhds_iff.mp (IdealSheaf.eventuallyEq_stalkIdeal_of_eq h)
  exact ⟨⟨t, hto⟩, hat, fun b hb => hts hb⟩

end IdealSheaf

/-! ### The geometric form of Krull's theorem -/

section Geometric

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  (I J : IdealSheaf (structureSheaf 𝕜 E M)) (a : M)

/-- Kollár's geometric form of Krull's intersection theorem [Kol07, Definition 55], "if
`Ẑ_x = Ŵ_x` then `Z ∩ U = W ∩ U`": two locally finitely generated ideal sheaves with equal
completions at `a` agree on a neighbourhood of `a`, for `𝒪_{M,a}` Noetherian — Kollár's hypothesis,
carried explicitly (the instance for the analytic stalk is proved in
`Hironaka/Manifold/Germ/StalkNoetherian.lean`). -/
theorem exists_opens_forall_stalkIdeal_eq_of_map_adicCompletion_eq
    [IsNoetherianRing ((structureSheaf 𝕜 E M).presheaf.stalk a)]
    (h : (I.stalkIdeal a).map (algebraMap ((structureSheaf 𝕜 E M).presheaf.stalk a)
        (AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
          ((structureSheaf 𝕜 E M).presheaf.stalk a))) =
      (J.stalkIdeal a).map (algebraMap ((structureSheaf 𝕜 E M).presheaf.stalk a)
        (AdicCompletion (maximalIdeal ((structureSheaf 𝕜 E M).presheaf.stalk a))
          ((structureSheaf 𝕜 E M).presheaf.stalk a)))) :
    ∃ U : Opens M, a ∈ U ∧ ∀ b ∈ U, I.stalkIdeal b = J.stalkIdeal b :=
  IdealSheaf.exists_opens_forall_stalkIdeal_eq (Ideal.eq_of_map_adicCompletion_eq h)

end Geometric

end Manifold
