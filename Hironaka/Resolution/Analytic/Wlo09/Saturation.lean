/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Resolution.Defs
public import Hironaka.AnalyticSpace.Noether.Saturation
public import Hironaka.AnalyticSpace.Manifold.Defs
import Hironaka.Algebra.Local.Regular
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.Ideal
import Hironaka.Resolution.Analytic.MaximalContact.OneStepDescentLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The strict transform as the saturation of the total transform

Włodarczyk's strict transform `Ỹ ⊂ M̃` [Wlo09, Theorem 2.0.2] is defined here on the glued space
`M̃` as the saturation of the total transform `σ^*(I_Y)` by the exceptional divisor `E`
(`IdealSheaf.saturation`: the ideal sheaf whose stalk at `q` is `⋃_k (σ^*(I_Y)_q : E_q^k)`, coherent
by the finite type of saturations, [BM97, Proposition 3.13],
`AnalyticSpace.saturation_hasLocalGenerators`). The library's strict transform along a succession
is built stage by stage; this module shows that at the last stage of a succession
desingularizing `Y` (`IdealSheaf.IsDesingularizedBy`) it is the saturation of the total transform
along the composite by the last exceptional divisor
(`IsDesingularizedBy.stalkIdeal_strictTransformSubspaceSeq_last_eq_iSup_colon`), from the clauses
(3) and (6) alone: with `J` the stalk of `Ỹ`, `e` a generator of the stalk of `E_r` and
`σ^*(I_Y) = J · m` with `m` a monomial in the members of `E_r` through the point (clause (6)),
`m` divides a power of `e`, so `J ⊆ (J m : e^∞)`; and `J` is prime (the quotient is a regular local
ring by (3), hence a domain) with `e ∉ J`: `e` is a product of coordinates of a chart adapted to
`Ỹ` off the block of `Ỹ` (the transversality of (3)), and such a coordinate does not vanish on
`Ỹ` near the point (`coord_notMem_vanishingStalk_of_notMem_range`), while every element of `J`
does. Not in the sources beyond the statements cited; the saturation description of the strict
transform is [BM97, Proposition 3.13].
-/

public section

noncomputable section

open Set Topology TopologicalSpace Filter Opposite Manifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- A coordinate of a chart adapted to `Y` off the block of `Y` does not vanish on `Y` near a
point `a` of `Y`: along the curve `t ↦ φ⁻¹(φ(a) + t e_k)`, which lies in `Y` and tends to `a`,
the coordinate is `z_k(a) + t`. -/
theorem coord_notMem_vanishingStalk_of_notMem_range {Y : Set M} {φ : OpenPartialHomeomorph M E}
    {c : ℕ} {σ : Fin c ↪ Fin n} (hφ : IsAdaptedChart ψ Y φ σ) {a : M} (ha : a ∈ φ.source)
    (haY : a ∈ Y) {k : Fin n} (hk : k ∉ Set.range σ) :
    coord E ψ φ hφ.1 ha k ∉ vanishingStalk (𝕜 := 𝕜) (E := E) Y a := by
  intro hmem
  by_cases hk0 : ψ (φ a) k = 0
  · -- the curve in `Y` through `a` along which the coordinate is `t`
    set v : 𝕜 → E := fun t => ψ.symm (ψ (φ a) + Pi.single k t) with hv
    have hv0 : v 0 = φ a := by
      simp only [hv, Pi.single_zero, add_zero, ContinuousLinearEquiv.symm_apply_apply]
    have hvt : Tendsto v (𝓝 0) (𝓝 (φ a)) := by
      rw [← hv0]
      exact (ψ.symm.continuous.tendsto _).comp
        ((continuous_const.add (continuous_single k)).tendsto 0)
    have htgt : ∀ᶠ t in 𝓝 (0 : 𝕜), v t ∈ φ.target :=
      hvt.eventually (φ.open_target.mem_nhds (φ.map_source ha))
    have hcoord : ∀ t, v t ∈ φ.target → ∀ i,
        ψ (φ (φ.symm (v t))) i = ψ (φ a) i + (Pi.single k t : Fin n → 𝕜) i :=
      fun t ht i => by
        rw [φ.right_inv ht]
        simp only [hv, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply]
    have hmemY : ∀ t, v t ∈ φ.target → φ.symm (v t) ∈ Y := fun t ht => by
      refine (hφ.2 _ (φ.map_target ht)).mpr fun i => ?_
      rw [hcoord t ht, (hφ.2 a ha).mp haY i, Pi.single_eq_of_ne (fun h => hk ⟨i, h⟩), add_zero]
    have hya : Tendsto (fun t => φ.symm (v t)) (𝓝[≠] 0) (𝓝[Y] a) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have := ((φ.continuousAt_symm (φ.map_source ha)).tendsto.comp hvt).mono_left
          (nhdsWithin_le_nhds (s := {(0 : 𝕜)}ᶜ))
        rwa [φ.left_inv ha] at this
      · exact (htgt.filter_mono (nhdsWithin_le_nhds (s := {(0 : 𝕜)}ᶜ))).mono fun t ht => hmemY t ht
    rw [mem_vanishingStalk_iff, stalkToGerm_coord, Germ.vanishesOn_coe] at hmem
    have h1 := (hya.eventually hmem).and
      ((htgt.filter_mono (nhdsWithin_le_nhds (s := {(0 : 𝕜)}ᶜ))).and self_mem_nhdsWithin)
    obtain ⟨t, h2, h3, h4⟩ := h1.exists
    rw [extendSection_of_mem 𝕜 E _ (φ.map_target h3)] at h2
    change ψ (φ (φ.symm (v t))) k = 0 at h2
    rw [hcoord t h3, hk0, Pi.single_eq_same, zero_add] at h2
    exact h4 h2
  · -- the coordinate is a unit at `a`, and a germ vanishing on `Y` lies in the maximal ideal
    have hle : vanishingStalk (𝕜 := 𝕜) (E := E) Y a ≤ IsLocalRing.maximalIdeal _ :=
      IsLocalRing.le_maximalIdeal (vanishingStalk_ne_top_of_mem_closure (subset_closure haY))
    have := hle hmem
    rw [mem_maximalIdeal_iff_eval, eval_coord] at this
    exact hk0 this

end Manifold

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The two inclusions of the saturation identity, in a commutative ring: if `T = J m` and `B = (e)`
with `e^N ∈ m`, then `J ⊆ ⋃_k (T : B^k)`. -/
theorem le_iSup_colon_pow_of_pow_mem {J T B m : Ideal R} {e : R} (hT : T = J * m)
    (hB : B = Ideal.span {e}) {N : ℕ} (hpow : e ^ N ∈ m) :
    J ≤ ⨆ k : ℕ, Submodule.colon T (SetLike.coe (B ^ k)) := by
  refine le_iSup_of_le N fun g hg => ?_
  rw [Submodule.mem_colon]
  intro r hr
  rw [hB, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hr
  obtain ⟨t, rfl⟩ := hr
  rw [hT, smul_eq_mul]
  exact Ideal.mul_mem_mul hg (Ideal.mul_mem_left _ t hpow)

/-- If moreover `J` is prime and `e ∉ J`, then `⋃_k (T : B^k) ⊆ J`. -/
theorem iSup_colon_pow_le_of_isPrime {J T B m : Ideal R} {e : R} (hT : T = J * m)
    (hB : B = Ideal.span {e}) (hne : e ∉ J) (hJ : J.IsPrime) :
    (⨆ k : ℕ, Submodule.colon T (SetLike.coe (B ^ k))) ≤ J := by
  refine iSup_le fun k g hg => ?_
  have h1 : e ^ k ∈ (SetLike.coe (B ^ k) : Set R) := by
    rw [hB, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have h2 : g * e ^ k ∈ J := by
    have h3 := Submodule.mem_colon.mp hg _ h1
    rw [hT, smul_eq_mul] at h3
    exact (Ideal.mul_le_left : J * m ≤ J) h3
  rcases hJ.mem_or_mem h2 with hgJ | hek
  · exact hgJ
  · exact absurd (hJ.mem_of_pow_mem k hek) hne

end Ideal

namespace AnalyticManifold.IdealSheaf

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

/-- The saturation stalks `⋃_k (J_x : B_x^k)` of an ideal sheaf `J` by an ideal sheaf `B` have
local generators: Bierstone–Milman's finite type of saturations [BM97, Proposition 3.13]
(`AnalyticSpace.saturation_hasLocalGenerators`, read on the analytic space of `M`). -/
theorem hasLocalGenerators_saturation (J B : IdealSheaf M) :
    Manifold.IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M) fun x =>
      ⨆ k : ℕ, Submodule.colon (J.stalkIdeal x) (SetLike.coe (B.stalkIdeal x ^ k)) :=
  AnalyticSpace.saturation_hasLocalGenerators
    (AnalyticSpace.toSpace
      (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun 𝕜).symm : E ≃L[𝕜] _) M) J B

/-- **The saturation of `J` by `B`**: the ideal sheaf whose stalk at `x` is
`⋃_k (J_x : B_x^k)`, the germs `g` with `b g ∈ J_x` for some `b ∈ B_x^k`. For `J = σ^*(I_Y)` and
`B` the exceptional divisor it is the strict transform of `Y` [BM97, Proposition 3.13]. -/
def saturation (J B : IdealSheaf M) : IdealSheaf M :=
  Manifold.IdealSheaf.ofStalks _ _ (hasLocalGenerators_saturation J B)

@[simp]
theorem stalkIdeal_saturation (J B : IdealSheaf M) (x : M) :
    (J.saturation B).stalkIdeal x =
      ⨆ k : ℕ, Submodule.colon (J.stalkIdeal x) (SetLike.coe (B.stalkIdeal x ^ k)) := by
  unfold saturation
  exact Manifold.IdealSheaf.stalkIdeal_ofStalks (𝒪 := structureSheaf 𝕜 E M) _
    (hasLocalGenerators_saturation J B) x

/-- The saturation pulls back along a local analytic isomorphism to the saturation of the
pull-backs: the colon ideals and their union transport along the bijective germ maps
(`Ideal.map_colon_pow_of_bijective`, `Ideal.map_iSup`). -/
theorem saturation_pullback {N : AnalyticManifold.{u} 𝕜 E} (J B : IdealSheaf M)
    (g : AnalyticMap N M) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    (J.saturation B).pullback g g.contMDiff =
      saturation (J.pullback g g.contMDiff) (B.pullback g g.contMDiff) := by
  refine Manifold.IdealSheaf.ext fun x => ?_
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, stalkIdeal_saturation, stalkIdeal_saturation,
    Ideal.map_iSup]
  refine iSup_congr fun k => ?_
  rw [Ideal.map_colon_pow_of_bijective _ (germMap_bijective_of_isLocalDiffeomorphAt g g.contMDiff
    (hg x)), Manifold.IdealSheaf.stalkIdeal_pullback, Manifold.IdealSheaf.stalkIdeal_pullback]

omit [FiniteDimensional 𝕜 E] in
/-- **The last strict transform is the saturation of the total transform by the last exceptional
divisor**, at every point, for a succession desingularizing `Y`: from clauses (3) and (6) of
[Wlo09, Theorem 2.0.2] (`isNonsingular_strictTransform`,
`isSncBoundaryTransversalTo_strictTransform`, `isMulBoundaryMonomial_pullback`). -/
theorem IsDesingularizedBy.stalkIdeal_strictTransformSubspaceSeq_last_eq_iSup_colon
    {I : IdealSheaf M} {S : FiniteSuccession M} (h : I.IsDesingularizedBy S) (a : S.last) :
    (S.strictTransformSubspaceSeq I (Fin.last _)).stalkIdeal a =
      ⨆ k : ℕ, Submodule.colon ((I.pullback S.composite S.composite.contMDiff).stalkIdeal a)
        (SetLike.coe ((S.boundarySeq ⊤ (Fin.last _)).stalkIdeal a ^ k)) := by
  set J := S.strictTransformSubspaceSeq I (Fin.last _) with hJ
  set Er := S.boundarySeq ⊤ (Fin.last _) with hEr
  set T := I.pullback S.composite S.composite.contMDiff with hT
  obtain ⟨n, ψ, G, hG, hGE, hpt⟩ := h.isMulBoundaryMonomial_pullback
  obtain ⟨s, α, hs, hmon⟩ := hpt a
  -- (⊇) for any generator `e` of the stalk of `E_r`: `e` vanishes on every member of `G` through
  -- `a`, so the monomial contains a power of `e`
  have hsup : ∀ e, Er.stalkIdeal a = Ideal.span {e} →
      J.stalkIdeal a ≤ ⨆ k : ℕ, Submodule.colon (T.stalkIdeal a)
        (SetLike.coe (Er.stalkIdeal a ^ k)) := by
    intro e he
    have he_mem : ∀ j, a ∈ G.hyp j → e ∈ vanishingStalk (𝕜 := 𝕜) (E := E) (G.hyp j) a := by
      intro j hj
      have : e ∈ vanishingStalk (𝕜 := 𝕜) (E := E) G.support a := by
        rw [← hG.stalkIdeal_idealSheaf, hGE, he]
        exact Ideal.mem_span_singleton_self e
      exact vanishingStalk_anti (Set.subset_iUnion G.hyp j) a this
    have hpow : e ^ (∑ j ∈ s, α j) ∈
        ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E) (G.hyp j) a ^ α j := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod fun j hj => Ideal.pow_mem_pow (he_mem j (hs j hj)) _
    exact Ideal.le_iSup_colon_pow_of_pow_mem hmon he hpow
  by_cases ha : a ∈ J.support
  · -- `J` is prime, and the generator of `E_r` from a chart adapted to `Ỹ` is not in `J`
    obtain ⟨n', ψ', G', hG', hG'E, hpt'⟩ := h.isSncBoundaryTransversalTo_strictTransform
    obtain ⟨c, φ', σ, cidx', hadapt, hsnc', hdisj⟩ := hpt' a ha
    have he' := hG'.stalkIdeal_idealSheaf_eq_span_prod hsnc'
    rw [hG'E] at he'
    have hreg : IsRegularLocalRing (stalkRing S.last a ⧸ J.stalkIdeal a) :=
      h.isNonsingular_strictTransform a ha
    have hdom : IsDomain (stalkRing S.last a ⧸ J.stalkIdeal a) :=
      IsLocalRing.instIsDomainOfIsRegularLocalRing _
    have hprime : (J.stalkIdeal a).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    have hne : (∏ j ∈ (hG'.2.1.point_finite a).toFinset.attach,
        coord E ψ' φ' hsnc'.1 hsnc'.2.1
          (cidx' ⟨j.1, (hG'.2.1.point_finite a).mem_toFinset.mp j.2⟩)) ∉ J.stalkIdeal a := by
      intro hmem
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hprime)).mp hmem
      have hvan :=
        Hironaka.Manifold.stalkIdeal_le_vanishingStalk_of_subset_cosupport J subset_rfl a hj
      exact coord_notMem_vanishingStalk_of_notMem_range hadapt hsnc'.2.1 ha
        (hdisj ⟨j.1, (hG'.2.1.point_finite a).mem_toFinset.mp j.2⟩) hvan
    exact le_antisymm (hsup _ he') (Ideal.iSup_colon_pow_le_of_isPrime hmon he' hne hprime)
  · -- `J` is the unit ideal at `a`
    have htop : J.stalkIdeal a = ⊤ := by
      by_contra hne
      exact ha hne
    obtain ⟨φ, cidx, hc⟩ := hG.2.2 a
    have he := hG.stalkIdeal_idealSheaf_eq_span_prod hc
    rw [hGE] at he
    refine le_antisymm (hsup _ he) ?_
    rw [htop]
    exact le_top

/-- The last strict transform of a succession desingularizing `Y` is the saturation of the total
transform of `I_Y` along the composite by the last exceptional divisor. -/
theorem IsDesingularizedBy.strictTransformSubspaceSeq_last_eq_saturation {I : IdealSheaf M}
    {S : FiniteSuccession M} (h : I.IsDesingularizedBy S) :
    S.strictTransformSubspaceSeq I (Fin.last _) =
      saturation (I.pullback S.composite S.composite.contMDiff) (S.boundarySeq ⊤ (Fin.last _)) :=
  Manifold.IdealSheaf.ext fun a => by
    rw [stalkIdeal_saturation, h.stalkIdeal_strictTransformSubspaceSeq_last_eq_iSup_colon a]

end AnalyticManifold.IdealSheaf

end

end
