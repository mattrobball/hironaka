/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.LimitFamily
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The glued blow-down of a compatible family: the isomorphism off `Z` and normal crossings

The blow-down `σ = C.limitBlowDown Kex hemb hcomp : M̃ → M` of a compatible family's direct limit
(`Hironaka.Resolution.Analytic.Functor.LimitFamily`) is glued from the composite blow-downs
`Π^{(m)} : M'_m → M_m` of the pieces over the members `M_m = relCompactOpen Kex m` of the
exhaustion. Two pointwise properties of the compatible families of the main theorems glue, for
any `C : CompatibleFamily T`:

* `CompatibleFamily.isAnalyticIsoOver_limitBlowDown` ([Kol07, Theorem 35, (3)];
  [Wlo09, Lemma 4.0.3]): if every piece's composite blow-down is an analytic isomorphism off the
  trace of `Z`, then `σ` is an analytic isomorphism off `Z`: a local diffeomorphism at every point
  of `σ⁻¹(Zᶜ)` through the piece containing it (`σ ∘ toLimit m` is the piece's blow-down,
  `toLimit m` a local diffeomorphism, `IsLocalDiffeomorphAt.of_comp_left`), injective on `σ⁻¹(Zᶜ)`
  because two points with the same image lie in a common piece (`exists_common_toLimit`), where
  the piece's bijection decides, and onto `Zᶜ` because every point of `M` lies in some `M_m`
  (`iUnion_relCompactOpen`).
* `CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown` ([Kol07, Theorem 35, (2)];
  [Wlo09, Theorem 2.0.3, (3)]): if over every `M_m` the pull-back of `J|_{M_m}` along the piece's
  composite blow-down is a normal-crossings divisor, so is `J.comap σ`: the condition is
  pointwise, and at `toLimit m y` the stalk of `J.comap σ` is carried by the germ isomorphism of
  the open embedding `toLimitMap m` onto the stalk at `y` of the piece's pull-back
  (`IdealSheaf.pullback_comp`, `limitDesc_comp_toLimitMap`,
  `exists_monomial_of_comap_of_isLocalDiffeomorphAt`).

Two general lemmas carry the transport: `IsLocalDiffeomorphAt.of_comp_left` (if `g ∘ f` and `f`
are local diffeomorphisms at `x`, so is `g` at `f x`, through Mathlib's `localInverse`) and
`exists_monomial_of_comap_of_isLocalDiffeomorphAt` (the pointwise normal-crossings condition
descends along a local diffeomorphism at the point: the germ map is a ring isomorphism of the
stalks, `germMap_bijective_of_isLocalDiffeomorphAt`, carrying a regular system of parameters onto
one and the Krull dimension along, `stalkIdeal_comap_eq_map_germMap`).
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section LocalDiffeo

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {H₃ : Type*} [TopologicalSpace H₃]
  {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂} {K : ModelWithCorners 𝕜 F' H₃}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H₃ P] {n : WithTop ℕ∞}

/-- If `g ∘ f` and `f` are local diffeomorphisms at `x`, then `g` is one at `f x`: the local inverse
of `f` followed by the local diffeomorphism of `g ∘ f` (the general form behind the
gluing of `σ ∘ toLimit m = Π^{(m)}`). -/
theorem IsLocalDiffeomorphAt.of_comp_left {f : M → N} {g : N → P} {x : M}
    (hgf : IsLocalDiffeomorphAt I K n (g ∘ f) x) (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt J K n g (f x) := by
  obtain ⟨Φ, hxΦ, hΦ⟩ := hgf.exists_partialDiffeomorph
  refine IsLocalDiffeomorphAt.of_eqOn (hf.localInverse.trans Φ) ⟨hf.localInverse_mem_source, ?_⟩ ?_
  · change hf.localInverse (f x) ∈ Φ.source
    rw [hf.localInverse_left_inv hf.localInverse_mem_target]
    exact hxΦ
  · rintro y ⟨hyl, hyr⟩
    have h1 : f (hf.localInverse y) = y := hf.localInverse_right_inv hyl
    have h2 : (g ∘ f) (hf.localInverse y) = Φ (hf.localInverse y) := hΦ hyr
    calc g y = (g ∘ f) (hf.localInverse y) := by rw [Function.comp_apply, h1]
      _ = Φ (hf.localInverse y) := h2
      _ = (hf.localInverse.trans Φ) y := rfl

end LocalDiffeo

section Transport

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M N : AnalyticManifold.{u} 𝕜 E}

/-- The pointwise normal-crossings condition (record predicate at one point) descends
along a local diffeomorphism at the point (gluing): the germ map is a
ring isomorphism of the stalks carrying the stalk of the pull-back onto the stalk of `J`
(`stalkIdeal_comap_eq_map_germMap`), a regular system of parameters onto one (the image of the
maximal ideal is the maximal ideal), and the Krull dimensions agree. -/
theorem exists_monomial_of_comap_of_isLocalDiffeomorphAt (h : AnalyticMap N M)
    (J : AnalyticManifold.IdealSheaf M) {a : N}
        (hh : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω h a)
    (H : ∃ (k : ℕ) (z : Fin k → AnalyticManifold.IdealSheaf.stalkRing N a) (α : Fin k → ℕ),
      (Ideal.span (Set.range z) =
          IsLocalRing.maximalIdeal (AnalyticManifold.IdealSheaf.stalkRing N a) ∧
        (k : WithBot ℕ∞) = ringKrullDim (AnalyticManifold.IdealSheaf.stalkRing N a)) ∧
      (J.pullback h h.contMDiff).stalkIdeal a = Ideal.span {∏ i, z i ^ α i}) :
    ∃ (k : ℕ) (z : Fin k → AnalyticManifold.IdealSheaf.stalkRing M (h a)) (α : Fin k → ℕ),
      (Ideal.span (Set.range z) =
          IsLocalRing.maximalIdeal (AnalyticManifold.IdealSheaf.stalkRing M (h a)) ∧
        (k : WithBot ℕ∞) = ringKrullDim (AnalyticManifold.IdealSheaf.stalkRing M (h a))) ∧
      J.stalkIdeal (h a) = Ideal.span {∏ i, z i ^ α i} := by
  obtain ⟨k, z, α, ⟨hz, hk⟩, hJ⟩ := H
  have hb := germMap_bijective_of_isLocalDiffeomorphAt (⇑h) h.contMDiff hh
  let e :
      AnalyticManifold.IdealSheaf.stalkRing M (h a) ≃+*
          AnalyticManifold.IdealSheaf.stalkRing N a :=
    RingEquiv.ofBijective (germMap (⇑h) h.contMDiff a) hb
  refine ⟨k, fun i => e.symm (z i), α, ⟨?_, ?_⟩, ?_⟩
  · have h1 : Ideal.span (Set.range fun i => e.symm (z i)) =
        Ideal.map e.symm (Ideal.span (Set.range z)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [h1, hz, Ideal.map_symm]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective e e.surjective)
  · rw [hk]
    exact (ringKrullDim_eq_of_ringEquiv e).symm
  · have hmap : Ideal.map e (J.stalkIdeal (h a)) = Ideal.span {∏ i, z i ^ α i} := by
      rw [← hJ, stalkIdeal_comap_eq_map_germMap]
      rfl
    calc J.stalkIdeal (h a) = Ideal.comap e (Ideal.map e (J.stalkIdeal (h a))) :=
          (Ideal.comap_map_of_bijective e e.bijective).symm
      _ = Ideal.map e.symm (Ideal.span {∏ i, z i ^ α i}) := by rw [hmap, Ideal.map_symm]
      _ = Ideal.span {∏ i, e.symm (z i) ^ α i} := by
          rw [Ideal.map_span, Set.image_singleton, map_prod]
          simp only [map_pow]

end Transport

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
  (C : CompatibleFamily T) (Kex : CompactExhaustion M)

/-- The gluing of the isomorphism off `Z` ([Kol07, Theorem 35, (3)]; [Wlo09, Lemma 4.0.3]),
the general form: if over every `M_m` the piece's composite blow-down is an analytic isomorphism off
the trace of `Z`, then `σ` is an analytic isomorphism off `Z` — pointwise a local diffeomorphism
through the piece (`σ ∘ toLimit m = Π^{(m)}`, `IsLocalDiffeomorphAt.of_comp_left`), injective on
`σ⁻¹(Zᶜ)` through a common piece (`exists_common_toLimit`), onto `Zᶜ` through the piece over the
member of the exhaustion containing the point. -/
theorem CompatibleFamily.isAnalyticIsoOver_limitBlowDown
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (Z : Set M)
    (hiso : ∀ m, ((C.seqOn (relCompactOpen Kex m)
      (isCompact_closure_relCompactOpen Kex m)).toSuccession.stageMap
        (Fin.last _)).IsIsoOver (Subtype.val ⁻¹' Z)ᶜ) :
    (C.limitBlowDown Kex hemb hcomp).IsIsoOver Zᶜ := by
  refine ⟨?_, fun _ hp => hp, ?_, ?_⟩
  · -- a local diffeomorphism at every point of `σ⁻¹(Zᶜ)`, through its piece
    rintro ⟨p, hp⟩
    obtain ⟨m, y, rfl⟩ := (C.endResultChain Kex hemb).toLimit_surjective p
    have hld := (hiso m).1 ⟨y, hp⟩
    have hbd : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω
        ((C.limitBlowDown Kex hemb hcomp) ∘ (C.endResultChain Kex hemb).toLimit m) y :=
      hld.comp 𝓘(𝕜, E) _ (isLocalDiffeomorph_inclusion M (relCompactOpen Kex m) _)
    change IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (C.limitBlowDown Kex hemb hcomp)
      ((C.endResultChain Kex hemb).toLimit m y)
    exact IsLocalDiffeomorphAt.of_comp_left hbd
      ((C.endResultChain Kex hemb).isLocalDiffeomorph_toLimit m y)
  · -- injective on `σ⁻¹(Zᶜ)`: two points lie in a common piece, where the piece's bijection decides
    intro p hp q hq hpq
    obtain ⟨k, x, y, rfl, rfl⟩ := (C.endResultChain Kex hemb).exists_common_toLimit p q
    have h : x = y := (hiso k).2.2.1 hp hq (Subtype.ext hpq)
    subst h
    rfl
  · -- onto `Zᶜ`: a point of `M_m` has a preimage in the piece over `M_m`
    intro z hz
    obtain ⟨m, hm⟩ : ∃ m, z ∈ relCompactOpen Kex m := by
      have : z ∈ ⋃ m, (relCompactOpen Kex m : Set M) := by
        rw [iUnion_relCompactOpen]
        exact mem_univ z
      exact mem_iUnion.mp this
    obtain ⟨y, hy, hyz⟩ := (hiso m).2.2.2 (show (⟨z, hm⟩ : M.restrict (relCompactOpen Kex m)) ∈
      (Subtype.val ⁻¹' Z)ᶜ from hz)
    refine ⟨(C.endResultChain Kex hemb).toLimit m y, ?_, congrArg Subtype.val hyz⟩
    change ((C.seqOn (relCompactOpen Kex m)
      (isCompact_closure_relCompactOpen Kex m)).toSuccession.stageMap (Fin.last _) y).1 ∈ Zᶜ
    rw [hyz]
    exact hz

/-- The gluing of the normal-crossings clause ([Kol07, Theorem 35, (2)];
[Wlo09, Theorem 2.0.3, (3)]), the general form: if over every `M_m` the pull-back of `J|_{M_m}`
along the piece's composite blow-down is a normal-crossings divisor, so is the pull-back of `J`
along `σ` — the condition is pointwise, and at `toLimit m y` the stalk of `J.pullback σ
σ.contMDiff` is carried
onto the stalk at `y` of the piece's pull-back by the germ isomorphism of `toLimitMap m`
(`σ ∘ toLimitMap m = Π^{(m)}` after the inclusion of `M_m`, `IdealSheaf.pullback_comp`). -/
theorem CompatibleFamily.isNormalCrossingsDivisor_comap_limitBlowDown
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (J : AnalyticManifold.IdealSheaf M)
    (hsnc : ∀ m, AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor
      ((J.pullback _ (M.inclusion (relCompactOpen Kex m)).contMDiff).pullback _
        ((C.seqOn (relCompactOpen Kex m)
          (isCompact_closure_relCompactOpen Kex m)).toSuccession.stageMap
            (Fin.last _)).contMDiff)) :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor (J.pullback _ (C.limitBlowDown Kex hemb
        hcomp).contMDiff) := by
  intro p
  obtain ⟨m, y, rfl⟩ := (C.endResultChain Kex hemb).toLimit_surjective p
  have heq : (J.pullback _ (C.limitBlowDown Kex hemb hcomp).contMDiff).pullback _
      ((C.endResultChain Kex hemb).toLimitMap m).contMDiff =
      (J.pullback _ (M.inclusion (relCompactOpen Kex m)).contMDiff).pullback _ ((C.seqOn
          (relCompactOpen Kex m)
          (isCompact_closure_relCompactOpen Kex m)).toSuccession.stageMap (Fin.last _)).contMDiff
              := by
    have hσ : (C.limitBlowDown Kex hemb hcomp).comp ((C.endResultChain Kex hemb).toLimitMap m) =
        C.blowDownOn Kex m :=
      (C.endResultChain Kex hemb).limitDesc_comp_toLimitMap _ _ m
    have h1 := AnalyticManifold.IdealSheaf.pullback_comp J (C.limitBlowDown Kex hemb hcomp)
      ((C.endResultChain Kex hemb).toLimitMap m)
    have h2 := AnalyticManifold.IdealSheaf.pullback_comp J (M.inclusion (relCompactOpen Kex m))
      ((C.seqOn (relCompactOpen Kex m)
        (isCompact_closure_relCompactOpen Kex m)).toSuccession.stageMap (Fin.last _))
    rw [hσ] at h1
    exact h1.trans h2.symm
  have hy : AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor ((J.pullback _ (C.limitBlowDown
      Kex hemb hcomp).contMDiff).pullback _
      ((C.endResultChain Kex hemb).toLimitMap m).contMDiff) := by
    rw [heq]
    exact hsnc m
  exact exists_monomial_of_comap_of_isLocalDiffeomorphAt
    ((C.endResultChain Kex hemb).toLimitMap m) (J.pullback _ (C.limitBlowDown Kex hemb
        hcomp).contMDiff)
    ((C.endResultChain Kex hemb).isLocalDiffeomorph_toLimit m y) (hy y)

end Hironaka.Manifold

end
