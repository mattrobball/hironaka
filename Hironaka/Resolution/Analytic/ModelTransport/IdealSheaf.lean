/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.ModelTransport.Manifold
public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Ideal sheaves along an analytic isomorphism across the models

The second layer of the model transport (`Hironaka/Resolution/Analytic/ModelTransport/`). An
analytic isomorphism `g : N ≃ M` between manifolds modelled on `E'` and `E` — for the main theorems
the identity `M.transport ψ → M` of `Hironaka/Resolution/Analytic/ModelTransport/Manifold.lean` and
the identities of its open subsets — carries every stalk-level notion of the analytic main
theorems from `M` to `N`:

* the germ map `𝒪_{M, g b} → 𝒪_{N, b}` is bijective at a local analytic isomorphism, whatever the
  two models (`germMap_bijective_of_isLocalDiffeomorphAt'`, the two-model form of the lemma of
  `Hironaka/Manifold/IdealSheaf/DerivLocality.lean`), so it is a ring isomorphism of the stalks
  (`Diffeomorph.stalkRingEquiv`);
* the pull-back `pullbackDiffeomorph g J := J.pullback g` (`IdealSheaf.pullback`, which takes two
  models) has stalks the images of the stalks (`stalkIdeal_pullbackDiffeomorph`), support the
  preimage of the support, respects `⊤`, `⊥` and products, is inverted by the pull-back along `g⁻¹`
  and hence injective, and transports the pull-back along an analytic map across a square
  `f ∘ g' = g ∘ f'` (`IsModelSquare`, `pullbackDiffeomorph_comap`);
* the predicates of the vocabulary read on the stalks — `IsNonzeroEverywhere`, `IsNonsingular`,
  `IsReduced`, `IsInvertible`, `HasOnlyNormalCrossingsWith` and `HasOnlyNormalCrossings` (Hironaka's
  normal crossings at the stalk, [Hir64, Definition 2, p. 141]), `IsNormalCrossingsDivisor`
  (Bierstone–Milman's normal-crossings divisor, [BM97, Theorem 1.10]), `ord` — hold for the
  pull-back iff they hold for the ideal sheaf: each is a ring-theoretic statement about a stalk,
  carried by the stalk isomorphism (`IsLocalRing.map_ringEquiv_maximalIdeal`,
  `ringKrullDim_eq_of_ringEquiv`, `Ideal.quotientEquiv`, `IsRegularLocalRing.of_ringEquiv`,
  `Ideal.IsRadical.comap`, `Ideal.comap_minimalPrimes_eq_of_surjective`), and the points correspond
  under `g`; the simple locus `regularLocus` of the pull-back is the preimage of the simple locus
  (`regularLocus_pullbackDiffeomorph`);
* `IdealSheaf.transport ψ J`: an ideal sheaf on `M` read on `M.transport ψ`.

The pointwise bodies of `HasOnlyNormalCrossingsWith` and `IsNormalCrossingsDivisor` are transported
on the ring side (`exists_regularSystem_normalCrossings_map`, `exists_regularSystem_monomial_map`);
the two directions of each iff are the lemma at the stalk isomorphism and at its inverse. These are
chart-independence statements: the predicates of the vocabulary are defined on stalks and see no
coordinates.
-/

@[expose] public section

noncomputable section

open AnalyticManifold TopologicalSpace Set
open scoped Manifold ContDiff

universe u v

namespace Hironaka.Manifold

open _root_.Manifold

section Bijective

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {N : Type v} [TopologicalSpace N] [ChartedSpace E' N]

/-- **The germ map of a local analytic isomorphism across the models is bijective**: the germ map
of a local inverse is a two-sided inverse (`germMap_bijective_of_isLocalDiffeomorphAt` of
`Hironaka/Manifold/IdealSheaf/DerivLocality.lean` with the two models free; the same proof, the
models only in its binders). -/
theorem germMap_bijective_of_isLocalDiffeomorphAt' (φ : N → M)
    (hφ : ContMDiff 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ) {b : N}
    (h : IsLocalDiffeomorphAt 𝓘(𝕜, E') 𝓘(𝕜, E) ω φ b) : Function.Bijective (germMap φ hφ b) := by
  obtain ⟨Φ, hbΦ, heq⟩ := h.exists_partialDiffeomorph
  have hφb : φ b ∈ Φ.target := heq hbΦ ▸ Φ.map_source hbΦ
  have hinv : Φ.invFun (φ b) = b := by rw [heq hbΦ]; exact Φ.left_inv hbΦ
  set g := germMapOn Φ.invFun (V := ⟨Φ.target, Φ.open_target⟩) Φ.contMDiffOn_invFun hφb hinv
    with hg
  have hcomp : g.comp (germMap φ hφ b) = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E) ω M (φ b) ?_
    rw [RingHom.comp_apply, hg, stalkToGerm_germMapOn, stalkToGerm_germMap, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E) ω M (φ b) t using Filter.Germ.inductionOn with
    | h k =>
      rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto]
      refine Filter.Germ.coe_eq.mpr ?_
      filter_upwards [Φ.open_target.mem_nhds hφb] with y hy
      simp only [Function.comp_apply]
      have hmem : Φ.invFun y ∈ Φ.source := Φ.map_target hy
      have hri : Φ.toPartialEquiv (Φ.invFun y) = y := Φ.right_inv hy
      rw [heq hmem, hri]
  have hcomp' : (germMap φ hφ b).comp g = RingHom.id _ := by
    refine RingHom.ext fun t => stalkToGerm_injective 𝓘(𝕜, E') ω N b ?_
    rw [RingHom.comp_apply, stalkToGerm_germMap, hg, stalkToGerm_germMapOn, RingHom.id_apply]
    induction stalkToGerm 𝓘(𝕜, E') ω N b t using Filter.Germ.inductionOn with
    | h k =>
      rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_compTendsto]
      refine Filter.Germ.coe_eq.mpr ?_
      filter_upwards [Φ.open_source.mem_nhds hbΦ] with y hy
      simp only [Function.comp_apply]
      rw [heq hy]
      exact congrArg k (Φ.left_inv hy)
  refine ⟨Function.LeftInverse.injective (g := g) fun t => ?_,
    Function.RightInverse.surjective (g := g) fun t => ?_⟩
  · rw [← RingHom.comp_apply, hcomp, RingHom.id_apply]
  · rw [← RingHom.comp_apply, hcomp', RingHom.id_apply]

end Bijective

/-! ### Ideals along a ring isomorphism -/

section RingEquivTransport

variable {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- The minimal primes of the image of an ideal under a ring isomorphism are the images of its
minimal primes (`Ideal.comap_minimalPrimes_eq_of_surjective` along the inverse). -/
theorem minimalPrimes_map_ringEquiv (I : Ideal R) :
    (Ideal.map e I).minimalPrimes = Ideal.map e '' I.minimalPrimes := by
  have h1 := Ideal.comap_minimalPrimes_eq_of_surjective (f := (e.symm : S →+* R))
    e.symm.surjective I
  have h2 : ∀ J : Ideal R, Ideal.comap (e.symm : S →+* R) J = Ideal.map e J := fun J =>
    Ideal.comap_symm e
  rw [h2] at h1
  rw [h1]
  congr 1
  funext J
  exact h2 J

/-- A ring isomorphism preserves and reflects non-zero-divisors. -/
theorem mem_nonZeroDivisors_map_ringEquiv_iff (a : R) :
    e a ∈ nonZeroDivisors S ↔ a ∈ nonZeroDivisors R :=
  ⟨fun h => mem_nonZeroDivisors_of_injective e.injective h,
    fun h => by
      have := mem_nonZeroDivisors_of_injective (f := e.symm) e.symm.injective
        (x := e a)
      exact this (by rwa [e.symm_apply_apply])⟩

/-- The pointwise body of `HasOnlyNormalCrossingsWith` (Hironaka's normal crossings at the stalk,
[Hir64, Definition 2, p. 141]: a regular system of parameters containing an equation of each
minimal prime of `I` and equations for `J`) transports along a ring isomorphism of the stalks: the
image of a regular system is a regular system (`IsLocalRing.map_ringEquiv_maximalIdeal`,
`ringKrullDim_eq_of_ringEquiv`), the minimal primes correspond (`minimalPrimes_map_ringEquiv`). -/
theorem exists_regularSystem_normalCrossings_map [IsLocalRing R] [IsLocalRing S] (I J : Ideal R)
    (h : ∃ (n : ℕ) (z : Fin n → R),
      (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R ∧
        (n : WithBot ℕ∞) = ringKrullDim R) ∧
      (∀ P ∈ I.minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
      ∃ s : Finset (Fin n), J = Ideal.span (z '' ↑s)) :
    ∃ (n : ℕ) (z : Fin n → S),
      (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal S ∧
        (n : WithBot ℕ∞) = ringKrullDim S) ∧
      (∀ P ∈ (Ideal.map e I).minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
      ∃ s : Finset (Fin n), Ideal.map e J = Ideal.span (z '' ↑s) := by
  obtain ⟨n, z, ⟨hz, hn⟩, hP, s, hs⟩ := h
  refine ⟨n, fun i => e (z i), ⟨?_, ?_⟩, ?_, s, ?_⟩
  · rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← hz, Ideal.map_span]
    exact congrArg Ideal.span (Set.range_comp _ _)
  · rw [hn]
    exact ringKrullDim_eq_of_ringEquiv e
  · intro P hP'
    rw [minimalPrimes_map_ringEquiv] at hP'
    obtain ⟨Q, hQ, rfl⟩ := hP'
    obtain ⟨i, rfl⟩ := hP Q hQ
    exact ⟨i, by rw [Ideal.map_span, Set.image_singleton]⟩
  · rw [hs, Ideal.map_span, Set.image_image]

/-- The pointwise body of `IsNormalCrossingsDivisor` (Bierstone–Milman's normal-crossings divisor
at the stalk, [BM97, Theorem 1.10]: a monomial in a regular system of parameters) transports along
a ring isomorphism of the stalks. -/
theorem exists_regularSystem_monomial_map [IsLocalRing R] [IsLocalRing S] (J : Ideal R)
    (h : ∃ (n : ℕ) (z : Fin n → R) (α : Fin n → ℕ),
      (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R ∧
        (n : WithBot ℕ∞) = ringKrullDim R) ∧
      J = Ideal.span {∏ i, z i ^ α i}) :
    ∃ (n : ℕ) (z : Fin n → S) (α : Fin n → ℕ),
      (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal S ∧
        (n : WithBot ℕ∞) = ringKrullDim S) ∧
      Ideal.map e J = Ideal.span {∏ i, z i ^ α i} := by
  obtain ⟨n, z, α, ⟨hz, hn⟩, hJ⟩ := h
  refine ⟨n, fun i => e (z i), α, ⟨?_, ?_⟩, ?_⟩
  · rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← hz, Ideal.map_span]
    exact congrArg Ideal.span (Set.range_comp _ _)
  · rw [hn]
    exact ringKrullDim_eq_of_ringEquiv e
  · rw [hJ, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]

/-- The image under the inverse of the image is the ideal. -/
theorem ideal_map_symm_map (I : Ideal R) : Ideal.map e.symm (Ideal.map e I) = I := by
  rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ e.bijective]

end RingEquivTransport

/-! ### The pull-back along an analytic isomorphism across the models -/

section Pullback

variable {𝕜 : Type} [RCLike 𝕜] {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {M : AnalyticManifold.{u} 𝕜 E}
  {N : AnalyticManifold.{u} 𝕜 E'} (g : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N M ω)

/-- **The stalk isomorphism `𝒪_{M, g b} ≃+* 𝒪_{N, b}` of an analytic isomorphism across the
models**: its germ map, bijective by `germMap_bijective_of_isLocalDiffeomorphAt'`. -/
def _root_.Diffeomorph.stalkRingEquiv (b : N) :
    IdealSheaf.stalkRing M (g b) ≃+* IdealSheaf.stalkRing
        N b :=
  RingEquiv.ofBijective (germMap ⇑g g.contMDiff b)
    (germMap_bijective_of_isLocalDiffeomorphAt' ⇑g g.contMDiff (g.isLocalDiffeomorph b))

/-- The stalk isomorphism is the germ map on points. -/
theorem _root_.Diffeomorph.coe_stalkRingEquiv (b : N) :
    ⇑(g.stalkRingEquiv b) = germMap ⇑g g.contMDiff b := rfl

/-- **The pull-back of an ideal sheaf along an analytic isomorphism across the models**
(`IdealSheaf.pullback`, which takes two models). -/
abbrev _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph
    (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf N :=
  J.pullback ⇑g g.contMDiff

/-- The stalk of the pull-back is the image of the stalk under the stalk isomorphism. -/
theorem _root_.AnalyticManifold.IdealSheaf.stalkIdeal_pullbackDiffeomorph
    (J : AnalyticManifold.IdealSheaf M)
    (b : N) :
    (J.pullbackDiffeomorph g).stalkIdeal b =
      Ideal.map (g.stalkRingEquiv b) (J.stalkIdeal (g b)) :=
  IdealSheaf.stalkIdeal_pullback _ _ J b

/-- The support of the pull-back is the preimage of the support. -/
theorem _root_.AnalyticManifold.IdealSheaf.support_pullbackDiffeomorph
    (J : AnalyticManifold.IdealSheaf M) :
    (J.pullbackDiffeomorph g).support = ⇑g ⁻¹' J.support :=
  IdealSheaf.support_pullback _ _ J

/-- The unit ideal pulls back to the unit ideal. -/
theorem _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph_top :
    ((⊤ : M.IdealSheaf)).pullbackDiffeomorph g =
        ⊤ :=
  IdealSheaf.pullback_top _ _

/-- The pull-back of a product is the product of the pull-backs. -/
theorem _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph_mul
    (I J : AnalyticManifold.IdealSheaf M) :
    (I * J).pullbackDiffeomorph g = (I.pullbackDiffeomorph g * J.pullbackDiffeomorph g) :=
  IdealSheaf.pullback_mul _ _ I J

/-- The zero ideal sheaf pulls back to the zero ideal sheaf. -/
theorem _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph_bot :
    (⊥ : AnalyticManifold.IdealSheaf M).pullbackDiffeomorph g = ⊥ :=
  IdealSheaf.ext fun x => by
    rw [IdealSheaf.stalkIdeal_pullback, IdealSheaf.stalkIdeal_bot, Ideal.map_bot,
      IdealSheaf.stalkIdeal_bot]

/-- Pulling back along `g` and then along `g⁻¹` is the identity. -/
theorem _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph
    (J : AnalyticManifold.IdealSheaf M) :
        AnalyticManifold.IdealSheaf.pullbackDiffeomorph g.symm (J.pullbackDiffeomorph g) = J :=
  (IdealSheaf.pullback_pullback J _ _ _ _).trans
    ((IdealSheaf.pullback_congr J _ contMDiff_id (funext fun x => g.apply_symm_apply x)).trans
      (IdealSheaf.pullback_id_eq_self J))

/-- The pull-back along an analytic isomorphism is injective. -/
theorem _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph_injective :
    Function.Injective (fun J : AnalyticManifold.IdealSheaf M => J.pullbackDiffeomorph g) := by
  intro J K h
  have := congrArg (fun J : AnalyticManifold.IdealSheaf N => J.pullbackDiffeomorph g.symm) h
  simpa only [IdealSheaf.pullbackDiffeomorph_symm_pullbackDiffeomorph] using this

variable {M' : AnalyticManifold.{u} 𝕜 E} {N' : AnalyticManifold.{u} 𝕜 E'}

/-- The square `f ∘ g' = g ∘ f'` of two analytic isomorphisms across the models and two analytic
maps: the hypothesis of the transport lemmas of
`Hironaka/Resolution/Analytic/ModelTransport/Square.lean` and `SquareChart.lean`. -/
abbrev IsModelSquare (g' : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N' M' ω)
    (f : AnalyticMap M' M)
    (f' : AnalyticMap N' N) : Prop :=
  ∀ x, f (g' x) = g (f' x)

/-- The pull-back along an analytic map (`comap`) transports along a square of analytic
isomorphisms across the models. -/
theorem _root_.AnalyticManifold.IdealSheaf.pullbackDiffeomorph_comap
    (g' : Diffeomorph 𝓘(𝕜, E') 𝓘(𝕜, E) N' M' ω) (f : AnalyticMap M' M)
    (f' : AnalyticMap N' N)
    (hsq : IsModelSquare g g' f f') (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.pullbackDiffeomorph g' (J.pullback f f.contMDiff) =
      (J.pullbackDiffeomorph g).pullback f' f'.contMDiff := by
  change (J.pullback ⇑f f.contMDiff).pullback ⇑g' g'.contMDiff =
    (J.pullback ⇑g g.contMDiff).pullback ⇑f' f'.contMDiff
  rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
  exact IdealSheaf.pullback_congr J _ _ (funext hsq)

/-- `IsNonzeroEverywhere` along the isomorphism. -/
theorem _root_.AnalyticManifold.IdealSheaf.isNonzeroEverywhere_pullbackDiffeomorph_iff
    (J : AnalyticManifold.IdealSheaf M) :
    (J.pullbackDiffeomorph g).IsNonzeroEverywhere ↔ J.IsNonzeroEverywhere := by
  refine ⟨fun h x => ?_, fun h b => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, g b = x := ⟨g.symm x, g.apply_symm_apply x⟩
    have := h b
    rwa [IdealSheaf.stalkIdeal_pullbackDiffeomorph, Ne,
      Ideal.map_eq_bot_iff_of_injective (g.stalkRingEquiv b).injective] at this
  · rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, Ne,
      Ideal.map_eq_bot_iff_of_injective (g.stalkRingEquiv b).injective]
    exact h (g b)

/-- `IsNonsingular` (the regularity of the local rings `𝒪_x / J_x`) along the isomorphism: the
quotients are isomorphic rings (`Ideal.quotientEquiv`, `IsRegularLocalRing.of_ringEquiv`). -/
theorem _root_.AnalyticManifold.IdealSheaf.isNonsingular_pullbackDiffeomorph_iff
    (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.IsNonsingular (J.pullbackDiffeomorph g) ↔ J.IsNonsingular := by
  refine ⟨fun h x hx => ?_, fun h b hb => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, g b = x := ⟨g.symm x, g.apply_symm_apply x⟩
    have hb : b ∈ (J.pullbackDiffeomorph g).support := by
      rw [IdealSheaf.support_pullbackDiffeomorph]; exact hx
    have := h b hb
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph] at this
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv (J.stalkIdeal (g b))
      (Ideal.map (g.stalkRingEquiv b) (J.stalkIdeal (g b))) (g.stalkRingEquiv b) rfl).symm
  · rw [IdealSheaf.support_pullbackDiffeomorph] at hb
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph]
    have := h _ hb
    exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv (J.stalkIdeal (g b))
      (Ideal.map (g.stalkRingEquiv b) (J.stalkIdeal (g b))) (g.stalkRingEquiv b) rfl)

/-- The simple locus `regularLocus` along the isomorphism, the pointwise form of
`isNonsingular_pullbackDiffeomorph_iff`: the quotients `𝒪_b / (g^*J)_b` and `𝒪_{g b} / J_{g b}` are
isomorphic rings. -/
theorem _root_.AnalyticManifold.IdealSheaf.regularLocus_pullbackDiffeomorph
    (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.regularLocus (J.pullbackDiffeomorph g) =
      ⇑g ⁻¹' J.regularLocus := by
  ext b
  change IsRegularLocalRing (IdealSheaf.stalkRing N b ⧸ (J.pullbackDiffeomorph g).stalkIdeal b) ↔
    IsRegularLocalRing (IdealSheaf.stalkRing M (g b) ⧸ J.stalkIdeal (g b))
  rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph]
  have e := Ideal.quotientEquiv (J.stalkIdeal (g b))
    (Ideal.map (g.stalkRingEquiv b) (J.stalkIdeal (g b))) (g.stalkRingEquiv b) rfl
  exact ⟨fun _ => IsRegularLocalRing.of_ringEquiv e.symm,
    fun _ => IsRegularLocalRing.of_ringEquiv e⟩

/-- `IsReduced` along the isomorphism (`Ideal.IsRadical.comap`). -/
theorem _root_.AnalyticManifold.IdealSheaf.isReduced_pullbackDiffeomorph_iff
    (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.IsReduced (J.pullbackDiffeomorph g) ↔ J.IsReduced := by
  refine ⟨fun h x => ?_, fun h b => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, g b = x := ⟨g.symm x, g.apply_symm_apply x⟩
    have := (h b).comap (g.stalkRingEquiv b)
    rwa [IdealSheaf.stalkIdeal_pullbackDiffeomorph,
      Ideal.comap_map_of_bijective _ (g.stalkRingEquiv b).bijective] at this
  · rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, ← Ideal.comap_symm]
    exact (h (g b)).comap _

/-- `IsInvertible` along the isomorphism: the generating non-zero-divisor is carried by the stalk
isomorphism. -/
theorem _root_.AnalyticManifold.IdealSheaf.isInvertible_pullbackDiffeomorph_iff
    (J : AnalyticManifold.IdealSheaf M) :
    (J.pullbackDiffeomorph g).IsInvertible ↔ J.IsInvertible := by
  refine ⟨fun h x => ?_, fun h b => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, g b = x := ⟨g.symm x, g.apply_symm_apply x⟩
    obtain ⟨a, ha, hJ⟩ := h b
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph] at hJ
    refine ⟨(g.stalkRingEquiv b).symm a, ?_, ?_⟩
    · rw [← mem_nonZeroDivisors_map_ringEquiv_iff (g.stalkRingEquiv b),
        RingEquiv.apply_symm_apply]
      exact ha
    · have := congrArg (Ideal.map (g.stalkRingEquiv b).symm) hJ
      rwa [ideal_map_symm_map, Ideal.map_span, Set.image_singleton] at this
  · obtain ⟨a, ha, hJ⟩ := h (g b)
    refine ⟨g.stalkRingEquiv b a, (mem_nonZeroDivisors_map_ringEquiv_iff _ a).mpr ha, ?_⟩
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, hJ, Ideal.map_span, Set.image_singleton]

/-- `HasOnlyNormalCrossingsWith` along the isomorphism. -/
theorem _root_.AnalyticManifold.IdealSheaf.hasOnlyNormalCrossingsWith_pullbackDiffeomorph_iff
    (E₀ D : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossingsWith (E₀.pullbackDiffeomorph g)
        (D.pullbackDiffeomorph g) ↔
      E₀.HasOnlyNormalCrossingsWith D := by
  refine ⟨fun h x hx => ?_, fun h b hb => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, g b = x := ⟨g.symm x, g.apply_symm_apply x⟩
    have hb : b ∈ (D.pullbackDiffeomorph g).support := by
      rw [IdealSheaf.support_pullbackDiffeomorph]; exact hx
    have := exists_regularSystem_normalCrossings_map (g.stalkRingEquiv b).symm _ _ (h b hb)
    rwa [IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_pullbackDiffeomorph,
      ideal_map_symm_map, ideal_map_symm_map] at this
  · rw [IdealSheaf.support_pullbackDiffeomorph] at hb
    rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph, IdealSheaf.stalkIdeal_pullbackDiffeomorph]
    exact exists_regularSystem_normalCrossings_map (g.stalkRingEquiv b) _ _ (h _ hb)

/-- `HasOnlyNormalCrossings` along the isomorphism. -/
theorem _root_.AnalyticManifold.IdealSheaf.hasOnlyNormalCrossings_pullbackDiffeomorph_iff
    (E₀ : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.HasOnlyNormalCrossings (E₀.pullbackDiffeomorph g) ↔
        E₀.HasOnlyNormalCrossings := by
  unfold IdealSheaf.HasOnlyNormalCrossings
  rw [← IdealSheaf.pullbackDiffeomorph_bot g]
  exact IdealSheaf.hasOnlyNormalCrossingsWith_pullbackDiffeomorph_iff g E₀ ⊥

/-- `IsNormalCrossingsDivisor` along the isomorphism. -/
theorem _root_.AnalyticManifold.IdealSheaf.isNormalCrossingsDivisor_pullbackDiffeomorph_iff
    (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf.IsNormalCrossingsDivisor (J.pullbackDiffeomorph g) ↔
        J.IsNormalCrossingsDivisor := by
  refine ⟨fun h x => ?_, fun h b => ?_⟩
  · obtain ⟨b, rfl⟩ : ∃ b, g b = x := ⟨g.symm x, g.apply_symm_apply x⟩
    have := exists_regularSystem_monomial_map (g.stalkRingEquiv b).symm _ (h b)
    rwa [IdealSheaf.stalkIdeal_pullbackDiffeomorph, ideal_map_symm_map] at this
  · rw [IdealSheaf.stalkIdeal_pullbackDiffeomorph]
    exact exists_regularSystem_monomial_map (g.stalkRingEquiv b) _ (h (g b))

/-- The order along the isomorphism (`ord_pullback_of_isLocalDiffeomorphAt`, which takes two
models). -/
theorem _root_.AnalyticManifold.IdealSheaf.ord_pullbackDiffeomorph
    (J : AnalyticManifold.IdealSheaf M) (b : N) :
    (J.pullbackDiffeomorph g).ord b = J.ord (g b) :=
  IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ J (g.isLocalDiffeomorph b)

variable (ψ : E ≃L[𝕜] E')

/-- **An ideal sheaf on `M` read on the re-modelled `M`**: the same sections, pulled back along the
identity `M.transport ψ → M`. -/
abbrev _root_.AnalyticManifold.IdealSheaf.transport (J : AnalyticManifold.IdealSheaf M) :
    AnalyticManifold.IdealSheaf (M.transport ψ) :=
  J.pullbackDiffeomorph (M.transportDiffeomorph ψ).symm

end Pullback

end Hironaka.Manifold

end
