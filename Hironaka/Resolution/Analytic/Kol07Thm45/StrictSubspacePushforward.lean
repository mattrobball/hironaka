/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.Pushforward
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Manifold.FiniteSuccession.Restrict.Lift
public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeq
public import Hironaka.Manifold.IdealSheaf.Basic
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.StrictSmooth
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.FiniteSuccession.Restrict.GermRestrict
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The ideal-theoretic strict transforms along the push-forward of a blow-up sequence

Kollár pushes a blow-up sequence `T` of a closed submanifold `S ⊆ X` forward to a sequence
`j_* T` of `X` whose centres are the carried centres `Z_i^X = (j_i)_* Z_i^S`, and declares that
"for all practical purposes `Z_i^X = Z_i^S`" [Kol07, Definition 30.3]; the identification behind
it is that `S_{i+1} := Bl_{Z_i ∩ S_i} S_i` is the birational (strict) transform of `S_i` in
`X_{i+1}` [Kol07, Definition 30.2] (`strictTransform_submanifold_eq_blowUp`,
`BlowUp/Transform/StrictSmooth.lean`). The comparison of the local resolutions of a piece for two
embeddings needs the IDEAL-level content of the sentence for a closed subspace `Y ⊆ S` given by an
ideal sheaf `I ⊇ 𝓘_S` of `X`: the strict transforms `strictTransformSubspace` of `I` along `j_* T`
stay inside the carried `S_i` and restrict to the strict transforms of `I|_S` along `T` itself.
This module proves it. Labels used below: (A) the containment `𝓘_{S'} ≤ Yt`, (A′) its
consequence off `S'`, (S) and (S′) the saturation identities, (C) the branch coincidence, (B) the
restriction identity, (Q) the diffeomorphism square.

## The one-step core (section `PushforwardStep`)

For one blowing-up `σ : X' → X` along `Y ⊆ S` with `S' := strictTransformSet σ Y S` (a closed
submanifold) and the restricted blow-down `σ|_{S'} : S' → S` (a blowing-up of the bundled `S`
along `Y`, `isBlowUp_restrictMap`), write `ρ_p : 𝒪_{X',p} → 𝒪_{S',p}` for the restriction of
germs at `p ∈ S'` — surjective (`germMap_inclusionMap_surjective`) with kernel `𝓘_{S',p}`
(`stalkIdeal_idealSheaf_of_mem`).

* `idealSheaf_strictTransform_le_strictTransformSubspace` **(A)**: `𝓘_{S'} ≤ Yt`, the strict
  transform of `I` lies inside `S'` — from the inclusion `𝓘_{S'} ≤ saturation(σ^*𝓘_S)`
  (`idealSheaf_strictTransform_stalkIdeal_le_saturationStalk`, the adapted-chart computation
  `σ^*𝓘_S = 𝓘_{S'} · 𝓘_E`) and the monotonicity of the saturation in the ideal; trivial in the
  `⊤` branch. Its stalk form `𝓘_{S',p} ≤ Sat_X(I)_p` is the INPUT of the colon step below: the
  kernel of `ρ_p` lies in the saturation.
* `saturationStalk_restrictMap_eq_map` **(S)**: `Sat_S(I|_S)_p = ρ_p(Sat_X(I)_p)`. The exceptional
  stalk is principal, `𝓘_{E,p} = (u)` (`exists_stalkIdeal_totalTransform_self_eq_span_singleton`);
  `k = 0` is the pull-back identity `σ|_{S'}^*(I|_S) = (σ^*I)|_{S'}`; for `k ≥ 1` a germ `g` with
  `u^k g ∈ σ^*I` restricts into `(σ^*I|_{S'} : ρ(u)^k)`, and conversely a lift `g` of
  `h ∈ (σ^*I|_{S'} : ρ(u)^k)` has `u^k g ∈ σ^*I + 𝓘_{S'} ⊆ Sat_X(I)`, so `g ∈ Sat_X(I)` (the
  saturation is saturated: `u^m x ∈ Sat ⇒ x ∈ Sat`).
* `comap_saturationStalk_restrictMap` **(S′)**: `Sat_X(I)_p = ρ_p⁻¹(Sat_S(I|_S)_p)` (the kernel
  lies in `Sat_X`), and `saturationStalk_eq_top_of_notMem_strictTransform_of_le` **(A′)**: off
  `S'` the saturation is the unit ideal (`𝓘_{S',p} = ⊤ ≤ Sat_X(I)_p`).
* `hasLocalGenerators_saturationStalk_restrictMap_iff` **(C)**, the BRANCH COINCIDENCE of the
  `if` in the definition of `strictTransformSubspace`: `Sat_X(I)` has local generators iff
  `Sat_S(I|_S)` has. Generators RESTRICT (`hasLocalGenerators_pullback` on `ofStalks`,
  `ρ(ρ⁻¹J) = J`) and LIFT: near `p ∈ S'` the `S'`-generators' germs lift along the surjective `ρ_p`
  to germs of `X'`, represented by sections agreeing with the generators near `p`
  (`TopCat.Presheaf.germ_eq`); together with local generators of `𝓘_{S'}` (which are `⊤` at the
  nearby points off `S'`) they generate `ρ_q⁻¹(Sat_S)` = `Sat_X` at every nearby `q`; off `S'` the
  single section `1` generates on the open `S'ᶜ`. No finite-type input is needed: the result
  holds over every `RCLike` field.
* `strictTransformSubspace_pullback_inclusionMap` **(B)**, UNCONDITIONAL:
  `(strict transform of I along σ)|_{S'} = strict transform of I|_S along σ|_{S'}` — in the `then`
  branches by (S), in the `else` branches by `⊤` pulling back to `⊤`, the branches coinciding
  by (C).

## The diffeomorphism square (section `DiffeoSquare`) — (Q)

`T`'s stage `i+1` is blown up along the GIVEN `T.map i`, the core along the restricted blow-down;
the unique diffeomorphism `PushforwardStage.blowUpStep.iso : T_{i+1} ≃ S_{i+1}` lies over
`e_i : T_i ≃ S_i` (`restrictMap_blowUpStep_iso`).
`strictTransformSubspace_comap_of_diffeomorph_square` carries the strict transform across any such
square of blow-up models of the same centre (`saturationStalk_comap_of_diffeomorph_square` at the
sheaf level: bijective germ maps, the exceptional ideal sheaf by
`comap_idealSheaf_of_isLocalDiffeomorph` and `idealSheaf_congr`, the branches by
`hasLocalGenerators_pullback` / `HasLocalGenerators.of_map_germMap_of_surjective`).

## The chain (namespace `AnalyticManifold.FiniteSuccession`)

`isClosedSubmanifold_range_pushforwardIncl` types the carried `S_i = j_i(T_i)` on the stage;
**(A)** `idealSheaf_range_pushforwardIncl_le_strictTransformSubspaceSeq`, **(B)**
`strictTransformSubspaceSeq_pushforward_pullback_incl` and **(C)**
`hasLocalGenerators_saturationStalk_pushforward_iff` follow by ONE induction on the stage
(`strictTransformSubspaceSeq_pushforward_aux`: (A) ∧ (B) at stage `i`; the step is the core at
`P := pushforwardAux i` with `I := Yt^X_i`, its hypothesis `𝓘_{S_i} ≤ Yt^X_i` the (A) of the
previous stage, the branch coincidence (C) of the step supplying both `then`/`else` cases, and the
square (Q) carrying the result from the restricted blow-down to `T.map i`; stage `0` is
`J := I|_S`, `pushforwardIncl_zero`). The witnesses of the push-forward at a step are its CHOSEN
chart and codimension on the cosupport of the carried centre; `strictTransformSubspace_congr`
bridges them to `pushforwardCenterOfSub` (`support_pushforwardCenterOf`).

Sources: [Kol07, Definitions 30.2–30.3]; the saturation is that of [BM97, §3, Proposition 3.13].
The proofs are bookkeeping of the printed steps; not in the sources.
-/

public section

noncomputable section

open TopologicalSpace Set CategoryTheory
open scoped Manifold ContDiff Topology

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-! ### (Q) The diffeomorphism square of two blow-up models of the same centre -/

section DiffeoSquare

variable {𝕜 : Type} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
  {ψ : F ≃L[𝕜] (Fin n → 𝕜)} {M₁ M₂ M₁' M₂' : AnalyticManifold.{u} 𝕜 F} {Y₁ : Set M₁} {Y₂ : Set M₂}
  {c : ℕ} {π₁ : M₁' → M₁} {π₂ : M₂' → M₂}
  (hY₁ : IsClosedSubmanifold ψ Y₁ c) (h₁ : IsBlowUp ψ Y₁ c π₁)
  (hY₂ : IsClosedSubmanifold ψ Y₂ c) (h₂ : IsBlowUp ψ Y₂ c π₂)
  (g : Diffeomorph 𝓘(𝕜, F) 𝓘(𝕜, F) M₁ M₂ ω) (hg : ⇑g '' Y₁ = Y₂)
  (g' : Diffeomorph 𝓘(𝕜, F) 𝓘(𝕜, F) M₁' M₂' ω) (hsq : ∀ p, π₂ (g' p) = g (π₁ p))

include hg hsq in
/-- The saturation stalks across a DIFFEOMORPHISM square (the saturation half of (Q)): two
blowings-up `π₁ : M₁' → M₁` along `Y₁`, `π₂ : M₂' → M₂` along `Y₂ = g(Y₁)`, and a
diffeomorphism `g'` of the blow-ups over `g` — the saturation stalks of `g^*I₂` along `π₁` are the
images of the saturation stalks of `I₂` along `π₂` under the bijective germ maps of `g'`. -/
theorem saturationStalk_comap_of_diffeomorph_square (I₂ : AnalyticManifold.IdealSheaf M₂)
    (p : M₁') :
    saturationStalk hY₁ h₁ (I₂.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff)
        p =
      Ideal.map (germMap ⇑(Diffeomorph.toAnalyticMap g') (Diffeomorph.toAnalyticMap g').contMDiff p)
        (saturationStalk hY₂ h₂ I₂ (Diffeomorph.toAnalyticMap g' p)) := by
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt ⇑(Diffeomorph.toAnalyticMap g')
    (Diffeomorph.toAnalyticMap g').contMDiff (g'.isLocalDiffeomorph p)
  have hcomp : π₂ ∘ ⇑(Diffeomorph.toAnalyticMap g') = ⇑(Diffeomorph.toAnalyticMap g) ∘ π₁ :=
    funext hsq
  have hT : (I₂.pullback π₂ h₂.contMDiff).pullback ⇑(Diffeomorph.toAnalyticMap g')
      (Diffeomorph.toAnalyticMap g').contMDiff =
      (I₂.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff).pullback π₁ h₁.contMDiff := by
    change (I₂.pullback π₂ h₂.contMDiff).pullback _ _ =
      (I₂.pullback ⇑(Diffeomorph.toAnalyticMap g) _).pullback π₁ h₁.contMDiff
    rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I₂ _ _ hcomp
  have hpb : hY₂.idealSheaf.pullback ⇑(Diffeomorph.toAnalyticMap g)
      (Diffeomorph.toAnalyticMap g).contMDiff = hY₁.idealSheaf := by
    have h1 := comap_idealSheaf_of_isLocalDiffeomorph ψ (Diffeomorph.toAnalyticMap g)
      g.isLocalDiffeomorph hY₂
    refine h1.trans (IsClosedSubmanifold.idealSheaf_congr _ hY₁ ?_)
    rw [← hg]
    exact g.toEquiv.preimage_image Y₁
  have hE : (hY₂.idealSheaf.pullback π₂ h₂.contMDiff).pullback ⇑(Diffeomorph.toAnalyticMap g')
      (Diffeomorph.toAnalyticMap g').contMDiff = hY₁.idealSheaf.pullback π₁ h₁.contMDiff := by
    rw [IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_congr hY₂.idealSheaf _
        ((Diffeomorph.toAnalyticMap g).contMDiff.comp h₁.contMDiff) hcomp,
      ← IdealSheaf.pullback_pullback hY₂.idealSheaf ⇑(Diffeomorph.toAnalyticMap g)
        (Diffeomorph.toAnalyticMap g).contMDiff π₁ h₁.contMDiff, hpb]
  have e1 := IdealSheaf.stalkIdeal_pullback ⇑(Diffeomorph.toAnalyticMap g')
    (Diffeomorph.toAnalyticMap g').contMDiff (I₂.pullback π₂ h₂.contMDiff) p
  have e2 := IdealSheaf.stalkIdeal_pullback ⇑(Diffeomorph.toAnalyticMap g')
    (Diffeomorph.toAnalyticMap g').contMDiff (hY₂.idealSheaf.pullback π₂ h₂.contMDiff) p
  unfold saturationStalk
  rw [Ideal.map_iSup]
  refine iSup_congr fun k => ?_
  rw [Ideal.map_colon_pow_of_bijective _ hbij, ← e1, ← e2, hT, hE]

include hg hsq in
/-- The two saturations take the same branch of the `if` in `strictTransformSubspace` (`g'` is a
surjective local isomorphism) — the branch half of (Q). -/
theorem hasLocalGenerators_saturationStalk_comap_of_diffeomorph_square_iff
    (I₂ : AnalyticManifold.IdealSheaf M₂) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 F M₁')
        (saturationStalk hY₁ h₁
            (I₂.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff)) ↔
      IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 F M₂') (saturationStalk hY₂ h₂ I₂) := by
  have hfun : saturationStalk hY₁ h₁
      (I₂.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff) =
      fun p => Ideal.map (germMap ⇑(Diffeomorph.toAnalyticMap g')
        (Diffeomorph.toAnalyticMap g').contMDiff p)
        (saturationStalk hY₂ h₂ I₂ (Diffeomorph.toAnalyticMap g' p)) :=
    funext (saturationStalk_comap_of_diffeomorph_square hY₁ h₁ hY₂ h₂ g hg g' hsq I₂)
  rw [hfun]
  constructor
  · intro h1
    exact IdealSheaf.HasLocalGenerators.of_map_germMap_of_surjective (Diffeomorph.toAnalyticMap g')
      g'.isLocalDiffeomorph g'.toEquiv.surjective _ h1
  · intro h2
    have hpb := hasLocalGenerators_pullback ⇑(Diffeomorph.toAnalyticMap g')
      (Diffeomorph.toAnalyticMap g').contMDiff (IdealSheaf.ofStalks _ _ h2)
    simpa only [IdealSheaf.stalkIdeal_ofStalks] using hpb

include hg hsq in
/-- (Q) The strict transform transports along a diffeomorphism square of blow-up models:
`g'^* (strict transform of I₂ along π₂) = strict transform of g^*I₂ along π₁` — branch by branch,
UNCONDITIONAL. Used at each step of the chain to pass from the restricted blow-down
`S_{i+1} → S_i` (the core's model) to the given `T.map i` through the unique diffeomorphism
`PushforwardStage.blowUpStep.iso` (`restrictMap_blowUpStep_iso`). -/
theorem strictTransformSubspace_comap_of_diffeomorph_square
    (I₂ : AnalyticManifold.IdealSheaf M₂) :
    (strictTransformSubspace hY₂ h₂ I₂).pullback _ (Diffeomorph.toAnalyticMap g').contMDiff =
      strictTransformSubspace hY₁ h₁
        (I₂.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff) := by
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 F M₂')
    (saturationStalk hY₂ h₂ I₂)
  · have hex' := (hasLocalGenerators_saturationStalk_comap_of_diffeomorph_square_iff hY₁ h₁ hY₂ h₂
      g hg g' hsq I₂).mpr hex
    refine IdealSheaf.ext fun p => ?_
    rw [IdealSheaf.stalkIdeal_pullback,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex,
      stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex',
      saturationStalk_comap_of_diffeomorph_square hY₁ h₁ hY₂ h₂ g hg g' hsq I₂ p]
  · have hex' : ¬ IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 F M₁')
        (saturationStalk hY₁ h₁
            (I₂.pullback _ (Diffeomorph.toAnalyticMap g).contMDiff)) :=
      fun h' => hex ((hasLocalGenerators_saturationStalk_comap_of_diffeomorph_square_iff hY₁ h₁ hY₂
        h₂ g hg g' hsq I₂).mp h')
    rw [strictTransformSubspace_of_not_hasLocalGenerators _ _ _ hex,
      strictTransformSubspace_of_not_hasLocalGenerators _ _ _ hex']
    exact IdealSheaf.pullback_top _ _

end DiffeoSquare

/-! ### The core: one blowing-up of `M` along `Y ⊆ S`, restricted to the strict transform `S'` -/

section PushforwardStep

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)}
  {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M] [T2Space M]
  [SecondCountableTopology M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M']
  [SecondCountableTopology M'] {π : M' → M} {Y S : Set M} {c s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
  (hYS : Y ⊆ S) (I : IdealSheaf (structureSheaf 𝕜 E M)) (hI : hS.idealSheaf ≤ I)

omit [T2Space M] [SecondCountableTopology M] in
include hI in
/-- The stalk form of (A): the ideal of the strict transform `S'` lies in the saturation of
`σ^*I` at every point — the inclusion `𝓘_{S'} ≤ saturation(σ^*𝓘_S)` (the adapted-chart
computation) and the monotonicity of the saturation in the ideal. -/
theorem idealSheaf_strictTransform_stalkIdeal_le_saturationStalk_of_le (p : M') :
    (hS.strictTransform hY h hYS).idealSheaf.stalkIdeal p ≤ saturationStalk hY h I p := by
  refine le_trans (idealSheaf_strictTransform_stalkIdeal_le_saturationStalk hY h hS hYS
    (hS.strictTransform hY h hYS) p) ?_
  unfold saturationStalk
  exact iSup_mono fun k => Submodule.colon_mono
    (IdealSheaf.le_def.mp (IdealSheaf.pullback_le_pullback _ _ hI) p) le_rfl

omit [T2Space M] [SecondCountableTopology M] in
include hI in
/-- (A) core ("`Z_i^X = Z_i^S`" of [Kol07, Definition 30.3] made explicit: the strict transform of
a subspace of `S` stays in the strict transform `S'` of `S`): `𝓘_{S'} ≤` the strict transform of
`I` — from `𝓘_{S'} = saturation of σ^*𝓘_S ≤ saturation of σ^*I` ([Kol07, Definition 30.2],
`strictTransform_submanifold_eq_blowUp`); trivial in the `⊤` branch. -/
theorem idealSheaf_strictTransform_le_strictTransformSubspace :
    (hS.strictTransform hY h hYS).idealSheaf ≤ strictTransformSubspace hY h I := by
  rw [IdealSheaf.le_def]
  intro p
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M')
    (saturationStalk hY h I)
  · rw [stalkIdeal_strictTransformSubspace_of_hasLocalGenerators hY h I hex]
    exact idealSheaf_strictTransform_stalkIdeal_le_saturationStalk_of_le hS hY h hYS I hI p
  · rw [strictTransformSubspace_of_not_hasLocalGenerators hY h I hex, IdealSheaf.stalkIdeal_top]
    exact le_top

omit [T2Space M] [SecondCountableTopology M] in
include hYS hI in
/-- (A′) core: off the strict transform `S'` the saturation of `σ^*I` is the unit ideal (the
ideal of `S'` is the unit ideal there and lies in the saturation). -/
theorem saturationStalk_eq_top_of_notMem_strictTransform_of_le {p : M'}
    (hp : p ∉ strictTransformSet π Y S) : saturationStalk hY h I p = ⊤ :=
  eq_top_iff.mpr (le_trans (le_of_eq
    ((hS.strictTransform hY h hYS).stalkIdeal_idealSheaf_of_notMem hp).symm)
    (idealSheaf_strictTransform_stalkIdeal_le_saturationStalk_of_le hS hY h hYS I hI p))

omit [IsManifold 𝓘(𝕜, E) ω M] [T2Space M] [SecondCountableTopology M] in
/-- The saturation is saturated: if `u^m x` lies in `⋃_k (σ^*I : (u)^k)`, `u` generating the
exceptional stalk, so does `x` (the union is directed). -/
theorem mem_saturationStalk_of_pow_mul_mem {p : M'}
    {u : (structureSheaf 𝕜 E M').presheaf.stalk p}
    (hu : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p = Ideal.span {u}) {m : ℕ}
    {x : (structureSheaf 𝕜 E M').presheaf.stalk p} (hx : x * u ^ m ∈ saturationStalk hY h I p) :
    x ∈ saturationStalk hY h I p := by
  have hdir : Directed (· ≤ ·) fun k : ℕ =>
      Submodule.colon ((I.pullback π h.contMDiff).stalkIdeal p)
        (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal p ^ k)) := by
    refine Monotone.directed_le fun a b hab => Submodule.colon_mono le_rfl ?_
    exact SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right hab)
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hx
  refine Submodule.mem_iSup_of_mem (m + k) (Submodule.mem_colon.mpr fun q hq => ?_)
  rw [SetLike.mem_coe, hu, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hq
  obtain ⟨a, rfl⟩ := hq
  have h1 : x * u ^ m * u ^ k ∈ (I.pullback π h.contMDiff).stalkIdeal p := by
    have := Submodule.mem_colon.mp hk (u ^ k) (by
      rw [SetLike.mem_coe, hu, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _)
    simpa only [smul_eq_mul] using this
  have h2 : x • (a * u ^ (m + k)) = a * (x * u ^ m * u ^ k) := by
    rw [smul_eq_mul, pow_add]; ring
  rw [h2]
  exact Ideal.mul_mem_left _ a h1

include hI in
/-- (S) core: at a point `p ∈ S'` the saturation of `σ|_{S'}^*(I|_S)` by the exceptional
divisor of `S' → S` is the IMAGE of the saturation of `σ^*I` under the surjective restriction
`𝒪_{M',p} → 𝒪_{S',p}` (`germMap_inclusionMap_surjective`): `k = 0` is the pull-back identity,
`k ≥ 1` the colon step `(σ^*I : 𝓘_E^k) ↦ (σ^*I|_{S'} : 𝓘_{E_S}^k)` with (A) at the step —
`𝓘_{S'} ≤ Sat_X(I)` from `𝓘_{S'} · 𝓘_E = σ^*𝓘_S ≤ σ^*I` — as the input that lets the kernel drop
out. -/
theorem saturationStalk_restrictMap_eq_map
    (p : (hS.strictTransform hY h hYS).toAnalyticManifold) :
    saturationStalk (hS.preimage_val_of_subset hY hYS)
        (isBlowUp_restrictMap hS hY h hYS)
        (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) p =
      Ideal.map (germMap ⇑(hS.strictTransform hY h hYS).inclusionMap
          (hS.strictTransform hY h hYS).inclusionMap.contMDiff p)
        (saturationStalk hY h I ((hS.strictTransform hY h hYS).inclusionMap p)) := by
  have hS' := hS.strictTransform hY h hYS
  have hπS : ∀ x ∈ strictTransformSet π Y S, π x ∈ S :=
    strictTransform_subset_preimage h.contMDiff.continuous hS.isClosed
  set ρ := germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p with hρ
  have hρs : Function.Surjective ρ := hS'.germMap_inclusionMap_surjective p
  have hker : RingHom.ker ρ = hS'.idealSheaf.stalkIdeal (hS'.inclusionMap p) := by
    rw [hρ, hS'.germMap_inclusionMap p]
    exact (hS'.stalkIdeal_idealSheaf_of_mem p.2).symm
  have hK : hS'.idealSheaf.stalkIdeal (hS'.inclusionMap p) ≤
      saturationStalk hY h I (hS'.inclusionMap p) :=
    idealSheaf_strictTransform_stalkIdeal_le_saturationStalk_of_le hS hY h hYS I hI _
  have hTle : (I.pullback π h.contMDiff).stalkIdeal (hS'.inclusionMap p) ≤
      saturationStalk hY h I (hS'.inclusionMap p) :=
    totalTransform_stalkIdeal_le_saturationStalk hY h I _
  have hsquare : ⇑hS.inclusionMap ∘ ⇑(hS'.restrictMap hS π h.contMDiff hπS) =
      π ∘ ⇑hS'.inclusionMap :=
    funext fun q => hS'.restrictMap_apply hS π h.contMDiff hπS q
  have hT : (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).pullback _
      (isBlowUp_restrictMap hS hY h hYS).contMDiff =
      (I.pullback π h.contMDiff).pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff := by
    change (I.pullback _ _).pullback _ _ = (I.pullback π h.contMDiff).pullback _ _
    rw [IdealSheaf.pullback_pullback, IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr I _ _ hsquare
  have hEx : (hS.preimage_val_of_subset hY hYS).idealSheaf.pullback _
      (isBlowUp_restrictMap hS hY h hYS).contMDiff =
      (hY.idealSheaf.pullback π h.contMDiff).pullback ⇑hS'.inclusionMap
        hS'.inclusionMap.contMDiff := by
    change (hS.preimage_val_of_subset hY hYS).idealSheaf.pullback _ _ =
      (hY.idealSheaf.pullback π h.contMDiff).pullback _ _
    rw [idealSheaf_preimageVal_eq_pullback hS hY hYS, IdealSheaf.pullback_pullback,
      IdealSheaf.pullback_pullback]
    exact IdealSheaf.pullback_congr _ _ _ hsquare
  obtain ⟨u, hu⟩ := exists_stalkIdeal_totalTransform_self_eq_span_singleton hY h
    (hS'.inclusionMap p)
  have hu' : (hY.idealSheaf.pullback π h.contMDiff).stalkIdeal (hS'.inclusionMap p) =
      Ideal.span {u} := hu
  -- the saturation on `S'`, written out with the principal generator
  set T := (I.pullback π h.contMDiff).stalkIdeal (hS'.inclusionMap p) with hTdef
  have hSatS : saturationStalk (hS.preimage_val_of_subset hY hYS)
      (isBlowUp_restrictMap hS hY h hYS)
      (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) p =
      ⨆ k : ℕ, Submodule.colon (Ideal.map ρ T) (SetLike.coe (Ideal.span {ρ u ^ k})) := by
    unfold saturationStalk
    rw [hT, hEx,
      IdealSheaf.stalkIdeal_pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff
        (I.pullback π h.contMDiff) p,
      IdealSheaf.stalkIdeal_pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff
        (hY.idealSheaf.pullback π h.contMDiff) p,
      hu', Ideal.map_span, Set.image_singleton]
    simp only [Ideal.span_singleton_pow]
    rfl
  have hdir : Directed (· ≤ ·) fun k : ℕ =>
      Submodule.colon T (SetLike.coe ((hY.idealSheaf.pullback π h.contMDiff).stalkIdeal
        (hS'.inclusionMap p) ^ k)) := by
    refine Monotone.directed_le fun a b hab => Submodule.colon_mono le_rfl ?_
    exact SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right hab)
  refine le_antisymm ?_ ?_
  · -- a member of `(ρ T : ρ(u)^k)` is the image of a member of the saturation
    rw [hSatS]
    refine iSup_le fun k => ?_
    intro y hy
    obtain ⟨x, rfl⟩ := hρs y
    have hxu : ρ (x * u ^ k) ∈ Ideal.map ρ T := by
      have := Submodule.mem_colon.mp hy (ρ u ^ k) (by
        rw [SetLike.mem_coe]; exact Ideal.mem_span_singleton_self _)
      rw [smul_eq_mul] at this
      rw [map_mul, map_pow]
      exact this
    obtain ⟨t, ht, hte⟩ := (Ideal.mem_map_iff_of_surjective ρ hρs).mp hxu
    have hker' : x * u ^ k - t ∈ saturationStalk hY h I (hS'.inclusionMap p) := by
      refine hK ?_
      rw [← hker, RingHom.mem_ker, map_sub, hte, sub_self]
    have hsat : x * u ^ k ∈ saturationStalk hY h I (hS'.inclusionMap p) := by
      have := Ideal.add_mem _ hker' (hTle ht)
      rwa [sub_add_cancel] at this
    exact Ideal.mem_map_of_mem ρ (mem_saturationStalk_of_pow_mul_mem hY h I hu' hsat)
  · -- the image of the saturation lies in the saturation on `S'`
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, hSatS]
    obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hx
    refine Submodule.mem_iSup_of_mem k (Submodule.mem_colon.mpr fun q hq => ?_)
    rw [SetLike.mem_coe, Ideal.mem_span_singleton'] at hq
    obtain ⟨a, rfl⟩ := hq
    have hxT : x * u ^ k ∈ T := by
      have := Submodule.mem_colon.mp hk (u ^ k) (by
        rw [SetLike.mem_coe, hu', Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self _)
      simpa only [smul_eq_mul] using this
    have h2 : ρ x • (a * ρ u ^ k) = a * ρ (x * u ^ k) := by
      rw [smul_eq_mul, map_mul, map_pow]; ring
    rw [h2]
    exact Ideal.mul_mem_left _ a (Ideal.mem_map_of_mem ρ hxT)

include hI in
/-- (S′) core: the saturation of `σ^*I` at `p ∈ S'` is the PREIMAGE of the saturation on `S'` (it
contains the kernel `𝓘_{S'}` by (A)). -/
theorem comap_saturationStalk_restrictMap
    (p : (hS.strictTransform hY h hYS).toAnalyticManifold) :
    Ideal.comap (germMap ⇑(hS.strictTransform hY h hYS).inclusionMap
          (hS.strictTransform hY h hYS).inclusionMap.contMDiff p)
        (saturationStalk (hS.preimage_val_of_subset hY hYS)
          (isBlowUp_restrictMap hS hY h hYS)
          (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) p) =
      saturationStalk hY h I ((hS.strictTransform hY h hYS).inclusionMap p) := by
  have hS' := hS.strictTransform hY h hYS
  have hρs := hS'.germMap_inclusionMap_surjective p
  rw [saturationStalk_restrictMap_eq_map hS hY h hYS I hI p, Ideal.comap_map_of_surjective _ hρs]
  refine sup_eq_left.mpr fun x hx => ?_
  have hx0 : germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p x = 0 :=
    (Ideal.mem_bot).mp (Ideal.mem_comap.mp hx)
  rw [hS'.germMap_inclusionMap p] at hx0
  have hxK : x ∈ hS'.idealSheaf.stalkIdeal (hS'.inclusionMap p) :=
    (congrArg (x ∈ ·) (hS'.stalkIdeal_idealSheaf_of_mem p.2)).mpr ((RingHom.mem_ker).mpr hx0)
  exact idealSheaf_strictTransform_stalkIdeal_le_saturationStalk_of_le hS hY h hYS I hI _ hxK

include hI in
/-- (C) core, the BRANCH COINCIDENCE of the `if` in `strictTransformSubspace`: the saturation of
`σ^*I` on `M'` has local generators iff the saturation of `σ|_{S'}^*(I|_S)` on `S'` has —
generators LIFT (the `S'`-generators' local representatives along the closed embedding, together
with the adapted coordinates generating `𝓘_{S'}`, which also give `⊤` at the nearby points off
`S'`) and RESTRICT (the restriction is surjective on stalks, `ρ(ρ⁻¹ J) = J`). No finite-type input
is needed. -/
theorem hasLocalGenerators_saturationStalk_restrictMap_iff :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M') (saturationStalk hY h I) ↔
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin (n - s) → 𝕜) (hS.strictTransform hY h hYS).toAnalyticManifold)
        (saturationStalk (hS.preimage_val_of_subset hY hYS)
          (isBlowUp_restrictMap hS hY h hYS)
          (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)) := by
  have hS' := hS.strictTransform hY h hYS
  set 𝒪' := structureSheaf 𝕜 E M' with h𝒪'
  constructor
  · -- restrict the generators
    intro hX
    have e : saturationStalk (hS.preimage_val_of_subset hY hYS)
        (isBlowUp_restrictMap hS hY h hYS)
        (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) = fun p =>
          Ideal.map (germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff p)
            ((IdealSheaf.ofStalks _ _ hX).stalkIdeal (hS'.inclusionMap p)) := by
      funext p
      rw [saturationStalk_restrictMap_eq_map hS hY h hYS I hI p, IdealSheaf.stalkIdeal_ofStalks]
    rw [e]
    exact hasLocalGenerators_pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff _
  · -- lift the generators
    intro hSg a
    by_cases ha : a ∈ strictTransformSet π Y S
    · -- the generators of the saturation on `S'` near `p₀ = a`, and their lifts
      set p₀ : hS'.toAnalyticManifold := ⟨a, ha⟩ with hp₀
      obtain ⟨W, hp₀W, k, f, hf⟩ := hSg.exists_fin p₀
      -- lift the germs at `p₀`
      have hsurj := hS'.germMap_inclusionMap_surjective p₀
      choose g₀ hg₀ using fun i =>
        hsurj ((structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.germ W p₀ hp₀W
          (f i))
      choose V hV gs hgs using fun i => 𝒪'.presheaf.exists_germ_eq (g₀ i)
      -- the generators of `𝓘_{S'}` near `a`
      obtain ⟨U₀, haU₀, k₀, kf, -, hkf⟩ := hS'.idealSheaf.exists_generators a
      -- the common open `V₀ ∋ a` of the lifts
      let V₀ : Opens M' := ⟨⋂ i, (V i : Set M'), isOpen_iInter_of_finite fun i => (V i).2⟩
      have haV₀ : a ∈ V₀ := Set.mem_iInter.mpr hV
      have hV₀V : ∀ i, V₀ ≤ V i := fun i x hx => Set.mem_iInter.mp hx i
      -- on `S'`, the restricted lifts agree with the `f i` near `p₀`
      have hagree : ∀ i, ∃ (W' : Opens hS'.toAnalyticManifold) (_ : p₀ ∈ W') (iW : W' ⟶ W)
          (iV : W' ⟶ preimageOpens ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff (V i)),
          (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.map iW.op (f i) =
            (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.map iV.op
              (comapSection ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff (gs i)) := by
        intro i
        have e1 : (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.germ W p₀
            hp₀W (f i) =
            (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.germ
              (preimageOpens ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff (V i)) p₀
              ((mem_preimageOpens _ _).mpr (hV i))
              (comapSection ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff (gs i)) := by
          rw [← germMap_germ ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff (hV i) (gs i), hgs i,
            hg₀ i]
        obtain ⟨W', hp₀W', iW, iV, hW'⟩ :=
          (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.germ_eq p₀ hp₀W
            ((mem_preimageOpens _ _).mpr (hV i)) _ _ e1
        exact ⟨W', hp₀W', iW, iV, hW'⟩
      choose W' hp₀W' iW iV hW' using hagree
      -- the common open `W₀ ∋ p₀` of `S'`, and an open `V'` of `M'` cutting it out
      let W₀ : Opens hS'.toAnalyticManifold :=
        ⟨(W : Set hS'.toAnalyticManifold) ∩ ⋂ i, (W' i : Set hS'.toAnalyticManifold),
          W.2.inter (isOpen_iInter_of_finite fun i => (W' i).2)⟩
      have hp₀W₀ : p₀ ∈ W₀ := ⟨hp₀W, Set.mem_iInter.mpr hp₀W'⟩
      have hW₀W : W₀ ≤ W := fun x hx => hx.1
      have hW₀W' : ∀ i, W₀ ≤ W' i := fun i x hx => Set.mem_iInter.mp hx.2 i
      obtain ⟨V', hV'open, hV'⟩ := isOpen_induced_iff.mp W₀.2
      have haV' : a ∈ V' := by
        have : p₀ ∈ (Subtype.val ⁻¹' V' : Set hS'.toAnalyticManifold) := by rw [hV']; exact hp₀W₀
        exact this
      -- the open `U ∋ a` on which the lifted generators live
      let U : Opens M' := ⟨(V₀ : Set M') ∩ U₀ ∩ V', (V₀.2.inter U₀.2).inter hV'open⟩
      have haU : a ∈ U := ⟨⟨haV₀, haU₀⟩, haV'⟩
      have hUV₀ : U ≤ V₀ := fun x hx => hx.1.1
      have hUU₀ : U ≤ U₀ := fun x hx => hx.1.2
      refine ⟨U, haU, Fin k ⊕ Fin k₀, inferInstance, Sum.elim
        (fun i => 𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i))
        (fun j => 𝒪'.presheaf.map (homOfLE hUU₀).op (kf j)), fun b hb => ?_⟩
      -- the kernel generators at `b`
      have hres : (fun j => 𝒪'.presheaf.germ U b hb (𝒪'.presheaf.map (homOfLE hUU₀).op (kf j))) =
          fun j => 𝒪'.presheaf.germ U₀ b (hUU₀ hb) (kf j) :=
        funext fun j => TopCat.Presheaf.germ_res_apply 𝒪'.presheaf (homOfLE hUU₀) b hb (kf j)
      have hKb : hS'.idealSheaf.stalkIdeal b = Ideal.span (Set.range fun j =>
          𝒪'.presheaf.germ U b hb (𝒪'.presheaf.map (homOfLE hUU₀).op (kf j))) := by
        rw [hkf b (hUU₀ hb), hres]
      have hsum : (fun i : Fin k ⊕ Fin k₀ => 𝒪'.presheaf.germ U b hb
          (Sum.elim (fun i => 𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i))
            (fun j => 𝒪'.presheaf.map (homOfLE hUU₀).op (kf j)) i)) =
          Sum.elim (fun i => 𝒪'.presheaf.germ U b hb
              (𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i)))
            (fun j => 𝒪'.presheaf.germ U b hb (𝒪'.presheaf.map (homOfLE hUU₀).op (kf j))) :=
        funext fun i => by rcases i with i | j <;> rfl
      have hspan : Ideal.span (Set.range fun i : Fin k ⊕ Fin k₀ => 𝒪'.presheaf.germ U b hb
          (Sum.elim (fun i => 𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i))
            (fun j => 𝒪'.presheaf.map (homOfLE hUU₀).op (kf j)) i)) =
          Ideal.span (Set.range fun i => 𝒪'.presheaf.germ U b hb
            (𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i))) ⊔
          hS'.idealSheaf.stalkIdeal b := by
        rw [hKb, ← Ideal.span_union, ← Set.Sum.elim_range, hsum]
      by_cases hb' : b ∈ strictTransformSet π Y S
      · -- on `S'`: the saturation is the preimage of the `S'`-saturation, generated by the lifts
        obtain ⟨q, rfl⟩ : ∃ q : hS'.toAnalyticManifold, hS'.inclusionMap q = b := ⟨⟨b, hb'⟩, rfl⟩
        have hqW₀ : q ∈ W₀ := by
          have : q ∈ (Subtype.val ⁻¹' V' : Set hS'.toAnalyticManifold) := hb.2
          rwa [hV'] at this
        have hqW : q ∈ W := hW₀W hqW₀
        set ρq := germMap ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff q with hρq
        have hρqs : Function.Surjective ρq := hS'.germMap_inclusionMap_surjective q
        have hgerm : ∀ i,
            (structureSheaf 𝕜 (Fin (n - s) → 𝕜) hS'.toAnalyticManifold).presheaf.germ W q hqW
              (f i) = ρq (𝒪'.presheaf.germ U (hS'.inclusionMap q) hb
                (𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i))) := by
          intro i
          have hqW' : q ∈ W' i := hW₀W' i hqW₀
          rw [TopCat.Presheaf.germ_res_apply]
          have e2 := germMap_germ ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff (b := q) (U := V i)
            (hV₀V i (hUV₀ hb)) (gs i)
          refine Eq.trans ?_ e2.symm
          rw [← TopCat.Presheaf.germ_res_apply _ (iW i) q hqW' (f i), hW' i,
            TopCat.Presheaf.germ_res_apply]
        have hgerm' : (fun i => (structureSheaf 𝕜 (Fin (n - s) → 𝕜)
            hS'.toAnalyticManifold).presheaf.germ W q hqW (f i)) =
            ρq ∘ fun i => 𝒪'.presheaf.germ U (hS'.inclusionMap q) hb
              (𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i)) :=
          funext hgerm
        set G := Ideal.span (Set.range fun i => 𝒪'.presheaf.germ U (hS'.inclusionMap q) hb
          (𝒪'.presheaf.map (homOfLE (hUV₀.trans (hV₀V i))).op (gs i))) with hG
        have hSq : saturationStalk (hS.preimage_val_of_subset hY hYS)
            (isBlowUp_restrictMap hS hY h hYS)
            (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) q = Ideal.map ρq G := by
          rw [hf q hqW, hgerm', hG, Ideal.map_span, Set.range_comp]
        have hX : saturationStalk hY h I (hS'.inclusionMap q) = Ideal.comap ρq (saturationStalk
            (hS.preimage_val_of_subset hY hYS)
            (isBlowUp_restrictMap hS hY h hYS)
            (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) q) :=
          (comap_saturationStalk_restrictMap hS hY h hYS I hI q).symm
        have hkq : RingHom.ker ρq = hS'.idealSheaf.stalkIdeal (hS'.inclusionMap q) := by
          rw [hρq, hS'.germMap_inclusionMap q]
          exact (hS'.stalkIdeal_idealSheaf_of_mem q.2).symm
        have hkq' : Ideal.comap ρq ⊥ = hS'.idealSheaf.stalkIdeal (hS'.inclusionMap q) :=
          (RingHom.ker_eq_comap_bot ρq).symm.trans hkq
        refine (hX.trans (congrArg (Ideal.comap ρq) hSq)).trans ?_
        refine (Ideal.comap_map_of_surjective ρq hρqs G).trans ?_
        exact (congrArg (G ⊔ ·) hkq').trans hspan.symm
      · -- off `S'`: both sides are the unit ideal
        rw [saturationStalk_eq_top_of_notMem_strictTransform_of_le hS hY h hYS I hI hb', hspan,
          hS'.stalkIdeal_idealSheaf_of_notMem hb', sup_top_eq]
    · -- off `S'` the saturation is `⊤` on the open `S'ᶜ`, generated by `1`
      refine ⟨⟨(strictTransformSet π Y S)ᶜ, hS'.isClosed.isOpen_compl⟩, ha, Unit, inferInstance,
        fun _ => 1, fun b hb => ?_⟩
      rw [saturationStalk_eq_top_of_notMem_strictTransform_of_le hS hY h hYS I hI hb,
        Set.range_const, map_one, Ideal.span_singleton_one]

include hI in
/-- (B) core, UNCONDITIONAL ([Kol07, Definitions 30.2–30.3]): the strict transform of `I ⊇ 𝓘_S`
under `σ = Bl_Y M → M`, restricted to the strict transform `S' = Bl_Y S`, is the strict transform
of `I|_S` under the restricted blowing-up `σ|_{S'} : S' → S` — in the `then` branches by (S), in
the `else` branches by `⊤` pulling back to `⊤`, the branches coinciding by (C). -/
theorem strictTransformSubspace_pullback_inclusionMap :
    (strictTransformSubspace hY h I).pullback ⇑(hS.strictTransform hY h hYS).inclusionMap
        (hS.strictTransform hY h hYS).inclusionMap.contMDiff =
      strictTransformSubspace (hS.preimage_val_of_subset hY hYS)
        (isBlowUp_restrictMap hS hY h hYS)
        (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) := by
  by_cases hex : IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E M')
    (saturationStalk hY h I)
  · have hex' := (hasLocalGenerators_saturationStalk_restrictMap_iff hS hY h hYS I hI).mp hex
    refine IdealSheaf.ext fun p => ?_
    rw [IdealSheaf.stalkIdeal_pullback, stalkIdeal_strictTransformSubspace_of_hasLocalGenerators
      _ _ _ hex, stalkIdeal_strictTransformSubspace_of_hasLocalGenerators _ _ _ hex',
      saturationStalk_restrictMap_eq_map hS hY h hYS I hI p]
  · have hex' := fun h' =>
      hex ((hasLocalGenerators_saturationStalk_restrictMap_iff hS hY h hYS I hI).mpr h')
    rw [strictTransformSubspace_of_not_hasLocalGenerators _ _ _ hex,
      strictTransformSubspace_of_not_hasLocalGenerators _ _ _ hex']
    exact IdealSheaf.pullback_top _ _

end PushforwardStep

end Hironaka.Manifold


/-! ### Along the push-forward `j_* T` of a sequence of the bundled `S` -/

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {S : Set M} {s : ℕ}
  (hS : IsClosedSubmanifold ψ S s) (T : FiniteSuccession hS.toAnalyticManifold)

/-- The carried `S_i = j_i(T_i) ⊆ X_i` as a closed submanifold of the stage `X_i` of the
push-forward, typed on the stage (the `pushforwardAux` witness, read through `range_incl`). -/
theorem isClosedSubmanifold_range_pushforwardIncl (i : Fin (T.length + 1)) :
    IsClosedSubmanifold ψ (Set.range (T.pushforwardIncl hS i)) s := by
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · change IsClosedSubmanifold ψ (Set.range (T.pushforwardAux hS 0 hi).incl) s
    rw [(T.pushforwardAux hS 0 hi).range_incl]
    exact (T.pushforwardAux hS 0 hi).isClosedSubmanifold
  · change IsClosedSubmanifold ψ (Set.range (T.pushforwardAux hS (i + 1) hi).incl) s
    rw [(T.pushforwardAux hS (i + 1) hi).range_incl]
    exact (T.pushforwardAux hS (i + 1) hi).isClosedSubmanifold

variable (I : IdealSheaf M)

/-- One step of the chain, on a stage datum `P` at the given stage `T_j` (`PushforwardStage`; the
induction instantiates `P := pushforwardAux j`): from the strict transform `Yt` of `I` on
`P.space` containing `𝓘_{S_j}` and restricting to the `T`-chain's `Y_j`, the same two facts on
`P.blowUpStep` — the core (A)/(B) at `P` and the diffeomorphism square (Q) from the restricted
blow-down to the given `T.map j`. -/
theorem strictTransformSubspaceSeq_pushforward_step (j : ℕ) (hj : j < T.length)
    (P : PushforwardStage ψ s (T.stage (⟨j, hj⟩ : Fin T.length).castSucc)) (Yt : IdealSheaf P.space)
    (hle : P.isClosedSubmanifold.idealSheaf ≤ Yt)
    (hIH : Yt.pullback ⇑P.incl P.incl.contMDiff =
      T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
        (⟨j, hj⟩ : Fin T.length).castSucc) :
    ((strictTransformSubspace
      (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))
          (isBlowUp_blowUpπ ψ
            (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj)))
          Yt).pullback
        ⇑(P.isClosedSubmanifold.strictTransform
          (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))
          (isBlowUp_blowUpπ ψ
            (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj)))
          (P.isClosedSubmanifold.imageVal_subset _)).inclusionMap
        (P.isClosedSubmanifold.strictTransform
          (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))
          (isBlowUp_blowUpπ ψ
            (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj)))
          (P.isClosedSubmanifold.imageVal_subset _)).inclusionMap.contMDiff).pullback
        ⇑(Diffeomorph.toAnalyticMap (IsBlowUp.diffeomorph
          ((T.pushforwardCenterSub hS j hj).image_diffeomorph P.iso)
          ((T.pushforwardIsBlowUp hS j hj).diffeomorph_comp P.iso)
          (P.isBlowUp_restrictMap_imageVal (T.pushforwardCenterSub hS j hj))))
        (Diffeomorph.toAnalyticMap (IsBlowUp.diffeomorph
          ((T.pushforwardCenterSub hS j hj).image_diffeomorph P.iso)
          ((T.pushforwardIsBlowUp hS j hj).diffeomorph_comp P.iso)
          (P.isBlowUp_restrictMap_imageVal (T.pushforwardCenterSub hS j hj)))).contMDiff =
      T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
        (⟨j, hj⟩ : Fin T.length).succ ∧
    (P.isClosedSubmanifold.strictTransform
        (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))
        (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj)))
        (P.isClosedSubmanifold.imageVal_subset _)).idealSheaf ≤
      strictTransformSubspace
        (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))
        (isBlowUp_blowUpπ ψ (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj)))
        Yt := by
  have hZ := T.pushforwardCenterSub hS j hj
  have hπ := T.pushforwardIsBlowUp hS j hj
  have hZX := P.isClosedSubmanifold_imageVal_image hZ
  have hsub : P.isClosedSubmanifold.imageVal (P.iso '' (T.center ⟨j, hj⟩).support) ⊆ P.sub :=
    P.isClosedSubmanifold.imageVal_subset _
  have hS' := P.isClosedSubmanifold.strictTransform hZX (isBlowUp_blowUpπ ψ hZX) hsub
  refine ⟨?_, idealSheaf_strictTransform_le_strictTransformSubspace P.isClosedSubmanifold hZX
    (isBlowUp_blowUpπ ψ hZX) hsub Yt hle⟩
  -- the core (B) on the inner pull-back, then the witnesses of the restricted blow-down
  have e1 := congrArg (fun X : IdealSheaf hS'.toAnalyticManifold =>
      X.pullback ⇑(Diffeomorph.toAnalyticMap (IsBlowUp.diffeomorph (hZ.image_diffeomorph P.iso)
        (hπ.diffeomorph_comp P.iso) (P.isBlowUp_restrictMap_imageVal hZ)))
        (Diffeomorph.toAnalyticMap (IsBlowUp.diffeomorph (hZ.image_diffeomorph P.iso)
          (hπ.diffeomorph_comp P.iso) (P.isBlowUp_restrictMap_imageVal hZ))).contMDiff)
    ((strictTransformSubspace_pullback_inclusionMap P.isClosedSubmanifold hZX
      (isBlowUp_blowUpπ ψ hZX) hsub Yt hle).trans (strictTransformSubspace_congr
        (P.isClosedSubmanifold.preimage_val_of_subset hZX hsub)
        (isBlowUp_restrictMap P.isClosedSubmanifold hZX (isBlowUp_blowUpπ ψ hZX) hsub)
        (hZ.image_diffeomorph P.iso) (P.isBlowUp_restrictMap_imageVal hZ)
        (P.isClosedSubmanifold.preimageVal_imageVal _) _))
  -- the diffeomorphism square `e_{j+1}` over `e_j`
  have hsqr := strictTransformSubspace_comap_of_diffeomorph_square hZ hπ
    (hZ.image_diffeomorph P.iso) (P.isBlowUp_restrictMap_imageVal hZ) P.iso rfl
    (IsBlowUp.diffeomorph (hZ.image_diffeomorph P.iso) (hπ.diffeomorph_comp P.iso)
      (P.isBlowUp_restrictMap_imageVal hZ)) (fun p => P.restrictMap_blowUpStep_iso hZ hπ p)
    (Yt.pullback ⇑P.isClosedSubmanifold.inclusionMap P.isClosedSubmanifold.inclusionMap.contMDiff)
  -- `Yt|_{S_j}` pulled back along `e_j` is `Yt` pulled back along `incl_j`
  have hincl' : ⇑P.isClosedSubmanifold.inclusionMap ∘ ⇑(Diffeomorph.toAnalyticMap P.iso) =
      ⇑P.incl :=
    (funext fun p => P.incl_apply p).symm
  have e3 : (Yt.pullback ⇑P.isClosedSubmanifold.inclusionMap
        P.isClosedSubmanifold.inclusionMap.contMDiff).pullback _ (Diffeomorph.toAnalyticMap
            P.iso).contMDiff =
      T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
        (⟨j, hj⟩ : Fin T.length).castSucc :=
    (IdealSheaf.pullback_pullback Yt _ _ _ _).trans
      ((IdealSheaf.pullback_congr Yt _ P.incl.contMDiff hincl').trans hIH)
  exact e1.trans (hsqr.trans ((congrArg (strictTransformSubspace hZ hπ) e3).trans
    (strictTransformSubspace_congr hZ hπ (T.isClosedSubmanifold_center ⟨j, hj⟩)
      (T.isBlowUp_map ⟨j, hj⟩) rfl _)))

/-- One step of the branch coincidence along the chain, on a stage datum `P` at `T_j`: the core
(C) at `P`, the restricted blow-down's witnesses read as `isBlowUp_restrictMap_imageVal`'s, and
the square (Q) to the given `T.map j`. -/
theorem hasLocalGenerators_saturationStalk_pushforward_step (j : ℕ) (hj : j < T.length)
    (P : PushforwardStage ψ s (T.stage (⟨j, hj⟩ : Fin T.length).castSucc)) (Yt : IdealSheaf P.space)
    (hle : P.isClosedSubmanifold.idealSheaf ≤ Yt)
    (hIH : Yt.pullback ⇑P.incl P.incl.contMDiff =
      T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
        (⟨j, hj⟩ : Fin T.length).castSucc) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E (Manifold.blowUp ψ
          (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))))
        (saturationStalk (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj))
          (isBlowUp_blowUpπ ψ
            (P.isClosedSubmanifold_imageVal_image (T.pushforwardCenterSub hS j hj)))
          Yt) ↔
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin (n - s) → 𝕜) (T.stage (⟨j, hj⟩ : Fin T.length).succ))
        (saturationStalk (T.isClosedSubmanifold_center ⟨j, hj⟩) (T.isBlowUp_map ⟨j, hj⟩)
          (T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
            (⟨j, hj⟩ : Fin T.length).castSucc)) := by
  have hZ := T.pushforwardCenterSub hS j hj
  have hπ := T.pushforwardIsBlowUp hS j hj
  have hZX := P.isClosedSubmanifold_imageVal_image hZ
  have hsub : P.isClosedSubmanifold.imageVal (P.iso '' (T.center ⟨j, hj⟩).support) ⊆ P.sub :=
    P.isClosedSubmanifold.imageVal_subset _
  have hcore := hasLocalGenerators_saturationStalk_restrictMap_iff P.isClosedSubmanifold hZX
    (isBlowUp_blowUpπ ψ hZX) hsub Yt hle
  have hwS : saturationStalk (P.isClosedSubmanifold.preimage_val_of_subset hZX hsub)
      (isBlowUp_restrictMap P.isClosedSubmanifold hZX (isBlowUp_blowUpπ ψ hZX) hsub)
      (Yt.pullback ⇑P.isClosedSubmanifold.inclusionMap
        P.isClosedSubmanifold.inclusionMap.contMDiff) =
      saturationStalk (hZ.image_diffeomorph P.iso) (P.isBlowUp_restrictMap_imageVal hZ)
        (Yt.pullback ⇑P.isClosedSubmanifold.inclusionMap
          P.isClosedSubmanifold.inclusionMap.contMDiff) :=
    saturationStalk_congr _ _ _ _ (P.isClosedSubmanifold.preimageVal_imageVal _) _
  have hsqr := hasLocalGenerators_saturationStalk_comap_of_diffeomorph_square_iff hZ hπ
    (hZ.image_diffeomorph P.iso) (P.isBlowUp_restrictMap_imageVal hZ) P.iso rfl
    (IsBlowUp.diffeomorph (hZ.image_diffeomorph P.iso) (hπ.diffeomorph_comp P.iso)
      (P.isBlowUp_restrictMap_imageVal hZ)) (fun p => P.restrictMap_blowUpStep_iso hZ hπ p)
    (Yt.pullback ⇑P.isClosedSubmanifold.inclusionMap P.isClosedSubmanifold.inclusionMap.contMDiff)
  have hincl' : ⇑P.isClosedSubmanifold.inclusionMap ∘ ⇑(Diffeomorph.toAnalyticMap P.iso) =
      ⇑P.incl :=
    (funext fun p => P.incl_apply p).symm
  have hJ : (Yt.pullback ⇑P.isClosedSubmanifold.inclusionMap
        P.isClosedSubmanifold.inclusionMap.contMDiff).pullback _ (Diffeomorph.toAnalyticMap
            P.iso).contMDiff =
      T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
        (⟨j, hj⟩ : Fin T.length).castSucc :=
    (IdealSheaf.pullback_pullback Yt _ _ _ _).trans
      ((IdealSheaf.pullback_congr Yt _ P.incl.contMDiff hincl').trans hIH)
  have hwT : saturationStalk hZ hπ (T.strictTransformSubspaceSeq
      (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) (⟨j, hj⟩ : Fin T.length).castSucc) =
      saturationStalk (T.isClosedSubmanifold_center ⟨j, hj⟩) (T.isBlowUp_map ⟨j, hj⟩)
        (T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
          (⟨j, hj⟩ : Fin T.length).castSucc) :=
    saturationStalk_congr _ _ _ _ rfl _
  exact hcore.trans ((Iff.of_eq (congrArg IdealSheaf.HasLocalGenerators hwS)).trans
    (hsqr.symm.trans ((Iff.of_eq (congrArg (fun J => IdealSheaf.HasLocalGenerators
      (saturationStalk hZ hπ J)) hJ)).trans
        (Iff.of_eq (congrArg IdealSheaf.HasLocalGenerators hwT)))))

variable (hI : hS.idealSheaf ≤ I)

include hI in
/-- The chain, ℕ-indexed: (B) ∧ (A) at every stage, by ONE induction on the stage ((B) at `i + 1`
needs (A) at `i` as the core's hypothesis and (B) at `i` for the identification of the inputs). -/
theorem strictTransformSubspaceSeq_pushforward_aux :
    ∀ (i : ℕ) (hi : i < T.length + 1),
      ((T.pushforward hS).strictTransformSubspaceSeq I ⟨i, hi⟩).pullback
          ⇑(T.pushforwardIncl hS ⟨i, hi⟩) (T.pushforwardIncl hS ⟨i, hi⟩).contMDiff =
        T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
          ⟨i, hi⟩ ∧
      (T.isClosedSubmanifold_range_pushforwardIncl hS ⟨i, hi⟩).idealSheaf ≤
        (T.pushforward hS).strictTransformSubspaceSeq I ⟨i, hi⟩
  | 0, hi => by
    refine ⟨?_, ?_⟩
    · exact IdealSheaf.pullback_congr I _ _
        (congrArg DFunLike.coe (T.pushforwardIncl_zero hS))
    · exact le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ hS
        (T.pushforwardAux hS 0 hi).range_incl) hI
  | i + 1, hi => by
    have hi' : i < T.length := Nat.lt_of_succ_lt_succ hi
    have ih := strictTransformSubspaceSeq_pushforward_aux i (Nat.lt_succ_of_lt hi')
    rcases i with _ | i
    · have hle : (T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).isClosedSubmanifold.idealSheaf ≤
          (T.pushforward hS).strictTransformSubspaceSeq I ⟨0, Nat.lt_succ_of_lt hi'⟩ :=
        le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ _
          (T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).range_incl.symm) ih.2
      have hstep := T.strictTransformSubspaceSeq_pushforward_step hS I 0 hi' _ _ hle ih.1
      have hw : (T.pushforward hS).strictTransformSubspaceSeq I ⟨0 + 1, hi⟩ =
          strictTransformSubspace (T.pushforwardCenterOfSub hS 0 hi')
            (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS 0 hi'))
            ((T.pushforward hS).strictTransformSubspaceSeq I ⟨0, Nat.lt_succ_of_lt hi'⟩) :=
        strictTransformSubspace_congr _ _ _ _ (T.support_pushforwardCenterOf hS 0 hi') _
      refine ⟨?_, ?_⟩
      · rw [hw]
        have hincl : ⇑(T.pushforwardIncl hS ⟨0 + 1, hi⟩) =
            ⇑((T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).isClosedSubmanifold.strictTransform
              (T.pushforwardCenterOfSub hS 0 hi')
              (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS 0 hi'))
              ((T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).isClosedSubmanifold.imageVal_subset
                _)).inclusionMap ∘
            ⇑(Diffeomorph.toAnalyticMap (IsBlowUp.diffeomorph
              ((T.pushforwardCenterSub hS 0 hi').image_diffeomorph
                (T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).iso)
              ((T.pushforwardIsBlowUp hS 0 hi').diffeomorph_comp
                (T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).iso)
              ((T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hi')).isBlowUp_restrictMap_imageVal
                (T.pushforwardCenterSub hS 0 hi')))) :=
          funext fun p => (T.pushforwardAux hS (0 + 1) hi).incl_apply p
        exact ((IdealSheaf.pullback_congr _ _ _ hincl).trans
          (IdealSheaf.pullback_pullback _ _ _ _ _).symm).trans hstep.1
      · rw [hw]
        exact le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ _
          (T.pushforwardAux hS (0 + 1) hi).range_incl) hstep.2
    · have hle :
          (T.pushforwardAux hS (i + 1) (Nat.lt_succ_of_lt hi')).isClosedSubmanifold.idealSheaf ≤
          (T.pushforward hS).strictTransformSubspaceSeq I ⟨i + 1, Nat.lt_succ_of_lt hi'⟩ :=
        le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ _
          (T.pushforwardAux hS (i + 1) (Nat.lt_succ_of_lt hi')).range_incl.symm) ih.2
      have hstep := T.strictTransformSubspaceSeq_pushforward_step hS I (i + 1) hi' _ _ hle ih.1
      have hw : (T.pushforward hS).strictTransformSubspaceSeq I ⟨i + 1 + 1, hi⟩ =
          strictTransformSubspace (T.pushforwardCenterOfSub hS (i + 1) hi')
            (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS (i + 1) hi'))
            ((T.pushforward hS).strictTransformSubspaceSeq I ⟨i + 1, Nat.lt_succ_of_lt hi'⟩) :=
        strictTransformSubspace_congr _ _ _ _ (T.support_pushforwardCenterOf hS (i + 1) hi') _
      refine ⟨?_, ?_⟩
      · rw [hw]
        have hincl : ⇑(T.pushforwardIncl hS ⟨i + 1 + 1, hi⟩) =
            ⇑((T.pushforwardAux hS (i + 1)
                (Nat.lt_succ_of_lt hi')).isClosedSubmanifold.strictTransform
              (T.pushforwardCenterOfSub hS (i + 1) hi')
              (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS (i + 1) hi'))
              ((T.pushforwardAux hS (i + 1)
                (Nat.lt_succ_of_lt hi')).isClosedSubmanifold.imageVal_subset
                _)).inclusionMap ∘
            ⇑(Diffeomorph.toAnalyticMap (IsBlowUp.diffeomorph
              ((T.pushforwardCenterSub hS (i + 1) hi').image_diffeomorph
                (T.pushforwardAux hS (i + 1) (Nat.lt_succ_of_lt hi')).iso)
              ((T.pushforwardIsBlowUp hS (i + 1) hi').diffeomorph_comp
                (T.pushforwardAux hS (i + 1) (Nat.lt_succ_of_lt hi')).iso)
              ((T.pushforwardAux hS (i + 1) (Nat.lt_succ_of_lt hi')).isBlowUp_restrictMap_imageVal
                (T.pushforwardCenterSub hS (i + 1) hi')))) :=
          funext fun p => (T.pushforwardAux hS (i + 1 + 1) hi).incl_apply p
        exact ((IdealSheaf.pullback_congr _ _ _ hincl).trans
          (IdealSheaf.pullback_pullback _ _ _ _ _).symm).trans hstep.1
      · rw [hw]
        exact le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ _
          (T.pushforwardAux hS (i + 1 + 1) hi).range_incl) hstep.2

include hI in
/-- (A) Along the push-forward `j_* T` [Kol07, Definition 30.3] the strict transform of `I ⊇ 𝓘_S`
stays inside the carried `S_i`: `𝓘_{S_i} ≤ Ỹ^X_i` at every stage (stage `0` is the
hypothesis). -/
theorem idealSheaf_range_pushforwardIncl_le_strictTransformSubspaceSeq (i : Fin (T.length + 1)) :
    (T.isClosedSubmanifold_range_pushforwardIncl hS i).idealSheaf ≤
      (T.pushforward hS).strictTransformSubspaceSeq I i :=
  (T.strictTransformSubspaceSeq_pushforward_aux hS I hI i.1 i.2).2

include hI in
/-- (B) UNCONDITIONAL ("for all practical purposes `Z_i^X = Z_i^S`", [Kol07, Definition 30.3]):
the strict transform of `I` along the push-forward, restricted to the carried `S_i` through
`j_i : T_i ↪ X_i`, is the strict transform of `I|_S` along `T` itself — one induction on the stage
with (C) (both chains take the same branch at each step; stage `0` is `J := I|_S`). -/
theorem strictTransformSubspaceSeq_pushforward_pullback_incl (i : Fin (T.length + 1)) :
    ((T.pushforward hS).strictTransformSubspaceSeq I i).pullback ⇑(T.pushforwardIncl hS i)
        (T.pushforwardIncl hS i).contMDiff =
      T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff) i :=
  (T.strictTransformSubspaceSeq_pushforward_aux hS I hI i.1 i.2).1

include hI in
/-- The branch coincidence along the chains, ℕ-indexed (the `Fin` form below): at step `j` the
saturation of the `X`-chain has local generators iff the saturation of the `S`-chain has. -/
theorem hasLocalGenerators_saturationStalk_pushforward_iff_aux (j : ℕ) (hj : j < T.length) :
    IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 E
          ((T.pushforward hS).stage (⟨j, hj⟩ : Fin (T.pushforward hS).length).succ))
        (saturationStalk ((T.pushforward hS).isClosedSubmanifold_center ⟨j, hj⟩)
          ((T.pushforward hS).isBlowUp_map ⟨j, hj⟩)
          ((T.pushforward hS).strictTransformSubspaceSeq I
            (⟨j, hj⟩ : Fin (T.pushforward hS).length).castSucc)) ↔
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin (n - s) → 𝕜) (T.stage (⟨j, hj⟩ : Fin T.length).succ))
        (saturationStalk (T.isClosedSubmanifold_center ⟨j, hj⟩) (T.isBlowUp_map ⟨j, hj⟩)
          (T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
            (⟨j, hj⟩ : Fin T.length).castSucc)) := by
  have ih := T.strictTransformSubspaceSeq_pushforward_aux hS I hI j (Nat.lt_succ_of_lt hj)
  rcases j with _ | j
  · have hle : (T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hj)).isClosedSubmanifold.idealSheaf ≤
        (T.pushforward hS).strictTransformSubspaceSeq I ⟨0, Nat.lt_succ_of_lt hj⟩ :=
      le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ _
        (T.pushforwardAux hS 0 (Nat.lt_succ_of_lt hj)).range_incl.symm) ih.2
    have hstep := T.hasLocalGenerators_saturationStalk_pushforward_step hS I 0 hj _ _ hle ih.1
    have hw : saturationStalk ((T.pushforward hS).isClosedSubmanifold_center ⟨0, hj⟩)
        ((T.pushforward hS).isBlowUp_map ⟨0, hj⟩)
        ((T.pushforward hS).strictTransformSubspaceSeq I
          (⟨0, hj⟩ : Fin (T.pushforward hS).length).castSucc) =
        saturationStalk (T.pushforwardCenterOfSub hS 0 hj)
          (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS 0 hj))
          ((T.pushforward hS).strictTransformSubspaceSeq I
            (⟨0, hj⟩ : Fin (T.pushforward hS).length).castSucc) :=
      saturationStalk_congr _ _ _ _ (T.support_pushforwardCenterOf hS 0 hj) _
    rw [hw]
    exact hstep
  · have hle : (T.pushforwardAux hS (j + 1) (Nat.lt_succ_of_lt hj)).isClosedSubmanifold.idealSheaf ≤
        (T.pushforward hS).strictTransformSubspaceSeq I ⟨j + 1, Nat.lt_succ_of_lt hj⟩ :=
      le_of_eq_of_le (IsClosedSubmanifold.idealSheaf_congr _ _
        (T.pushforwardAux hS (j + 1) (Nat.lt_succ_of_lt hj)).range_incl.symm) ih.2
    have hstep := T.hasLocalGenerators_saturationStalk_pushforward_step hS I (j + 1) hj _ _ hle ih.1
    have hw : saturationStalk ((T.pushforward hS).isClosedSubmanifold_center ⟨j + 1, hj⟩)
        ((T.pushforward hS).isBlowUp_map ⟨j + 1, hj⟩)
        ((T.pushforward hS).strictTransformSubspaceSeq I
          (⟨j + 1, hj⟩ : Fin (T.pushforward hS).length).castSucc) =
        saturationStalk (T.pushforwardCenterOfSub hS (j + 1) hj)
          (isBlowUp_blowUpπ ψ (T.pushforwardCenterOfSub hS (j + 1) hj))
          ((T.pushforward hS).strictTransformSubspaceSeq I
            (⟨j + 1, hj⟩ : Fin (T.pushforward hS).length).castSucc) :=
      saturationStalk_congr _ _ _ _ (T.support_pushforwardCenterOf hS (j + 1) hj) _
    rw [hw]
    exact hstep

include hI in
/-- (C) The BRANCH COINCIDENCE along the chains: at every step the saturation of the `X`-chain
has local generators iff the saturation of the `S`-chain has (the core (C) at the step, the two
chains' inputs identified by (B) at the previous stage). -/
theorem hasLocalGenerators_saturationStalk_pushforward_iff (i : Fin T.length) :
    IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 E ((T.pushforward hS).stage i.succ))
        (saturationStalk ((T.pushforward hS).isClosedSubmanifold_center i)
          ((T.pushforward hS).isBlowUp_map i)
          ((T.pushforward hS).strictTransformSubspaceSeq I i.castSucc)) ↔
      IdealSheaf.HasLocalGenerators (𝒪 := structureSheaf 𝕜 (Fin (n - s) → 𝕜) (T.stage i.succ))
        (saturationStalk (T.isClosedSubmanifold_center i) (T.isBlowUp_map i)
          (T.strictTransformSubspaceSeq (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff)
            i.castSucc)) := by
  obtain ⟨j, hj⟩ := i
  exact T.hasLocalGenerators_saturationStalk_pushforward_iff_aux hS I hI j hj

end AnalyticManifold.FiniteSuccession

end
