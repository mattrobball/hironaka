/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Defs
public import Hironaka.Manifold.BlowUp.Restrict
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.FiniteSuccession.Restrict.BaseTransport
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Compatible families of finite successions over the compact subsets

Włodarczyk's compatible-family form of principalization [Wlo09, Theorem 2.0.3; Definition 3.2.6;
Theorem 3.5.1 (2)], the form in which Hironaka's Main Theorem II''(N) and the real-analytic
principalization theorem are stated: a proper analytic map `M̃ → M` which over an open
neighbourhood of every compact set is a finite composite of blow-ups with smooth centres,
compatibly across compacts. Włodarczyk's principalization is "locally but not globally a sequence
of blow-ups at smooth centers" [Wlo09, Introduction]: over a neighbourhood `U` of a compact set `Z`
the morphism splits into a finite sequence of blow-ups `U = U_0 ← U_1 ← ⋯ ← U_r` with smooth
centres `C_{i-1} ⊆ U_{i-1}`, and for `Z_1 ⊆ Z_2` with `U_1 ⊆ U_2` the restriction of the sequence
over `U_2` to `U_1` "determines" the sequence over `U_1` — it is an extension of it in the sense of
[Wlo09, Definition 3.2.6]: the same blow-ups with isomorphisms (blow-ups with empty centre)
interspersed.

* `FiniteSuccession.restrict S h`: the restriction of a succession over `U_2` to an open
  `U_1 ≤ U_2` (stages the preimages of `U_1`, centres and maps restricted; a blow-up restricted to
  an open subset is the blow-up of the restricted centre), and
  `FiniteSuccession.IsExtensionOf T S`, Włodarczyk's "`T` is an extension of `S`".
* `FiniteSuccession.Hom R S φ`: a morphism of successions over `φ : N → M`, an index map from the
  stages of `S` to those of `R` with maps between the stages over `φ`, compatible with the
  blow-downs; the two relations below are such morphisms with conditions on the maps and centres.
* `FiniteSuccession.IsPullbackUpToEmptyAlong R S g`: for a local analytic isomorphism
  `g : N → M`, the succession `R` over an open of `N` is the pull-back of the succession `S` over an
  open of `M` along `g`, up to blow-ups with empty centre — the induced sequence `g^*(S)` is an
  extension of `R`, the form of [Wlo09, Theorem 3.5.1 (2)] in which the commutation of
  principalization with local analytic isomorphisms is stated.
* `FiniteSuccession.IsPushforwardUpToEmptyAlong S R τ`: for a closed embedding `τ : N → M`, the
  succession `S` over an open `U` of `M` is the push-forward along `τ` of the succession `R` over an
  open `U'` of `N` with `τ(U') ⊆ U`, up to blow-ups whose centres lie outside the part over
  `τ(U')` — Kollár's `j_* B` [Kol07, Definition 30.3], the form in which the commutation of
  principalization with closed embeddings [Kol07, 34.3] is stated over the compact sets.
* `ExtensionCompatibleFamily M`: Włodarczyk's data in [Wlo09, Theorem 2.0.3 (1), (4)] — a
  manifold `space = M̃` with an analytic map `map : M̃ → M`; for every compact `K ⊆ M` (Mathlib's
  `Compacts M`) an open neighbourhood `nhd K ⊇ K`, monotone in `K`, and a finite succession
  `seq K` over `nhd K` whose end result is identified with `map⁻¹(nhd K)` over `nhd K`
  (`toSpace`, `map_toSpace`, `toSpace_isIso`); and the compatibility `isExtensionOf_restrict`:
  for `K_1 ⊆ K_2` the restriction of `seq K_2` to `nhd K_1` is an extension of `seq K_1`. The
  properness of `map` is a clause of the main theorems, not of the structure.
* `ExtensionCompatibleFamily.IsPullbackAlong F' F g` and
  `ExtensionCompatibleFamily.IsPushforwardAlong F F' τ`: the two relations between successions,
  over every pair of compacts `K' ⊆ N`, `K ⊆ M` whose neighbourhoods correspond under the map.
-/

@[expose] public section

universe u

open scoped Manifold ContDiff
open TopologicalSpace

namespace AnalyticManifold

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace FiniteSuccession

/-! ### The restriction of a finite succession to an open subset -/

section Restrict

open Manifold

variable {M : AnalyticManifold.{u} 𝕜 E} {U₂ : Opens M} (S : FiniteSuccession (M.restrict U₂))
  (U₁ : Opens M)

/-- A map into an open subset `V` of a manifold `M'` is analytic when it is analytic as a map into
`M'` (Mathlib's `liftPropWithinAt_subtypeVal_comp_iff`; the general-domain form of
`contMDiff_codRestrict_opens`). -/
theorem contMDiff_codRestrictOpens {N M' : AnalyticManifold.{u} 𝕜 E} {f : N → M'}
    (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) {V : Opens M'} {f' : N → V}
    (hf' : ∀ p, (f' p : M') = f p) : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f' := by
  intro p
  have h1 : Subtype.val ∘ f' = f := funext hf'
  have hp : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Subtype.val ∘ f') p := by
    rw [h1]
    exact hf p
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f' Set.univ p).mp hp

/-- The trace of `U₁` on the stage `U_i` of `S`: the preimage of `U₁` under the composite
blow-down `σ^i : U_i → U₂ ⊆ M` (Włodarczyk's restriction of the factorization to `Ũ₁`,
[Wlo09, Theorem 2.0.3 (4)]). -/
def restrictStageOpens (i : Fin (S.length + 1)) : Opens (S.stage i) :=
  ⟨(fun p : S.stage i => (S.stageMap i p).1) ⁻¹' (U₁ : Set M),
    U₁.2.preimage (continuous_subtype_val.comp (S.stageMap i).contMDiff.continuous)⟩

/-- The later stages of the restriction: the traces of `U₁` on `U_1, …, U_r`. -/
def restrictOpensLater (j : Fin S.length) : AnalyticManifold.{u} 𝕜 E :=
  (S.stage j.succ).restrict (S.restrictStageOpens U₁ j.succ)

/-- The restricted blow-downs `σ_{i+1}|` between the traces: the first lands in `U₁` itself, the
others between traces of later stages (a blowing-up restricted over an open subset). -/
def restrictOpensMapAux :
    ∀ (i : ℕ) (hi : i < S.length),
      AnalyticMap (finStages (M.restrict U₁) (S.restrictOpensLater U₁) ⟨i + 1, Nat.succ_lt_succ hi⟩)
        (finStages (M.restrict U₁) (S.restrictOpensLater U₁) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi =>
    ⟨fun q => ⟨(S.map ⟨0, hi⟩ q.1).1, q.2⟩,
      contMDiff_codRestrict_opens (contMDiff_subtype_val.comp (S.map ⟨0, hi⟩).contMDiff)
        fun _ => rfl⟩
  | i + 1, hi =>
    ⟨fun q => ⟨S.map ⟨i + 1, hi⟩ q.1, q.2⟩,
      contMDiff_codRestrict_opens (S.map ⟨i + 1, hi⟩).contMDiff fun _ => rfl⟩

variable {U₁} (h : U₁ ≤ U₂)

/-- The open inclusion `U₁ → U₂` as an analytic map (Mathlib's `Opens.inclusion` with
`contMDiff_inclusion`), the stage-`0` inclusion of the restriction. -/
def restrictOpensIncl : AnalyticMap (M.restrict U₁) (M.restrict U₂) :=
  ⟨Opens.inclusion h, contMDiff_inclusion h⟩

/-- The restricted centres `C_i ∩ σ^{-i}(U₁)`: the centre `C_i` comapped along the inclusion of
the trace (possibly empty: Włodarczyk's isomorphism steps,
[Wlo09, Definition 3.2.6, Remark (1)]). -/
def restrictOpensCenterAux :
    ∀ (i : ℕ) (hi : i < S.length),
      IdealSheaf (finStages (M.restrict U₁) (S.restrictOpensLater U₁) ⟨i, Nat.lt_succ_of_lt hi⟩)
  | 0, hi => (S.center ⟨0, hi⟩).pullback (restrictOpensIncl h) (restrictOpensIncl h).contMDiff
  | i + 1, hi =>
    (S.center ⟨i + 1, hi⟩).restrict (S.restrictStageOpens U₁ ⟨i + 1, Nat.lt_succ_of_lt hi⟩)

/-- The trace of `U₁` in `U₂`, as an open of the stage `U_0 = U₂`, is `U₁`: the canonical analytic
isomorphism `↥(val⁻¹' U₁) ≃ ↥U₁` (the stage-`0` transport). -/
def restrictTraceDiffeomorph :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E)
      ((S.stage ⟨0, Nat.zero_lt_succ _⟩).restrict (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩))
      (M.restrict U₁) ω where
  toFun q := ⟨q.1.1, q.2⟩
  invFun x := ⟨⟨x.1, h x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    contMDiff_codRestrict_opens (f := (Subtype.val : M.restrict U₂ → M)) contMDiff_subtype_val
      fun _ => rfl
  contMDiff_invFun := contMDiff_codRestrictOpens (restrictOpensIncl h).contMDiff fun _ => rfl

/-- The inverse of the stage-`0` transport as an analytic map `U₁ → ↥(val⁻¹' U₁)`. -/
def restrictTraceInv :
    AnalyticMap (M.restrict U₁)
      ((S.stage ⟨0, Nat.zero_lt_succ _⟩).restrict
        (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)) :=
  ⟨fun x => ⟨⟨x.1, h x.2⟩, x.2⟩,
    contMDiff_codRestrictOpens (restrictOpensIncl h).contMDiff fun _ => rfl⟩

theorem isLocalDiffeomorph_restrictTraceInv :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (S.restrictTraceInv h) :=
  (S.restrictTraceDiffeomorph h).symm.isLocalDiffeomorph

/-- Each restricted map is the monoidal transformation of the restricted centre: a blowing-up
restricted over an open subset is the blowing-up of the restricted centre
(`IsBlowUp.restrictOpens'`), with the trace lemmas for closed submanifolds and their ideal sheaves
(`IsClosedSubmanifold.preimage_val`, `isIdealSheafOf_pullback_val`); at stage `0` the statement is
transported along `restrictTraceDiffeomorph` (`IsBlowUp.diffeomorph_comp`,
`IsClosedSubmanifold.preimage_of_isLocalDiffeomorph`, `comap_idealSheaf_of_isLocalDiffeomorph`). -/
theorem restrictOpensIsMonoidalAux :
    ∀ (i : ℕ) (hi : i < S.length),
      AnalyticMap.IsMonoidalTransformation (S.restrictOpensMapAux U₁ i hi)
        (S.restrictOpensCenterAux h i hi)
  | 0, hi => by
    obtain ⟨n, ψ, c, hcl, hid, hbl⟩ := S.isMonoidal ⟨0, hi⟩
    -- `D = C_0` the centre, `ι : U₁ → U₂` the inclusion, `V₀ = val⁻¹' U₁` the trace on `U_0 = U₂`,
    -- `g : ↥V₀ ≃ U₁` the stage-`0` transport, `gs = g⁻¹` as an analytic map
    set D := S.center ⟨0, hi⟩ with hD
    set ι := restrictOpensIncl h with hι
    have hsupp : (S.restrictOpensCenterAux h 0 hi).support = ⇑ι ⁻¹' D.support :=
      IdealSheaf.support_pullback ι ι.contMDiff D
    have hset : ⇑(S.restrictTraceDiffeomorph h) ''
          ((Subtype.val : S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩ →
            S.stage ⟨0, Nat.zero_lt_succ _⟩) ⁻¹' D.support) =
        ⇑ι ⁻¹' D.support := by
      ext x
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact hq
      · intro hx
        exact ⟨(S.restrictTraceDiffeomorph h).symm x, hx,
          (S.restrictTraceDiffeomorph h).apply_symm_apply x⟩
    -- the trace of the centre in `U₁`, as a closed submanifold: the preimage under `g⁻¹` of its
    -- trace on `V₀` (the two sets are the same set `ι⁻¹(C_0)`, definitionally)
    have hY₀ : IsClosedSubmanifold ψ (⇑ι ⁻¹' D.support) c :=
      (hcl.preimage_val
        (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).preimage_of_isLocalDiffeomorph
        (S.isLocalDiffeomorph_restrictTraceInv h)
    refine ⟨n, ψ, c, ?_, ?_, ?_⟩
    · rw [hsupp]
      exact hY₀
    · rw [hsupp]
      -- the ideal sheaf of the restricted centre is the comap of the ideal sheaf of the centre
      have hDeq : D = hcl.idealSheaf := hid.eq_idealSheaf hcl
      -- `ι = incl₀ ∘ g⁻¹`, the inclusion `incl₀ : ↥V₀ → U₂` of the trace after the transport
      have e₁ : D.pullback ι ι.contMDiff = hcl.idealSheaf.pullback ι ι.contMDiff :=
        congrArg (fun J : IdealSheaf (M.restrict U₂) => J.pullback ι ι.contMDiff) hDeq
      have e₂ : hcl.idealSheaf.pullback ι ι.contMDiff =
          Manifold.IdealSheaf.pullback _ (((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
              (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).comp (S.restrictTraceInv
                  h)).contMDiff
            hcl.idealSheaf :=
        IdealSheaf.pullback_congr hcl.idealSheaf ι.contMDiff
          (((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
            (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).comp
              (S.restrictTraceInv h)).contMDiff
          (funext fun _ => rfl)
      have e₃ : Manifold.IdealSheaf.pullback _ (((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
              (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).comp (S.restrictTraceInv
                  h)).contMDiff
            hcl.idealSheaf =
          (hcl.idealSheaf.pullback _ ((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
              (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).contMDiff).pullback _
                  (S.restrictTraceInv h).contMDiff :=
        (IdealSheaf.pullback_pullback hcl.idealSheaf
          ⇑((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
            (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩))
          ((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
            (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).contMDiff
          ⇑(S.restrictTraceInv h) (S.restrictTraceInv h).contMDiff).symm
      have e₄ : hcl.idealSheaf.pullback _ ((S.stage ⟨0, Nat.zero_lt_succ _⟩).inclusion
            (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).contMDiff =
          (hcl.preimage_val (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)).idealSheaf :=
        (IsClosedSubmanifold.idealSheaf_preimage_val hcl _
          (hcl.preimage_val (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩))).symm
      have e₅ : (hcl.preimage_val (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ
          _⟩)).idealSheaf.pullback _ (S.restrictTraceInv h).contMDiff =
          hY₀.idealSheaf :=
        comap_idealSheaf_of_isLocalDiffeomorph ψ (S.restrictTraceInv h)
          (S.isLocalDiffeomorph_restrictTraceInv h)
          (hcl.preimage_val (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩))
      have e : S.restrictOpensCenterAux h 0 hi = hY₀.idealSheaf :=
        e₁.trans (e₂.trans (e₃.trans
          ((congrArg (fun J : IdealSheaf ((S.stage ⟨0, Nat.zero_lt_succ _⟩).restrict
              (S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)) =>
            J.pullback _ (S.restrictTraceInv h).contMDiff) e₄).trans e₅)))
      rw [e]
      exact hY₀.isIdealSheafOf_idealSheaf
    · rw [hsupp]
      -- the restricted blow-down over the trace `V₀`, then transported to `U₁` along `g`
      have hbl' : IsBlowUp ψ
          ((Subtype.val : S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩ →
            S.stage ⟨0, Nat.zero_lt_succ _⟩) ⁻¹' D.support) c
          (fun q : S.restrictStageOpens U₁ ⟨1, Nat.succ_lt_succ hi⟩ =>
            (⟨S.map ⟨0, hi⟩ q.1, q.2⟩ : S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩)) := by
        refine IsBlowUp.restrictOpens' ?_ ?_ hcl hbl
        · exact Set.ext fun _ => Iff.rfl
        · intro _
          rfl
      have key := hbl'.diffeomorph_comp (S.restrictTraceDiffeomorph h)
      exact (congrArg (fun Z : Set (M.restrict U₁) => IsBlowUp ψ Z c
        (⇑(S.restrictTraceDiffeomorph h) ∘
          fun q : S.restrictStageOpens U₁ ⟨1, Nat.succ_lt_succ hi⟩ =>
            (⟨S.map ⟨0, hi⟩ q.1, q.2⟩ : S.restrictStageOpens U₁ ⟨0, Nat.zero_lt_succ _⟩))) hset).mp
        key
  | i + 1, hi => by
    obtain ⟨n, ψ, c, hcl, hid, hbl⟩ := S.isMonoidal ⟨i + 1, hi⟩
    set D := S.center ⟨i + 1, hi⟩ with hD
    set V := S.restrictStageOpens U₁ ⟨i + 1, Nat.lt_succ_of_lt hi⟩ with hV
    have hsupp : (S.restrictOpensCenterAux h (i + 1) hi).support =
        (Subtype.val : V → S.stage ⟨i + 1, Nat.lt_succ_of_lt hi⟩) ⁻¹' D.support :=
      IdealSheaf.support_pullback _ contMDiff_subtype_val D
    refine ⟨n, ψ, c, ?_, ?_, ?_⟩
    · rw [hsupp]
      exact hcl.preimage_val V
    · rw [hsupp]
      have hDeq : D = hcl.idealSheaf := hid.eq_idealSheaf hcl
      have e : S.restrictOpensCenterAux h (i + 1) hi =
          hcl.idealSheaf.pullback (Subtype.val : V → S.stage ⟨i + 1, Nat.lt_succ_of_lt hi⟩)
            contMDiff_subtype_val :=
        congrArg (fun J : IdealSheaf (S.stage ⟨i + 1, Nat.lt_succ_of_lt hi⟩) => J.restrict V)
          hDeq
      rw [e]
      exact isIdealSheafOf_pullback_val hcl V
    · rw [hsupp]
      refine IsBlowUp.restrictOpens' ?_ ?_ hcl hbl
      · exact Set.ext fun _ => Iff.rfl
      · intro _
        rfl

end Restrict

/-- The restriction of a finite succession `S` over the open `U₂ ⊆ M` to an open `U₁ ≤ U₂`
(Włodarczyk's restriction of the factorization of `prin_{I|Ũ_2}` to `Ũ_1`,
[Wlo09, Theorem 2.0.3 (4)]): the stages are the preimages `(σ^i)⁻¹(U₁) ⊆ U_i`, the centres the
restrictions `C_i ∩ (σ^i)⁻¹(U₁)` (possibly empty: Włodarczyk's isomorphism steps,
[Wlo09, Definition 3.2.6, Remark (1)]), the maps the restrictions of the `σ_{i+1}` — a blow-up
restricted to an open subset is the blow-up of the open subset with the restricted centre, as is
immediate from the chart description of the blowing-up [BM88, Definition 4.1]
(`IsBlowUp.restrictOpens'`). -/
def restrict {M : AnalyticManifold.{u} 𝕜 E} {U₂ : Opens M} (S : FiniteSuccession (M.restrict U₂))
    {U₁ : Opens M} (h : U₁ ≤ U₂) : FiniteSuccession (M.restrict U₁) where
  length := S.length
  later := S.restrictOpensLater U₁
  center i := S.restrictOpensCenterAux h i.1 i.2
  map i := S.restrictOpensMapAux U₁ i.1 i.2
  isMonoidal i := S.restrictOpensIsMonoidalAux h i.1 i.2

/-! ### Włodarczyk's extension relation -/

section Extension

variable {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The composite `σ_{a+1} ∘ ⋯ ∘ σ_b : U_b → U_a` of the maps of `S` between two stages `a ≤ b`
(`Nat.leRecOn` on `a ≤ b`; the identity at `a = b`, `σ_{a+1}` at `b = a + 1`; `stageMap` is the
case `a = 0`). -/
def stageMapLE {a b : Fin (S.length + 1)} (hab : a ≤ b) :
    AnalyticMap (S.stage b) (S.stage a) :=
  Nat.leRecOn (C := fun k => (hk : k < S.length + 1) →
      AnalyticMap (finStages M S.later ⟨k, hk⟩) (S.stage a))
    (n := a.1) (m := b.1) hab
    (fun {k} f hk => (f (Nat.lt_of_succ_lt hk)).comp (S.map ⟨k, Nat.lt_of_succ_lt_succ hk⟩))
    (fun _ => ContMDiffMap.id) b.2

/-- The centre `C_a` on the stage `U_a`, `a < r`, indexed by the stage. -/
def centerAt (a : Fin (S.length + 1)) (ha : a.1 < S.length) : IdealSheaf (S.stage a) :=
  S.center ⟨a.1, ha⟩

end Extension

/-- Włodarczyk's extension of a sequence of blow-ups [Wlo09, Definition 3.2.6]: `T` is an
**extension** of `S` when `T` is a sequence of blow-ups and isomorphisms
`M = T_0 = ⋯ = T_{j_1-1} ← T_{j_1} = ⋯ = T_{j_2-1} ← ⋯ ← T_{j_m} = ⋯ = T_{m'}` with `T_{j_i} = S_i`:
there are indices `j_1 < ⋯ < j_m` (`m = S.length`, `m' = T.length`) such that the blow-ups of `T`
at the indices `j_i` are those of `S` (the stages `T_{j_i}` identified with `S_i` over `M`,
compatibly with the maps and the centres) and every other step of `T` is an isomorphism, a
blow-up with empty centre. In the Lean: a block index `blk : {0, …, m'} → {0, …, m}` (the stage
`T_k` is identified with `S_{blk k}`; `blk 0 = 0`, `blk m' = m`, each step raises `blk` by `0` or
`1`, the steps raising it being the `j_i`), identifications `e k : T_k ≃ S_{blk k}` (Włodarczyk's
"=": analytic isomorphisms over `M`, i.e. commuting with the composite blow-downs, so that `e 0`
is the identity of `M`), compatible with the maps (`σ^S_{blk k + 1} ∘ ⋯ ∘ σ^S_{blk (k+1)} ∘ e (k+1)
= e k ∘ σ^T_{k+1}`, through `stageMapLE`: at a jump the blow-up of `S`, at a non-jump the
identity) and with the centres (at a jump `C^T_k` is the pull-back of `C^S_{blk k}` along `e k`);
at a non-jump the step is an isomorphism, a blow-up with empty centre
[Wlo09, Definition 3.2.6, Remark (1)]. "The definition of extension arises naturally when we pass
to open subsets of the considered ambient manifold" (loc. cit.); [Wlo09, Theorem 3.5.1 (2)]
states the compatibility of the canonical resolution with local analytic isomorphisms in these
terms. That the restriction of a compatible family's succession is an extension of the
succession over the smaller compact is the content of `ExtensionCompatibleFamily`'s last field,
not of this definition. -/
def IsExtensionOf {M : AnalyticManifold.{u} 𝕜 E} (T S : FiniteSuccession M) : Prop :=
  ∃ (blk : Fin (T.length + 1) → Fin (S.length + 1))
    (e : ∀ k, Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (T.stage k) (S.stage (blk k)) ω),
    blk 0 = 0 ∧ blk (Fin.last _) = Fin.last _ ∧
    (∀ k : Fin T.length,
      (blk k.succ : ℕ) = blk k.castSucc ∨ (blk k.succ : ℕ) = blk k.castSucc + 1) ∧
    (∀ (k : Fin (T.length + 1)) (p : T.stage k), S.stageMap (blk k) (e k p) = T.stageMap k p) ∧
    (∀ (k : Fin T.length) (hle : blk k.castSucc ≤ blk k.succ) (p : T.stage k.succ),
      S.stageMapLE hle (e k.succ p) = e k.castSucc (T.map k p)) ∧
    (∀ (k : Fin T.length) (ha : (blk k.castSucc : ℕ) < S.length),
      (blk k.succ : ℕ) = blk k.castSucc + 1 →
        T.center k =
          (S.centerAt (blk k.castSucc) ha).pullback (e k.castSucc) (e k.castSucc).contMDiff) ∧
    (∀ k : Fin T.length, (blk k.succ : ℕ) = blk k.castSucc → (T.center k).support = ∅)

/-- A **morphism of finite successions over `φ : N → M`**, from the finite succession `R` over an
open `U'` of `N` to the finite succession `S` over an open `U` of `M`. With `r = S.length` and
`r' = R.length`: an index `j_k = blk k` of a stage of `R` for every stage `S_k`, with `j_0 = 0`,
`j_r = r'` and each step of `S` raising the index by `0` or `1`, and analytic maps
`f_k : R_{j_k} → S_k` (`map k`) lying over `φ` (`σ^S_k ∘ f_k = φ ∘ σ^R_{j_k}`, read in `M` through
the inclusions of `U` and `U'`) and compatible with the blow-downs
(`σ^S_{k+1} ∘ f_{k+1} = f_k ∘ σ^R_{j_k + 1} ∘ ⋯ ∘ σ^R_{j_{k+1}}`, through `stageMapLE`). The
pull-back and the push-forward of successions (`IsPullbackUpToEmptyAlong`,
`IsPushforwardUpToEmptyAlong`) are morphisms with conditions on the maps and the centres. -/
structure Hom {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : AnalyticManifold.{u} 𝕜 E} {N : AnalyticManifold.{u} 𝕜 E'} {U : Opens M} {U' : Opens N}
    (R : FiniteSuccession (N.restrict U')) (S : FiniteSuccession (M.restrict U))
    (φ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) where
  /-- The index `j_k` of the stage of `R` mapped to the stage `S_k`. -/
  blk : Fin (S.length + 1) → Fin (R.length + 1)
  /-- The map `f_k : R_{j_k} → S_k`. -/
  map : ∀ k, C^ω⟮𝓘(𝕜, E'), R.stage (blk k); 𝓘(𝕜, E), S.stage k⟯
  /-- `j_0 = 0`. -/
  blk_zero : blk 0 = 0
  /-- `j_r = r'`. -/
  blk_last : blk (Fin.last _) = Fin.last _
  /-- Each step of `S` raises the index by `0` or `1`. -/
  blk_succ : ∀ k : Fin S.length,
    (blk k.succ : ℕ) = blk k.castSucc ∨ (blk k.succ : ℕ) = blk k.castSucc + 1
  /-- `f_k` lies over `φ`: `σ^S_k ∘ f_k = φ ∘ σ^R_{j_k}`, read in `M`. -/
  stageMap_map : ∀ k p,
    M.inclusion U (S.stageMap k (map k p)) = φ (N.inclusion U' (R.stageMap (blk k) p))
  /-- The `f_k` are compatible with the blow-downs. -/
  map_map : ∀ (k : Fin S.length) (hle : blk k.castSucc ≤ blk k.succ) (p : R.stage (blk k.succ)),
    S.map k (map k.succ p) = map k.castSucc (R.stageMapLE hle p)

/-- `R`, a finite succession over an open `U'` of `N`, is **the pull-back of the finite succession
`S` over an open `U` of `M` along `g : N → M`, up to blow-ups with empty centre**: there is a
morphism `R → S` over `g` (`FiniteSuccession.Hom`), with index `j_k` and maps `f_k : R_{j_k} → S_k`,
whose maps are local analytic isomorphisms, such that at a step raising the index the centre of
`R` is the pull-back `f_k^*(C_k)` of the centre of `S` and at a step that does not, the pull-back
of the centre is empty. So `R` is the sequence of the fibre products `N ×_M S_k` with some of its
blow-ups of empty centre (isomorphisms) removed.

Relation to the source.
* **Translation.** `R.IsPullbackUpToEmptyAlong S g` is Włodarczyk's "the induced resolution
  $\varphi^*(M_{iZ_i})$ is an extension of the canonical resolution of
  $\varphi^*(M_Z, I, E, \mu)$" [Wlo09, Theorem 3.5.1 (2)], read for successions: the induced
  sequence $g^*(S)$, of the fibre products $N \times_M S_k$ [Wlo09, Proposition 3.4.1;
  Definition 3.4.2], is an extension of $R$ in the sense of [Wlo09, Definition 3.2.6]
  (`FiniteSuccession.IsExtensionOf`).
* **Restatement.** The fibre products $N \times_M S_k$ are not formed. The relation is stated
  through local analytic isomorphisms $f_k$ from the stages of $R$ to those of $S$, lying over $g$
  (Włodarczyk's lifts $\varphi_k$ of [Wlo09, Proposition 3.4.1 (1)], read on the stages of $R$),
  compatible with the blow-downs, with the centre of $R$ the pulled-back centre at a step that
  raises the index and an empty pulled-back centre at the others. These data determine the stages of
  $R$ as the fibre products, because a blowing-up commutes with pull-back along a local analytic
  isomorphism and $f_0$ is the restriction of $g$. -/
def IsPullbackUpToEmptyAlong {M N : AnalyticManifold.{u} 𝕜 E} {U : Opens M} {U' : Opens N}
    (R : FiniteSuccession (N.restrict U')) (S : FiniteSuccession (M.restrict U))
    (g : AnalyticMap N M) : Prop :=
  ∃ f : R.Hom S g,
    (∀ k, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (f.map k)) ∧
    (∀ (k : Fin S.length) (ha : (f.blk k.castSucc : ℕ) < R.length),
      (f.blk k.succ : ℕ) = f.blk k.castSucc + 1 →
        R.centerAt (f.blk k.castSucc) ha =
          (S.center k).pullback (f.map k.castSucc) (f.map k.castSucc).contMDiff) ∧
    (∀ k : Fin S.length, (f.blk k.succ : ℕ) = f.blk k.castSucc →
      ((S.center k).pullback (f.map k.castSucc) (f.map k.castSucc).contMDiff).support = ∅)

/-- `S`, a finite succession over an open `U` of `M`, is **the push-forward of the finite succession
`R` over an open `U'` of `N` along the closed embedding `τ : N → M`, up to blow-ups whose centres
lie outside the part over `τ(U')`** — Kollár's `j_* B` [Kol07, Definition 30.3], with centres
`Z_i^X := (j_i)_*(Z_i^S)` and the natural inclusions `j_i : S_i → X_i` of the strict transforms of
`τ(N)`, for a succession `S` over an open `U ⊇ τ(U')`: there is a morphism `R → S` over `τ`
(`FiniteSuccession.Hom`), with index `j_k` and maps `f_k : R_{j_k} → S_k`, whose maps are
embeddings with image closed in the part of `S_k` over `τ(U')`, such that at a step raising the
index the centre of `R` is the preimage `f_k⁻¹(C_k)` of the centre of `S`, at a step that does
not, `f_k` misses the centre, and every point of a centre of `S` lying over `τ(U')` is in the image
of `f_k`. So over `τ(U')` the centres of `S` are the images of the centres of `R` and the images
of the `f_k` are the strict transforms of `τ(U')`, and `S` is the push-forward of `R` with
blow-ups whose centres lie away from `τ(U')` interspersed.

Relation to the source.
* **Translation.** `S.IsPushforwardUpToEmptyAlong R τ` is Kollár's equation
  $B(X, I_X, E) = j_* B(Y, I_Y, E|_Y)$ for a closed embedding $j$ [Kol07, 34.3], read over the opens
  of two compatible families: $j_* B$ is the push-forward of [Kol07, Definition 30.3], whose
  centres are $Z_i^X := (j_i)_*(Z_i^S)$ for the natural inclusions $j_i \colon S_i \to X_i$ of the
  strict transforms.
* **Restatement.** Kollár's equation compares sequences over one space. Here the succession over
  the open $U$ of $M$ is compared with the succession over an open $U'$ of $N$ with
  $\tau(U') \subseteq U$, so it is the push-forward up to the blow-ups whose centres lie outside
  the part over $\tau(U')$ — the blow-ups of the sequence over $\tau^{-1}(U)$ that the sequence
  over the smaller open $U'$ omits, as the pull-back relation `IsPullbackUpToEmptyAlong` omits the
  blow-ups with empty pulled-back centre.
* **Restatement.** The strict transforms $S_i$ and the inclusions $j_i$ are not formed. The
  relation is stated through embeddings $f_k$ from the stages of $R$, whose images are closed in
  the part over $\tau(U')$ and contain every centre point over $\tau(U')$, with the centre of $R$
  the preimage of the centre of $S$ at a step raising the index and $f_k$ missing the centre at the
  others. These data determine $S$ over $\tau(U')$ as the push-forward: $f_0$ is the restriction of
  $\tau$, and the image of $f_{k+1}$ is the strict transform of the image of $f_k$ under a blow-up
  whose centre is the image of a centre of $R$, or misses the image. -/
def IsPushforwardUpToEmptyAlong {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : AnalyticManifold.{u} 𝕜 E} {N : AnalyticManifold.{u} 𝕜 E'} {U : Opens M} {U' : Opens N}
    (S : FiniteSuccession (M.restrict U)) (R : FiniteSuccession (N.restrict U'))
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) : Prop :=
  ∃ f : R.Hom S τ,
    (∀ k, Topology.IsEmbedding (f.map k)) ∧
    (∀ k (q : S.stage k), q ∈ closure (Set.range (f.map k)) →
      M.inclusion U (S.stageMap k q) ∈ ⇑τ '' (U' : Set N) → q ∈ Set.range (f.map k)) ∧
    (∀ (k : Fin S.length) (ha : (f.blk k.castSucc : ℕ) < R.length),
      (f.blk k.succ : ℕ) = f.blk k.castSucc + 1 →
        ⇑(f.map k.castSucc) ⁻¹' (S.center k).support =
          (R.centerAt (f.blk k.castSucc) ha).support) ∧
    (∀ k : Fin S.length, (f.blk k.succ : ℕ) = f.blk k.castSucc →
      ⇑(f.map k.castSucc) ⁻¹' (S.center k).support = ∅) ∧
    (∀ (k : Fin S.length) (q : S.stage k.castSucc), q ∈ (S.center k).support →
      M.inclusion U (S.stageMap k.castSucc q) ∈ ⇑τ '' (U' : Set N) →
        q ∈ Set.range (f.map k.castSucc))

end FiniteSuccession

/-! ### Compatible families of finite successions over the compact subsets -/

/-- Włodarczyk's data in [Wlo09, Theorem 2.0.3 (1), (4)] with [Wlo09, Definition 3.2.6], the
compatible-family form of the analytic main theorems: a manifold `M̃` (`space`) with an analytic
map `M̃ → M` (`map`; Włodarczyk's `prin_I`, Hironaka's canonical modification `X_γ → X`); for every
compact `K ⊆ M` an open neighbourhood `U_K = nhd K ⊇ K`, monotone in `K` ("corresponding open
neighborhoods `U_1 ⊂ U_2`"), and a finite succession `seq K` of blow-ups with smooth centres over
`U_K` whose end result `U_r` is identified with `Ũ = map⁻¹(U_K)` over `U_K` (`toSpace`,
`map_toSpace`, `toSpace_isIso`: "`U_r = Ũ`", "the restriction `prin_{I|Ũ}` splits into" the
sequence); and the compatibility (4): for `K_1 ⊆ K_2` the restriction of `seq K_2` to `U_{K_1}` is
an extension of `seq K_1` — "the restriction of the factorization of `prin_{I|Ũ_2}` to `Ũ_1`
determines the factorization of `prin_{I|Ũ_1}`". The properness of `map` is a clause of the main
theorems.

Relation to the source.
* **Restatement.** The compatibility of the identifications across compacts (over $U_{K_1}$,
  `toSpace K_2` restricted to the end result of the restriction of `seq K_2` is `toSpace K_1` after
  the identification of the end results given by the extension) is not a field because it is a
  theorem, `ExtensionCompatibleFamily.toSpace_comp_restrictStageIncl_eq`
  (`Hironaka.Resolution.Analytic.Wlo09.FamilyCoherence`): a map from the end result of a succession
  over $U_K$ to $\tilde M$ over $U_K$ is unique (`ExtensionCompatibleFamily.eq_of_map_comp_eq`). -/
structure ExtensionCompatibleFamily (M : AnalyticManifold.{u} 𝕜 E) where
  /-- The manifold `M̃`. -/
  space : AnalyticManifold.{u} 𝕜 E
  /-- The analytic map `M̃ → M` (Włodarczyk's `prin_I`; Hironaka's canonical modification `X_γ → X`
[Hir64, p. 155]). -/
  map : AnalyticMap space M
  /-- For every compact `K ⊆ M`, an open neighbourhood `U_K` of `K` [Wlo09, Theorem 2.0.3 (1)]. -/
  nhd : Compacts M → Opens M
  /-- `K ⊆ U_K`. -/
  subset_nhd : ∀ K : Compacts M, (K : Set M) ⊆ nhd K
  /-- `K_1 ⊆ K_2` gives `U_{K_1} ⊆ U_{K_2}` ([Wlo09, Theorem 2.0.3 (4)]: "corresponding open
neighborhoods `U_1 ⊂ U_2`"). -/
  nhd_mono : Monotone nhd
  /-- The finite sequence of blow-ups over `U_K` [Wlo09, Theorem 2.0.3 (1)]. -/
  seq : ∀ K : Compacts M, FiniteSuccession (M.restrict (nhd K))
  /-- The identification of the end result `U_r` of (∗) with `Ũ = map⁻¹(U_K)`: an analytic map
  `U_r → M̃` … -/
  toSpace : ∀ K : Compacts M, AnalyticMap (seq K).last space
  /-- … over `U_K`: `map ∘ toSpace = σ^r` as maps to `M`, … -/
  map_toSpace : ∀ K : Compacts M,
    map.comp (toSpace K) = (M.inclusion (nhd K)).comp (seq K).composite
  /-- … which is an analytic isomorphism onto `map⁻¹(U_K)` ("`U_r = Ũ`"). -/
  toSpace_isIso : ∀ K : Compacts M,
    AnalyticMap.IsIsoOver (toSpace K) (map ⁻¹' (nhd K : Set M))
  /-- [Wlo09, Theorem 2.0.3 (4)] with [Wlo09, Definition 3.2.6]: for `K_1 ⊆ K_2`, the restriction of
the sequence over `U_{K_2}` to `U_{K_1}` is an extension of the sequence over `U_{K_1}`. -/
  isExtensionOf_restrict : ∀ (K₁ K₂ : Compacts M) (h : K₁ ≤ K₂),
    ((seq K₂).restrict (nhd_mono h)).IsExtensionOf (seq K₁)

namespace ExtensionCompatibleFamily

/-- The compatible family `F'` over `N` is **the pull-back of the compatible family `F` over `M`
along `g : N → M`**: for compacts `K' ⊆ N`, `K ⊆ M` with `g(U_{K'}) ⊆ U_K`, the succession of `F'`
over `U_{K'}` is the pull-back along `g` of the succession of `F` over `U_K`, up to blow-ups with
empty centre (`FiniteSuccession.IsPullbackUpToEmptyAlong`, [Wlo09, Theorem 3.5.1 (2)]). -/
def IsPullbackAlong {M N : AnalyticManifold.{u} 𝕜 E} (F' : ExtensionCompatibleFamily N)
    (F : ExtensionCompatibleFamily M) (g : AnalyticMap N M) : Prop :=
  ∀ (K' : Compacts N) (K : Compacts M), ⇑g '' (F'.nhd K' : Set N) ⊆ F.nhd K →
    (F'.seq K').IsPullbackUpToEmptyAlong (F.seq K) g

/-- The compatible family `F` over `M` is **the push-forward of the compatible family `F'` over `N`
along `τ : N → M`**: for compacts `K' ⊆ N`, `K ⊆ M` with `τ(U_{K'}) ⊆ U_K`, the succession of `F`
over `U_K` is the push-forward along `τ` of the succession of `F'` over `U_{K'}`, up to blow-ups
whose centres lie outside the part over `τ(U_{K'})` (`FiniteSuccession.IsPushforwardUpToEmptyAlong`,
[Kol07, 34.3]). -/
def IsPushforwardAlong {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : AnalyticManifold.{u} 𝕜 E} {N : AnalyticManifold.{u} 𝕜 E'}
    (F : ExtensionCompatibleFamily M) (F' : ExtensionCompatibleFamily N)
    (τ : C^ω⟮𝓘(𝕜, E'), N; 𝓘(𝕜, E), M⟯) : Prop :=
  ∀ (K' : Compacts N) (K : Compacts M), ⇑τ '' (F'.nhd K' : Set N) ⊆ F.nhd K →
    (F.seq K).IsPushforwardUpToEmptyAlong (F'.seq K') τ

end ExtensionCompatibleFamily

end

end AnalyticManifold
