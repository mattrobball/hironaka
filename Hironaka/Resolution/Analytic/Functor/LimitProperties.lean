/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.LimitFamily
import Hironaka.AnalyticSpace.CoverLemmas
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The glued blow-down of a compatible family is proper

The blow-down `σ = C.limitBlowDown Kex hemb hcomp : M̃ → M` of a compatible family's direct limit
(`Hironaka.Resolution.Analytic.Functor.LimitFamily`) is proper: Hironaka's canonical
modification is a proper morphism ([Hir64, p. 155]), Włodarczyk's `prin : M̃ → M` is a proper
bimeromorphic morphism ([Wlo09, Theorem 2.0.3, (1)]; [Wlo09, §4.1 and §4.3]), and the compatible
families of the main theorems carry the clause `IsProperMap F.map`. Properness is local on the
target (`AnalyticSpace.isProperMap_of_restrictPreimage_cover`): over the member
`M_m = relCompactOpen Kex m` of the exhaustion's open cover, `σ⁻¹(M_m)` is the piece `M'_m`
(`limitBlowDown_preimage_relCompactOpen`) and the restriction of `σ` is the piece's composite
blow-down `Π^{(m)} : M'_m → M_m`, a finite composite of blow-ups, hence proper
(`FiniteSuccession.isProperMap_stageMap`), after the homeomorphism `toLimit m` of the piece onto
`σ⁻¹(M_m)`. The theorem `CompatibleFamily.isProperMap_limitBlowDown` is stated for any
`C : CompatibleFamily T`; the resolution family of the main theorems is an instance.
-/

public noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
  (C : CompatibleFamily T) (Kex : CompactExhaustion M)

/-- The glued blow-down `σ : M̃ → M` of a compatible family is
proper — properness is local on the target for the open cover `{M_m}`
(`AnalyticSpace.isProperMap_of_restrictPreimage_cover`), and over `M_m` the restriction of `σ`
is the piece's composite blow-down (a finite composite of blow-ups,
`FiniteSuccession.isProperMap_stageMap`) after the homeomorphism `toLimit m : M'_m ≃ₜ σ⁻¹(M_m)`.
Three properties of the end-result embeddings enter as the hypotheses `hemb`, `hcomp`, `hrange`. -/
theorem CompatibleFamily.isProperMap_limitBlowDown
    (hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h))
    (hcomp : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)
      (p : (C.seqOn U₁ hU₁).stage (Fin.last _)),
      (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
        M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p))
    (hrange : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
      (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
      Set.range (C.endResultEmbedding hU₁ hU₂ h) =
        (C.seqOn U₂ hU₂).toSuccession.composite ⁻¹' Set.range (M.restrictLE h)) :
    IsProperMap (C.limitBlowDown Kex hemb hcomp) := by
  refine AnalyticSpace.isProperMap_of_restrictPreimage_cover (C.limitBlowDown Kex hemb hcomp)
    (C.limitBlowDown Kex hemb hcomp).contMDiff.continuous
    (fun m => (relCompactOpen Kex m : Set M)) (fun m => (relCompactOpen Kex m).isOpen)
    (iUnion_relCompactOpen Kex) fun m => ?_
  have hpre : Set.range ((C.endResultChain Kex hemb).toLimit m) =
      ⇑(C.limitBlowDown Kex hemb hcomp) ⁻¹' (relCompactOpen Kex m : Set M) :=
    (C.limitBlowDown_preimage_relCompactOpen Kex hemb hcomp hrange m).symm
  -- the piece is homeomorphic to `σ⁻¹(M_m)` through its inclusion
  let e : (C.endResultChain Kex hemb).X m ≃ₜ
      (⇑(C.limitBlowDown Kex hemb hcomp) ⁻¹' (relCompactOpen Kex m : Set M)) :=
    ((C.endResultChain Kex hemb).isOpenEmbedding_toLimit m).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hpre)
  -- over `M_m`, `σ` is the piece's composite blow-down after that homeomorphism
  have hfac : (relCompactOpen Kex m : Set M).restrictPreimage (C.limitBlowDown Kex hemb hcomp) =
      ⇑((C.seqOn (relCompactOpen Kex m)
        (isCompact_closure_relCompactOpen Kex m)).toSuccession.composite) ∘ e.symm := by
    funext q
    apply Subtype.ext
    have hq : (C.endResultChain Kex hemb).toLimit m (e.symm q) = q.1 :=
      congrArg Subtype.val (e.apply_symm_apply q)
    change (C.limitBlowDown Kex hemb hcomp) q.1 = _
    rw [← hq]
    rfl
  rw [hfac]
  exact (AnalyticManifold.FiniteSuccession.isProperMap_stageMap
    (S := (C.seqOn (relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex m)).toSuccession)
    (Fin.last _)).comp e.symm.isProperMap

end Hironaka.Manifold
