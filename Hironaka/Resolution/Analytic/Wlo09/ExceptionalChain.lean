/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.LimitFamily
public import Hironaka.Manifold.DirectLimit.SncFamily
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Resolution.Analytic.ModelTransport.Square
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.Kol07Thm45.ExceptionalTransitionRestrict
import Hironaka.Resolution.Analytic.OrderReduction.Step22Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The exceptional divisor of a compatible family, glued along the exhaustion

Włodarczyk's divisor `E` on `M̃` [Wlo09, Theorem 2.0.2] is the union of the exceptional divisors
of the successions over the members of the exhaustion, which agree on the overlaps up to the empty
blow-ups. For a compatible family `C` (`CompatibleFamily`), the last-stage exceptional families
`exceptionalOn U` of its values on the members `U_m` of a compact exhaustion form a chain along the
end-result embeddings (`exceptionalChain`: the transition of the members along
`endResultEmbedding`, `exists_orderEmb_exceptionalOn_endResultEmbedding`, is the one of
`exists_orderEmb_totalTransformSeqFrom_last_pullback_eraseEmpty` read through the compatibility
`compat`), and they glue to a hypersurface family on the glued space `M̃ = endResultLimit`
(`gluedExceptional`, by `FamilyChain.glue`): a simple normal crossings family when the pieces are
(`isSnc_gluedExceptional`), whose trace on every piece is the piece's family
(`preimage_toLimit_support_gluedExceptional`). Its reduced ideal sheaf pulls back along the
inclusion of every piece to the piece's last exceptional divisor
(`idealSheaf_gluedExceptional_pullback_toLimitMap`), by the general transport of the reduced ideal
sheaf of a simple normal crossings family along a local analytic isomorphism
(`HypersurfaceFamily.idealSheaf_pullback_eq_idealSheaf_of_preimage_support`).

Not in the sources beyond the statement cited; bookkeeping.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace Filter AnalyticManifold Manifold
open scoped Manifold ContDiff

universe u

/-! ### The reduced ideal sheaf of an snc family along a local analytic isomorphism -/

namespace Manifold.HypersurfaceFamily

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M N : AnalyticManifold.{u} 𝕜 E}

/-- The reduced ideal sheaf of a simple normal crossings family `G`, pulled back along a local
analytic isomorphism `g`, is the reduced ideal sheaf of any simple normal crossings family `H`
whose support is `g⁻¹(|G|)`: the vanishing ideals of a set transport along the bijective germ
maps of `g` (`comap_germMap_vanishingStalk`). -/
theorem idealSheaf_pullback_eq_idealSheaf_of_preimage_support (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) {G : HypersurfaceFamily M}
    {H : HypersurfaceFamily N} (hG : G.IsSnc ψ) (hH : H.IsSnc ψ)
    (hsupp : ⇑g ⁻¹' G.support = H.support) :
    (G.idealSheaf (𝕜 := 𝕜) (E := E)).pullback g g.contMDiff = H.idealSheaf := by
  refine Manifold.IdealSheaf.ext fun x => ?_
  rw [Manifold.IdealSheaf.stalkIdeal_pullback, hG.stalkIdeal_idealSheaf, hH.stalkIdeal_idealSheaf,
    ← hsupp,
    Hironaka.Manifold.vanishingStalk_preimage_of_isLocalDiffeomorphAt_models g.contMDiff (hg x)]

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold.CompatibleFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  {T : AnalyticTriple ψ₀ M} (C : CompatibleFamily T)

/-! ### The transition of the exceptional families along the end-result embeddings -/

/-- The last-stage exceptional family of the value of `C` on the relatively compact open `U`. -/
abbrev exceptionalOn (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    HypersurfaceFamily ((C.seqOn U hU).stage (Fin.last _)) :=
  (C.seqOn U hU).toSuccession.totalTransformSeq (Fin.last _)

/-- **The transition of the exceptional families along an end-result embedding**: for
`U₁ ≤ U₂`, an order embedding of the index set of the family over `U₁` into that over `U₂` such
that the trace of a matched member is the member and an unmatched member has empty trace
(`exists_orderEmb_totalTransformSeqFrom_last_pullback_eraseEmpty`, transported through the
compatibility `compat` and `empty_comap`). -/
theorem exists_orderEmb_exceptionalOn_endResultEmbedding {U₁ U₂ : Opens M}
    (hU₁ : IsCompact (closure (U₁ : Set M))) (hU₂ : IsCompact (closure (U₂ : Set M)))
    (h : U₁ ≤ U₂) :
    ∃ ε : (C.exceptionalOn U₁ hU₁).ι ↪o (C.exceptionalOn U₂ hU₂).ι,
      (∀ i, ⇑(C.endResultEmbedding hU₁ hU₂ h) ⁻¹' (C.exceptionalOn U₂ hU₂).hyp (ε i) =
        (C.exceptionalOn U₁ hU₁).hyp i) ∧
      ∀ b, b ∉ Set.range ε →
        ⇑(C.endResultEmbedding hU₁ hU₂ h) ⁻¹' (C.exceptionalOn U₂ hU₂).hyp b = ∅ := by
  obtain ⟨ε₀, h₀a, h₀b⟩ :=
    AnalyticManifold.BlowUpSequence.exists_orderEmb_totalTransformSeqFrom_last_pullback_eraseEmpty
      (C.seqOn U₂ hU₂) (M.restrictLE h) (isLocalDiffeomorph_restrictLE h)
      (HypersurfaceFamily.empty _) (fun j => j.elim)
  obtain ⟨o₁, ho₁⟩ := HypersurfaceFamily.exists_orderIso_of_eq
    (congrArg (fun G => ((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
        (isLocalDiffeomorph_restrictLE h)).eraseEmpty.toSuccession.totalTransformSeqFrom G
        (Fin.last _))
      (HypersurfaceFamily.empty_comap ⇑(M.restrictLE h)))
  obtain ⟨o₂, ho₂⟩ := HypersurfaceFamily.exists_orderIso_of_eq
    (AnalyticManifold.BlowUpSequence.totalTransformSeqFrom_last_stageOfEq
      (C.compat U₁ U₂ hU₁ hU₂ h) (HypersurfaceFamily.empty _))
  have hlift : ⇑(C.endResultEmbedding hU₁ hU₂ h) =
      (⇑((C.seqOn U₂ hU₂).pullbackLiftLast (M.restrictLE h) (isLocalDiffeomorph_restrictLE h)) ∘
        ⇑(Diffeomorph.toAnalyticMap ((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
          (isLocalDiffeomorph_restrictLE h)).eraseEmptyLast.symm)) ∘
        ⇑(Diffeomorph.toAnalyticMap
          (AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h))) := rfl
  have hσ : ∀ s, ⇑(Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h))) ⁻¹'
      (⇑(Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h)).symm) ⁻¹' s) =
      s := by
    intro s
    rw [← Set.preimage_comp]
    exact (congrArg (fun g : _ → _ => g ⁻¹' s) (funext fun x =>
      (AnalyticManifold.BlowUpSequence.stageOfEq
        (C.compat U₁ U₂ hU₁ hU₂ h)).symm_apply_apply x)).trans Set.preimage_id
  refine ⟨(o₂.symm.trans o₁.symm).toOrderEmbedding.trans ε₀, fun i => ?_, fun b hb => ?_⟩
  · rw [hlift, Set.preimage_comp]
    refine (congrArg _ (h₀a (o₁.symm (o₂.symm i)))).trans ?_
    refine (congrArg _ ((ho₁ _).trans (congrArg _ (o₁.apply_symm_apply (o₂.symm i))))).trans ?_
    refine (congrArg _ ((ho₂ _).trans (congrArg _ (o₂.apply_symm_apply i)))).trans ?_
    exact hσ _
  · have hb' : b ∉ Set.range ε₀ := fun ⟨k, hk⟩ => hb ⟨o₂ (o₁ k), by
      change ε₀ (o₁.symm (o₂.symm (o₂ (o₁ k)))) = b
      exact (congrArg (fun z => ε₀ (o₁.symm z)) (o₂.symm_apply_apply (o₁ k))).trans
        ((congrArg ε₀ (o₁.symm_apply_apply k)).trans hk)⟩
    rw [hlift, Set.preimage_comp]
    exact (congrArg _ (h₀b b hb')).trans Set.preimage_empty

/-! ### The glued exceptional family -/

variable (Kex : CompactExhaustion M)

/-- The end-result embeddings are analytic open embeddings (the hypothesis `hemb` of the gluing,
`isAnalyticOpenEmbedding_endResultEmbedding`). -/
abbrev hemb : ∀ (U₁ U₂ : Opens M) (hU₁ : IsCompact (closure (U₁ : Set M)))
    (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂),
    IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h) :=
  fun _ _ hU₁ hU₂ h => C.isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h

/-- **The chain of the exceptional families along the exhaustion** (`FamilyChain` on the chain of
end results `endResultChain`), with the transitions of
`exists_orderEmb_exceptionalOn_endResultEmbedding`. -/
def exceptionalChain : (C.endResultChain Kex C.hemb).FamilyChain where
  H m := C.exceptionalOn (relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex m)
  ε m := (C.exists_orderEmb_exceptionalOn_endResultEmbedding
    (isCompact_closure_relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex (m + 1))
    (relCompactOpen_le_succ Kex m)).choose
  preimage_hyp_ε m j := (C.exists_orderEmb_exceptionalOn_endResultEmbedding
    (isCompact_closure_relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex (m + 1))
    (relCompactOpen_le_succ Kex m)).choose_spec.1 j
  preimage_hyp_eq_empty m b hb := (C.exists_orderEmb_exceptionalOn_endResultEmbedding
    (isCompact_closure_relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex (m + 1))
    (relCompactOpen_le_succ Kex m)).choose_spec.2 b hb

theorem exceptionalChain_H (m : ℕ) :
    (C.exceptionalChain Kex).H m =
      C.exceptionalOn (relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex m) :=
  rfl

/-- **Włodarczyk's exceptional divisor on `M̃`, as a hypersurface family**: the exceptional
families of the pieces glued along the exhaustion. -/
def gluedExceptional : HypersurfaceFamily (C.endResultChain Kex C.hemb).limitManifold :=
  (C.exceptionalChain Kex).glue

/-- The glued exceptional family has simple normal crossings when the exceptional families of the
pieces do. -/
theorem isSnc_gluedExceptional
    (hsnc : ∀ m, (C.exceptionalOn (relCompactOpen Kex m)
      (isCompact_closure_relCompactOpen Kex m)).IsSnc ψ₀) :
    (C.gluedExceptional Kex).IsSnc ψ₀ :=
  (C.exceptionalChain Kex).isSnc_glue ψ₀ hsnc

/-- The trace of the glued exceptional family on a piece is the piece's exceptional family. -/
theorem preimage_toLimit_support_gluedExceptional (m : ℕ) :
    (C.endResultChain Kex C.hemb).toLimit m ⁻¹' (C.gluedExceptional Kex).support =
      (C.exceptionalOn (relCompactOpen Kex m) (isCompact_closure_relCompactOpen Kex m)).support :=
  (C.exceptionalChain Kex).preimage_toLimit_support_glue m

/-- **The reduced ideal sheaf of the glued exceptional family pulls back along the inclusion of a
piece to the reduced ideal sheaf of the piece's exceptional family.** -/
theorem idealSheaf_gluedExceptional_pullback_toLimitMap
    (hsnc : ∀ m, (C.exceptionalOn (relCompactOpen Kex m)
      (isCompact_closure_relCompactOpen Kex m)).IsSnc ψ₀) (m : ℕ) :
    ((C.gluedExceptional Kex).idealSheaf (𝕜 := 𝕜) (E := E)).pullback
        ((C.endResultChain Kex C.hemb).toLimitMap m)
        ((C.endResultChain Kex C.hemb).toLimitMap m).contMDiff =
      (C.exceptionalOn (relCompactOpen Kex m)
        (isCompact_closure_relCompactOpen Kex m)).idealSheaf :=
  HypersurfaceFamily.idealSheaf_pullback_eq_idealSheaf_of_preimage_support ψ₀ _
    ((C.endResultChain Kex C.hemb).isLocalDiffeomorph_toLimit m)
    (C.isSnc_gluedExceptional Kex hsnc) (hsnc m)
    (C.preimage_toLimit_support_gluedExceptional Kex m)

end Hironaka.Manifold.CompatibleFamily

end

end
