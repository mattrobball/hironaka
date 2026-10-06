/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.EndResultEmbedding
public import Hironaka.Manifold.FiniteSuccession.CompatibleFamily.Defs
import Hironaka.Resolution.Analytic.Functor.ExtensionOf
import Hironaka.Resolution.Analytic.OrderReduction.ChainTransportPrep
import Hironaka.Resolution.Analytic.OrderReduction.LiftUnique
import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The compatibility clause and the end-result embedding of a compatible family

[Wlo09, Theorem 2.0.3, (4)] for every compatible family: for relatively compact opens `U₁ ≤ U₂`
the restriction of the succession over `U₂` is an extension ([Wlo09, Definition 3.2.6]) of the
succession over `U₁`. Indeed `compat` says the value on `U₁` is the value on `U₂` pulled back
along the open inclusion with the empty blow-ups erased; the restriction is stage-wise isomorphic
to that pull-back (`isExtensionOf_restrict_toSuccession_of_pullback`), which is an extension of
its cleaned list (`isExtensionOf_toSuccession_eraseEmpty`). By the second clause of [Kol07, 34.1]
and [Wlo09, Theorem 3.5.1, (2)], the end-result embedding `endResultEmbedding` is an analytic open
embedding over `M` onto the preimage of `U₁`, functorial and the identity on `U₁ ≤ U₁`, from the
last-stage lemmas `isLocalDiffeomorph_pullbackLiftLast`, `injective_pullbackLiftLast`,
`stageMap_last_pullbackLiftLast`, `range_pullbackLiftLast`, `stageMap_last_eraseEmptyLast`,
`stageMap_last_stageOfEq` and `eq_of_stageMap_last_comp_eq`.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}
  (C : CompatibleFamily T)

/-- For a compatible family and relatively
compact opens `U₁ ≤ U₂`, the restriction to `U₁` of the succession over `U₂` is an extension of the
succession over `U₁`: the clause `isExtensionOf_restrict` of the extension-compatible families, for
every compatible family. -/
theorem CompatibleFamily.isExtensionOf_restrict_seqOn (U₁ U₂ : Opens M)
    (hU₁ : IsCompact (closure (U₁ : Set M))) (hU₂ : IsCompact (closure (U₂ : Set M)))
    (h : U₁ ≤ U₂) :
    ((C.seqOn U₂ hU₂).toSuccession.restrict h).IsExtensionOf (C.seqOn U₁ hU₁).toSuccession := by
  rw [C.compat U₁ U₂ hU₁ hU₂ h]
  exact AnalyticManifold.BlowUpSequence.isExtensionOf_restrict_toSuccession_of_pullback
      (C.seqOn U₂ hU₂) h
    (AnalyticManifold.BlowUpSequence.isExtensionOf_toSuccession_eraseEmpty _)

variable {U₁ U₂ : Opens M} (hU₁ : IsCompact (closure (U₁ : Set M)))
  (hU₂ : IsCompact (closure (U₂ : Set M))) (h : U₁ ≤ U₂)

/-- The end-result embedding is a local analytic isomorphism (a composite of the last-stage lift of
the open inclusion and two diffeomorphisms). -/
theorem CompatibleFamily.isLocalDiffeomorph_endResultEmbedding :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (C.endResultEmbedding hU₁ hU₂ h) :=
  AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp (Diffeomorph.isLocalDiffeomorph _)
      (Diffeomorph.isLocalDiffeomorph _))

/-- The embedding of
end results is an analytic open embedding (Kollár's open immersion): a local analytic
isomorphism, injective as the last-stage lift of the injective open inclusion after two
diffeomorphisms. -/
theorem CompatibleFamily.isAnalyticOpenEmbedding_endResultEmbedding :
    IsAnalyticOpenEmbedding (C.endResultEmbedding hU₁ hU₂ h) := by
  refine ⟨C.isLocalDiffeomorph_endResultEmbedding hU₁ hU₂ h, ?_⟩
  change Function.Injective (⇑((C.seqOn U₂ hU₂).pullbackLiftLast (M.restrictLE h)
      (isLocalDiffeomorph_restrictLE h)) ∘
    (⇑((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
        (isLocalDiffeomorph_restrictLE h)).eraseEmptyLast.symm ∘
      ⇑(AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h))))
  exact (AnalyticManifold.BlowUpSequence.injective_pullbackLiftLast _ _ _
      (isAnalyticOpenEmbedding_restrictLE h).2).comp
    ((EquivLike.injective _).comp (EquivLike.injective _))

/-- The end-result embedding is OVER `M` — the composite blow-down of `U₂`'s end
result after the embedding is the inclusion `U₁ ⊆ U₂` after the composite blow-down of `U₁`'s end
result (`stageMap_last_pullbackLiftLast`, `stageMap_last_eraseEmptyLast`,
`stageMap_last_stageOfEq`). -/
theorem CompatibleFamily.composite_endResultEmbedding (p : (C.seqOn U₁ hU₁).stage (Fin.last _)) :
    (C.seqOn U₂ hU₂).toSuccession.composite (C.endResultEmbedding hU₁ hU₂ h p) =
      M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.composite p) := by
  change (C.seqOn U₂ hU₂).toSuccession.stageMap (Fin.last _)
      ((C.seqOn U₂ hU₂).pullbackLiftLast (M.restrictLE h) (isLocalDiffeomorph_restrictLE h)
        (((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
          (isLocalDiffeomorph_restrictLE h)).eraseEmptyLast.symm
          (AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h) p))) =
    M.restrictLE h ((C.seqOn U₁ hU₁).toSuccession.stageMap (Fin.last _) p)
  rw [AnalyticManifold.BlowUpSequence.stageMap_last_pullbackLiftLast]
  congr 1
  have h1 := AnalyticManifold.BlowUpSequence.stageMap_last_eraseEmptyLast
    ((C.seqOn U₂ hU₂).pullback (M.restrictLE h) (isLocalDiffeomorph_restrictLE h))
    (((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
      (isLocalDiffeomorph_restrictLE h)).eraseEmptyLast.symm
      (AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h) p))
  rw [Diffeomorph.apply_symm_apply] at h1
  rw [← h1]
  exact AnalyticManifold.BlowUpSequence.stageMap_last_stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h) p

/-- The image of the
embedding of end results is the preimage of `U₁` under the composite blow-down of `U₂`'s end result
(`range_pullbackLiftLast`; the two diffeomorphisms are onto). -/
theorem CompatibleFamily.range_endResultEmbedding :
    Set.range (C.endResultEmbedding hU₁ hU₂ h) =
      (C.seqOn U₂ hU₂).toSuccession.composite ⁻¹' Set.range (M.restrictLE h) := by
  change Set.range (⇑((C.seqOn U₂ hU₂).pullbackLiftLast (M.restrictLE h)
      (isLocalDiffeomorph_restrictLE h)) ∘
    (⇑((C.seqOn U₂ hU₂).pullback (M.restrictLE h)
        (isLocalDiffeomorph_restrictLE h)).eraseEmptyLast.symm ∘
      ⇑(AnalyticManifold.BlowUpSequence.stageOfEq (C.compat U₁ U₂ hU₁ hU₂ h)))) = _
  rw [Function.Surjective.range_comp ((EquivLike.surjective _).comp (EquivLike.surjective _)),
    AnalyticManifold.BlowUpSequence.range_pullbackLiftLast]
  rfl

/-- The embeddings compose —
`emb₂₃ ∘ emb₁₂ = emb₁₃` for `U₁ ≤ U₂ ≤ U₃` (uniqueness of maps over `M`,
`eq_of_stageMap_last_comp_eq`: both sides are open maps over `M`). -/
theorem CompatibleFamily.endResultEmbedding_comp {U₃ : Opens M}
    (hU₃ : IsCompact (closure (U₃ : Set M))) (h₂₃ : U₂ ≤ U₃)
    (p : (C.seqOn U₁ hU₁).stage (Fin.last _)) :
    C.endResultEmbedding hU₂ hU₃ h₂₃ (C.endResultEmbedding hU₁ hU₂ h p) =
      C.endResultEmbedding hU₁ hU₃ (h.trans h₂₃) p := by
  have key := AnalyticManifold.BlowUpSequence.eq_of_stageMap_last_comp_eq (C.seqOn U₃ hU₃)
    (f := fun z => C.endResultEmbedding hU₂ hU₃ h₂₃ (C.endResultEmbedding hU₁ hU₂ h z))
    (g := fun z => C.endResultEmbedding hU₁ hU₃ (h.trans h₂₃) z)
    ((C.endResultEmbedding hU₂ hU₃ h₂₃).contMDiff.continuous.comp
      (C.endResultEmbedding hU₁ hU₂ h).contMDiff.continuous)
    (C.endResultEmbedding hU₁ hU₃ (h.trans h₂₃)).contMDiff.continuous
    (fun D _ hD => hD.preimage ((C.isLocalDiffeomorph_endResultEmbedding hU₂ hU₃ h₂₃).isOpenMap.comp
      (C.isLocalDiffeomorph_endResultEmbedding hU₁ hU₂ h).isOpenMap))
    (fun z => by
      change (C.seqOn U₃ hU₃).toSuccession.composite _ = (C.seqOn U₃ hU₃).toSuccession.composite _
      rw [C.composite_endResultEmbedding hU₂ hU₃ h₂₃, C.composite_endResultEmbedding hU₁ hU₂ h,
        C.composite_endResultEmbedding hU₁ hU₃ (h.trans h₂₃)]
      rfl)
  exact congrFun key p

/-- The embedding of an open into itself is the identity,
`emb₁₁ = id` (`eq_of_stageMap_last_comp_eq` against `id`). -/
theorem CompatibleFamily.endResultEmbedding_self (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) (p : (C.seqOn U hU).stage (Fin.last _)) :
    C.endResultEmbedding hU hU le_rfl p = p := by
  have key := AnalyticManifold.BlowUpSequence.eq_of_stageMap_last_comp_eq (C.seqOn U hU)
    (f := fun z => C.endResultEmbedding hU hU le_rfl z) (g := id)
    (C.endResultEmbedding hU hU le_rfl).contMDiff.continuous continuous_id
    (fun D _ hD => hD.preimage (C.isLocalDiffeomorph_endResultEmbedding hU hU le_rfl).isOpenMap)
    (fun z => by
      change (C.seqOn U hU).toSuccession.composite _ = (C.seqOn U hU).toSuccession.composite z
      rw [C.composite_endResultEmbedding hU hU le_rfl]
      rfl)
  exact congrFun key p

end Hironaka.Manifold

end
