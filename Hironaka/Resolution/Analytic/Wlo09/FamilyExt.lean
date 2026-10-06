/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Canonicity
public import Hironaka.Resolution.Analytic.Functor.LimitFamily
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
public import Mathlib.Analysis.InnerProductSpace.Basic
import Hironaka.Manifold.IdealSheaf.Pullback
public import Hironaka.Resolution.Analytic.Functor.EndResultEmbeddingLemmas
import Hironaka.Resolution.Analytic.Functor.LimitGluing
import Hironaka.Resolution.Analytic.Functor.LimitProperties
import Hironaka.Resolution.Analytic.Wlo09.CentersOver
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The resolution of a triple as one family over the manifold

`CompatibleFamily.toExtensionCompatibleFamily C` is the extension-compatible family of a
compatible family `C` along the exhaustion of `M` by relatively compact opens
(`ExtensionCompatibleFamily.ofCompatibleFamily`), and its blow-down is proper
(`CompatibleFamily.isProperMap_toExtensionCompatibleFamily_map`). It is the gluing both of the
resolution of a triple below and of the embedded desingularization
(`Hironaka/Resolution/Analytic/Wlo09/EmbeddedDesingularization.lean`).

`resolveFamExt bo T` is the extension-compatible family of the resolution `resolveFam bo T`
(`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`) along the exhaustion of `M` by relatively
compact opens (`ExtensionCompatibleFamily.ofCompatibleFamily`; Włodarczyk's compatible family of
resolutions [Wlo09, Theorem 2.0.3 (4)], Kollár's passage from neighbourhoods of compacts to the
whole space [Kol07, 44]). Its `map` is the glued blow-down `σ`:

* `isProperMap_resolveFamExt_map` — `σ` is proper (Hironaka's canonical modification is a proper
  morphism [Hir64, p. 155]; [Wlo09, Theorem 2.0.3]; the gluing of the local principalizations
  [Wlo09, §4.1]), one application of `CompatibleFamily.isProperMap_limitBlowDown`;
* `isAnalyticIsoOver_resolveFamExt_map` — `σ` is an analytic isomorphism off the cosupport of the
  ideal sheaf ([Kol07, Theorem 35 (3)]; [Wlo09, Lemma 4.0.3]), one application of
  `CompatibleFamily.isAnalyticIsoOver_limitBlowDown`.
-/

@[expose] public section

open Set Topology TopologicalSpace AnalyticManifold Opposite Filter
open scoped Manifold ContDiff

noncomputable section

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Glue

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} (C : CompatibleFamily T)

/-- **A compatible family of blow-up sequences as one family over the manifold**: the
extension-compatible family of `C` along the exhaustion of `M`
(`ExtensionCompatibleFamily.ofCompatibleFamily`; Włodarczyk's gluing of the local
principalizations and desingularizations [Wlo09, §4.1 and §4.2]). -/
def CompatibleFamily.toExtensionCompatibleFamily : ExtensionCompatibleFamily M :=
  ExtensionCompatibleFamily.ofCompatibleFamily C (exhaustion M)
    (fun _ _ hU₁ hU₂ h => C.isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h)
    (fun _ _ hU₁ hU₂ h p => C.composite_endResultEmbedding hU₁ hU₂ h p)
    (fun _ _ hU₁ hU₂ h => C.range_endResultEmbedding hU₁ hU₂ h)
    C.isExtensionOf_restrict_seqOn

/-- The glued blow-down of a compatible family is proper
(`CompatibleFamily.isProperMap_limitBlowDown`). -/
theorem CompatibleFamily.isProperMap_toExtensionCompatibleFamily_map :
    IsProperMap C.toExtensionCompatibleFamily.map :=
  CompatibleFamily.isProperMap_limitBlowDown C (exhaustion M)
    (fun _ _ hU₁ hU₂ h => C.isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h)
    (fun _ _ hU₁ hU₂ h p => C.composite_endResultEmbedding hU₁ hU₂ h p)
    (fun _ _ hU₁ hU₂ h => C.range_endResultEmbedding hU₁ hU₂ h)

end Glue

section Sigma

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)

/-- **The resolution of `T` as one family over `M`**: the extension-compatible family of
`resolveFam bo T` along the exhaustion of `M` (`ExtensionCompatibleFamily.ofCompatibleFamily`),
Włodarczyk's compatible family of resolutions of the relatively compact opens
[Wlo09, Theorem 2.0.3 (4)] (`CompatibleFamily.toExtensionCompatibleFamily`). Its `map` is the glued
blow-down `σ`. -/
def resolveFamExt : ExtensionCompatibleFamily M :=
  (resolveFam bo T).toExtensionCompatibleFamily

/-- **`σ` is proper** (Hironaka's canonical modification is a proper morphism [Hir64, p. 155];
[Wlo09, Theorem 2.0.3]; [Wlo09, §4.1]): one application of the gluing tool
`CompatibleFamily.isProperMap_limitBlowDown`
(`CompatibleFamily.isProperMap_toExtensionCompatibleFamily_map`). -/
theorem isProperMap_resolveFamExt_map : IsProperMap (resolveFamExt bo T).map :=
  (resolveFam bo T).isProperMap_toExtensionCompatibleFamily_map

/-- **`σ` is an analytic isomorphism off the cosupport of `𝓘`** ([Kol07, Theorem 35 (3)];
[Wlo09, Lemma 4.0.3]): one application of `CompatibleFamily.isAnalyticIsoOver_limitBlowDown` fed
per piece by `isAnalyticIsoOver_stageMap_last_resolveSeqOn`. -/
theorem isAnalyticIsoOver_resolveFamExt_map :
    AnalyticMap.IsIsoOver (resolveFamExt bo T).map (T.I.support)ᶜ :=
  CompatibleFamily.isAnalyticIsoOver_limitBlowDown (resolveFam bo T) (exhaustion M)
    (fun _ _ hU₁ hU₂ h => (resolveFam bo T).isAnalyticOpenEmbedding_endResultEmbedding hU₁ hU₂ h)
    (fun _ _ hU₁ hU₂ h p => (resolveFam bo T).composite_endResultEmbedding hU₁ hU₂ h p)
    T.I.support fun m => by
      have h := isAnalyticIsoOver_stageMap_last_resolveSeqOn bo T (relCompactOpen (exhaustion M) m)
        (isCompact_closure_relCompactOpen (exhaustion M) m)
      have e : (restrictTriple T (relCompactOpen (exhaustion M) m)).I.support =
          Subtype.val ⁻¹' T.I.support :=
        IdealSheaf.support_pullback _ _ T.I
      rw [e] at h
      exact h

end Sigma

end Hironaka.Manifold
