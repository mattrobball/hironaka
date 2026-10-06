/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyData
public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackCover
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Tools for the transport of the chain of Step 2.1

Two facts used in the transport of a link along a value functor (`ValueTransport.lean`,
`ChainTransport.lean`):

* `BlowUpSequence.range_pullbackLiftLast`, `mem_liftRange_iff` — the range of the last-stage lift of
  a local analytic isomorphism `h` along a sequence of centres is the preimage of the range of `h`
  under the composite blow-down (one step is `exists_liftStep_eq`: every point over a point of the
  range of `h` lifts), so the reading open of the chain (`FamilyChain.lean`) is the preimage of the
  smaller open under the blow-down.
* `BDanFamData.fam_seqOn_induced_pullback_congr` — for two equal sequences of centres, opens of
  their last stages corresponding under `stageOfEq`, and maps into them agreeing under `stageOfEq`,
  the pull-backs of the family's values at the induced triples agree (a substitution).
-/

public section

universe u

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- **The range of the last-stage lift of `h` is the preimage of the range of `h` under the
composite blow-down**: `⊆` is `range_pullbackLiftLast_subset`; for `⊇`, a point over `h b` is in the
range of the lift of the first step (`exists_liftStep_eq`), then the induction. -/
theorem range_pullbackLiftLast : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Set.range (L.pullbackLiftLast h hh) =
      ⇑(L.toSuccession.stageMap (Fin.last _)) ⁻¹' Set.range h
  | _, _, nil _, h, hh => by
    ext p
    exact ⟨fun hp => hp, fun hp => hp⟩
  | _, _, cons hY rest, h, hh => by
    refine Set.Subset.antisymm (range_pullbackLiftLast_subset _ h hh) ?_
    rintro p ⟨x, hx⟩
    have hx' : h x = Manifold.blowUpπ ψ₀ hY (rest.toSuccession.stageMap (Fin.last _) p) :=
      hx.trans (stageMapAux_cons_succ hY rest _ _ p)
    obtain ⟨q₀, hq₀⟩ := exists_liftStep_eq h hh hY (rest.toSuccession.stageMap (Fin.last _) p) hx'
    have hmem : p ∈ ⇑(rest.toSuccession.stageMap (Fin.last _)) ⁻¹'
        Set.range (liftStep h hh hY) := ⟨q₀, hq₀⟩
    rw [← range_pullbackLiftLast rest (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)]
      at hmem
    exact hmem

/-- The reading open of the chain is the preimage of the range of `h` under the composite
blow-down. -/
theorem mem_liftRange_iff {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (p : L.stage (Fin.last _)) :
    p ∈ L.liftRange h hh ↔ L.toSuccession.stageMap (Fin.last _) p ∈ Set.range h := by
  change p ∈ Set.range (L.pullbackLiftLast h hh) ↔ _
  rw [range_pullbackLiftLast]
  exact Iff.rfl

end AnalyticManifold.BlowUpSequence

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace BDanFamData

open _root_.Manifold

variable {s : ℕ} (bd : BDanFamData ψ₀ s)

/-- **Congruence of pulled-back induced values along equal sequences**: for equal sequences
`L₁ = L₂`, opens of their last stages corresponding under `stageOfEq`, and maps into those opens
agreeing under `stageOfEq`, the pull-backs of the family's values at the induced triples agree (a
substitution). -/
theorem fam_seqOn_induced_pullback_congr {X Z : AnalyticManifold.{u} 𝕜 E}
    {T : AnalyticTriple ψ₀ X} (hT : AnalyticTriple.BOClass s T)
        {L₁ L₂ : AnalyticManifold.BlowUpSequence ψ₀ X}
    (e : L₁ = L₂) (hL₁ : L₁.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf)
    (hL₂ : L₂.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (j : T.F.ι)
    {U₁ : Opens (L₁.stage (Fin.last _))} {U₂ : Opens (L₂.stage (Fin.last _))}
    (hU₁ : IsCompact (closure (U₁ : Set (L₁.stage (Fin.last _)))))
    (hU₂ : IsCompact (closure (U₂ : Set (L₂.stage (Fin.last _)))))
    (hU : ∀ p, p ∈ U₁ ↔ AnalyticManifold.BlowUpSequence.stageOfEq e p ∈ U₂)
    (f₁ : AnalyticMap Z ((L₁.stage (Fin.last _)).restrict U₁))
    (f₂ : AnalyticMap Z ((L₂.stage (Fin.last _)).restrict U₂))
    (hf₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₁)
    (hf₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f₂)
    (hf : ∀ z, AnalyticManifold.BlowUpSequence.stageOfEq e (f₁ z).1 = (f₂ z).1) :
    ((bd.fam (T.induced s L₁ hL₁) (AnalyticTriple.boClass_induced T s L₁ hL₁ hT)
        (L₁.toSuccession.originalIdx T.F (Fin.last _) j)).seqOn U₁ hU₁).pullback f₁ hf₁ =
      ((bd.fam (T.induced s L₂ hL₂) (AnalyticTriple.boClass_induced T s L₂ hL₂ hT)
        (L₂.toSuccession.originalIdx T.F (Fin.last _) j)).seqOn U₂ hU₂).pullback f₂ hf₂ := by
  subst e
  have hUU : U₁ = U₂ := by
    ext p
    have := hU p
    rw [AnalyticManifold.BlowUpSequence.stageOfEq_rfl] at this
    exact this
  subst hUU
  have hff : f₁ = f₂ := ContMDiffMap.ext fun z => Subtype.ext (by
    have := hf z
    rw [AnalyticManifold.BlowUpSequence.stageOfEq_rfl] at this
    exact this)
  subst hff
  rfl

end BDanFamData

end Hironaka.Manifold
