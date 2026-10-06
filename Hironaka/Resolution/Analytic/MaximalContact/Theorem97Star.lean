/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Resolution.Analytic.MaximalContact.OneStepDescent
import Hironaka.Resolution.Analytic.MaximalContact.Theorem97Induction
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's Theorem 97 in marked form, on lists of centres

Two blow-up sequences `L, L'` of `M` (lists of centres) that are local-isomorphism equivalent for
`(I, m)` through `ψ, ψ' : U ⇉ M` ([Kol07, Definition 96], with local analytic isomorphisms in
place of étale surjections), whose common pull-back `C = ψ^*L = ψ'^*L'` is of order `≥ 1` for
`(MC(ψ^*I), 1)` and whose centres lie in the images of the lifts, are equal
(`BlowUpSequence.eq_of_locallyIsoEquivalentSequences`) — Kollár's uniqueness of blow-up sequences
[Kol07, Theorem 97], with the hypothesis "of order `m = max-ord I`" replaced by the marked form
his induction actually uses (his "`Z_i^U ⊆ W_i` by (77)"). It is the induction
`BlowUpSequence.eq_of_pullback_eq_of_step`
(`Hironaka/Resolution/Analytic/MaximalContact/Theorem97Induction.lean`) fed with the one-step
descent lemma `agreeOnSubspace_blowUpLift`
(`Hironaka/Resolution/Analytic/MaximalContact/OneStepDescent.lean`) at the list's model chart `ψ₀`
at every stage. Włodarczyk's descent of the canonical resolution through the glueing automorphism is
the same statement [Wlo09, Lemma 5.5.3 (5); §6, Step 1bb of the proof of Theorem 6.0.6]. It is what
makes the order-reduction algorithm independent of the choice of the hypersurface of maximal contact
(`Hironaka/Resolution/Analytic/OrderReduction/FamilyIndependence.lean`).
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff

universe u v

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- **Kollár's Theorem 97 in marked form** [Kol07, Theorem 97]: two local-isomorphism equivalent
lists of centres whose common pull-back is of order `≥ 1` for `(MC(ψ^*I), 1)`, with centres in the
images of the lifts, are equal — the induction `eq_of_pullback_eq_of_step` with the one-step
descent lemma `agreeOnSubspace_blowUpLift`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.eq_of_locallyIsoEquivalentSequences
    {I : AnalyticManifold.IdealSheaf M}
    {m : ℕ}
    {L L' : AnalyticManifold.BlowUpSequence ψ₀ M} (e : LocallyIsoEquivalentSequences I m L L')
    (hW : (L.pullback e.ψ e.isLocalDiffeomorph_ψ).toSuccession.IsMarkedOne
      ((Manifold.IdealSheaf.pullback e.ψ e.ψ.contMDiff I).iteratedDeriv (m - 1)))
    (h3 : ∀ i : Fin L.length, (L.toSuccession.center i).support ⊆
      Set.range (L.pullbackLift e.ψ e.isLocalDiffeomorph_ψ i.castSucc))
    (h3' : ∀ i : Fin L'.length, (L'.toSuccession.center i).support ⊆
      Set.range (L'.pullbackLift e.ψ' e.isLocalDiffeomorph_ψ' i.castSucc)) :
    L = L' :=
  AnalyticManifold.BlowUpSequence.eq_of_pullback_eq_of_step
    (fun {_M _U} f g {_Y _Z _c} hY hZ hZf hZg J hJZ hfg f' g' hf' hg' =>
      agreeOnSubspace_blowUpLift ψ₀ f g hY hZ hZf hZg J hJZ hfg f' g' hf' hg')
    L e.ψ e.ψ' e.isLocalDiffeomorph_ψ e.isLocalDiffeomorph_ψ' L' _ e.h2 hW h3 h3' e.h3

end Manifold

end
