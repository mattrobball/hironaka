/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Rounds
public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyPullback
public import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyConcat
import Hironaka.Resolution.Analytic.OrderReduction.LiftUnique
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The rounds read through a composite: restriction of the reading map

The rounds of the resolution family (`resolveFrom`,
`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`) read through a composite `ι ∘ j` of local analytic
isomorphisms are the rounds read through `ι`, pulled back along `j`: an equality of lists before any
erasing (`resolveFrom_comp`). This is the pull-back of a blow-up sequence along a smooth morphism
[Kol07, 30.1] for the concatenation of the rounds, and it gives the `compat` field of the resolution
family `resolveFam` at `ι := restrictLE (V ≤ W)`, `j := restrictLE (U ≤ V)`, once canonicity
(`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`) has identified the values along the two
chains.

The proof is the induction on the number of rounds that defines `resolveFrom`, unfolded at the
successor case only: the round's list pulled back along `ι' ∘ j` is its pull-back along `ι'` pulled
back along `j` (`pullback_comp`), the last-stage lift of the composite is the composite of the
last-stage lifts up to the identification `stageOfEq` of the two pulled-back lists
(`pullbackLiftLast_comp_apply`, uniqueness of lifts), and the concatenation absorbs that
identification (`concat_pullback_stageOfEq`). Two congruences do the bookkeeping: the rounds
depend on the reading map alone (`resolveFrom_congr_ι`), and pulling the second piece of a
concatenation back along `stageOfEq` of an equality of first pieces is the identity
(`concat_pullback_stageOfEq`, the pull-back form of `concat_map_stageOfEq`). List algebra, not in
the sources.
-/

public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

section Tools

variable {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- Transport of the second piece of a concatenation along an equality of first pieces, the
pull-back form of `concat_map_stageOfEq`: pulling the second piece back along the cast
`stageOfEq e` absorbs the cast. -/
theorem concat_pullback_stageOfEq
    {L₁ L₂ : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M}
        (e : L₂ = L₁)
    (R : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (L₁.stage
        (Fin.last _)))
    (he : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
      (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq e))) :
    L₂.concat (R.pullback (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq e))
        he) =
      L₁.concat R := by
  subst e
  congr 1
  exact (AnalyticManifold.BlowUpSequence.pullback_congr R (ContMDiffMap.ext fun _ => rfl) he
    (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id _)).trans
        (AnalyticManifold.BlowUpSequence.pullback_id R)

end Tools

section Comp

variable (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- The rounds depend on the reading map only (its proofs are irrelevant): a congruence along an
equality of reading maps. -/
theorem resolveFrom_congr_ι (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} {ι₁ ι₂ : AnalyticMap N X} (hι : ι₁ = ι₂)
    (h₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι₁) (r₁ : Set.range ι₁ ⊆ Ω 0)
    (h₂ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι₂) (r₂ : Set.range ι₂ ⊆ Ω 0) :
    resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι₁ h₁ r₁ =
      resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι₂ h₂ r₂ := by
  subst hι
  rfl

/-- **Restriction of the reading map.** The rounds read through `ι ∘ j` are the rounds read through
`ι`, pulled back along the local analytic isomorphism `j`: an equality of lists before any erasing
([Kol07, 30.1] for the concatenation: `pullback_concat`, `pullback_comp`, the last-stage lifts
compose). The `compat` field of `resolveFam` is this at `ι := restrictLE (V ≤ W)`,
`j := restrictLE (U ≤ V)`, after canonicity. -/
theorem resolveFrom_comp (d : ℕ) {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N N' : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0)
    (j : AnalyticMap N' N) (hj : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω j)
    (hrange' : Set.range (ι.comp j) ⊆ Ω 0) :
    resolveFrom bo d cur hord hfin Ω hΩ hΩsub (ι.comp j)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hι hj) hrange' =
      (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).pullback j hj := by
  induction d generalizing X N N' with
  | zero => rw [resolveFrom, resolveFrom, AnalyticManifold.BlowUpSequence.pullback_nil]
  | succ d ih =>
    -- the round's list `L'`, the corestricted reading map `ι'` and its composite with `j`
    have hr : Set.range ι ⊆ Ω d := range_subset_chain hΩsub hrange
    have hr' : Set.range (ι.comp j) ⊆ Ω d := range_subset_chain hΩsub hrange'
    have hι' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (AnalyticMap.corestrict ι (Ω d) hr) := isLocalDiffeomorph_corestrict ι (Ω d) hι hr
    have hι'j : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        ((AnalyticMap.corestrict ι (Ω d) hr).comp j) :=
            AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hι' hj
    set L' := roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
      (hΩ d (Nat.lt_succ_self d))
    -- the lists: `pc : (L'.pullback ι').pullback j = L'.pullback (ι' ∘ j)`
    have pc := AnalyticManifold.BlowUpSequence.pullback_comp L' (AnalyticMap.corestrict ι
        (Ω d) hr) hι' j hj
    -- the lifts and their local-isomorphism / range facts
    set k := L'.pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hr) hι'
    set jl := (L'.pullback (AnalyticMap.corestrict ι (Ω d) hr) hι').pullbackLiftLast j hj
    set k₁ := L'.pullbackLiftLast ((AnalyticMap.corestrict ι (Ω d) hr).comp j) hι'j
    have hk : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω k :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _
    have hjl : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω jl :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _
    have hk₁ : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω k₁ :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _
    have hs : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq pc)) :=
            Diffeomorph.isLocalDiffeomorph _
    have hkjl : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (k.comp jl) :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hk hjl
    have hk₁s : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω
        (k₁.comp (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq pc))) :=
      AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hk₁ hs
    have hrk : Set.range k ⊆ liftChain L' Ω 0 :=
      range_pullbackLiftLast_subset_liftOpens _ ι hι (Ω 0) hrange hr
    have hrk₁ : Set.range k₁ ⊆ liftChain L' Ω 0 :=
      range_pullbackLiftLast_subset_liftOpens _ (ι.comp j)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_comp hι hj) (Ω 0) hrange' hr'
    have hrkjl : Set.range (k.comp jl) ⊆ liftChain L' Ω 0 := by
      rintro _ ⟨q, rfl⟩
      exact hrk ⟨jl q, rfl⟩
    have hrk₁s : Set.range (k₁.comp (Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq pc))) ⊆
        liftChain L' Ω 0 := by
      rintro _ ⟨q, rfl⟩
      exact hrk₁ ⟨AnalyticManifold.BlowUpSequence.stageOfEq pc q, rfl⟩
    -- `k ∘ jl = k₁ ∘ stageOfEq pc` (uniqueness of the last-stage lift)
    have hcomp : k.comp jl = k₁.comp (Diffeomorph.toAnalyticMap
        (AnalyticManifold.BlowUpSequence.stageOfEq pc)) :=
      ContMDiffMap.ext fun q => AnalyticManifold.BlowUpSequence.pullbackLiftLast_comp_apply _ _ _ j
          hj q
    -- the derived data of the round
    set cur' := derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
      (hΩ d (Nat.lt_succ_self d))
    have hord' : ∀ x, cur'.I.ord x ≤ (d : ℕ∞) := derivedTriple_ord_le bo cur _ (Ω d) _
    have hfin' : Finite {j // cur'.F.hyp j ≠ ∅} := derivedTriple_finite bo cur _ (Ω d) _
    have hΩ' := liftChain_isCompact L' hΩ hΩsub rfl
    have hΩsub' := liftChain_closure_subset L' hΩsub
    -- the second factors: the induction hypothesis twice around the congruence `hcomp`
    have e₂ : (resolveFrom bo d cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' k hk hrk).pullback
          jl hjl =
        (resolveFrom bo d cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' k₁ hk₁ hrk₁).pullback
          (Diffeomorph.toAnalyticMap (AnalyticManifold.BlowUpSequence.stageOfEq pc)) hs :=
      (ih cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' k hk hrk jl hjl hrkjl).symm.trans
        ((resolveFrom_congr_ι bo d cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' hcomp hkjl hrkjl
          hk₁s hrk₁s).trans
        (ih cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' k₁ hk₁ hrk₁ _ hs hrk₁s))
    -- assemble: unfold both sides at `d + 1` (never `rfl` across the recursion)
    change (L'.pullback ((AnalyticMap.corestrict ι (Ω d) hr).comp j) hι'j).concat
        (resolveFrom bo d cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' k₁ hk₁ hrk₁) =
      ((L'.pullback (AnalyticMap.corestrict ι (Ω d) hr) hι').concat
        (resolveFrom bo d cur' hord' hfin' (liftChain L' Ω) hΩ' hΩsub' k hk hrk)).pullback j hj
    rw [AnalyticManifold.BlowUpSequence.pullback_concat]
    exact ((congrArg ((L'.pullback (AnalyticMap.corestrict ι (Ω d) hr) hι').pullback j hj).concat
      e₂).trans (concat_pullback_stageOfEq pc _ hs)).symm

end Comp

end Hironaka.Manifold

end
