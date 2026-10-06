/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmpty
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Pull-back along surjective local analytic isomorphisms: empty centres and injectivity

A good blow-up sequence functor should commute with smooth surjections [Kol07, 34.1]: the pull-back
along a surjective local analytic isomorphism of a list without empty centres has none (the centres
are preimages of nonempty sets under surjective lifts, `surjective_blowUpLift`), so `eraseEmpty`
changes nothing. The uniqueness of [Kol07, Proposition 37] (`g^* B̄'(X) = B(X') = g^* B̄(X)` forces
`B̄'(X) = B̄(X)`, by [Kol07, Definition 30, 30.1]): pull-back along a surjective local analytic
isomorphism is injective on lists of centres (the centres are recovered as images, and the lifts
are again surjective).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- [Kol07, Definition 30, 30.1]: the lift of a surjective local analytic isomorphism is surjective
(`surjective_blowUpLift`). -/
theorem surjective_liftStep (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (hs : Function.Surjective h) :
    Function.Surjective (liftStep h hh hY) :=
  surjective_blowUpLift hY hh (isBlowUp_blowUpπ ψ₀ hY)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) hs

/-- The pull-back along a surjective local analytic isomorphism of a list without empty centres
has no empty centre. -/
theorem noEmptyCenters_pullback_of_surjective : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    Function.Surjective h → L.NoEmptyCenters → (L.pullback h hh).NoEmptyCenters
  | _, _, nil _, _, _, _, _ => noEmptyCenters_nil
  | _, _, cons hY rest, h, hh, hs, hL => by
    rw [pullback_cons, noEmptyCenters_cons_iff]
    obtain ⟨hne, hrest⟩ := (noEmptyCenters_cons_iff hY rest).mp hL
    refine ⟨fun h0 => hne (hs.preimage_injective (h0.trans Set.preimage_empty.symm)),
      noEmptyCenters_pullback_of_surjective rest _ _ (surjective_liftStep h hh hY hs) hrest⟩

/-- [Kol07, 34.1] (`eraseEmpty_pullback_of_surjective`): deleting the
empty blow-ups of the pull-back along a surjective local analytic isomorphism changes nothing. -/
theorem eraseEmpty_pullback_of_surjective (L : BlowUpSequence ψ₀ M) (hL : L.NoEmptyCenters)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hs : Function.Surjective h) : (L.pullback h hh).eraseEmpty = L.pullback h hh :=
  eraseEmpty_of_noEmptyCenters _ (noEmptyCenters_pullback_of_surjective L h hh hs hL)

/-- [Kol07, Proposition 37]: pull-back along a surjective local
analytic isomorphism is injective on lists of centres. -/
theorem pullback_injective_of_surjective : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h), Function.Surjective h →
    ∀ (L L' : BlowUpSequence ψ₀ M), L.pullback h hh = L'.pullback h hh → L = L'
  | _, _, _, _, _, nil _, nil _, _ => rfl
  | _, _, h, hh, _, nil _, cons hY' rest', heq => by
    rw [pullback_nil, pullback_cons] at heq
    cases heq
  | _, _, h, hh, _, cons hY rest, nil _, heq => by
    rw [pullback_nil, pullback_cons] at heq
    cases heq
  | _, _, h, hh, hs, @cons _ _ _ _ _ _ _ _ Y c hY rest, @cons _ _ _ _ _ _ _ _ Y' c' hY' rest',
      heq => by
    rw [pullback_cons, pullback_cons] at heq
    have hinj := cons.inj heq
    have hYY : Y = Y' := hs.preimage_injective hinj.1
    subst hYY
    have hcc : c = c' := hinj.2.1
    subst hcc
    have hr : rest = rest' :=
      pullback_injective_of_surjective (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)
        (surjective_liftStep h hh hY hs) rest rest' (eq_of_heq hinj.2.2)
    subst hr
    rfl

end AnalyticManifold.BlowUpSequence

end
