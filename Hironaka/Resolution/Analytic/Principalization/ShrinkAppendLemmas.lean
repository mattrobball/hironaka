/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
public import Hironaka.Resolution.Analytic.Functor.Family
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Restricting the shrink-and-append step

The value of the principalization family on a relatively compact open `U` (`Assembly.lean`) is a
shrink-and-append step (`shrinkAppend` of
`Hironaka/Resolution/Analytic/OrderReduction/FamilyChain.lean`): the disjoining list `L` over the
shrinking open `W`, pulled back along the open inclusion `U → W`, followed by the order-reduction
value read on the reading open, carried along the corestricted lift, with the empty rounds erased.
The compatibility clause of the compatible-family form ([Wlo09, Theorem 2.0.3 (4)]; Kollár's
functoriality for smooth morphisms, [Kol07, 34.1], per open) compares the value on `U ≤ V`: this
module proves the general restriction law of the step,

* `shrinkAppend_pullback_eraseEmpty`: pulling `L.shrinkAppend h B` back along a further local
  isomorphism `k` and erasing the empty rounds gives `L.shrinkAppend (h ∘ k) B'`, up to empty
  rounds, whenever `B'` is `B` restricted to the smaller reading open (up to empty rounds) — by
  induction on `L`, the `cons` step being `liftStep_comp`, the `nil` step the commutation of
  `eraseEmpty` with pull-back (`eraseEmpty_pullback_eraseEmpty`) and the functoriality of the
  pull-back of a sequence (`pullback_comp`; [Kol07, 30.1]);

together with the bookkeeping it needs: the reading opens are nested
(`range_pullbackLiftLast_subset_of_comp`), the last-stage lift carries the reading open of a
composite into the reading open (`image_pullbackLiftLast_liftRange_subset`), `eraseEmpty`
respects a common head (`eraseEmpty_cons_congr`), and the `nil` case in plain variables
(`pullback_pullback_eraseEmpty_of_restrict`). The statements carry the composite as a separate
map `e` with `h.comp k = e` so that the induction can instantiate it with `liftStep e` (the
equation `liftStep (h ∘ k) = liftStep h ∘ liftStep k` is propositional; it enters through
`subst`). Used by `ValueRestrict.lean`, `ShrinkAppendPullback.lean` and the functoriality for
closed embeddings (`Hironaka/Resolution/Analytic/OrderReduction/ClosedEmbeddingFam.lean`).
-/

public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### `eraseEmpty` and the constructors of the step -/

/-- `eraseEmpty` respects a common head: two lists with the same first centre whose tails agree up
to empty rounds agree up to empty rounds. -/
theorem eraseEmpty_cons_congr {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) {R₁ R₂ : BlowUpSequence ψ₀ (Manifold.blowUp ψ₀ hY)}
    (h : R₁.eraseEmpty = R₂.eraseEmpty) :
    (cons hY R₁).eraseEmpty = (cons hY R₂).eraseEmpty := by
  rw [eraseEmpty_cons, eraseEmpty_cons, h]

/-- The shrink-and-append step of the empty list: the appended list pulled back along the
corestriction of `h` onto its range. -/
theorem shrinkAppend_nil {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (B : BlowUpSequence ψ₀ (((nil (ψ₀ := ψ₀) M).stage (Fin.last _)).restrict
      ((nil (ψ₀ := ψ₀) M).liftRange h hh))) :
    (nil (ψ₀ := ψ₀) M).shrinkAppend h hh B =
      B.pullback ((nil (ψ₀ := ψ₀) M).liftCorestrict h hh)
        (isLocalDiffeomorph_liftCorestrict _ h hh) := rfl

/-- The shrink-and-append step of `cons hY rest`: the pulled-back first centre, then the step of
`rest` along the lift of `h` to the blow-ups (`liftStep`). -/
theorem shrinkAppend_cons {M N : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀ (Manifold.blowUp ψ₀ hY))
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (B : BlowUpSequence ψ₀ (((cons hY rest).stage (Fin.last _)).restrict
      ((cons hY rest).liftRange h hh))) :
    (cons hY rest).shrinkAppend h hh B =
      cons (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.shrinkAppend (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) B) := rfl

/-! ### The reading opens of a composite -/

/-- The reading open of a composite `h ∘ k` lies in the reading open of `h`: the ranges of the
last-stage lifts are nested. -/
theorem range_pullbackLiftLast_subset_of_comp :
    ∀ {M N P : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
      (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
      (k : AnalyticMap P N), IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k →
      ∀ (e : AnalyticMap P M) (he : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e), h.comp k = e →
      Set.range (L.pullbackLiftLast e he) ⊆ Set.range (L.pullbackLiftLast h hh)
  | _, _, _, nil _, h, hh, k, _, e, he, hcomp => by
    subst hcomp
    change Set.range (⇑h ∘ ⇑k) ⊆ Set.range ⇑h
    exact Set.range_comp_subset_range ⇑k ⇑h
  | _, _, _, cons hY rest, h, hh, k, hk, e, he, hcomp => by
    subst hcomp
    exact range_pullbackLiftLast_subset_of_comp rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY) (liftStep k hk (hY.preimage_of_isLocalDiffeomorph hh))
      (isLocalDiffeomorph_liftStep k hk _) (liftStep (h.comp k) he hY)
      (isLocalDiffeomorph_liftStep (h.comp k) he hY) (liftStep_comp h hh k hk hY).symm

/-- The last-stage lift of `π` carries the reading open of `j` (through `π^* L`) into the reading
open of the composite `π ∘ j` (through `L`). -/
theorem image_pullbackLiftLast_liftRange_subset :
    ∀ {M X P : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
      (π : AnalyticMap X M) (hπ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
      (j : AnalyticMap P X) (hj : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω j)
      (e : AnalyticMap P M) (he : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e), π.comp j = e →
      ⇑(L.pullbackLiftLast π hπ) '' ((L.pullback π hπ).liftRange j hj : Set _) ⊆
        (L.liftRange e he : Set (L.stage (Fin.last _)))
  | _, _, _, nil _, π, hπ, j, hj, e, he, hcomp => by
    subst hcomp
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, rfl⟩
  | _, _, _, cons hY rest, π, hπ, j, hj, e, he, hcomp => by
    subst hcomp
    exact image_pullbackLiftLast_liftRange_subset rest (liftStep π hπ hY)
      (isLocalDiffeomorph_liftStep π hπ hY) (liftStep j hj (hY.preimage_of_isLocalDiffeomorph hπ))
      (isLocalDiffeomorph_liftStep j hj _) (liftStep (π.comp j) he hY)
      (isLocalDiffeomorph_liftStep (π.comp j) he hY) (liftStep_comp π hπ j hj hY).symm

/-! ### The restriction law of the step -/

/-- The `nil` case of the restriction law, in plain variables: two pull-backs of `B` along maps
into the reading open agree with the pull-back of the restricted list `B'` along the composite,
up to empty rounds (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`, `pullback_congr`). -/
theorem pullback_pullback_eraseEmpty_of_restrict {X N P : AnalyticManifold.{u} 𝕜 E}
    {R R' : Opens X} (hle : R' ≤ R) (B : BlowUpSequence ψ₀ (X.restrict R))
    (B' : BlowUpSequence ψ₀ (X.restrict R'))
    (hB : B'.eraseEmpty =
      (B.pullback (X.restrictLE hle) (isLocalDiffeomorph_restrictLE hle)).eraseEmpty)
    (c₁ : AnalyticMap N (X.restrict R)) (hc₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω c₁)
    (k : AnalyticMap P N) (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k)
    (c₂ : AnalyticMap P (X.restrict R')) (hc₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω c₂)
    (hcomp : c₁.comp k = (X.restrictLE hle).comp c₂) :
    ((B.pullback c₁ hc₁).pullback k hk).eraseEmpty = (B'.pullback c₂ hc₂).eraseEmpty := by
  rw [pullback_comp B c₁ hc₁ k hk,
    pullback_congr B hcomp _ (isLocalDiffeomorph_comp (isLocalDiffeomorph_restrictLE hle) hc₂),
    ← pullback_comp B _ (isLocalDiffeomorph_restrictLE hle) c₂ hc₂,
    ← eraseEmpty_pullback_eraseEmpty (B.pullback _ (isLocalDiffeomorph_restrictLE hle)) c₂ hc₂,
    ← hB, eraseEmpty_pullback_eraseEmpty]

/-- **The shrink-and-append step restricts** (the compatibility clause of
[Wlo09, Theorem 2.0.3 (4)]; [Kol07, 34.1] per open). Pulling `L.shrinkAppend h B` back along a
further local analytic isomorphism `k` and erasing the empty rounds is `L.shrinkAppend (h ∘ k) B'`
up to empty rounds, whenever `B'` is `B` restricted to the smaller reading open, up to empty
rounds. The composite is carried as a separate map `e` with `h.comp k = e` so the induction can
instantiate it with `liftStep e` (`liftStep_comp`). -/
theorem shrinkAppend_pullback_eraseEmpty :
    ∀ {M N P : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
      (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
      (k : AnalyticMap P N) (hk : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω k)
      (e : AnalyticMap P M) (he : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e), h.comp k = e →
      ∀ (B : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange h hh)))
        (B' : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange e he)))
        (hle : L.liftRange e he ≤ L.liftRange h hh),
        B'.eraseEmpty = (B.pullback ((L.stage (Fin.last _)).restrictLE hle)
          (isLocalDiffeomorph_restrictLE hle)).eraseEmpty →
        ((L.shrinkAppend h hh B).pullback k hk).eraseEmpty = (L.shrinkAppend e he B').eraseEmpty
  | _, _, _, nil M, h, hh, k, hk, e, he, hcomp, B, B', hle, hB => by
    subst hcomp
    have hc : ((nil (ψ₀ := ψ₀) M).liftCorestrict h hh).comp k =
        (((nil (ψ₀ := ψ₀) M).stage (Fin.last _)).restrictLE hle).comp
          ((nil (ψ₀ := ψ₀) M).liftCorestrict (h.comp k) he) :=
      ContMDiffMap.ext fun _ => Subtype.ext rfl
    exact pullback_pullback_eraseEmpty_of_restrict hle B B' hB _
      (isLocalDiffeomorph_liftCorestrict _ h hh) k hk _
      (isLocalDiffeomorph_liftCorestrict _ (h.comp k) he) hc
  | _, _, _, cons hY rest, h, hh, k, hk, e, he, hcomp, B, B', hle, hB => by
    subst hcomp
    exact eraseEmpty_cons_congr _ (shrinkAppend_pullback_eraseEmpty rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY) (liftStep k hk (hY.preimage_of_isLocalDiffeomorph hh))
      (isLocalDiffeomorph_liftStep k hk _) (liftStep (h.comp k) he hY)
      (isLocalDiffeomorph_liftStep (h.comp k) he hY) (liftStep_comp h hh k hk hY).symm
      B B' hle hB)

end AnalyticManifold.BlowUpSequence
