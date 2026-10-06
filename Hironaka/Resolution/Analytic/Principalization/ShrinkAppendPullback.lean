/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.ShrinkAppendLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The shrink-and-append step of a pulled-back list

The second general law behind the compatibility clause of the principalization family: the
shrink-and-append step of the pulled-back list `π^* L` along `j`, up to empty rounds, is the step
of `L` along the composite `π ∘ j`, whenever the two appended lists correspond along the
last-stage lift of `π` restricted to the reading opens (`pullbackLiftRestrict`, the corestriction
of `pullbackLiftLast π`). With `shrinkAppend_pullback_eraseEmpty` this reduces the comparison of
the values of two disjoining lists related by a local analytic isomorphism to the commutation of
the input family with local isomorphisms (`CommutesWithLocalIsos`; Kollár's functoriality for
smooth morphisms [Kol07, 34.1], the pull-back of a blow-up sequence being [Kol07, 30.1]). Used by
`ValueNatural.lean`.
-/

@[expose] public section

universe u

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The `nil` case in plain variables: the pull-backs of two lists corresponding along `l` agree
up to empty rounds when the maps compose (`eraseEmpty_pullback_eraseEmpty`, `pullback_comp`,
`pullback_congr`). -/
theorem pullback_eraseEmpty_of_restrictMap {X Y P : AnalyticManifold.{u} 𝕜 E} {R₁ : Opens X}
    {R₂ : Opens Y} (B₁ : BlowUpSequence ψ₀ (X.restrict R₁)) (B₂ : BlowUpSequence ψ₀ (Y.restrict R₂))
    (l : AnalyticMap (X.restrict R₁) (Y.restrict R₂))
    (hl : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω l)
    (hB : B₁.eraseEmpty = (B₂.pullback l hl).eraseEmpty)
    (c₁ : AnalyticMap P (X.restrict R₁)) (hc₁ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω c₁)
    (c₂ : AnalyticMap P (Y.restrict R₂)) (hc₂ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω c₂)
    (hcomp : l.comp c₁ = c₂) :
    (B₁.pullback c₁ hc₁).eraseEmpty = (B₂.pullback c₂ hc₂).eraseEmpty := by
  rw [← eraseEmpty_pullback_eraseEmpty B₁ c₁ hc₁, hB, eraseEmpty_pullback_eraseEmpty,
    pullback_comp B₂ l hl c₁ hc₁, pullback_congr B₂ hcomp _ hc₂]

/-- The last-stage lift of `π`, restricted to the reading open of `j` through `π^* L` and
corestricted to the reading open of the composite `π ∘ j` through `L`
(`image_pullbackLiftLast_liftRange_subset`). -/
noncomputable def pullbackLiftRestrict {M X P : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (π : AnalyticMap X M) (hπ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
    (j : AnalyticMap P X) (hj : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω j)
    (e : AnalyticMap P M) (he : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e) (hcomp : π.comp j = e) :
    AnalyticMap (((L.pullback π hπ).stage (Fin.last _)).restrict
        ((L.pullback π hπ).liftRange j hj))
      ((L.stage (Fin.last _)).restrict (L.liftRange e he)) :=
  AnalyticMap.restrictMap (L.pullbackLiftLast π hπ) _ _
    (image_pullbackLiftLast_liftRange_subset L π hπ j hj e he hcomp)

theorem isLocalDiffeomorph_pullbackLiftRestrict {M X P : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (π : AnalyticMap X M) (hπ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
    (j : AnalyticMap P X) (hj : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω j)
    (e : AnalyticMap P M) (he : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e) (hcomp : π.comp j = e) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (L.pullbackLiftRestrict π hπ j hj e he hcomp) :=
  AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_pullbackLiftLast L π hπ) _ _ _

/-- **The shrink-and-append step of a pulled-back list** ([Kol07, 30.1; 34.1]). The step of `π^* L`
along `j`, up to empty rounds, is the step of `L` along `π ∘ j`, whenever the appended lists
correspond along the restricted last-stage lift of `π` (up to empty rounds). Induction on `L`;
the `cons` step is `liftStep_comp`. -/
theorem pullback_shrinkAppend_eraseEmpty :
    ∀ {M X P : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
      (π : AnalyticMap X M) (hπ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω π)
      (j : AnalyticMap P X) (hj : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω j)
      (e : AnalyticMap P M) (he : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω e) (hcomp : π.comp j = e)
      (B₁ : BlowUpSequence ψ₀ (((L.pullback π hπ).stage
          (Fin.last _)).restrict
        ((L.pullback π hπ).liftRange j hj)))
      (B₂ : BlowUpSequence ψ₀ ((L.stage (Fin.last _)).restrict (L.liftRange e he))),
      B₁.eraseEmpty = (B₂.pullback (L.pullbackLiftRestrict π hπ j hj e he hcomp)
        (isLocalDiffeomorph_pullbackLiftRestrict L π hπ j hj e he hcomp)).eraseEmpty →
      ((L.pullback π hπ).shrinkAppend j hj B₁).eraseEmpty = (L.shrinkAppend e he B₂).eraseEmpty
  | _, _, _, nil M, π, hπ, j, hj, e, he, hcomp, B₁, B₂, hB => by
    subst hcomp
    have hc : ((nil (ψ₀ := ψ₀) M).pullbackLiftRestrict π hπ j hj (π.comp j) he rfl).comp
        (((nil (ψ₀ := ψ₀) M).pullback π hπ).liftCorestrict j hj) =
        (nil (ψ₀ := ψ₀) M).liftCorestrict (π.comp j) he :=
      ContMDiffMap.ext fun _ => Subtype.ext rfl
    exact pullback_eraseEmpty_of_restrictMap B₁ B₂ _ _ hB _
      (isLocalDiffeomorph_liftCorestrict _ j hj) _
      (isLocalDiffeomorph_liftCorestrict _ (π.comp j) he) hc
  | _, _, _, cons hY rest, π, hπ, j, hj, e, he, hcomp, B₁, B₂, hB => by
    subst hcomp
    exact eraseEmpty_cons_congr _ (pullback_shrinkAppend_eraseEmpty rest (liftStep π hπ hY)
      (isLocalDiffeomorph_liftStep π hπ hY) (liftStep j hj (hY.preimage_of_isLocalDiffeomorph hπ))
      (isLocalDiffeomorph_liftStep j hj _) (liftStep (π.comp j) he hY)
      (isLocalDiffeomorph_liftStep (π.comp j) he hY) (liftStep_comp π hπ j hj hY).symm
      B₁ B₂ hB)

end AnalyticManifold.BlowUpSequence
