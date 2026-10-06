/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Cons
public import Hironaka.Manifold.FiniteSuccession.Lift
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Blow-up sequences as lists of centres

A blow-up sequence is determined by its list of centres [Kol07, Definition 29]. This module
realises that view on analytic manifolds: the inductive type `CenterList ψ₀ M` of blow-up
sequences `(X_r, …) → ⋯ → (X_0) = M` given by their centres, with constructors `nil M` and
`cons hY rest`, where `hY : IsClosedSubmanifold ψ₀ Y c` is a closed submanifold of the current
stage and `rest` a list on the blowing-up `blowUp ψ₀ hY`, with one fixed model chart
`ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)` for every stage. The algebraic counterpart is the inductive
`BlowUpSequence X`, on which equality is equality of the centres, the form in which the uniqueness
theorem for blow-up sequence functors [Kol07, Theorem 97] concludes `B = B'`. On the structure
`FiniteSuccession M` (Włodarczyk's finite sequence, with the stages, blow-downs and chart data as
fields) equality is strictly finer than equality of the centres, since a stage may be replaced by
a diffeomorphic copy and the chart of a stage is chosen from `isMonoidal i`; the uniqueness
theorems for analytic blow-up sequences are therefore stated on lists. Every list is a
`FiniteSuccession` through `toSuccession` (the constructors `FiniteSuccession.nil` and
`FiniteSuccession.cons`), so that the theorems on sequences apply to it.

* `CenterList ψ₀ M`, `toSuccession`, `length`, `stage`;
* `pullback L h hh`: the pull-back `h^*B` of the list along a local analytic isomorphism
  `h : N → M` [Kol07, 30.1], with the blowing-up of the preimage centre in place
  of the fibre product `X_{i+1} ×_X Y`: by recursion on the list, the centre `h_i⁻¹(Z_i)` at
  every stage (`IsClosedSubmanifold.preimage_of_isLocalDiffeomorph`) and the lift `h_{i+1}` of
  `h_i` to the blow-ups (`blowUpLift`, `liftStep`), canonically and with no choice of chart;
* `pullbackLift L h hh i`: the lifts `h_i : N_i → M_i`, local analytic isomorphisms;
* `length_pullback`, `toSuccession_nil`, `toSuccession_cons`, `pullback_nil`, `pullback_cons`,
  and the recursion `stageMapAux_cons_succ` of the composite blow-down.
-/

@[expose] public section

noncomputable section

open TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u v

namespace AnalyticManifold

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-- **A blow-up sequence as its list of centres** [Kol07, Definition 29], on analytic manifolds:
`nil M` is the empty sequence, and `cons hY rest` blows up the closed submanifold `Y` of the
current stage (`hY : IsClosedSubmanifold ψ₀ Y c`, with the model chart `ψ₀` fixed once for all
stages) and continues with `rest` on the blowing-up `blowUp ψ₀ hY`. Equality of lists is equality
of the centres stage by stage (the `hY` fields are proofs). -/
inductive BlowUpSequence (ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)) : AnalyticManifold.{u} 𝕜 E → Type (max
    (u + 1) v)
  | nil (M : AnalyticManifold.{u} 𝕜 E) : BlowUpSequence ψ₀ M
  | cons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
      (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) : BlowUpSequence ψ₀ M

namespace BlowUpSequence

open Manifold

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The list as a finite sequence of monoidal transformations (through the constructors `nil` and
`cons` of `FiniteSuccession`), so that every theorem on sequences applies to it. -/
def toSuccession : {M : AnalyticManifold.{u} 𝕜 E} → BlowUpSequence ψ₀ M → FiniteSuccession M
  | _, nil M => FiniteSuccession.nil M
  | _, cons hY rest => FiniteSuccession.cons ψ₀ hY rest.toSuccession

theorem toSuccession_nil (M : AnalyticManifold.{u} 𝕜 E) :
    (nil (ψ₀ := ψ₀) M).toSuccession = FiniteSuccession.nil M := rfl

@[simp]
theorem toSuccession_cons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) :
    (cons hY rest).toSuccession = FiniteSuccession.cons ψ₀ hY rest.toSuccession := rfl

/-- The length `r` (the number of blow-ups). -/
abbrev length {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) : ℕ := L.toSuccession.length

/-- The stages `M = M_0, M_1, …, M_r`. -/
abbrev stage {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) (i : Fin (L.length + 1)) :
    AnalyticManifold.{u} 𝕜 E :=
  L.toSuccession.stage i

/-! ### The pull-back along a local analytic isomorphism -/

section Pullback

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- One step of the pull-back: the lift `h₁ : Bl_{h⁻¹Y} N → Bl_Y M` of the local analytic
isomorphism `h` over the two blow-downs, as a bundled analytic map. -/
def liftStep (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M}
    {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) :
    AnalyticMap (blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) (blowUp ψ₀ hY) :=
  ⟨blowUpLift hY hh (isBlowUp_blowUpπ ψ₀ hY)
      (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)),
    contMDiff_blowUpLift hY hh (isBlowUp_blowUpπ ψ₀ hY)
      (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))⟩

/-- The lift is a local analytic isomorphism (`isLocalDiffeomorph_blowUpLift`). -/
theorem isLocalDiffeomorph_liftStep (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (liftStep h hh hY) :=
  isLocalDiffeomorph_blowUpLift hY hh (isBlowUp_blowUpπ ψ₀ hY)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))

/-- The lift lies over `h`: `π ∘ h₁ = h ∘ π'`. -/
theorem blowUpπ_liftStep (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (q : blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) :
    blowUpπ ψ₀ hY (liftStep h hh hY q) = h (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh) q) :=
  blowDown_blowUpLift hY hh (isBlowUp_blowUpπ ψ₀ hY)
    (isBlowUp_blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh)) q

/-- **The pull-back `h^*L`** of the list along a local analytic isomorphism `h : N → M`
[Kol07, 30.1]: the list of the preimage centres `h_i⁻¹(Z_i)` under the successive
lifts `h_i`, by recursion on the list. -/
def pullback : {M N : AnalyticManifold.{u} 𝕜 E} → BlowUpSequence ψ₀ M → (h : AnalyticMap N M) →
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h → BlowUpSequence ψ₀ N
  | _, N, nil _, _, _ => nil N
  | _, _, cons hY rest, h, hh =>
    cons (hY.preimage_of_isLocalDiffeomorph hh)
      (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY))

@[simp]
theorem pullback_nil (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (nil (ψ₀ := ψ₀) M).pullback h hh = nil N := rfl

@[simp]
theorem pullback_cons {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (cons hY rest).pullback h hh =
      cons (hY.preimage_of_isLocalDiffeomorph hh)
        (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)) := rfl

/-- The pull-back has the length of the list. -/
@[simp]
theorem length_pullback : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    (L.pullback h hh).length = L.length
  | _, _, nil _, _, _ => rfl
  | _, _, cons hY rest, h, hh => by
    change (rest.pullback _ _).length + 1 = rest.length + 1
    rw [length_pullback rest]

/-- The lifts `h_i : N_i → M_i` of `h` to the stages of the pull-back, indexed by the stage number
(`h_0 = h`, `h_{i+1}` the lift of `h_i`, `liftStep`). -/
def pullbackLiftAux : {M N : AnalyticManifold.{u} 𝕜 E} → (L : BlowUpSequence ψ₀ M) →
    (h : AnalyticMap N M) → (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) → (i : ℕ) →
    (hi : i < L.length + 1) → (hi' : i < (L.pullback h hh).length + 1) →
    AnalyticMap (finStages N (L.pullback h hh).toSuccession.later ⟨i, hi'⟩)
      (finStages M L.toSuccession.later ⟨i, hi⟩)
  | _, _, nil _, h, _, 0, _, _ => h
  | _, _, cons _ _, h, _, 0, _, _ => h
  | _, _, cons hY rest, h, hh, i + 1, hi, hi' =>
    rest.pullbackLiftAux (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY) i
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hi')
  | _, _, nil _, _, _, i + 1, hi, _ =>
    absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- **The lifts `h_i : N_i → M_i`** of the local analytic isomorphism `h` to the stages of `h^*L`
and `L`. -/
def pullbackLift (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (i : Fin (L.length + 1)) :
    AnalyticMap ((L.pullback h hh).stage ⟨i.1, by rw [length_pullback]; exact i.2⟩) (L.stage i) :=
  L.pullbackLiftAux h hh i.1 i.2 (by rw [length_pullback]; exact i.2)

theorem pullbackLift_zero (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) : L.pullbackLift h hh 0 = h := by
  cases L <;> rfl

end Pullback

section M20

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The composite blow-down of the list `cons hY rest` at stage `i + 1` is the first blow-down after
the composite of the rest at stage `i`. -/
theorem stageMapAux_cons_succ {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)
    (rest : BlowUpSequence ψ₀ (blowUp ψ₀ hY)) : ∀ (i : ℕ)
    (hi : i + 1 < (cons hY rest).toSuccession.length + 1)
    (p : (cons hY rest).toSuccession.stage ⟨i + 1, hi⟩),
    (cons hY rest).toSuccession.stageMapAux (i + 1) hi p =
      blowUpπ ψ₀ hY (rest.toSuccession.stageMapAux i (Nat.lt_of_succ_lt_succ hi) p)
  | 0, _, _ => rfl
  | i + 1, hi, p =>
    stageMapAux_cons_succ hY rest i (Nat.lt_of_succ_lt hi)
      (rest.toSuccession.map ⟨i, Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)⟩ p)

end M20

end BlowUpSequence

end AnalyticManifold

end
