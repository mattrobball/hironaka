/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.Restrict.BaseTransport
public import Hironaka.Manifold.FiniteSuccession.Basic
public import Hironaka.Manifold.BlowUp.Divisor
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Transport of a list of centres along an analytic isomorphism, and the deletion of empty blow-ups

Kollár adopts the convention that the final outputs of the named blow-up sequence functors do not
contain empty blow-ups; the steps of their construction that happen to lead to empty blow-ups
"are then ignored without explicit mention" [Kol07, 32]. Accordingly `B(Y, h^* I, h⁻¹(E))` is
obtained from the pull-back `h^* B(X, I, E)` by deleting every blow-up `h^* π_i` whose centre is
empty and reindexing [Kol07, 34.1]. The definition of the deletion needs the fact that a
blowing-up composed with an analytic isomorphism of its base is a blowing-up with the transported
centre (`IsBlowUp.diffeomorph_comp`).

On the lists of centres `CenterList ψ₀ M`:

* `BlowUpSequence.liftDiffeomorph g hY`: the lift `Bl_Y M ≃ Bl_{g(Y)} N` of an analytic isomorphism
  `g : M ≃ N` to the chosen blowings-up, the canonical isomorphism
  (`IsBlowUp.exists_unique_diffeomorph`) between `g ∘ π_Y` (a blowing-up of `N` along `g(Y)`,
  `IsBlowUp.diffeomorph_comp`) and `π_{g(Y)}`;
* `BlowUpSequence.map g L`: the list transported along `g`: the centres `g(Y_i)`
  (`IsClosedSubmanifold.image_diffeomorph`), the tails along the lifts;
* `BlowUpSequence.emptyBlowUpDiffeomorph hY hY₀`: the analytic isomorphism `Bl_∅ M ≃ M` of an empty
  blowing-up (`IsBlowUp.exists_diffeomorph_of_empty`; the empty blow-up of [Kol07, Warning 20]),
  whose map is `π` itself (`∀ p, g p = π p`), so that the choice is only of the proof-carrying
  wrapper of a determined function; the analogue for schemes is the inverse of the blow-down of
  the empty blow-up used by `Scheme.BlowUpSequence.eraseEmpty`;
* `BlowUpSequence.eraseEmpty L`: delete every empty blow-up and reindex, by recursion on the list:
  the empty step `cons h∅ rest` is removed by carrying `rest.eraseEmpty`, a list on `Bl_∅ M`, back
  to `M` along that isomorphism (the analogue of the scheme-theoretic
  `Scheme.BlowUpSequence.eraseEmpty`);
* `BlowUpSequence.NoEmptyCenters L`: no centre is empty (the `NoEmptyCenters` of the succession).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- [Kol07, 32] on lists: no centre of the list is empty — `NoEmptyCenters`
of the succession. -/
abbrev NoEmptyCenters {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M) : Prop :=
  L.toSuccession.NoEmptyCenters

/-- The lift `Bl_Y M ≃ Bl_{g(Y)} N` of an analytic isomorphism `g : M ≃ N` to the chosen
blowings-up: canonical isomorphism between `g ∘ π_Y`, a blowing-up of `N` along `g(Y)`
(`IsBlowUp.diffeomorph_comp`), and the chosen blowing-up `π_{g(Y)}`. -/
def liftDiffeomorph {M N : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (blowUp ψ₀ hY) (blowUp ψ₀ (hY.image_diffeomorph g)) ω :=
  IsBlowUp.diffeomorph (hY.image_diffeomorph g) ((isBlowUp_blowUpπ ψ₀ hY).diffeomorph_comp g)
    (isBlowUp_blowUpπ ψ₀ (hY.image_diffeomorph g))

/-- The list of centres transported along an analytic isomorphism `g : M ≃ N`: the centres
`g(Y_i)` (`IsClosedSubmanifold.image_diffeomorph`), the tails along the lifts
`liftDiffeomorph`. -/
def map : {M N : AnalyticManifold.{u} 𝕜 E} → Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω →
    BlowUpSequence ψ₀ M → BlowUpSequence ψ₀ N
  | _, N, _, nil _ => nil N
  | _, _, g, cons hY rest => cons (hY.image_diffeomorph g) (rest.map (liftDiffeomorph g hY))

theorem map_nil {M N : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω) :
    (nil (ψ₀ := ψ₀) M).map g = nil N := rfl

theorem map_cons {M N : AnalyticManifold.{u} 𝕜 E} (g : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M N ω)
    {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀
        (blowUp ψ₀ hY)) :
    (cons hY rest).map g = cons (hY.image_diffeomorph g) (rest.map (liftDiffeomorph g hY)) := rfl

/-- The chosen blowing-up along an empty centre, read as a blowing-up along `∅`. -/
theorem isBlowUp_blowUpπ_of_eq_empty {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) :
    IsBlowUp ψ₀ (∅ : Set M) c (blowUpπ ψ₀ hY) := by
  subst hY₀
  exact isBlowUp_blowUpπ ψ₀ hY

/-- [Kol07, Warning 20] ("`π_{Z,X}` is an isomorphism" for `Z = ∅`): the
analytic isomorphism `Bl_∅ M ≃ M` of an empty blowing-up — the one whose map is `π` itself
(`emptyBlowUpDiffeomorph_apply`); the choice is of the proof-carrying wrapper of a determined
function. -/
def emptyBlowUpDiffeomorph {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) :
    Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) (blowUp ψ₀ hY) M ω :=
  Classical.choose (IsBlowUp.exists_diffeomorph_of_empty (isBlowUp_blowUpπ_of_eq_empty hY hY₀))

theorem emptyBlowUpDiffeomorph_apply {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (hY₀ : Y = ∅) (p : blowUp ψ₀ hY) :
    emptyBlowUpDiffeomorph hY hY₀ p = blowUpπ ψ₀ hY p :=
  Classical.choose_spec
    (IsBlowUp.exists_diffeomorph_of_empty (isBlowUp_blowUpπ_of_eq_empty hY hY₀)) p

open scoped Classical in
/-- One step of `eraseEmpty`: the step `cons hY rest` with the tail already cleaned — dropped
(the tail carried back along `Bl_∅ M ≃ M`) when `Y = ∅`, kept otherwise. -/
def eraseEmptyCons {M : AnalyticManifold.{u} 𝕜 E} {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (rest : BlowUpSequence ψ₀
        (blowUp ψ₀ hY)) : BlowUpSequence ψ₀ M :=
  if hY₀ : Y = ∅ then rest.map (emptyBlowUpDiffeomorph hY hY₀) else cons hY rest

/-- [Kol07, 32] and 34.1: **delete every empty blow-up and reindex**
— by recursion on the list, an empty step `cons h∅ rest` is removed by carrying the cleaned tail,
a list on `Bl_∅ M`, back to `M` along the analytic isomorphism `Bl_∅ M ≃ M` of the empty
blowing-up (the scheme-theoretic `eraseEmpty` with `pullback (inv (blowUpπ X ⊤))`). -/
def eraseEmpty : {M : AnalyticManifold.{u} 𝕜 E} → BlowUpSequence ψ₀ M → BlowUpSequence ψ₀ M
  | _, nil M => nil M
  | _, cons hY rest => eraseEmptyCons hY rest.eraseEmpty

end AnalyticManifold.BlowUpSequence

end
