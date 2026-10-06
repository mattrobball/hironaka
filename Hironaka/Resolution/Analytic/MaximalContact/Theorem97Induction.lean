/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.LocalIsoEquiv
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Resolution.Analytic.MaximalContact.AgreeOnSubspaceLemmas
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The induction of Kollár's Theorem 97 on lists of centres

Kollár's proof of the uniqueness of blow-up sequences [Kol07, Theorem 97, proof] is an induction
on the length of the blow-up sequence: given the local-isomorphism equivalence `ψ, ψ' : U ⇉ M`
with the common pull-back `C = ψ^*L = ψ'^*L'`, `C` of order `≥ 1` for `(MC(ψ^*I), 1)`, one proves
at each stage

1. `Z_i = Z'_i`: every point of `Z_i` is `ψ_i(u)` for some `u ∈ Z_i^U ⊆ W_i` (the centres lie in
   the images of the lifts and in the cosupport of the marked transform), and `ψ_i(u) = ψ'_i(u)`
   there because `ψ_i, ψ'_i` agree on `V(M_i)` — so `Z_i ⊆ Z'_i`, and symmetrically;
2. `X_{i+1} = X'_{i+1}` — the blow-up of the same centre — and the pulled-back sequences of the
   tails are again equal (the lists are compared centre by centre: `cons.inj`);
3. the lifts `ψ_{i+1}, ψ'_{i+1}` agree on `V(M_{i+1})`, `M_{i+1} = (π_i^U)^{-1}_*(M_i, 1)`: the
   one-step descent lemma `agreeOnSubspace_blowUpLift`
   (`Hironaka/Resolution/Analytic/MaximalContact/OneStepDescent.lean`).

This module proves the induction with the one-step lemma as a hypothesis (`hstep`), so that the
assembly is checked independently of that lemma; Theorem 97 in marked form
(`eq_of_locallyIsoEquivalentSequences`,
`Hironaka/Resolution/Analytic/MaximalContact/Theorem97Star.lean`) is its instance. The list-level
bookkeeping:

* `BlowUpSequence.eq_nil_of_length_eq_zero`: a list of length `0` is `nil`;
* transport of the second lift along the equality of stages `Bl_{ψ⁻¹Y} U = Bl_{ψ'⁻¹Y} U` given by
  `ψ⁻¹Y = ψ'⁻¹Y` (`blowUp_congr`, `AnalyticMap.castDom` — the cast of an analytic map along an
  equality of its domain, with its lemmas all by `subst`), which lets the two pulled-back tails
  be compared as lists over one manifold;
* `IsMarkedOne` peeled on `cons` (`isMarkedOne_cons_zero`, `isMarkedOne_cons_tail`), the centre
  clause of the one-step lemma from `comap_idealSheaf_of_isLocalDiffeomorph`, and the
  identification of the marked transform of the sequence with the one-step lemma's
  (`cons_markedTransformSeq_one`).

Włodarczyk's equivariance of the test blow-ups under the glueing automorphism is the same
induction [Wlo09, Lemma 5.5.3 (5)]; the `Hironaka` library has it for schemes
(`Hironaka/Resolution/Algebraic/MaximalContact/Theorem97.lean`).
-/

@[expose] public section

noncomputable section

open TopologicalSpace AnalyticManifold Set
open scoped Manifold ContDiff

universe u v

namespace Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### Transport of an analytic map along an equality of its domain -/

section Cast

variable {U U' N : AnalyticManifold.{u} 𝕜 E}

/-- The analytic map `f : U' → N` read on `U` along `h : U = U'`. -/
def AnalyticMap.castDom (h : U = U') (f : AnalyticMap U' N) : AnalyticMap U N := h ▸ f

theorem AnalyticMap.isLocalDiffeomorph_castDom (h : U = U') {f : AnalyticMap U' N}
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (AnalyticMap.castDom h f) := by
  subst h
  exact hf

end Cast

end Hironaka.Manifold

namespace AnalyticManifold.BlowUpSequence

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- A list of centres of length `0` is the empty list. -/
theorem eq_nil_of_length_eq_zero (L : BlowUpSequence ψ₀ M) (h : L.length = 0) : L = nil M := by
  cases L with
  | nil => rfl
  | cons hY rest => exact absurd h (Nat.succ_ne_zero _)

/-- Kollár's "`X_{i+1} = X'_{i+1}`" [Kol07, Theorem 97, proof]: the blow-ups of equal centres are
equal. -/
theorem blowUp_congr {Z Z' : Set M} {c : ℕ} (hZZ' : Z = Z') (hZ : IsClosedSubmanifold ψ₀ Z c)
    (hZ' : IsClosedSubmanifold ψ₀ Z' c) : blowUp ψ₀ hZ = blowUp ψ₀ hZ' := by
  subst hZZ'
  rfl

/-- The pull-back along a transported map is the transported pull-back. -/
theorem pullback_castDom_heq {U U' : AnalyticManifold.{u} 𝕜 E} (h : U = U') (f : AnalyticMap U' M)
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (L : BlowUpSequence ψ₀ M) :
    HEq (L.pullback (AnalyticMap.castDom h f) (AnalyticMap.isLocalDiffeomorph_castDom h hf))
      (L.pullback f hf) := by
  subst h
  rfl

/-- The images of the lifts of a transported map are those of the lifts of the map. -/
theorem range_pullbackLift_castDom {U U' : AnalyticManifold.{u} 𝕜 E} (h : U = U')
    (f : AnalyticMap U' M) (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (L : BlowUpSequence ψ₀ M)
    (i : Fin (L.length + 1)) :
    Set.range (L.pullbackLift (AnalyticMap.castDom h f)
        (AnalyticMap.isLocalDiffeomorph_castDom h hf) i) =
      Set.range (L.pullbackLift f hf i) := by
  subst h
  rfl

/-- The transported lift of `g` (read on `Bl_Z N` for `Z = g⁻¹Y`) lies over `g`. -/
theorem blowUpπ_castDom_liftStep {Y : Set M} {Z : Set N} {c : ℕ} (g : AnalyticMap N M)
    (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) (hY : IsClosedSubmanifold ψ₀ Y c)
    (hZ : IsClosedSubmanifold ψ₀ Z c) (hZg : Z = ⇑g ⁻¹' Y) (q : blowUp ψ₀ hZ) :
    blowUpπ ψ₀ hY (AnalyticMap.castDom
      (blowUp_congr hZg hZ (hY.preimage_of_isLocalDiffeomorph hg)) (liftStep g hg hY) q) =
      g (blowUpπ ψ₀ hZ q) := by
  subst hZg
  exact blowUpπ_liftStep g hg hY q

/-! ### The induction -/

/-- **The induction of Theorem 97 with the one-step lemma as a hypothesis** ([Kol07, Theorem 97,
proof]; [Wlo09, Lemma 5.5.3 (5)]). Let `ψ, ψ' : U ⇉ M` be local analytic isomorphisms agreeing
on `V(J)`, let `L, L'` be lists of centres of `M` with `ψ^*L = ψ'^*L'`, the common pull-back of
order `≥ 1` for `(J, 1)`, and the centres of `L`, `L'` in the images of the lifts of `ψ`, `ψ'`.
If (`hstep`) at every stage agreement on `V(J_i)` descends through the blow-up of a common centre
`Z ⊆ V(J_i)` to agreement of the lifts on `V((π_i)^{-1}_*(J_i, 1))`, then `L = L'`: at each stage
the centre `Z_i = ψ_i(Z_i^U) = ψ'_i(Z_i^U) = Z'_i`, and the tails are compared over the blow-up of
that centre. -/
theorem eq_of_pullback_eq_of_step
    (hstep : ∀ {M U : AnalyticManifold.{u} 𝕜 E} (f g : AnalyticMap U M) {Y : Set M} {Z : Set U}
      {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c) (hZ : IsClosedSubmanifold ψ₀ Z c),
      hY.idealSheaf.pullback f f.contMDiff = hZ.idealSheaf →
      hY.idealSheaf.pullback g g.contMDiff = hZ.idealSheaf →
      ∀ (J : IdealSheaf U), Z ⊆ J.support → AgreeOnSubspace f g J →
      ∀ (f' g' : AnalyticMap (blowUp ψ₀ hZ) (blowUp ψ₀ hY)),
      (∀ q, blowUpπ ψ₀ hY (f' q) = f (blowUpπ ψ₀ hZ q)) →
      (∀ q, blowUpπ ψ₀ hY (g' q) = g (blowUpπ ψ₀ hZ q)) →
      AgreeOnSubspace f' g'
        (MarkedIdealSheaf.birationalTransform hZ (isBlowUp_blowUpπ ψ₀ hZ) ⟨J, 1⟩).I)
    (L : BlowUpSequence ψ₀ M) :
    ∀ {U : AnalyticManifold.{u} 𝕜 E} (ψ ψ' : AnalyticMap U M)
      (hψ : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ψ) (hψ' : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ψ')
      (L' : BlowUpSequence ψ₀ M) (J : IdealSheaf U), AgreeOnSubspace ψ ψ' J →
      (L.pullback ψ hψ).toSuccession.IsMarkedOne J →
      (∀ i : Fin L.length, (L.toSuccession.center i).support ⊆
        Set.range (L.pullbackLift ψ hψ i.castSucc)) →
      (∀ i : Fin L'.length, (L'.toSuccession.center i).support ⊆
        Set.range (L'.pullbackLift ψ' hψ' i.castSucc)) →
      L.pullback ψ hψ = L'.pullback ψ' hψ' → L = L' := by
  induction L with
  | nil M =>
    intro U ψ ψ' hψ hψ' L' J _ _ _ _ heq
    refine (eq_nil_of_length_eq_zero L' ?_).symm
    have h := congrArg length heq
    rw [length_pullback, length_pullback] at h
    exact h.symm
  | @cons M Y c hY rest ih =>
    intro U ψ ψ' hψ hψ' L' J hJ hW hcov hcov' heq
    cases L' with
    | nil =>
      exfalso
      have h := congrArg length heq
      rw [length_pullback, length_pullback] at h
      exact Nat.succ_ne_zero _ h
    | @cons _ Y' c' hY' rest' =>
      rw [pullback_cons, pullback_cons] at heq
      obtain ⟨hZ, hc, hrest⟩ := cons.inj heq
      -- the first centres lie in the images of `ψ`, `ψ'` (`h3`, `h3'` at stage `0`)
      have hY0 : Y ⊆ Set.range ψ := by
        have h0 : hY.idealSheaf.support ⊆ Set.range ψ := hcov ⟨0, Nat.succ_pos _⟩
        rwa [hY.cosupport_idealSheaf] at h0
      have hY0' : Y' ⊆ Set.range ψ' := by
        have h0 : hY'.idealSheaf.support ⊆ Set.range ψ' := hcov' ⟨0, Nat.succ_pos _⟩
        rwa [hY'.cosupport_idealSheaf] at h0
      -- the order condition at stage `0` and on the tail
      rw [pullback_cons, toSuccession_cons] at hW
      have hZJ := FiniteSuccession.isMarkedOne_cons_zero _ _ hW
      have hW₁ := FiniteSuccession.isMarkedOne_cons_tail _ _ hW
      -- `Z_0 = Z'_0`
      have hYY' : Y = Y' := by
        apply Set.Subset.antisymm
        · intro y hy
          obtain ⟨u, rfl⟩ := hY0 hy
          have hu : u ∈ ⇑ψ ⁻¹' Y := hy
          have hu' : u ∈ ⇑ψ' ⁻¹' Y' := hZ ▸ hu
          rw [hJ.apply_eq_of_mem_support (hZJ hu)]
          exact hu'
        · intro y hy
          obtain ⟨u, rfl⟩ := hY0' hy
          have hu' : u ∈ ⇑ψ' ⁻¹' Y' := hy
          have hu : u ∈ ⇑ψ ⁻¹' Y := hZ ▸ hu'
          rw [← hJ.apply_eq_of_mem_support (hZJ hu)]
          exact hu
      subst hYY'
      subst hc
      -- the tails, compared over the blow-up of `ψ⁻¹Y`
      have hB : blowUp ψ₀ (hY.preimage_of_isLocalDiffeomorph hψ) =
          blowUp ψ₀ (hY'.preimage_of_isLocalDiffeomorph hψ') :=
        blowUp_congr hZ _ _
      have hrest' : rest = rest' := by
        refine ih (liftStep ψ hψ hY) (AnalyticMap.castDom hB (liftStep ψ' hψ' hY'))
          (isLocalDiffeomorph_liftStep ψ hψ hY)
          (AnalyticMap.isLocalDiffeomorph_castDom hB (isLocalDiffeomorph_liftStep ψ' hψ' hY'))
          rest' _ ?_ hW₁ (fun i => hcov i.succ) ?_ ?_
        · refine hstep ψ ψ' hY (hY.preimage_of_isLocalDiffeomorph hψ)
            (comap_idealSheaf_of_isLocalDiffeomorph ψ₀ ψ hψ hY)
            ((comap_idealSheaf_of_isLocalDiffeomorph ψ₀ ψ' hψ' hY').trans
              (IsClosedSubmanifold.idealSheaf_congr (hY'.preimage_of_isLocalDiffeomorph hψ')
                (hY.preimage_of_isLocalDiffeomorph hψ) hZ.symm))
            J hZJ hJ _ _ (blowUpπ_liftStep ψ hψ hY) ?_
          intro q
          exact blowUpπ_castDom_liftStep ψ' hψ' hY' (hY.preimage_of_isLocalDiffeomorph hψ) hZ q
        · intro i
          rw [range_pullbackLift_castDom]
          exact hcov' i.succ
        · exact eq_of_heq (hrest.trans (pullback_castDom_heq hB _ _ rest').symm)
      exact congrArg (cons hY) hrest'

end AnalyticManifold.BlowUpSequence

end
