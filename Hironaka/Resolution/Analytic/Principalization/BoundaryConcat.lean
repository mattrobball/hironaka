/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Clauses along a concatenation of lists of centres

The value of the principalization functor on an open is a concatenation (`BlowUpSequence.concat`):
the disjoining list of [Kol07, 72] followed by the order-reduction list on the disjoined triple. Two
clauses of the value are read stage by stage and pass through the concatenation by induction on
the first list:

* clause (3′) of [Kol07, Definition 66] — the boundary `E_i` (`boundarySeq`) has only normal
  crossings with the centre `Z_i` — holds along `L.concat L'` when it holds along `L` and along
  `L'` started from `L`'s last boundary (`hasOnlyNormalCrossingsWith_boundarySeq_concat`; the
  boundary along `cons hY rest` after the first step is the boundary along `rest` from the
  reduced transform, `cons_boundarySeq_succ`);
* the centres of `L.concat L'` lie over `Z` when those of `L` do and those of `L'` lie over the
  preimage of `Z` under `L`'s composite (`centersOver_concat`; the composite of `cons hY rest`
  after the first step factors through the first blow-down, `stageMapAux_cons_succ`).

The boundary at a stage of the concatenation is not stated as an equation (its two sides live on
the two lists' stage types, equal only propositionally); the clauses are transported instead.
These are the two facts behind clauses (1) and (3) of [Kol07, Theorem 35] for the value
(`ClauseOne.lean`, `ClauseThree.lean`).
-/

public section

universe u

open AnalyticManifold
open scoped Manifold ContDiff

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Clause (3′) of [Kol07, Definition 66] along a concatenation: if every centre of `L` has only
normal crossings with the boundary from `E₀` at its stage, and every centre of `L'` has only
normal crossings with the boundary from `L`'s last boundary at its stage, then every centre of
`L.concat L'` has only normal crossings with the boundary from `E₀` at its stage. -/
theorem hasOnlyNormalCrossingsWith_boundarySeq_concat :
    ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
      (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (E₀ : IdealSheaf M),
      (∀ i : Fin L.toSuccession.length,
        (L.toSuccession.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith
          (L.toSuccession.center i)) →
      (∀ i : Fin L'.toSuccession.length,
        (L'.toSuccession.boundarySeq (L.toSuccession.boundarySeq E₀ (Fin.last _))
          i.castSucc).HasOnlyNormalCrossingsWith (L'.toSuccession.center i)) →
      ∀ i : Fin (L.concat L').toSuccession.length,
        ((L.concat L').toSuccession.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith
          ((L.concat L').toSuccession.center i)
  | _, nil _, _, _, _, h', i => h' i
  | _, cons hY rest, L', E₀, h, h', i => by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact h ⟨0, Nat.succ_pos _⟩
    | succ k =>
      -- the boundary along `cons hY rest` at its last stage, on the stage type of `L'`
      have hlast : ((cons hY rest).toSuccession.boundarySeq E₀ (Fin.last _) :
          IdealSheaf ((cons hY rest).stage (Fin.last _))) =
          rest.toSuccession.boundarySeq
            (IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) E₀ hY.idealSheaf) (Fin.last _) :=
        FiniteSuccession.cons_boundarySeqAux_succ hY rest.toSuccession E₀
          rest.toSuccession.length (Nat.lt_succ_self _)
      have ih := hasOnlyNormalCrossingsWith_boundarySeq_concat rest L'
        (IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) E₀ hY.idealSheaf)
        (fun j => by
          have hj : ((cons hY rest).toSuccession.boundarySeq E₀ j.succ.castSucc :
              IdealSheaf ((cons hY rest).stage j.succ.castSucc)) =
              rest.toSuccession.boundarySeq
                (IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) E₀ hY.idealSheaf) j.castSucc :=
            FiniteSuccession.cons_boundarySeq_succ_castSucc hY rest.toSuccession E₀ j
          exact hj ▸ h j.succ)
        (fun j => hlast ▸ h' j)
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      have hc : ((cons hY (rest.concat L')).toSuccession.boundarySeq E₀
          (⟨k, Nat.lt_of_succ_lt_succ hk⟩ :
            Fin (rest.concat L').toSuccession.length).succ.castSucc :
          IdealSheaf ((cons hY (rest.concat L')).stage
            (⟨k, Nat.lt_of_succ_lt_succ hk⟩ :
              Fin (rest.concat L').toSuccession.length).succ.castSucc)) =
          (rest.concat L').toSuccession.boundarySeq
            (IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) E₀ hY.idealSheaf)
            (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin (rest.concat L').toSuccession.length).castSucc :=
        FiniteSuccession.cons_boundarySeq_succ_castSucc hY (rest.concat L').toSuccession E₀ _
      change ((cons hY (rest.concat L')).toSuccession.boundarySeq E₀
        (⟨k, Nat.lt_of_succ_lt_succ hk⟩ :
          Fin (rest.concat L').toSuccession.length).succ.castSucc).HasOnlyNormalCrossingsWith
        ((rest.concat L').toSuccession.center ⟨k, Nat.lt_of_succ_lt_succ hk⟩)
      rw [hc]
      exact ih

/-- The centres of a concatenation lie over `Z` when those of the first list do and those of the
second list lie over the preimage of `Z` under the first list's composite. -/
theorem centersOver_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (Z : Set M),
    L.toSuccession.CentersOver Z →
    L'.toSuccession.CentersOver (L.toSuccession.stageMap (Fin.last _) ⁻¹' Z) →
    (L.concat L').toSuccession.CentersOver Z
  | _, nil _, _, _, _, h', i => fun p hp => h' i hp
  | _, cons hY rest, L', Z, h, h', i => by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact h ⟨0, Nat.succ_pos _⟩
    | succ k =>
      have ih := centersOver_concat rest L' (blowUpπ ψ₀ hY ⁻¹' Z)
        (fun j p hp => by
          have hj1 : j.1 + 1 < (cons hY rest).toSuccession.length + 1 :=
            Nat.lt_succ_of_lt j.succ.2
          have hs := stageMapAux_cons_succ hY rest j.1 hj1 p
          have hp' : (cons hY rest).toSuccession.stageMapAux (j.1 + 1) hj1 p ∈ Z := h j.succ hp
          rw [hs] at hp'
          exact hp')
        (fun j p hp => by
          have hp' := h' j hp
          have hs := stageMapAux_cons_succ hY rest rest.toSuccession.length (Nat.lt_succ_self _)
            (L'.toSuccession.stageMap j.castSucc p)
          change (cons hY rest).toSuccession.stageMapAux (rest.toSuccession.length + 1)
            (Nat.lt_succ_self _) (L'.toSuccession.stageMap j.castSucc p) ∈ Z at hp'
          rw [hs] at hp'
          exact hp')
        ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      intro p hp
      have hk' : k + 1 < (cons hY (rest.concat L')).toSuccession.length + 1 :=
        Nat.lt_succ_of_lt hk
      have hs := stageMapAux_cons_succ hY (rest.concat L') k hk' p
      change (cons hY (rest.concat L')).toSuccession.stageMapAux (k + 1) hk' p ∈ Z
      rw [hs]
      exact ih hp

end AnalyticManifold.BlowUpSequence
