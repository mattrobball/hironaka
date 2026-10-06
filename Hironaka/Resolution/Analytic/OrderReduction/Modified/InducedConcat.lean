/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Induced
public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialTriple
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.MaximalContact.MarkedOneLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The induced triple of a concatenation

The induced triple of a list of centres (`AnalyticTriple.induced`: the marked transform and the
total transform of the boundary at the last stage) decomposes along the constructors of the list:
the empty list induces the triple itself (`induced_nil`), and `cons hY R` induces what `R` induces
from the triple after the head blow-up (`induced_cons`). The head triple is read as the induced
triple of the one-element list `cons hY nil`; its ideal is the marked transform of the first step,
`birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) ⟨𝓘, m⟩` (`cons_markedTransformSeq_one`,
`cons_markedTransformSeq_last`: the chart witnesses of the succession are chosen, so the
identification across successions is a theorem, `birationalTransform_congr`, not a `rfl`), and its
boundary the total transform of the first step; the order clauses of the head and of the tail come
from `isOfOrderGe_cons_iff`.

The consequence used by the rounds on the nonmonomial part: a pointwise bound on the order of the
nonmonomial part of the induced ideal at the last stage passes through a concatenation `L.concat L'`
from the bound for `L'` at the triple induced by `L` (`nonmonomialOrdLe_induced_concat`), by
induction on `L` with the `cons` case definitional, so no transport across the type equality
`stage_last_concat` is needed. The triple `(X_j, I_j, E_j)` carried along a composite sequence is
Kollár's [Kol07, 104, Step 2.1].
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

namespace AnalyticTriple

/-- The induced triple of equal triples (on the same manifold) is the same triple. -/
theorem induced_congr {T₁ T₂ : AnalyticTriple ψ₀ M} (e : T₁ = T₂) (s : ℕ)
    (L : BlowUpSequence ψ₀ M) (h₁ : L.toSuccession.IsOfOrderGe T₁.I s T₁.F.idealSheaf)
    (h₂ : L.toSuccession.IsOfOrderGe T₂.I s T₂.F.idealSheaf) :
    T₁.induced s L h₁ = T₂.induced s L h₂ := by
  subst e
  rfl

variable (T : AnalyticTriple ψ₀ M) (m : ℕ)

/-- The empty list induces the triple itself (the marked and total transforms at index `0`). -/
theorem induced_nil
    (h : (BlowUpSequence.nil (ψ₀ := ψ₀) M).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) :
    T.induced m (BlowUpSequence.nil M) h = T :=
  AnalyticTriple.ext' rfl rfl

variable {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ₀ Y c)

/-- The head of a list of order `≥ m`, as the one-element list, is of order `≥ m`
(`isOfOrderGe_cons_iff`: the head clauses do not mention the tail). -/
theorem isOfOrderGe_head_of_cons {R : BlowUpSequence ψ₀ (blowUp ψ₀ hY)}
    (h : (BlowUpSequence.cons hY R).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) :
    (BlowUpSequence.cons hY (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf :=
  (FiniteSuccession.isOfOrderGe_cons_iff (I := T.I) (E₀ := T.F.idealSheaf) (m := m) hY _).mpr
    ⟨((FiniteSuccession.isOfOrderGe_cons_iff (I := T.I) (E₀ := T.F.idealSheaf) (m := m) hY
      R.toSuccession).mp h).1, FiniteSuccession.isOfOrderGe_nil _ _ _⟩

/-- The triple after the head blow-up: the induced triple of the one-element list. -/
abbrev headTriple
    (h₁ : (BlowUpSequence.cons hY (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I m
        T.F.idealSheaf) :
    AnalyticTriple ψ₀ (blowUp ψ₀ hY) :=
  T.induced m (BlowUpSequence.cons hY (BlowUpSequence.nil _)) h₁

/-- The ideal of the head triple is the marked transform of the first step
(`cons_markedTransformSeq_last` at the one-element list). -/
theorem headTriple_I
    (h₁ : (BlowUpSequence.cons hY (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I m
        T.F.idealSheaf) :
    (T.headTriple m hY h₁).I =
      (MarkedIdealSheaf.birationalTransform hY (isBlowUp_blowUpπ ψ₀ hY) ⟨T.I, m⟩).I :=
  FiniteSuccession.cons_markedTransformSeq_last hY _ T.I m

/-- The head triple's divisor is the total transform of the first step
(`cons_totalTransformSeqFromAux_succ` at the one-element list). -/
theorem headTriple_F
    (h₁ : (BlowUpSequence.cons hY (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I m
        T.F.idealSheaf) :
    (T.headTriple m hY h₁).F = T.F.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support :=
  FiniteSuccession.cons_totalTransformSeqFromAux_succ hY _ T.F 0 (Nat.lt_succ_self _)

/-- The boundary ideal of the head triple is the reduced transform of the boundary ideal (the total
transform of [Kol07, Definition 25] along one blow-up). -/
theorem headTriple_F_idealSheaf
    (h₁ : (BlowUpSequence.cons hY (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I m
        T.F.idealSheaf) :
    (T.headTriple m hY h₁).F.idealSheaf =
      IdealSheaf.reducedTransform (blowUpπ ψ₀ hY) (T.F.idealSheaf (𝕜 := 𝕜) (E := E))
        hY.idealSheaf :=
  (((BlowUpSequence.cons hY
    (BlowUpSequence.nil _)).toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq
    T.isSnc (fun i => h₁.hasOnlyNormalCrossingsWith i) (Fin.last _)).2).symm

/-- The tail of a list of order `≥ m` is of order `≥ m` for the head triple. -/
theorem isOfOrderGe_tail_of_cons {R : BlowUpSequence ψ₀ (blowUp ψ₀ hY)}
    (h : (BlowUpSequence.cons hY R).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) :
    R.toSuccession.IsOfOrderGe (T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY h)).I m
      (T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY h)).F.idealSheaf := by
  rw [headTriple_F_idealSheaf, headTriple_I,
    ← FiniteSuccession.cons_markedTransformSeq_one hY R.toSuccession T.I m]
  exact ((FiniteSuccession.isOfOrderGe_cons_iff (I := T.I) (E₀ := T.F.idealSheaf) (m := m) hY
    R.toSuccession).mp h).2

/-- **The induced triple of a `cons`**: what `cons hY R` induces from `T` is what `R` induces from
the head triple (the marked transform at the last stage through the transform of the first step,
`cons_markedTransformSeq_last`; the total transform, `cons_totalTransformSeqFromAux_succ`). -/
theorem induced_cons {R : BlowUpSequence ψ₀ (blowUp ψ₀ hY)}
    (h : (BlowUpSequence.cons hY R).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) :
    T.induced m (BlowUpSequence.cons hY R) h =
      (T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY h)).induced m R
        (T.isOfOrderGe_tail_of_cons m hY h) :=
  AnalyticTriple.ext'
    ((FiniteSuccession.cons_markedTransformSeq_last hY R.toSuccession T.I m).trans
      (congrArg (fun J : AnalyticManifold.IdealSheaf (blowUp ψ₀ hY) =>
        R.toSuccession.markedTransformSeq J m (Fin.last _)) (T.headTriple_I m hY _).symm))
    ((FiniteSuccession.cons_totalTransformSeqFromAux_succ hY R.toSuccession T.F R.length
        (Fin.last (R.length + 1)).2).trans
      (congrArg (fun G : HypersurfaceFamily (blowUp ψ₀ hY) =>
        R.toSuccession.totalTransformSeqFrom G (Fin.last _)) (T.headTriple_F m hY _).symm))

end AnalyticTriple

end Manifold

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

open Hironaka.Manifold.BMO

/-- The nonmonomial part of the ideal of a triple has order `≤ d` at every point: the invariant
carried along the descent of the rounds on the nonmonomial part. -/
def NonmonomialOrdLe {N : AnalyticManifold.{u} 𝕜 E} (S : AnalyticTriple ψ₀ N) (d : ℕ) : Prop :=
  ∀ x, (nonmonomialTriple S).I.ord x ≤ (d : ℕ∞)

theorem NonmonomialOrdLe.weaken {N : AnalyticManifold.{u} 𝕜 E} {S : AnalyticTriple ψ₀ N} {d d' : ℕ}
    (h : NonmonomialOrdLe S d) (hdd : d ≤ d') : NonmonomialOrdLe S d' :=
  fun x => (h x).trans (by exact_mod_cast hdd)

/-- **The pointwise bound transports through a concatenation**: if the nonmonomial part of the
ideal induced by `L'` from the triple induced by `L` is of order `≤ d` everywhere, so is the one
induced by `L.concat L'` — by induction on `L`, the `cons` case through `induced_cons`
(definitional at the constructors; no cast across `stage_last_concat`). -/
theorem nonmonomialOrdLe_induced_concat : ∀ {M : AnalyticManifold.{u} 𝕜 E}
    (T : AnalyticTriple ψ₀ M) (L : BlowUpSequence ψ₀ M) (L' : BlowUpSequence ψ₀ (L.stage
        (Fin.last _)))
    (m d : ℕ) (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf)
    (hL' : L'.toSuccession.IsOfOrderGe (T.induced m L hL).I m (T.induced m L hL).F.idealSheaf)
    (hC : (L.concat L').toSuccession.IsOfOrderGe T.I m T.F.idealSheaf),
    NonmonomialOrdLe ((T.induced m L hL).induced m L' hL') d →
      NonmonomialOrdLe (T.induced m (L.concat L') hC) d
  | _, T, BlowUpSequence.nil _, L', m, d, hL, hL', hC, h => by
    rw [AnalyticTriple.induced_congr (AnalyticTriple.induced_nil T m hL) m L' hL' hC] at h
    exact h
  | _, T, BlowUpSequence.cons hY rest, L', m, d, hL, hL', hC, h => by
    have e₁ := AnalyticTriple.induced_cons T m hY hL
    have hL'' : L'.toSuccession.IsOfOrderGe
        ((T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)).induced m rest
          (T.isOfOrderGe_tail_of_cons m hY hL)).I m
        ((T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)).induced m rest
          (T.isOfOrderGe_tail_of_cons m hY hL)).F.idealSheaf := by
      rw [← e₁]; exact hL'
    rw [AnalyticTriple.induced_congr e₁ m L' hL' hL''] at h
    have ih := nonmonomialOrdLe_induced_concat
      (T.headTriple m hY (T.isOfOrderGe_head_of_cons m hY hL)) rest L' m d
      (T.isOfOrderGe_tail_of_cons m hY hL) hL'' (T.isOfOrderGe_tail_of_cons m hY hC) h
    change NonmonomialOrdLe (T.induced m (BlowUpSequence.cons hY (rest.concat L')) hC) d
    rw [AnalyticTriple.induced_cons T m hY hC]
    exact ih

end Hironaka.Manifold.BMOmod

end
