/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Concat
public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictTransformSeq
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
import Hironaka.Resolution.Analytic.MaximalContactLemmas
import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 clears the boundary from the cosupport

After Step 2.1 of the proof of [Kol07, Theorem 103] has applied the functor of [Kol07, Lemma 102]
to every nonempty member of `E` in the order of the index set, "`cosupp(I_r, m)` is disjoint from
`Π^{-1}_* E`" ([Kol07, 104, Step 2.1.j]). Two facts carry the conclusion (1) of Lemma 102 for a
member `E^j` through the later blow-ups: along a blow-up sequence of order `≥ m` the cosupport
`{ord ≥ m}` of the controlled transform lies over the cosupport of the ideal sheaf one started with
(`IsOfOrderGe.le_ord_stageMap`), and the strict transform of a closed set lies over the set
(`strictTransform_subset_preimage`, stage by stage). So a closed set missing the cosupport at the
start has its strict transform missing the cosupport at every later stage
(`disjoint_setOf_le_ord_markedTransformSeq_strictTransformSeq`). The concatenation of Step 2.1
transports the clause from the tail to the whole sequence
(`BlowUpSequence.disjoint_concat_of_disjoint`), and the induction over the processed members
(`ChainState.step21FamAux_cosupp_disjoint`, `Step21FamCosupp.lean`) uses Lemma 102 (1) for the
member just processed and the two facts for the members processed before it. An empty member has
empty strict transform (`strictTransformSeq_empty`).

* `FiniteSuccession.strictTransformSeq_empty`,
  `FiniteSuccession.strictTransformSeq_subset_preimage_stageMap`,
  `FiniteSuccession.disjoint_setOf_le_ord_markedTransformSeq_strictTransformSeq` — the two facts.
* `BlowUpSequence.disjoint_concat_of_disjoint` — the clause along a concatenation.

The clause for Step 2.1 in the compatible-family form, `step21FamOn_cosupp_disjoint`
(`Step21FamCosupp.lean`), lets Step 2.2 run with the exceptional divisors and the transform of the
hypersurface of maximal contact as its boundary while the sequence stays of order `≥ m` for the
full transformed boundary (`Step22FamFull.lean`).
-/

public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The strict transforms of the empty set are empty (in the form indexed by a natural number). -/
theorem strictTransformSeqAux_empty :
    ∀ (i : ℕ) (hi : i < S.length + 1), S.strictTransformSeqAux (∅ : Set M) i hi = ∅
  | 0, _ => rfl
  | i + 1, hi => by
    change strictTransformSet (S.map ⟨i, _⟩) (S.center ⟨i, _⟩).support
      (S.strictTransformSeqAux ∅ i (Nat.lt_of_succ_lt hi)) = ∅
    rw [strictTransformSeqAux_empty i (Nat.lt_of_succ_lt hi)]
    exact strictTransformSet_empty _ _

/-- The strict transforms of the empty set are empty. -/
theorem strictTransformSeq_empty (i : Fin (S.length + 1)) :
    S.strictTransformSeq (∅ : Set M) i = ∅ :=
  S.strictTransformSeqAux_empty i.1 i.2

/-- The strict transform of a closed set at stage `i` of a sequence lies over the set
([Kol07, Definition 25]): `strictTransform_subset_preimage` stage by stage. -/
theorem strictTransformSeq_subset_preimage_stageMap {H : Set M} (hH : IsClosed H)
    (i : Fin (S.length + 1)) : S.strictTransformSeq H i ⊆ ⇑(S.stageMap i) ⁻¹' H := by
  induction i using Fin.induction with
  | zero => exact fun x hx => hx
  | succ i ih =>
    rw [strictTransformSeq_succ, stageMap_succ]
    intro x hx
    exact ih (strictTransform_subset_preimage (S.map i).contMDiff.continuous
      (S.isClosed_strictTransformSeq H hH i.castSucc) hx)

/-- Along a sequence of order `≥ m` for `(𝓘, m)`, a closed set missing the cosupport `{ord 𝓘 ≥ m}`
has its strict transforms missing the cosupports of the controlled transforms: the cosupport at
stage
`i` lies over the cosupport at the start (`IsOfOrderGe.le_ord_stageMap`) and the strict transform
over the set. This is how the conclusion of [Kol07, Lemma 102] for one member persists through the
later blow-ups of Step 2.1 ([Kol07, 104, Step 2.1.j]). -/
theorem disjoint_setOf_le_ord_markedTransformSeq_strictTransformSeq [FiniteDimensional 𝕜 E]
    {I E₀ : IdealSheaf M} {m : ℕ} (hge : S.IsOfOrderGe I m E₀) {H : Set M} (hH : IsClosed H)
    (hdis : Disjoint {x | (m : ℕ∞) ≤ I.ord x} H) (i : Fin (S.length + 1)) :
    Disjoint {x | (m : ℕ∞) ≤ (S.markedTransformSeq I m i).ord x}
      (S.strictTransformSeq H i) :=
  Set.disjoint_left.mpr fun x hx hxH =>
    Set.disjoint_left.mp hdis (hge.le_ord_stageMap i x hx)
      (S.strictTransformSeq_subset_preimage_stageMap hH i hxH)

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The clause "the cosupport of the last controlled transform misses the last strict transform"
along
a concatenation `L.concat L'` follows from the clause along `L'` for the controlled transform and
the
strict transform reached by `L`; by induction on `L`, reading both sides through the first blow-up
(`cons_markedTransformSeqAux_succ`, `cons_strictTransformSeqAux_succ`). -/
theorem disjoint_concat_of_disjoint : ∀ {M : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (L' : BlowUpSequence ψ₀ (L.stage (Fin.last _))) (I : IdealSheaf M) (m : ℕ)
        (H : Set M),
    Disjoint
      {x | (m : ℕ∞) ≤ (L'.toSuccession.markedTransformSeq
        (L.toSuccession.markedTransformSeq I m (Fin.last _)) m (Fin.last _)).ord x}
      (L'.toSuccession.strictTransformSeq (L.toSuccession.strictTransformSeq H (Fin.last _))
        (Fin.last _)) →
    Disjoint
      {x | (m : ℕ∞) ≤ ((L.concat L').toSuccession.markedTransformSeq I m (Fin.last _)).ord x}
      ((L.concat L').toSuccession.strictTransformSeq H (Fin.last _))
  | _, nil _, _, _, _, _, h => h
  | _, cons hY rest, L', I, m, H, h => by
    rw [concat_cons]
    -- the hypothesis, read through the first blowing-up
    have e1 : (cons hY rest).toSuccession.markedTransformSeq I m
          (Fin.last (cons hY rest).toSuccession.length) =
        rest.toSuccession.markedTransformSeq
          ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.length + 1)))) m (Fin.last rest.toSuccession.length) :=
      FiniteSuccession.cons_markedTransformSeqAux_succ hY rest.toSuccession I m rest.length
        (Fin.last (rest.length + 1)).2
    have e2 : (cons hY rest).toSuccession.strictTransformSeq H
          (Fin.last (cons hY rest).toSuccession.length) =
        rest.toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H)
          (Fin.last rest.toSuccession.length) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ hY rest.toSuccession H rest.length
        (Fin.last (rest.length + 1)).2
    rw [e1, e2] at h
    -- the goal, read through the first blowing-up
    have e1' : (cons hY (rest.concat L')).toSuccession.markedTransformSeq I m
          (Fin.last (cons hY (rest.concat L')).toSuccession.length) =
        (rest.concat L').toSuccession.markedTransformSeq
          ((FiniteSuccession.cons ψ₀ hY rest.toSuccession).markedTransformSeq I m
            (Fin.succ (0 : Fin (rest.length + 1)))) m
          (Fin.last (rest.concat L').toSuccession.length) :=
      FiniteSuccession.cons_markedTransformSeqAux_succ hY (rest.concat L').toSuccession I m
        (rest.concat L').length (Fin.last ((rest.concat L').length + 1)).2
    have e2' : (cons hY (rest.concat L')).toSuccession.strictTransformSeq H
          (Fin.last (cons hY (rest.concat L')).toSuccession.length) =
        (rest.concat L').toSuccession.strictTransformSeq
          (strictTransformSet (blowUpπ ψ₀ hY) hY.idealSheaf.support H)
          (Fin.last (rest.concat L').toSuccession.length) :=
      FiniteSuccession.cons_strictTransformSeqAux_succ hY (rest.concat L').toSuccession H
        (rest.concat L').length (Fin.last ((rest.concat L').length + 1)).2
    rw [e1', e2']
    exact disjoint_concat_of_disjoint rest L' _ m _ h

end AnalyticManifold.BlowUpSequence

end
