/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.MarkedWeak
import Hironaka.Manifold.FiniteSuccession.Lemmas
public import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
public import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
import Hironaka.Resolution.Analytic.GoingUp.MaxOrder
import Hironaka.Resolution.Analytic.Tuning
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The induced triple at the last stage of a blow-up sequence

Step 2.1 of the proof of Theorem 103 applies Lemma 102 to one boundary member after another
([Kol07, 104, Step 2.1.j]: given the sequence constructed so far, with end result
`Π_{r(j-1)} : X_{r(j-1)} → ⋯ → X_0`, "apply (102) to `(X_{r(j-1)}, I_{r(j-1)}, E_{r(j-1)})`"). After
a sequence of centres `L` of order `≥ m` starting
with `(M, 𝓘, E)`, the data at the last stage, the controlled transform `I_r` of `(𝓘, m)`
(`markedTransformSeq`; Kollár's birational transform of the marked ideal, [Kol07, Definition 60])
and the
total transform `E_r` of the boundary ([Kol07, Definition 25]), form again an analytic triple, the
**induced triple**, and it lies in the class `BOClass m` when `(M, 𝓘, E)` does.

* `isNonzeroEverywhere_markedTransformSeq` — the controlled transforms of an ideal sheaf nonzero
  everywhere are nonzero everywhere: the stalk of a controlled transform is the colon of the total
  transform's stalk by a power of the exceptional ideal ([Kol07, Definition 60]), which contains it,
  and the total transform's stalk is the image of a nonzero ideal under the injective germ map of
  the blowing-up.
* `finite_nonempty_totalTransform`, `finite_nonempty_totalTransformSeqFrom` — only finitely many
  members of the boundary stay nonempty along the sequence: the strict transform of an empty member
  is empty, and one exceptional divisor is added per blow-up.
* `AnalyticTriple.induced T m L hL`, `boClass_induced`, `boundarySeq_last_eq_idealSheaf` — the
  induced triple, its class (the order bound persists along a sequence of order `≥ m`), and the
  identification of the boundary ideal sheaf at the last stage with the ideal sheaf of the induced
  boundary.
* `FiniteSuccession.originalIdx` — the index of the strict transform of an original member `E^j`
  in the boundary at a stage (`hyp_originalIdx`), the exceptional divisors being appended after the
  original members at every step.

The induced triple is the input of the next application of Lemma 102 in `Step21Defs.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The controlled transforms of a nonzero ideal sheaf are nonzero -/

/-- Along a sequence of order `≥ m` for `(𝓘, m)` ([Kol07, Definition 66 (1′)] with the transform
of [Kol07, Definition 60]), every controlled transform of an ideal sheaf nonzero everywhere is
nonzero everywhere: the stalk of the controlled transform at `a'` is the colon of the total
transform's stalk by a power of the exceptional ideal, which contains the total transform's stalk,
the image of the nonzero stalk of `I_i` at `π a'` under the injective germ map of the blowing-up.
Not in the sources; the hypothesis of [Kol07, Definition 31 (1)] for the induced triple. -/
theorem _root_.Hironaka.Manifold.isNonzeroEverywhere_markedTransformSeq {S : FiniteSuccession M}
    {I E₀ : AnalyticManifold.IdealSheaf M} {m : ℕ} (hI : I.IsNonzeroEverywhere)
    (h : S.IsOfOrderGe I m E₀) (i : Fin (S.length + 1)) :
    (S.markedTransformSeq I m i).IsNonzeroEverywhere := by
  induction i using Fin.induction with
  | zero =>
    rw [FiniteSuccession.markedTransformSeq_zero]
    exact hI
  | succ i ih =>
    rw [FiniteSuccession.markedTransformSeq_succ]
    intro a' hbot
    have hdiv := isDivExceptional_birationalTransform (S.isClosedSubmanifold_center i)
      (S.isBlowUp_map i) ⟨S.markedTransformSeq I m i.castSucc, m⟩
      (fun a ha => h.le_ordAlong_center i a ha)
    have hst := hdiv a'
    rw [hbot] at hst
    have hle : ((S.markedTransformSeq I m i.castSucc).pullback _ (S.isBlowUp_map
        i).contMDiff).stalkIdeal a' ≤ ⊥ := by
      rw [hst]
      intro r hr
      exact Submodule.mem_colon.mpr fun p _ => Ideal.mul_mem_right p _ hr
    rw [IdealSheaf.stalkIdeal_pullback, le_bot_iff,
      Ideal.map_eq_bot_iff_of_injective
        (IsBlowUp.germMap_injective (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) a')] at hle
    exact ih (S.map i a') hle

/-! ### Finitely many nonempty members along the sequence -/

/-- The strict transform of the empty set is empty. -/
theorem _root_.Hironaka.Manifold.strictTransformSet_empty {M' : Type u} [TopologicalSpace M']
    (π : M' → M.carrier)
    (Y : Set M) : strictTransformSet π Y (∅ : Set M) = ∅ := by
  simp [strictTransformSet]

/-- The total transform ([Kol07, Definition 25]) of a family with finitely many nonempty members
has finitely many nonempty members: the strict transform of an empty member is empty, and one
exceptional divisor is added. -/
theorem _root_.Hironaka.Manifold.finite_nonempty_totalTransform {M' : Type u} [TopologicalSpace M']
    (π : M' → M.carrier)
    (Y : Set M) (F : HypersurfaceFamily M) (hF : Finite {j // F.hyp j ≠ ∅}) :
    Finite {k // (F.totalTransform π Y).hyp k ≠ ∅} := by
  change Finite {k : F.ι ⊕ₗ PUnit.{u + 1} // (F.totalTransform π Y).hyp k ≠ ∅}
  have hfin : Set.Finite {j : F.ι | F.hyp j ≠ ∅} := Set.finite_coe_iff.mp hF
  have hsub : {k : F.ι ⊕ₗ PUnit.{u + 1} | (F.totalTransform π Y).hyp k ≠ ∅} ⊆
      ((fun j : F.ι => toLex (Sum.inl j)) '' {j : F.ι | F.hyp j ≠ ∅}) ∪
        {toLex (Sum.inr PUnit.unit)} := by
    intro k hk
    rcases hk' : ofLex k with j | u
    · left
      refine ⟨j, fun hj => hk ?_, ?_⟩
      · have : (F.totalTransform π Y).hyp k = strictTransformSet π Y (F.hyp j) := by
          change (Sum.elim (fun j => strictTransformSet π Y (F.hyp j)) (fun _ => π ⁻¹' Y) ∘ ofLex) k
            = _
          rw [Function.comp_apply, hk']
          rfl
        rw [this, hj, strictTransformSet_empty]
      · change toLex (Sum.inl j) = k
        rw [← hk']
        exact toLex_ofLex k
    · right
      rw [Set.mem_singleton_iff]
      calc k = toLex (ofLex k) := (toLex_ofLex k).symm
        _ = toLex (Sum.inr PUnit.unit) := by rw [hk']
  exact Set.finite_coe_iff.mpr (Set.Finite.subset ((hfin.image _).union (Set.finite_singleton _))
    hsub)

/-- Along any sequence, the boundary from a start with finitely many nonempty members has finitely
many nonempty members at every stage. -/
theorem _root_.Hironaka.Manifold.finite_nonempty_totalTransformSeqFrom (S : FiniteSuccession M)
    (F : HypersurfaceFamily M)
    (hF : Finite {j // F.hyp j ≠ ∅}) (i : Fin (S.length + 1)) :
    Finite {k // (S.totalTransformSeqFrom F i).hyp k ≠ ∅} := by
  induction i using Fin.induction with
  | zero => exact hF
  | succ i ih =>
    rw [FiniteSuccession.totalTransformSeqFrom_succ]
    exact finite_nonempty_totalTransform _ _ _ ih

/-! ### The induced triple -/

namespace AnalyticTriple

open Hironaka.Manifold

variable (T : AnalyticTriple ψ₀ M) (m : ℕ) (L : BlowUpSequence ψ₀ M)
  (hL : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf)

/-- The induced triple `(X_j, I_j, E_j)` of [Kol07, 104, Step 2.1.j] at the last stage of a sequence
`L` of order `≥ m` starting with `(M, 𝓘, E)`: the controlled transform `I_r`, nonzero everywhere
(`isNonzeroEverywhere_markedTransformSeq`), and the total transform `E_r` of the boundary
([Kol07, Definition 25]), which has simple normal crossings by clause (3′) of
[Kol07, Definition 66]. -/
def induced : AnalyticTriple ψ₀ (L.stage (Fin.last _)) where
  I := L.toSuccession.markedTransformSeq T.I m (Fin.last _)
  isNonzeroEverywhere := isNonzeroEverywhere_markedTransformSeq T.isNonzeroEverywhere hL _
  F := L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)
  isSnc := (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq T.isSnc
    (fun i => hL.hasOnlyNormalCrossingsWith i) (Fin.last _)).1

@[simp] theorem induced_I :
    (T.induced m L hL).I = L.toSuccession.markedTransformSeq T.I m (Fin.last _) := rfl

@[simp] theorem induced_F :
    (T.induced m L hL).F = L.toSuccession.totalTransformSeqFrom T.F (Fin.last _) := rfl

/-- The boundary ideal sheaf of `L` at its last stage is the ideal sheaf of the induced boundary
family. -/
theorem boundarySeq_last_eq_idealSheaf :
    L.toSuccession.boundarySeq T.F.idealSheaf (Fin.last _) = (T.induced m L hL).F.idealSheaf :=
  (L.toSuccession.isSnc_totalTransformSeqFrom_and_boundarySeq_eq T.isSnc
    (fun i => hL.hasOnlyNormalCrossingsWith i) (Fin.last _)).2

/-- The induced triple of a triple of the class `BOClass m` lies in the class: the mark is kept, the
controlled transform has order `≤ m` everywhere (`ord_markedTransformSeq_le`), and finitely many
members of the boundary are nonempty. -/
theorem boClass_induced (hT : BOClass m T) : BOClass m (T.induced m L hL) :=
  ⟨hT.1,
    fun x => FiniteSuccession.ord_markedTransformSeq_le L.toSuccession hL hT.2.1 (Fin.last _) x,
    finite_nonempty_totalTransformSeqFrom L.toSuccession T.F hT.2.2 (Fin.last _)⟩

end AnalyticTriple

end Manifold

/-! ### The index of an original member along the sequence -/

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) (F : HypersurfaceFamily M)

/-- The index of the strict transform of the original member `j` in the boundary at stage `k`, by
recursion on `k` (the exceptional divisors are appended after the original members at every
step); the applications of Lemma 102 in Step 2.1 of the proof of [Kol07, Theorem 103] are to these
strict transforms. -/
def originalIdxAux : ∀ (k : ℕ) (h : k < S.length + 1), F.ι → (S.totalTransformSeqFromAux F k h).ι
  | 0, _, j => j
  | k + 1, h, j => toLex (Sum.inl (originalIdxAux k (Nat.lt_of_succ_lt h) j))

/-- The index of the strict transform of the original member `j` in the boundary at stage `i`. -/
def originalIdx (i : Fin (S.length + 1)) (j : F.ι) : (S.totalTransformSeqFrom F i).ι :=
  S.originalIdxAux F i.1 i.2 j

/-- The member indexed by `originalIdxAux` is the strict transform of the original member
([Kol07, Definition 25]). -/
theorem hyp_originalIdxAux : ∀ (k : ℕ) (h : k < S.length + 1) (j : F.ι),
    (S.totalTransformSeqFromAux F k h).hyp (S.originalIdxAux F k h j) =
      S.strictTransformSeqAux (F.hyp j) k h
  | 0, _, _ => rfl
  | k + 1, h, j => by
    change strictTransformSet (S.map ⟨k, _⟩) (S.center ⟨k, _⟩).support
      ((S.totalTransformSeqFromAux F k _).hyp (S.originalIdxAux F k _ j)) = _
    rw [hyp_originalIdxAux k (Nat.lt_of_succ_lt h) j]
    rfl

/-- The member indexed by `originalIdx` is the strict transform of the original member. -/
theorem hyp_originalIdx (i : Fin (S.length + 1)) (j : F.ι) :
    (S.totalTransformSeqFrom F i).hyp (S.originalIdx F i j) = S.strictTransformSeq (F.hyp j) i :=
  S.hyp_originalIdxAux F i.1 i.2 j

end AnalyticManifold.FiniteSuccession

end
