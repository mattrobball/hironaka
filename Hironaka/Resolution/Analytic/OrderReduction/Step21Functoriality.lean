/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.ConcatPullback
public import Hironaka.Resolution.Analytic.OrderReduction.Step21Defs
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Step 2.1 along a local analytic isomorphism: the induced triple and the member index

The functoriality of Step 2.1 of the proof of [Kol07, Theorem 103] is that of Lemma 102
("functoriality in Step 2.1 by the corresponding functoriality in (102)",
[Kol07, 104, Step 2.3]). Along a surjective local analytic isomorphism `h` the nonempty members of
`h⁻¹(E)` and their order are those of `E` (`nonemptyList_comap_of_surjective`), and each step of
the iteration pulls back: the triple induced by the pull-back is the pull-back of the induced
triple along the lift of `h` to the last stage (`induced_pullback`, from the transport lemmas of
`ConcatPullback.lean`), and the member index corresponds (`originalIdx_last_pullback_heq`, the
transform of the same original member).

* `FiniteSuccession.heq_toLex_inl`, `heq_originalIdx_congr`, `heq_originalIdxAux_cons_succ`,
  `BlowUpSequence.originalIdx_last_pullback_heq` — the member index of the pulled-back family at the
  last stage is the member index of the family (a heterogeneous equality, the two index sets being
  propositionally equal).
* `AnalyticTriple.induced_pullback`, `HypersurfaceFamily.nonemptyList_comap_of_surjective`.

Step 2.1 in the compatible-family form uses them (`Step21Fam.lean`, `InducedValue.lean`).
-/

public section

noncomputable section

open Set Topology AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

open Hironaka.Manifold

/-- `toLex ∘ Sum.inl` respects heterogeneous equality across equal summand types. -/
theorem heq_toLex_inl {α β : Type u} (e : α = β) {x : α} {y : β} (hxy : HEq x y) :
    HEq (toLex (Sum.inl x : α ⊕ PUnit.{u + 1})) (toLex (Sum.inl y : β ⊕ PUnit.{u + 1})) := by
  subst e
  cases hxy
  rfl

end AnalyticManifold.FiniteSuccession

namespace AnalyticManifold.BlowUpSequence

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- The index of the transform of a member in the pulled-back family at the last stage of `h^* L`
is its index in the family at the last stage of `L`; the two index sets are propositionally equal
(`totalTransformSeqFrom_last_pullbackLiftLast`), so the statement is a heterogeneous equality. -/
theorem originalIdx_last_pullback_heq : ∀ {M N : AnalyticManifold.{u} 𝕜 E} (L : BlowUpSequence ψ₀ M)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (G : HypersurfaceFamily M)
    (j : G.ι),
    HEq ((L.pullback h hh).toSuccession.originalIdx (G.comap h) (Fin.last _) j)
      (L.toSuccession.originalIdx G (Fin.last _) j)
  | _, _, nil _, _, _, _, _ => HEq.rfl
  | _, _, cons hY rest, h, hh, G, j => by
    have hfam : (G.comap h).totalTransform (blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
          (hY.preimage_of_isLocalDiffeomorph hh).idealSheaf.support =
        (G.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support).comap
          (liftStep h hh hY) := by
      rw [hY.cosupport_idealSheaf, (hY.preimage_of_isLocalDiffeomorph hh).cosupport_idealSheaf]
      exact HypersurfaceFamily.totalTransform_comap_liftStep h hh hY G
    refine HEq.trans (FiniteSuccession.heq_originalIdxAux_cons_succ
      (hY.preimage_of_isLocalDiffeomorph hh)
      (rest.pullback (liftStep h hh hY) (isLocalDiffeomorph_liftStep h hh hY)).toSuccession
      (G.comap h) j _ (Fin.last _).2) ?_
    refine HEq.trans ((rest.pullback (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY)).toSuccession.heq_originalIdx_congr hfam
      (Fin.last _) HEq.rfl) ?_
    refine HEq.trans (originalIdx_last_pullback_heq rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY)
      (G.totalTransform (blowUpπ ψ₀ hY) hY.idealSheaf.support) (toLex (Sum.inl j))) ?_
    exact (FiniteSuccession.heq_originalIdxAux_cons_succ hY rest.toSuccession G j _
      (Fin.last _).2).symm

end AnalyticManifold.BlowUpSequence

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- The triple induced by the pull-back of a sequence is the pull-back of the induced triple along
the lift of `h` to the last stage: the controlled transform and the boundary family at the last
stage
both pull back (`ConcatPullback.lean`). This is the step-by-step form of the functoriality argument
in [Kol07, 104, Step 2.3]. -/
theorem AnalyticTriple.induced_pullback {M N : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ M)
    (s : ℕ) (L : BlowUpSequence ψ₀ M)
    (hL : L.toSuccession.IsOfOrderGe T.I s T.F.idealSheaf) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (hL' : (L.pullback h hh).toSuccession.IsOfOrderGe (T.pullback h hh).I s
      (T.pullback h hh).F.idealSheaf) :
    (T.induced s L hL).pullback (L.pullbackLiftLast h hh)
        (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast L h hh) =
      (T.pullback h hh).induced s (L.pullback h hh) hL' :=
  AnalyticTriple.ext'
    (by
      change (L.toSuccession.markedTransformSeq T.I s (Fin.last _)).pullback _ (L.pullbackLiftLast
          h hh).contMDiff =
        (L.pullback h hh).toSuccession.markedTransformSeq
            (T.I.pullback h h.contMDiff) s
          (Fin.last _)
      exact (BlowUpSequence.markedTransformSeq_last_pullbackLiftLast L h hh T.I T.F.idealSheaf s
        hL).symm)
    (by
      change (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).comap
          (L.pullbackLiftLast h hh) =
        (L.pullback h hh).toSuccession.totalTransformSeqFrom (T.F.comap h) (Fin.last _)
      exact (BlowUpSequence.totalTransformSeqFrom_last_pullbackLiftLast L h hh T.F).symm)

/-- Along a surjective map the nonempty members of the inverse-image family, in the order of the
index set, are those of the family. -/
theorem HypersurfaceFamily.nonemptyList_comap_of_surjective {M N : Type u}
    (F : HypersurfaceFamily M) (h : N → M) (hs : Function.Surjective h)
    (hF : Finite {j // F.hyp j ≠ ∅}) (hF' : Finite {j // (F.comap h).hyp j ≠ ∅}) :
    (F.comap h).nonemptyList hF' = F.nonemptyList hF := by
  have hset : ({j | (F.comap h).hyp j ≠ ∅} : Set (F.comap h).ι) = {j | F.hyp j ≠ ∅} := by
    ext j
    change h ⁻¹' F.hyp j ≠ ∅ ↔ F.hyp j ≠ ∅
    constructor
    · intro hne h0
      exact hne (by rw [h0, Set.preimage_empty])
    · intro hne h0
      refine hne (Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_)
      obtain ⟨x, rfl⟩ := hs y
      exact Set.eq_empty_iff_forall_notMem.mp h0 x hy
  have hfin : (F.comap h).nonemptyFinset hF' = F.nonemptyFinset hF := by
    unfold HypersurfaceFamily.nonemptyFinset
    exact Set.Finite.toFinset_inj.mpr hset
  unfold HypersurfaceFamily.nonemptyList
  exact congrArg (fun t : Finset F.ι => t.sort (· ≤ ·)) hfin

end Manifold

end
