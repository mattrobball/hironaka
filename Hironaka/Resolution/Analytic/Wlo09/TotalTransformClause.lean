/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Basic
import Hironaka.Resolution.Analytic.Principalization.MonomialSeq
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Hironaka.Resolution.Analytic.Wlo09.StrictTransformClauses
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The total transform of the value is the strict transform times an exceptional monomial

Clause (6) of [Wlo09, Theorem 2.0.2], the strengthening of Bravo–Villamayor: the pull-back of the
ideal of `Y` to the last stage is `𝓘_Ỹ · 𝓘_Ẽ`, with `Ỹ` the strict transform and `Ẽ` a simple normal
crossing divisor which is a locally finite combination of the components of the exceptional divisor.
It is proved here for the value of the embedded desingularization functor `bedanFamOfInput bmod n`
over a relatively compact open `U`, at every point `x` of the last stage: the stalk of the
pulled-back ideal is the stalk of the final strict transform times a monomial in the vanishing
ideals of the exceptional components through `x`, with exponents chosen at `x`. The theorem carries
the explicit hypothesis `hsat` of `Hironaka/Resolution/Analytic/Wlo09/StrictTransformClauses.lean`
(local generators for the saturation stalks at every stage), which always holds; the assembly of
`BEDanFamStarOfInput_isEmbeddedDesing` uses the present form directly.

**Proof.** Along a blow-up sequence of order `≥ 1` for `(𝓘, 1)`, the pull-back of `𝓘` to stage `i`
is the marked transform times the ideal of an exceptional divisor with simple normal crossings,
`σ_i^* ⋯ σ_1^*(𝓘_0) = 𝓘_i · 𝓘(E_i)` with `𝓘(E_i) = σ_i^*(𝓘(E_{i−1})) · 𝓘(D_i)` (the induction in the
proof of [Wlo09, Proposition 4.0.2, (1)⇒(2)]); Kollár writes the pull-back as the ideal of an
explicit divisor supported on the total transforms of the exceptional divisors [Kol07, 72]. The
formula is proved stage by stage as `FiniteSuccession.isBoundaryMonomialAt_stageMapAux`
(`Hironaka/Resolution/Analytic/Principalization/MonomialSeq.lean`): the pull-back of `𝓘` to the last
stage is a boundary monomial in the total transform of the boundary with residual the final marked
transform `𝓘_r`. On `DomBEDan` the boundary of `T|_U` has no member, so the total transform grown
from it is the exceptional family `totalTransformSeq` up to the relabelling of
`Hironaka/Resolution/Analytic/Wlo09/BoundaryBridge.lean`
(`exists_equiv_totalTransformSeqFrom_of_isEmpty`), along which the finite set of components and the
exponents transport (`Finset.map`, `Finset.prod_map`); and `𝓘_r = Ỹ` by
`bedanFamOfInput_strictTransform_eq_of_hsat`.
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Clause6

variable (𝕜 : Type) [RCLike 𝕜] (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
  (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- Clause (6) of [Wlo09, Theorem 2.0.2] for the value of `bedanFamOfInput bmod n` over `U`, under
`hsat`: on the last stage, at every point the pulled-back ideal is the final strict transform's
ideal times a monomial in the vanishing ideals of the exceptional components through the point,
with the exponents chosen at the point. Kollár's formula for the pull-back at mark `1`
[Kol07, 72] (`isBoundaryMonomialAt_stageMapAux`), with the residual identified by
`bedanFamOfInput_strictTransform_eq_of_hsat` and the boundary read through the empty-boundary
bridge. -/
theorem bedanFamOfInput_totalTransform_eq_of_hsat
    (hsat : ∀ i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length,
      IdealSheaf.HasLocalGenerators
        (𝒪 := structureSheaf 𝕜 (Fin n → 𝕜)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.succ))
        (saturationStalk
          (π := ⇑((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.map i))
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.isClosedSubmanifold_center i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.isBlowUp_map i)
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
            U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I i.castSucc)))
    (x : (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage (Fin.last _)) :
    ∃ (s : Finset ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
          U hU).toSuccession.totalTransformSeq (Fin.last _)).ι)
      (α : ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq
          (Fin.last _)).ι → ℕ),
      (∀ j ∈ s, x ∈ ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn
        U hU).toSuccession.totalTransformSeq (Fin.last _)).hyp j) ∧
      ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.pullback _
          ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stageMap
            (Fin.last _)).contMDiff).stalkIdeal x =
        ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.strictTransformSubspaceSeq
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I
            (Fin.last _)).stalkIdeal x *
          ∏ j ∈ s,
            (vanishingStalk
              (((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.totalTransformSeq
                (Fin.last _)).hyp j) x) ^ α j := by
  have heq := bedanFamOfInput_strictTransform_eq_of_hsat 𝕜 bmod n T hT U hU hsat
  rw [← heq]
  have hge := (bmod n).isOfOrderGe T (DomBEDan.bmoClass_one 𝕜 hT) U hU
  have hF := (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
  obtain ⟨s, α, hs, hx⟩ :=
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.isBoundaryMonomialAt_stageMapAux
      hF hge (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length
      (Nat.lt_succ_self _) x
  have hT' : IsEmpty (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.ι := hT.1
  obtain ⟨e, he⟩ := exists_equiv_totalTransformSeqFrom_of_isEmpty
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F (Fin.last _)
  have hx' : ((T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I.pullback _
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stageMap
        (Fin.last _)).contMDiff).stalkIdeal x =
      (∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜)
        (((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.totalTransformSeqFrom
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F (Fin.last _)).hyp j) x
            ^ α j) *
        ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.markedTransformSeq
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I 1
          (Fin.last _)).stalkIdeal x := hx
  refine ⟨s.map e.toEmbedding, α ∘ e.symm, fun j hj => ?_, ?_⟩
  · obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    rw [Equiv.coe_toEmbedding, he]
    exact hs j' hj'
  · rw [hx', mul_comm]
    congr 1
    refine (Finset.prod_congr rfl fun j _ => ?_).trans (Finset.prod_map s e.toEmbedding _).symm
    exact congrArg₂ (fun Z k => vanishingStalk (𝕜 := 𝕜) (E := Fin n → 𝕜) Z x ^ k) (he j).symm
      (congrArg α (e.symm_apply_apply j)).symm

end Clause6

end Hironaka.Manifold
