/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.MonomialStep
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bMeasure
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Kollár's explicit formula along a sequence of order `≥ 1`

Kollár's principalization ends with an explicit monomial formula,
`Π^* I = 𝒪_{X_r}(−∑_{j ≥ s} Π^*_{r,j+1} F_j)` [Kol07, 72], for the order-reduction part of the
sequence. Here it is proved intrinsically and stage by stage: along a smooth blow-up sequence `S`
of order `≥ 1` for `(I, 1, E₀)` (clauses (2′)–(4′) of [Kol07, Definition 66]) the pull-back of `I`
to the stage `i` is a boundary monomial with residual the marked transform `I_i`
(`isBoundaryMonomialAt_stageMapAux`): at stage `0` the empty product with residual `I`; from stage
`i` to `i + 1` the residual is divided exactly by the exceptional ideal (mark `1`:
`π_i⁻¹(I_i) = I_{F_i} · I_{i+1}`, `MonomialStalk.lean`) and the monomial part is pulled back member
by member (`MonomialStep.lean`) — the centre `Z_i` has simple normal crossings with the boundary
family `F_i` by clause (3′) at the stages `≤ i`. When the last marked transform has order `< 1`
everywhere ([Kol07, Theorem 107 (1)]) its stalks are the unit ideal, and the pull-back of `I` to
the last stage is a boundary monomial in the final total transform of `E₀`
(`exists_boundaryMonomial_of_isOfOrderGe_one`) — the monomial clause of the principalization for
the order-reduction part. The general mark is `MonomialSeqMark.lean`; the clause on the total
transform of the boundary in the embedded resolution uses this module
(`Hironaka/Resolution/Analytic/Wlo09/TotalTransformClause.lean`).
-/

public section

universe u

open TopologicalSpace Hironaka.Manifold Manifold
open scoped Manifold ContDiff

namespace Manifold.IdealSheaf

end Manifold.IdealSheaf

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The stalk of the centre ideal `C_i` is the vanishing ideal of `Z_i`, as is the stalk of the
ideal sheaf of the closed submanifold `Z_i`. -/
theorem stalkIdeal_center_eq (i : Fin S.length) (a : S.stage i.castSucc) :
    (S.center i).stalkIdeal a = (S.isClosedSubmanifold_center i).idealSheaf.stalkIdeal a := by
  rw [(S.isIdealSheafOf_center i).stalkIdeal_eq_vanishingStalk (S.isClosedSubmanifold_center i) a,
    (S.isClosedSubmanifold_center i).stalkIdeal_idealSheaf_eq_vanishingStalk a]

/-- Kollár's (60.1) at mark `1` along the sequence [Kol07, (60.1)]: the marked transform `I_i`
pulls back to the exceptional ideal of `π_i` times `I_{i+1}`, the marking legitimate by clause (4′)
of [Kol07, Definition 66] (`1 ≤ ord_{Z_i} I_i`). -/
theorem map_germMap_stalkIdeal_markedTransformSeq {I E₀ : IdealSheaf M}
    (hge : S.IsOfOrderGe I 1 E₀) (i : Fin S.length) (x : S.stage i.succ) :
    Ideal.map (germMap (S.map i) (S.map i).contMDiff x)
        ((S.markedTransformSeq I 1 i.castSucc).stalkIdeal (S.map i x)) =
      vanishingStalk (𝕜 := 𝕜) (E := E) (⇑(S.map i) ⁻¹' (S.center i).support) x ^ 1 *
        (S.markedTransformSeq I 1 i.succ).stalkIdeal x := by
  have hm : ∀ a ∈ (S.center i).support, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
      (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq I 1 i.castSucc) a :=
    fun a ha => by
      rw [← IdealSheaf.ordAlongIdeal_congr_stalk_left _ _ _ (S.stalkIdeal_center_eq i a)]
      exact (hge i).2 a ha
  have e := stalkIdeal_totalTransform_eq_mul_birationalTransform (S.isClosedSubmanifold_center i)
    (S.isBlowUp_map i) (S.markedTransformSeq I 1 i.castSucc) hm x
  rw [pow_one, ← (S.isBlowUp_map i).stalkIdeal_exceptionalIdealSheaf_eq_vanishingStalk
    (S.isClosedSubmanifold_center i) x]
  rw [IdealSheaf.stalkIdeal_pullback] at e
  exact e

/-- Kollár's formula along the sequence [Kol07, 72], stage by stage: for a sequence of order `≥ 1`
for `(I, 1, red F)`, the pull-back of `I` to the stage `i` is a boundary monomial in the total
transform of `F` at that stage with residual the marked transform `I_i` — the empty product at
stage `0`, then the step of `MonomialStep.lean` with the exact division
`π_i⁻¹(I_i) = I_{F_i} · I_{i+1}`, the centre having snc with the boundary by clause (3′) at the
stages `≤ i`. -/
theorem isBoundaryMonomialAt_stageMapAux {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    {I : IdealSheaf M}
        (hge : S.IsOfOrderGe I 1 (F.idealSheaf (𝕜 := 𝕜) (E := E))) :
    ∀ (i : ℕ) (hi : i < S.length + 1) (x : finStages M S.later ⟨i, hi⟩),
      (S.totalTransformSeqFromAux F i hi).IsBoundaryMonomialAt
        (I.pullback _ (S.stageMapAux i hi).contMDiff)
            (S.markedTransformSeqAux I 1 i hi) x
  | 0, _, x => ⟨∅, fun _ => 0, fun j hj => absurd hj (Finset.notMem_empty j), by
      rw [Finset.prod_empty, one_mul]
      change (IdealSheaf.pullback (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id I).stalkIdeal x =
        I.stalkIdeal x
      rw [IdealSheaf.pullback_id_eq_self]⟩
  | i + 1, hi, x => by
    have hi' : i < S.length := Nat.lt_of_succ_lt_succ hi
    have h3 : ∀ i' : Fin S.length,
        (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i'.castSucc).HasOnlyNormalCrossingsWith
          (S.center i') :=
      fun i' => (hge i').1
    have hFi : (S.totalTransformSeqFrom F (⟨i, hi'⟩ : Fin S.length).castSucc).IsSnc ψ :=
      (isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF _ fun i' _ => h3 i').1
    have hsnci := hasSncWith_totalTransformSeqFrom_center_of_forall_lt hF ⟨i, hi'⟩
      fun i' _ => h3 i'
    have hY := (S.isClosedSubmanifold_center ⟨i, hi'⟩).congr_chart ψ
    have hπ := (S.isBlowUp_map ⟨i, hi'⟩).congr_chart ψ
    have ih := isBoundaryMonomialAt_stageMapAux hF hge i (Nat.lt_of_succ_lt hi)
      (S.map ⟨i, hi'⟩ x)
    have hR := S.map_germMap_stalkIdeal_markedTransformSeq hge ⟨i, hi'⟩ x
    have e : I.pullback _ (S.stageMapAux (i + 1) hi).contMDiff =
        (I.pullback _ (S.stageMapAux i (Nat.lt_of_succ_lt hi)).contMDiff).pullback _ (S.map ⟨i,
            hi'⟩).contMDiff :=
      (IdealSheaf.pullback_comp I _ _).symm
    rw [e]
    exact isBoundaryMonomialAt_pullback hY hπ hFi hsnci ih hR

/-- Kollár's explicit formula at the last stage, intrinsically [Kol07, 72]: along a sequence of
order `≥ 1` for `(I, 1, red F)` whose last marked transform has order `< 1` everywhere
([Kol07, Theorem 107 (1)]), the pull-back of `I` along the composite is, at every point `x` of the
last stage, a monomial in the vanishing ideals of finitely many members of the final total
transform of `F` through `x`. -/
theorem exists_boundaryMonomial_of_isOfOrderGe_one {F : HypersurfaceFamily M} (hF : F.IsSnc ψ)
    {I : IdealSheaf M}
        (hge : S.IsOfOrderGe I 1 (F.idealSheaf (𝕜 := 𝕜) (E := E)))
    (hlt : ∀ x : S.stage (Fin.last _),
      (S.markedTransformSeq I 1 (Fin.last _)).ord x < ((1 : ℕ) : ℕ∞))
    (x : S.stage (Fin.last _)) :
    ∃ (s : Finset (S.totalTransformSeqFrom F (Fin.last _)).ι)
      (α : (S.totalTransformSeqFrom F (Fin.last _)).ι → ℕ),
      (∀ j ∈ s, x ∈ (S.totalTransformSeqFrom F (Fin.last _)).hyp j) ∧
      (I.pullback _ (S.stageMap (Fin.last _)).contMDiff).stalkIdeal x =
        ∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E)
          ((S.totalTransformSeqFrom F (Fin.last _)).hyp j) x ^ α j := by
  obtain ⟨s, α, hs, hx⟩ :=
    S.isBoundaryMonomialAt_stageMapAux hF hge S.length (Nat.lt_succ_self _) x
  refine ⟨s, α, hs, ?_⟩
  have htop : (S.markedTransformSeq I 1 (Fin.last _)).stalkIdeal x = ⊤ := by
    have h0 : (S.markedTransformSeq I 1 (Fin.last _)).ord x = 0 := by
      have := hlt x
      rwa [Nat.cast_one, Order.lt_one_iff] at this
    have hnot := (IdealSheaf.ord_eq_zero_iff (J := S.markedTransformSeq I 1 (Fin.last _))).mp h0
    by_contra hne
    exact hnot ((IdealSheaf.mem_support _).mpr hne)
  have hx' : (I.pullback _ (S.stageMap (Fin.last _)).contMDiff).stalkIdeal x =
      (∏ j ∈ s, vanishingStalk (𝕜 := 𝕜) (E := E)
        ((S.totalTransformSeqFrom F (Fin.last _)).hyp j) x ^ α j) *
        (S.markedTransformSeq I 1 (Fin.last _)).stalkIdeal x := hx
  rw [hx', htop, Ideal.mul_top]
  exact rfl

end AnalyticManifold.FiniteSuccession
