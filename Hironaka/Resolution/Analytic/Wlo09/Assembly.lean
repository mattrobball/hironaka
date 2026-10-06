/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Functoriality
import Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.RegLocality
import Hironaka.Resolution.Analytic.Wlo09.StrictTransformClauses
import Hironaka.Resolution.Analytic.Wlo09.TotalTransformClause
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The assembly of the analytic embedded desingularization

The clauses of [Wlo09, Theorem 2.0.2] for the embedded desingularization functor
`bedanFamOfInput 𝕜 bmod n` of `Hironaka/Resolution/Analytic/Wlo09/Basic.lean`, assembled into
`BEDanFamStar.IsEmbeddedDesing` for the all-dimensions functor `BEDanFamStarOfInput 𝕜 bmod hbmod`
of `Hironaka/Resolution/Analytic/Wlo09/Functoriality.lean`.

* `BEDanFam_center_disjoint_reg`: clause (2) of [Wlo09, Theorem 2.0.2] ("all centers `C_i` are
  disjoint from the set `Reg(Y)` of points where `Y` is smooth"; the centres lie in the support by
  [Wlo09, Definition 3.2.4 (1)], and the stop rule of the proof of [Wlo09, Theorem 7.4.1] applies at
  a smooth point): no point of any centre lies over a simple point of `Y ∩ U`. From the local
  analysis `bedanFamOfInput_center_disjoint_fiber_near_regular`
  (`Hironaka/Resolution/Analytic/Wlo09/Clauses.lean`) and the locality of `regularLocus`
  (`exists_opens_reg_of_mem_reg`, `Hironaka/Resolution/Analytic/Wlo09/RegLocality.lean`).
* `BEDanFamStarOfInput_isEmbeddedDesing`: the assembly. Clause (1) is
  `bedanFamOfInput_isSnc_totalTransformSeq` and `bedanFamOfInput_hasSncWith_center`
  (`Clauses.lean`); clause (2) is the theorem above; clause (3), the smoothness of the final
  strict transform and its simple normal crossings with the exceptional divisor, is
  `bedanFamOfInput_isNonsingular_strictTransform_of_hsat` and
  `bedanFamOfInput_exists_adaptedChart_isSncChartAt_of_hsat` (`StrictTransformClauses.lean`) with
  the finite-type hypothesis discharged by `saturationStalk_hasLocalGenerators`; clause (6), the
  total transform formula `σ^*(I_Y) = I_Ỹ · I_Ẽ`, is `bedanFamOfInput_totalTransform_eq_of_hsat`
  (`TotalTransformClause.lean`); clause (4), the commutation with local analytic isomorphisms, is
  the field `commutesWithLocalIsos` of the modified marked resolution restricted to the class
  (`CommutesWithLocalIsos.restrictDomain`), read through `BEDanFamStarOfInput_fam` (`rfl`); clause
  (5), the compatibility of the values under restriction `U₁ ≤ U₂`, is the field `compat` of the
  compatible family itself.

This module constructs nothing; it assembles the theorems of the directory. The concrete instance
is `concreteBEDanFamStar_isEmbeddedDesing` in `Hironaka/Resolution/Analytic/Wlo09/Concrete.lean`.
-/

@[expose] public noncomputable section

open Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable (𝕜 : Type) [RCLike 𝕜]

/-- Clause (2) of [Wlo09, Theorem 2.0.2] for the embedded desingularization functor
`bedanFamOfInput 𝕜 bmod n`: no point of any centre of the embedded desingularization of `Y ∩ U`
lies over a simple point of `Y ∩ U`. From the local analysis
`bedanFamOfInput_center_disjoint_fiber_near_regular` (no centre over an open on which `Y` is
non-singular) and the locality of `regularLocus`: a simple point has an open neighbourhood `V` in
the ambient manifold on which `Y` is non-singular. -/
theorem BEDanFam_center_disjoint_reg (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n) (n : ℕ)
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M)))
    (i : Fin (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.length)
    (x : (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stage i.castSucc)
    (hx : x ∈
      ((((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.center i).support) :
    (((bedanFamOfInput 𝕜 bmod n).fam T hT).seqOn U hU).toSuccession.stageMap i.castSucc x ∉
      (fun y => ((IdealSheaf.toAnalyticSpaceι
          (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) y :
          M.restrict U)) ''
        (IdealSheaf.toAnalyticSpace
            (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I).regularLocus := by
  rintro ⟨y, hy, hyx⟩
  -- the image `p ∈ M` of the simple point `y` of `Y ∩ U`
  set p : M := M.inclusion U ((IdealSheaf.toAnalyticSpaceι
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) y) with hp
  have hy2 : (IdealSheaf.toAnalyticSpaceι
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I) y ∈
      (T.I.pullback _ (M.inclusion U).contMDiff).support := y.2
  have hpc : p ∈ T.I.support :=
    (mem_cosupport_comap_iff T.I (M.inclusion U) (isLocalDiffeomorph_inclusion M U) _).mp hy2
  -- `Y` is non-singular at `p`
  have hreg : IsRegularLocalRing
      ((structureSheaf 𝕜 (Fin n → 𝕜) M).presheaf.stalk p ⧸ T.I.stalkIdeal p) :=
    (isRegularLocalRing_quotient_stalkIdeal_comap_iff T.I (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U) _).mp ((mem_reg_toAnalyticSpace_iff _ y).mp hy)
  have hz₀ : (⟨p, hpc⟩ : T.I.toAnalyticSpace) ∈
      T.I.toAnalyticSpace.regularLocus :=
    (mem_reg_toAnalyticSpace_iff T.I ⟨p, hpc⟩).mpr hreg
  -- an open `V ∋ p` of `M` over which every point of `Y` is simple
  obtain ⟨V, hpV, hV⟩ := exists_opens_reg_of_mem_reg T.I hz₀
  have hVsing : (IdealSheaf.toAnalyticSpace
      (T.pullback (M.inclusion V) (isLocalDiffeomorph_inclusion M V)).I).singularLocus = ∅ := by
    rw [sing_toAnalyticSpace_eq_empty_iff]
    intro q hq
    have hq' : q ∈ (T.I.pullback _ (M.inclusion V).contMDiff).support := hq
    have hqc : M.inclusion V q ∈ T.I.support :=
      (mem_cosupport_comap_iff T.I (M.inclusion V) (isLocalDiffeomorph_inclusion M V) q).mp hq'
    exact (isRegularLocalRing_quotient_stalkIdeal_comap_iff T.I (M.inclusion V)
      (isLocalDiffeomorph_inclusion M V) q).mpr
      ((mem_reg_toAnalyticSpace_iff T.I ⟨_, hqc⟩).mp (hV ⟨_, hqc⟩ q.2))
  -- no centre point maps into `V`; but `x` maps to `p ∈ V`
  have hc := bedanFamOfInput_center_disjoint_fiber_near_regular 𝕜 bmod n T hT U hU V hVsing i x hx
  apply hc
  rw [← hyx]
  exact hpV


/-- **The embedded desingularization theorem for `BEDanFamStarOfInput`** [Wlo09, Theorem 2.0.2]:
the assembly of `IsEmbeddedDesing` from the clauses proved in this directory: (1)
`bedanFamOfInput_isSnc_totalTransformSeq` and `bedanFamOfInput_hasSncWith_center`; (2)
`BEDanFam_center_disjoint_reg`; (3) the smoothness and simple normal crossings of the final strict
transform, with the finite-type hypothesis discharged by `saturationStalk_hasLocalGenerators`;
(6) the total transform formula `bedanFamOfInput_totalTransform_eq_of_hsat`; (4) the commutation
with local analytic isomorphisms, the field of the modified marked resolution restricted to the
class (`CommutesWithLocalIsos.restrictDomain`). -/
theorem BEDanFamStarOfInput_isEmbeddedDesing (bmod : ∀ n : ℕ, BMOmodFam.{u} 𝕜 n)
    (hbmod : ∀ (n s : ℕ),
      (bmod n).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s)
        (bmod (n - s)).functor) :
    (BEDanFamStarOfInput 𝕜 bmod hbmod).IsEmbeddedDesing := by
  constructor
  · intro n M T hT U hU
    refine ⟨bedanFamOfInput_isSnc_totalTransformSeq 𝕜 bmod n T hT U hU,
      bedanFamOfInput_hasSncWith_center 𝕜 bmod n T hT U hU,
      fun i x hx => BEDanFam_center_disjoint_reg 𝕜 bmod n T hT U hU i x hx,
      bedanFamOfInput_isNonsingular_strictTransform_of_hsat 𝕜 bmod n T hT U hU
        fun _ => saturationStalk_hasLocalGenerators _ _ _,
      fun x hx => ?_,
      fun x => bedanFamOfInput_totalTransform_eq_of_hsat 𝕜 bmod n T hT U hU
        (fun _ => saturationStalk_hasLocalGenerators _ _ _) x⟩
    obtain ⟨c, φ, σ, cidx, h₁, h₂, -⟩ :=
      bedanFamOfInput_exists_adaptedChart_isSncChartAt_of_hsat 𝕜 bmod n T hT U hU
        (fun _ => saturationStalk_hasLocalGenerators _ _ _) x hx
    exact ⟨c, φ, σ, cidx, h₁, h₂⟩
  · intro n
    exact AnalyticFamilyFunctor.CommutesWithLocalIsos.restrictDomain (B := (bmod n).functor)
      (fun hT => DomBEDan.bmoClass_one 𝕜 hT) (fun _ _ => rfl) (bmod n).commutesWithLocalIsos

end Hironaka.Manifold
