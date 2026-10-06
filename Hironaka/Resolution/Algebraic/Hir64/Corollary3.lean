/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Kol07.UnionIdealInvertible
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Snc.SncSubfamily
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.NowhereDenseSupport
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Hironaka's Corollary 3: simplification of an algebraic boundary

[Hir64, Corollary 3, p. 146], "the simplification of an algebraic boundary", stated by Hironaka as
an immediate consequence of Main Theorem II: for a non-singular algebraic `k`-scheme `X` and a
nowhere dense closed subscheme `W`, there is a finite succession of monoidal transformations with
non-singular centres `D_i` lying over `W` (`D_i ⊆ f̄_i⁻¹(W)`, where `f̄_i = f_0 ∘ ⋯ ∘ f_{i-1}`) such
that `X_r` is non-singular and the associated reduced scheme `red(f̄_r⁻¹(W))` is defined by an
invertible sheaf of ideals and has only normal crossings ([Hir64, Definition 2] for the last
notion). It is proved here from Kollár's principalization theorem [Kol07, Theorem 35] applied to the
triple `(X, I_W, ∅)`:

* the hypothesis: Hironaka's "nowhere dense" is topological, while a triple asks the ideal to be
  nonzero on every irreducible component (Kollár's "not zero on any irreducible component"); the
  bridge is `isNonzeroEverywhere_of_isNowhereDense_support`;
* clause (ii): the centres of `BP` with empty boundary are the centres of the order reduction
  `BMO_1`, which lie over `V(I_W)` (`stageMap_mem_support_of_mem_center_BP`);
* clause (i): the end result of a smooth blow-up sequence over `k` is smooth, hence regular
  (`isRegular_of_smooth`);
* clause (iii): clause (2) of [Kol07, Theorem 35] writes `Π^* I_W = ∏ F_j^{a_j}` with `F` a simple
  normal crossing family (`BP_isIdealOfSncDivisor`); its radical is the reduced union of the
  members with positive multiplicity (`radical_prod_pow_eq_unionIdeal_subfamily`), a simple normal
  crossing subfamily, whose reduced union has only normal crossings
  (`IsSnc.isSncBoundary_unionIdeal`) and is invertible
  (`isInvertible_unionIdeal_of_isSnc`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Scheme IdealSheafData Hironaka
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### Corollary 3 -/

/-- [Hir64, Corollary 3, p. 146]: for `X` smooth of a single relative dimension over `k`
(Hironaka: `X` as in Main Theorem II, non-singular; its non-singularity follows from smoothness,
and the restriction to one relative dimension is lifted in `ComponentwiseCorollaries`) and `W` a
nowhere dense closed subscheme, a finite succession of monoidal transformations with non-singular
centres such that (i) the end result is non-singular, (ii) every centre lies over `W`, and (iii)
the reduced inverse image of `W` is defined by an invertible sheaf of ideals and has only normal
crossings. Proved from Kollár's principalization theorem [Kol07, Theorem 35] on `(X, I_W, ∅)`
rather than, as in Hironaka, from Main Theorem II. -/
theorem hironaka_corollary3 (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (hN : ∃ N : ℕ, SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of k)))
    (W : X.IdealSheafData) (hW : IsNowhereDense (W.support : Set X)) :
    ∃ S : BlowUpSequence X,
      (∀ i : Fin S.length, IsRegular (S.center i).subscheme) ∧
      IsRegular S.last ∧
      (∀ (i : Fin S.length) (x : S.stage i.castSucc),
        x ∈ (S.center i).support → S.stageMap i.castSucc x ∈ W.support) ∧
      (W.comap S.composite).radical.IsInvertible ∧
      IsSncBoundary (W.comap S.composite).radical := by
  obtain ⟨N, hNsm⟩ := hN
  have hsm : Smooth (X ↘ Spec (CommRingCat.of k)) := SmoothOfRelativeDimension.smooth N _
  have hLN : IsLocallyNoetherian X := (X ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hW' : IsNonzeroEverywhere W := isNonzeroEverywhere_of_isNowhereDense_support W hW
  have hE : IsEmpty (DivisorFamily.empty X).ι := ⟨fun i => i.elim⟩
  let T : Triple k := ⟨.of X, ⟨N, hNsm⟩, W, hW', DivisorFamily.empty X,
    isSnc_of_isEmpty (X ↘ Spec (CommRingCat.of k)) _ hE⟩
  have hsmS : (BP T).IsSmooth (X ↘ Spec (CommRingCat.of k)) := BP_isSmooth T
  have hsmLast : Smooth ((BP T).stageMap (Fin.last _) ≫ (X ↘ Spec (CommRingCat.of k))) :=
    IsSmooth.smooth_stageMap (n := N) hsmS (Fin.last _)
  have hsmC : Smooth ((BP T).composite ≫ (X ↘ Spec (CommRingCat.of k))) := hsmLast
  refine ⟨BP T, fun i => ?_, ?_, fun i x hx => ?_, ?_⟩
  · exact @isRegular_of_smooth k _ _ _ (((BP T).center i).subschemeι ≫
      (BP T).stageMap i.castSucc ≫ (X ↘ Spec (CommRingCat.of k))) (hsmS i)
  · exact @isRegular_of_smooth k _ _ _
      ((BP T).stageMap (Fin.last _) ≫ (X ↘ Spec (CommRingCat.of k))) hsmLast
  · exact stageMap_mem_support_of_mem_center_BP T hE i hx
  · obtain ⟨F, a, hFsnc, hEq⟩ := BP_isIdealOfSncDivisor T
    have hEq' : W.comap (BP T).composite = ∏ j, F.component j ^ a j := hEq
    rw [hEq', radical_prod_pow_eq_unionIdeal_subfamily]
    exact ⟨@isInvertible_unionIdeal_of_isSnc k _ _ _ hsmC _ (hFsnc.subfamily _),
      @IsSnc.isSncBoundary_unionIdeal k _ _ _ hsmC _ (hFsnc.subfamily _)⟩

end Hironaka.Resolution
