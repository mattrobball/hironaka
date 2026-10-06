/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.MarkedData
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
public import Hironaka.Resolution.Analytic.Principalization.Collapse
public import Hironaka.Resolution.Analytic.Principalization.Disjoin
import Hironaka.Resolution.Analytic.OrderReduction.BoundaryEnlarge
public import Hironaka.Resolution.Analytic.Principalization.DisjoinBoundary
import Hironaka.Resolution.Analytic.Principalization.DisjoinLemmas
import Hironaka.Resolution.Analytic.Principalization.OriginalFinite
public import Hironaka.Resolution.Analytic.Principalization.PullbackNonzero
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The disjoined triple

After the disjoining blow-ups of [Kol07, 72] the strict transforms `E^0 := π^{-1}_*(E_1 + ⋯ + E_k)`
are pairwise disjoint and form "a smooth divisor", declared a single member; the exceptional
divisors `E^1, …, E^{k−1}` follow; the ideal sheaf is pulled back along the composite `π`; and
"`(X', π^* I, ∑ E^i)` satisfies the assumptions of (68)", so `BMO_1` is applied to it. This module
assembles that triple on the last stage of `disjoinList`: the boundary is the total transform of
`F` with its original members collapsed into one (`disjoinedFamily`, snc by `isSnc_collapse` since
the original members are pairwise disjoint, `meetLocus_two_disjoinFinal_eq_empty`), the ideal sheaf
is `Π^* 𝓘` (nonzero everywhere, `isNonzeroEverywhere_comap_stageMap`), and the triple lies in the
marked class `BMOClass 1`: its boundary has finitely many members (one collapsed member and
finitely many exceptional divisors, `finite_notMem_range_originalIdx`), as the marked class at
mark `1` requires. The construction is stated first for an arbitrary list `L` along which the
original members become pairwise disjoint (`disjoinedTripleOf`), because the independence of the
shrinking open compares the disjoined triples of two lists (`DisjoinedNatural.lean`); the value of
the principalization functor is assembled from the disjoined triple in `Assembly.lean`. The
`Hironaka` library has the corresponding construction in
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Disjoin.lean`.
-/

@[expose] public section

universe u

open Set
open scoped Manifold ContDiff

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M) (F : HypersurfaceFamily M)

/-- The index of an original member is injective at every stage (`originalIdxAux_injective` of
`OrderReduction/BoundaryEnlarge.lean`, indexed by `Fin`). -/
theorem originalIdx_injective (i : Fin (S.length + 1)) : Function.Injective (S.originalIdx F i) :=
  S.originalIdxAux_injective F i.1 i.2

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The disjoined triple of a general list -/

/-- **The collapsed boundary at the last stage of a list** `L` — the total transform of `F` along
`L` with the original members collapsed into one first member (Kollár's `E^0`, [Kol07, 72]), the
exceptional divisors following. The disjoined boundary is its instance at the disjoining list; the
general form is what the independence of the shrinking open compares. -/
noncomputable def collapsedFamilyOf (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (F : HypersurfaceFamily M) :
    HypersurfaceFamily (L.stage (Fin.last _)) :=
  (L.toSuccession.totalTransformSeqFrom F (Fin.last _)).collapse
    (fun k => k ∈ Set.range (L.toSuccession.originalIdx F (Fin.last _)))

/-- The collapsed boundary has finitely many members: the collapsed one and the exceptional
divisors, one per blow-up (`finite_notMem_range_originalIdx`). -/
theorem finite_collapsedFamilyOf_ι (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (F : HypersurfaceFamily M) :
    Finite (collapsedFamilyOf L F).ι := by
  have := L.toSuccession.finite_notMem_range_originalIdx F (Fin.last _)
  exact inferInstanceAs (Finite (PUnit.{u + 1} ⊕ _))

/-- **The disjoined triple of a list** `L` along which the original members of `T.F` become
pairwise disjoint with snc total transform — the pull-back of the ideal sheaf along the composite
and the collapsed boundary (Kollár's `(X', π^* I, ∑ E^i)`, [Kol07, 72]). -/
noncomputable def disjoinedTripleOf (T : AnalyticTriple ψ₀ M)
    (L : AnalyticManifold.BlowUpSequence ψ₀ M)
    (hsnc : (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc ψ₀)
    (hdisj : ((L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅) :
    AnalyticTriple ψ₀ (L.stage (Fin.last _)) where
  I := T.I.pullback _ (L.toSuccession.stageMap (Fin.last _)).contMDiff
  isNonzeroEverywhere :=
    haveI := finiteDimensional_of_chartIso ψ₀
    isNonzeroEverywhere_comap_stageMap T.isNonzeroEverywhere _
  F := collapsedFamilyOf L T.F
  isSnc := HypersurfaceFamily.isSnc_collapse hsnc hdisj

/-- The disjoined triple of a list lies in the marked class at mark `1` (whose finiteness clause
asks for finitely many nonempty members). -/
theorem disjoinedTripleOf_bmoClass (T : AnalyticTriple ψ₀ M) (L : AnalyticManifold.BlowUpSequence
    ψ₀ M)
    (hsnc : (L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).IsSnc ψ₀)
    (hdisj : ((L.toSuccession.totalTransformSeqFrom T.F (Fin.last _)).subfamily
      (fun k => k ∈ Set.range (L.toSuccession.originalIdx T.F (Fin.last _)))).meetLocus 2 = ∅) :
    AnalyticTriple.BMOClass 1 (disjoinedTripleOf T L hsnc hdisj) :=
  ⟨le_rfl, @Subtype.finite _ (finite_collapsedFamilyOf_ι L T.F) _⟩

/-! ### The disjoined triple of the disjoining list -/

/-- **The disjoined boundary** — the total transform of `F` along the disjoining list at its last
stage, with the original members (the pairwise disjoint strict transforms `E^0` of [Kol07, 72])
collapsed into one first member, the exceptional divisors `E^1 < ⋯ < E^{k−1}` following. -/
noncomputable def disjoinedFamily (m : ℕ) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅) :
    HypersurfaceFamily ((disjoinList (ψ₀ := ψ₀) m F hF hm).stage (Fin.last _)) :=
  collapsedFamilyOf (disjoinList (ψ₀ := ψ₀) m F hF hm) F

/-- The original members of the final total transform are pairwise disjoint ("we get rid of all
pairwise intersections", [Kol07, 72]) — they are `disjoinFinal`'s members (`hyp_originalIdx`,
`hyp_disjoinFinal`). -/
theorem meetLocus_two_subfamily_original_eq_empty (m : ℕ) (F : HypersurfaceFamily M)
    (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅) :
    (((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.totalTransformSeqFrom F
      (Fin.last _)).subfamily (fun k => k ∈ Set.range
        ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.originalIdx F (Fin.last _)))).meetLocus 2
      = ∅ := by
  have h := HypersurfaceFamily.meetLocus_subfamily_range_eq
    (F := disjoinFinal (ψ₀ := ψ₀) m F hF hm)
    ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.originalIdx F (Fin.last _))
    ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.originalIdx_injective F (Fin.last _))
    (fun j => ((disjoinList (ψ₀ := ψ₀) m F hF hm).toSuccession.hyp_originalIdx F (Fin.last _)
      j).trans (hyp_disjoinFinal m F hF hm j).symm) 2
  exact h.trans (meetLocus_two_disjoinFinal_eq_empty m F hF hm)

/-- The disjoined boundary is a simple normal crossings divisor (`isSnc_collapse`). -/
theorem disjoinedFamily_isSnc (m : ℕ) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅) : (disjoinedFamily (ψ₀ := ψ₀) m F hF hm).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_collapse (disjoinList_isSnc_totalTransformSeqFrom m F hF hm (Fin.last _))
    (meetLocus_two_subfamily_original_eq_empty m F hF hm)

/-- The disjoined boundary has finitely many members: the collapsed one and the exceptional
divisors, one per disjoining blow-up. -/
theorem finite_disjoinedFamily_ι (m : ℕ) (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅) : Finite (disjoinedFamily (ψ₀ := ψ₀) m F hF hm).ι :=
  finite_collapsedFamilyOf_ι _ F

/-- **The disjoined triple** on the last stage of the disjoining list — the pull-back of the ideal
sheaf along the composite and the disjoined boundary (`disjoinedTripleOf` at the disjoining
list); Kollár's `(X', π^* I, ∑ E^i)`, to which `BMO_1` is applied [Kol07, 72]. -/
noncomputable def disjoinedTriple (T : AnalyticTriple ψ₀ M) {m : ℕ}
    (hm : T.F.meetLocus (m + 1) = ∅) :
    AnalyticTriple ψ₀ ((disjoinList (ψ₀ := ψ₀) m T.F T.isSnc hm).stage (Fin.last _)) :=
  disjoinedTripleOf T (disjoinList (ψ₀ := ψ₀) m T.F T.isSnc hm)
    (disjoinList_isSnc_totalTransformSeqFrom m T.F T.isSnc hm (Fin.last _))
    (meetLocus_two_subfamily_original_eq_empty m T.F T.isSnc hm)

/-- The disjoined triple lies in the marked class at mark `1` (whose finiteness clause asks for
finitely many nonempty members). -/
theorem disjoinedTriple_bmoClass (T : AnalyticTriple ψ₀ M) {m : ℕ}
    (hm : T.F.meetLocus (m + 1) = ∅) : AnalyticTriple.BMOClass 1 (disjoinedTriple T hm) :=
  disjoinedTripleOf_bmoClass T _ _ _

end Hironaka.Manifold
