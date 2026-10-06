/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncFamily
import Hironaka.AnalyticSpace.SncFamilyDivisor
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Germ.TaylorIdeal
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Snc.Dictionary
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Simple normal crossings families of a manifold as families of closed subspaces of `Sp(M)`

The members of a simple normal crossings family `F` of hypersurfaces of an analytic manifold `M`
(`HypersurfaceFamily.IsSnc`, `Hironaka/Manifold/Snc/Defs.lean`), read as closed subspaces of
the analytic space `Sp(M)` through their ideal sheaves (`HypersurfaceFamily.toClosedSubspaces`,
`Hironaka/AnalyticSpace/SncFamily.lean`), form a simple normal crossings family of closed subspaces
(`ClosedSubspace.IsSncFamily`) with the same support, so their divisor is an snc boundary of
`Sp(M)` with support `|F|` — the form in which each piece of a glued resolution contributes its
exceptional divisor ([Kol07, Theorem 45 (3)] on a piece).

* `support_toClosedSubspaces_apply`, `support_toClosedSubspaces`: the supports;
* `isSncFamily_toClosedSubspaces`: in an snc chart at `a` the centred coordinates are a regular
  system of parameters of the analytic stalk (`maximalIdeal_eq_span_coord'`,
  `Hironaka/Manifold/Germ/TaylorIdeal.lean`; `ringKrullDim_stalk_of_chart`,
  `Hironaka/Manifold/Germ/StalkNoetherian.lean`) and each member through `a` is cut out by its
  coordinate (`IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_span`,
  `Hironaka/Manifold/BlowUp/Transform/Object.lean`);
* `exists_isSncBoundary_toSpace_of_isSnc`: the divisor of the members is an snc boundary of `Sp(M)`
  with support `|F|`.

Used by `Hironaka/Resolution/Analytic/Kol07Thm45/CoproductExceptionalSnc.lean`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace

universe u

namespace Manifold.HypersurfaceFamily

open IsManifold (maximalAtlas)
open scoped _root_.Manifold ContDiff

variable {K : Type} [RCLike K] {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ}
  {ψ : E ≃L[K] (Fin n → K)} {M : AnalyticManifold.{u} K E}

/-- The support of a member read as a closed subspace of `Sp(M)` is the member
(`IsClosedSubmanifold.cosupport_idealSheaf`); `support_toClosedSubspaces` is the union form. -/
theorem support_toClosedSubspaces_apply (F : HypersurfaceFamily (M : Type u))
    (h : ∀ j, IsClosedSubmanifold ψ (F.hyp j) 1) (j : F.ι) :
    (toClosedSubspaces F h j).support = F.hyp j :=
  (h j).cosupport_idealSheaf

theorem support_toClosedSubspaces (F : HypersurfaceFamily (M : Type u))
    (h : ∀ j, IsClosedSubmanifold ψ (F.hyp j) 1) :
    (⋃ j, (toClosedSubspaces F h j).support) = F.support :=
  Set.iUnion_congr fun j => support_toClosedSubspaces_apply F h j

/-- An snc family of hypersurfaces of `M` is an snc family of closed subspaces of `Sp(M)`
([Kol07, Definition 24]): in an snc chart at `a` the centred coordinates are a regular system of
parameters of the analytic stalk (`maximalIdeal_eq_span_coord'`, `ringKrullDim_stalk_of_chart`) and
each member through `a` is cut out by its coordinate
(`IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_span`). -/
theorem isSncFamily_toClosedSubspaces {F : HypersurfaceFamily (M : Type u)} (hF : F.IsSnc ψ) :
    ClosedSubspace.IsSncFamily (toClosedSubspaces F hF.1) := by
  refine ⟨?_, fun a => ?_⟩
  · have hsupp : (fun j => (toClosedSubspaces F hF.1 j).support) = F.hyp :=
      funext fun j => support_toClosedSubspaces_apply F hF.1 j
    rw [hsupp]
    exact hF.2.1
  · obtain ⟨φ, c, hc⟩ := hF.2.2 a
    have hφ : φ ∈ maximalAtlas 𝓘(K, E) ω (M : Type u) := hc.1
    have ha : a ∈ φ.source := hc.2.1
    refine ⟨n, fun i => coord E ψ φ hφ ha i - const K E M a (eval K E M a (coord E ψ φ hφ ha i)),
      ⟨(maximalIdeal_eq_span_coord' E ψ φ ha hφ).symm,
        (ringKrullDim_stalk_of_chart E ψ φ ha hφ).symm⟩, ?_⟩
    let e : {j // a ∈ (toClosedSubspaces F hF.1 j).support} → {j // a ∈ F.hyp j} :=
      fun j => ⟨j.1, (support_toClosedSubspaces_apply F hF.1 j.1) ▸ j.2⟩
    refine ⟨fun j => c (e j), fun j₁ j₂ hj => ?_, fun j => ?_⟩
    · exact Subtype.ext (show (e j₁).1 = (e j₂).1 from congrArg Subtype.val (hc.2.2.2 hj))
    · have hmem : a ∈ F.hyp j.1 := (e j).2
      have h1 : (toClosedSubspaces F hF.1 j.1).stalkIdeal a =
          Ideal.span (Set.range fun i : Fin 1 => coord E ψ φ hφ ha (singleEmb (c (e j)) i)) :=
        (hF.1 j.1).stalkIdeal_idealSheaf_eq_span hmem (hc.isAdaptedChart_hyp (e j)) ha
      have h2 : (Set.range fun i : Fin 1 => coord E ψ φ hφ ha (singleEmb (c (e j)) i)) =
          {coord E ψ φ hφ ha (c (e j))} := by
        rw [show (fun i : Fin 1 => coord E ψ φ hφ ha (singleEmb (c (e j)) i)) =
            fun _ => coord E ψ φ hφ ha (c (e j)) from funext fun i => by rw [singleEmb_apply]]
        exact Set.range_const
      have h3 : coord E ψ φ hφ ha (c (e j)) -
          const K E M a (eval K E M a (coord E ψ φ hφ ha (c (e j)))) = coord E ψ φ hφ ha (c (e j))
          := by
        rw [eval_coord E ψ φ ha hφ, hc.coord_eq_zero (e j), map_zero, sub_zero]
      exact h1.trans (congrArg Ideal.span (h2.trans (congrArg (fun v => ({v} : Set _)) h3.symm)))

/-- The divisor of the members of an snc family of hypersurfaces of `M` is an snc boundary of
`Sp(M)` with support `|F|` ([Kol07, Theorem 45 (3)] on one piece of a glued resolution). -/
theorem exists_isSncBoundary_toSpace_of_isSnc {F : HypersurfaceFamily (M : Type u)}
    (hF : F.IsSnc ψ) :
    ∃ E : ClosedSubspace (toSpace ψ M), E.IsSncBoundary ∧ E.support = F.support :=
  ⟨ClosedSubspace.divisorOf _ (isSncFamily_toClosedSubspaces hF).1,
    ClosedSubspace.isSncBoundary_divisorOf (isSncFamily_toClosedSubspaces hF),
    (ClosedSubspace.support_divisorOf _ _).trans (support_toClosedSubspaces F hF.1)⟩

end Manifold.HypersurfaceFamily

end
