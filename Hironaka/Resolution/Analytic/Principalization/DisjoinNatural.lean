/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
public import Hironaka.Resolution.Analytic.Principalization.Disjoin
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.Principalization.DisjoinLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The disjoining list is natural under local analytic isomorphisms

Functoriality for smooth morphisms [Kol07, 34.1] for the preliminary blow-ups of [Kol07, 72]: the
meet loci of the pulled-back family are the preimages of the meet loci (`meetLocus_comap`), the
strict transforms under the lift of a local analytic isomorphism to the blow-ups are the strict
transforms of the pulled-back family (`strictTransforms_comap_liftStep`, from
`strictTransformSet_preimage_of_square`), so the pull-back of the disjoining list along `h` is the
disjoining list of the pulled-back family (`disjoinList_pullback`, by recursion on the multiplicity
with `pullback_cons`; the pull-back of a blow-up sequence, [Kol07, 30.1]). This is the disjoining
half of the compatibility clause of the principalization family (the independence of the shrinking
open, `Canonicity.lean`).
-/

public section

universe u

open Set
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

open _root_.Manifold
open Hironaka.Manifold

variable {M N : Type u}

/-- The meet loci of the pulled-back family are the preimages of the meet loci. -/
theorem meetLocus_comap (F : HypersurfaceFamily M) (h : N → M) (m : ℕ) :
    (F.comap h).meetLocus m = h ⁻¹' F.meetLocus m :=
  rfl

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The strict transforms of `F` under the blowing-up with centre `Y`, pulled back along the lift
of a local analytic isomorphism `h`, are the strict transforms of `h^* F` under the blowing-up with
centre `h⁻¹(Y)` (`strictTransformSet_preimage_of_square`). -/
theorem strictTransforms_comap_liftStep (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {Y : Set M} {c : ℕ}
    (hY : IsClosedSubmanifold ψ₀ Y c) (F : HypersurfaceFamily M) :
    (F.strictTransforms (Manifold.blowUpπ ψ₀ hY) Y).comap (AnalyticManifold.BlowUpSequence.liftStep
        h hh hY) =
      (F.comap h).strictTransforms (Manifold.blowUpπ ψ₀ (hY.preimage_of_isLocalDiffeomorph hh))
        (⇑h ⁻¹' Y) := by
  unfold HypersurfaceFamily.strictTransforms HypersurfaceFamily.comap
  congr 1
  funext j
  exact strictTransformSet_preimage_of_square h hY (hY.preimage_of_isLocalDiffeomorph hh) rfl
    (AnalyticManifold.BlowUpSequence.liftStep h hh hY)
        (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh hY)
    (AnalyticManifold.BlowUpSequence.blowUpπ_liftStep h hh hY) (F.hyp j)

/-- `disjoinList` respects an equality of families (the hypotheses transported). -/
theorem disjoinList_congr {F F' : HypersurfaceFamily M} (e : F = F') (m : ℕ) (hF : F.IsSnc ψ₀)
    (hm : F.meetLocus (m + 1) = ∅) (hF' : F'.IsSnc ψ₀) (hm' : F'.meetLocus (m + 1) = ∅) :
    disjoinList (ψ₀ := ψ₀) m F hF hm = disjoinList m F' hF' hm' := by
  subst e
  rfl

/-- Functoriality of the disjoining blow-ups for local analytic isomorphisms ([Kol07, 34.1]): the
pull-back of the disjoining list along a local analytic isomorphism `h` is the disjoining list of
the pulled-back family. -/
theorem disjoinList_pullback : ∀ (m : ℕ) {M N : AnalyticManifold.{u} 𝕜 E}
    (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀) (hm : F.meetLocus (m + 1) = ∅)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    (disjoinList (ψ₀ := ψ₀) m F hF hm).pullback h hh =
      disjoinList m (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
        (by rw [HypersurfaceFamily.meetLocus_comap, hm, Set.preimage_empty])
  | 0, _, _, _, _, _, _, _ => rfl
  | 1, _, _, _, _, _, _, _ => rfl
  | m + 2, _, _, F, hF, hm, h, hh => by
    have hrest := disjoinList_pullback (m + 1) (disjoinNext F hF hm) (disjoinNext_isSnc F hF hm)
      (meetLocus_disjoinNext F hF hm)
      (AnalyticManifold.BlowUpSequence.liftStep h hh (hF.isClosedSubmanifold_meetLocus hm))
      (AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_liftStep h hh
          (hF.isClosedSubmanifold_meetLocus hm))
    have hfam := strictTransforms_comap_liftStep h hh (hF.isClosedSubmanifold_meetLocus hm) F
    rw [disjoinList_succ_succ, AnalyticManifold.BlowUpSequence.pullback_cons, disjoinList_succ_succ]
    exact congrArg
      (AnalyticManifold.BlowUpSequence.cons ((hF.isClosedSubmanifold_meetLocus
          hm).preimage_of_isLocalDiffeomorph hh))
      (hrest.trans (disjoinList_congr hfam (m + 1) _ _
        (disjoinNext_isSnc (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
          (by rw [HypersurfaceFamily.meetLocus_comap, hm, Set.preimage_empty]))
        (meetLocus_disjoinNext (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
          (by rw [HypersurfaceFamily.meetLocus_comap, hm, Set.preimage_empty]))))

end Hironaka.Manifold
