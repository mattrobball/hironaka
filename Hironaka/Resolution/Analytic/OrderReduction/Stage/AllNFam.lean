/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Stage.InstancesFam
public import Hironaka.Resolution.Analytic.Functor.FamilyClosedEmbedding
import Hironaka.Resolution.Analytic.OrderReduction.ClosedEmbeddingFam
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Order reduction in every dimension, given the second reduction step

Kollár's Theorems 68 and 69 ([Kol07, Theorem 68], [Kol07, Theorem 69]) assert order reduction for
ideals and for marked ideals in every dimension and at every mark; they follow from the recursion
of [Kol07, 70], which starts from the trivial functors in dimension `0` and climbs by Theorem 103
(70.1) and Theorem 107 (70.2). On analytic manifolds the families in every dimension are the
components of the tower on the compatible-family structures (`Stage/Family.lean`), read at the
dimension `n` and the mark `m`.

The first reduction step is Theorem 103 as constructed in `Stage/InstancesFam.lean`
(`theorem103FamStar`); the second is left as a parameter `h107 : BMOanFamStep 𝕜`, so that the
statements here hold for any construction of Theorem 107 (the library's is
`theorem107FamStarOf` of `Stage/InstancesFamTheorem107.lean`, applied in `Stage/Concrete.lean`).

* `BOanFamAllOf 𝕜 h107 n m`, `BMOanFamAllOf 𝕜 h107 n m` — the two families as components of the
  tower `orderReductionTowerAnFam (theorem103FamStar 𝕜) h107`; their values in dimension `0` and
  at a successor are `BOanFamAllOf_zero`, `BOanFamAllOf_succ`, `BMOanFamAllOf_zero`,
  `BMOanFamAllOf_succ`, all by definition.
* `BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam` — Theorem 103 (3) at every stage,
  at the mark `1`:
  for a closed hypersurface `τ : Y ↪ X`, an ideal sheaf `I` containing the ideal sheaf of `Y` and
  `J = τ^* I` (so that `τ_*(𝒪_Y / J) = 𝒪_X / I`), the order-reduction family in dimension `n + 1`
  on `(X, I, ∅)` is the push-forward of the marked family in dimension `n` on `(Y, J, 1, ∅)`,
  over every relatively compact open ([Kol07, Theorem 103 (3)]); this is
  `BO.BOanFamOfInput_commutesWithClosedEmbeddingsOfEmptyDivisorFam` of `ClosedEmbeddingFam.lean`
  at the marked family of dimension `n`.
* `StepCommutesWithClosedEmbeddingsOfEmptyDivisorFam h107` — the corresponding property of a
  second reduction step: whenever the order-reduction family at the mark `1` commutes with closed
  embeddings of empty divisor through a family functor on the submanifolds, so does the marked
  family the step builds from it. This is the content of [Kol07, 108]: at the mark `1`,
  `BMO_{n,1}(X, I, 1, ∅) = BO_{n,1}(X, I, ∅)` by Theorem 107 (3), and the latter is the
  push-forward by Theorem 103 (3); the argument never inspects the functor on the submanifold.
* `BMOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam` — given that property of `h107`,
  the marked family in dimension `n + 1` at the mark `1` commutes with closed embeddings of empty
  divisor through the marked family in dimension `n` ([Kol07, Claim 71.2] for hypersurfaces,
  proved in [Kol07, 108]); the general codimension follows by Kollár's reduction to a chain of
  hypersurfaces, which is not carried out here.
-/

@[expose] public section

noncomputable section


universe u

namespace Hironaka.Manifold

variable (𝕜 : Type) [RCLike 𝕜]

/-- Order reduction for ideals in every dimension and at every mark ([Kol07, Theorem 68]), in the
compatible-family form, given a second reduction step `h107`: the component `bo` of the tower along
`theorem103FamStar 𝕜` and `h107`, at the dimension `n` and the mark `m`. -/
def BOanFamAllOf (h107 : BMOanFamStep.{u} 𝕜) (n m : ℕ) : BOanFam.{u} 𝕜 n m :=
  (orderReductionTowerAnFam (theorem103FamStar 𝕜) h107 n).bo m

/-- Order reduction for marked ideals in every dimension and at every mark ([Kol07, Theorem 69]),
in the compatible-family form, given a second reduction step `h107`: the component `bmo` of the
tower along `theorem103FamStar 𝕜` and `h107`. -/
def BMOanFamAllOf (h107 : BMOanFamStep.{u} 𝕜) (n m : ℕ) : BMOanFam.{u} 𝕜 n m :=
  (orderReductionTowerAnFam (theorem103FamStar 𝕜) h107 n).bmo m

variable (h107 : BMOanFamStep.{u} 𝕜)

/-- In dimension `0` the order-reduction family is the trivial one ([Kol07, 70]). -/
theorem BOanFamAllOf_zero (m : ℕ) : BOanFamAllOf.{u} 𝕜 h107 0 m = boZeroAnFam m := rfl

/-- In dimension `n + 1` the order-reduction family is Theorem 103 applied to the marked families
of dimension `n` ([Kol07, 70.1]). -/
theorem BOanFamAllOf_succ (n m : ℕ) :
    BOanFamAllOf.{u} 𝕜 h107 (n + 1) m = BO.BOanFamOfInput 𝕜 (n + 1) (BMOanFamAllOf 𝕜 h107 n) m :=
  rfl

/-- In dimension `0` the marked family is the trivial one ([Kol07, 70]). -/
theorem BMOanFamAllOf_zero (m : ℕ) : BMOanFamAllOf.{u} 𝕜 h107 0 m = bmoZeroAnFam m := rfl

/-- In dimension `n + 1` the marked family is the second reduction step applied to the
order-reduction families of dimension `n + 1` ([Kol07, 70.2]). -/
theorem BMOanFamAllOf_succ (n m : ℕ) :
    BMOanFamAllOf.{u} 𝕜 h107 (n + 1) m = h107.bmo (n + 1) (BOanFamAllOf 𝕜 h107 (n + 1)) m := rfl

/-- Theorem 103 (3) at every stage of the tower ([Kol07, Theorem 103 (3)]): the order-reduction
family in dimension `n + 1` at the mark `1` commutes with closed embeddings of hypersurfaces when
the boundary is empty, through the marked family in dimension `n` at the mark `1` — the value on
`(X, I, ∅)` is the push-forward of the value on `(Y, τ^* I, 1, ∅)` over every relatively compact
open. This is `BO.BOanFamOfInput_commutesWithClosedEmbeddingsOfEmptyDivisorFam` at the marked
family of dimension `n`, the recursion equation `BOanFamAllOf_succ` holding by definition. -/
theorem BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam (n : ℕ) :
    (BOanFamAllOf.{u} 𝕜 h107 (n + 1) 1).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam
      (s := 1) (BMOanFamAllOf 𝕜 h107 n 1).functor :=
  BO.BOanFamOfInput_commutesWithClosedEmbeddingsOfEmptyDivisorFam 𝕜 (n + 1) (BMOanFamAllOf 𝕜 h107 n)

/-- The property of a second reduction step `h107` behind [Kol07, 108]: for every dimension `n` and
every input `bo` of order-reduction families, if the family `bo 1` commutes with closed embeddings
of empty divisor through a family functor `B'` on the submanifolds of codimension `s`, then so does
the marked family `h107.bmo n bo 1`. Kollár's argument for the step never inspects `B'`:
`BMO_{n,1}(X, I, 1, ∅) = BO_{n,1}(X, I, ∅)` by Theorem 107 (3), and the latter is the push-forward
by
hypothesis. -/
def StepCommutesWithClosedEmbeddingsOfEmptyDivisorFam (h107 : BMOanFamStep.{u} 𝕜) : Prop :=
  ∀ (n : ℕ) (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d) {s : ℕ}
    {Dom' : ∀ {M' : AnalyticManifold.{u} 𝕜 (Fin (n - s) → 𝕜)},
      Manifold.AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) M' → Prop}
    (B' : AnalyticFamilyFunctor (ContinuousLinearEquiv.refl 𝕜 (Fin (n - s) → 𝕜)) Dom'),
    (bo 1).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B' →
      (h107.bmo n bo 1).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam (s := s) B'

/-- [Kol07, Claim 71.2] for hypersurfaces, as proved in [Kol07, 108]: given the property
`StepCommutesWithClosedEmbeddingsOfEmptyDivisorFam` of the second reduction step, the marked
family in dimension `n + 1` at the mark `1` commutes with closed embeddings of empty divisor
through the marked family in dimension `n` at the mark `1`. It is the property of the step at the
order-reduction families of dimension `n + 1`, with Theorem 103 (3)
(`BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam`) as its hypothesis; the recursion
equation `BMOanFamAllOf_succ` holds by definition. Kollár's reduction of the general codimension to
a chain of hypersurfaces is not carried out here. -/
theorem BMOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam
    (h16b : StepCommutesWithClosedEmbeddingsOfEmptyDivisorFam 𝕜 h107) (n : ℕ) :
    (BMOanFamAllOf.{u} 𝕜 h107 (n + 1) 1).functor.CommutesWithClosedEmbeddingsOfEmptyDivisorFam
      (s := 1) (BMOanFamAllOf 𝕜 h107 n 1).functor :=
  @h16b (n + 1) (BOanFamAllOf 𝕜 h107 (n + 1)) 1 _ (BMOanFamAllOf 𝕜 h107 n 1).functor
    (BOanFamAllOf_commutesWithClosedEmbeddingsOfEmptyDivisorFam 𝕜 h107 n)

end Hironaka.Manifold

end
