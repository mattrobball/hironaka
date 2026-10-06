/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
public import Hironaka.Manifold.FiniteSuccession.Order
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The data of the marked order-reduction functor `BMO_{n,m}` on analytic manifolds

Kollár's Theorem 107 ([Kol07, Theorem 107]; the inductive form of [Kol07, Theorem 69]) asserts,
for every `m`, a smooth blow-up sequence functor `BMO_{n,m}` on marked triples `(X, I, m, E)` with
`dim X = n` such that (1) the final transform has `max-ord I_r < m`, (2) the functor commutes with
smooth morphisms and with change of fields, and (3) it agrees with `BO_{n,m}` when
`m = max-ord I` and `E = ∅`. This module fixes the class and packages the analytic form of
(1)–(2) as a structure:

* `AnalyticTriple.BMOClass m` — the domain of `BMO_{n,m}`: `1 ≤ m` and only finitely many members
  of the boundary are nonempty. Kollár's `BMO_{n,m}` is defined on all marked triples of dimension
  `n`, with no bound on the order; the class differs from `BOClass m` by the missing
  order clause, and `1 ≤ m` is imposed because clause (1) cannot hold at `m = 0` on a nonempty
  manifold.
* `BMOanData 𝕜 n m` — a blow-up sequence functor on `BMOClass m` at the standard model
  `ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)` with four clauses: (i) its values are smooth blow-up
  sequences of order `≥ m` starting with `(M, 𝓘, m, E)` ([Kol07, Definition 66 (1′)–(4′)]);
  (ii) Theorem 107 (1), pointwise: the controlled transform `Π^{-1}_*(𝓘, m)` at the last stage has
  order `< m` at every point; (iii) Theorem 107 (2): the functor commutes with local analytic
  isomorphisms, the analytic form of [Kol07, 34.1] (the change-of-fields clause has no analytic
  counterpart); (iv) indifference to empty boundary members. Theorem 107 (3) and
  Kollár's item 108 are not fields.

The marked data of dimension `n - 1` is the input of Lemma 102 ([Kol07, Lemma 102]: the functor
`BD_{n,m,j}` is `BMO_{n-1,m}` on the hypersurface `E^j`, pushed forward and composed with the
first blow-up), in the construction `BDan` of `BD.lean`. The functor is valued in finite blow-up
sequences on the whole manifold; the form used by the main theorems is `BMOanFam`
(`Functor/Family.lean`), the parameter of the construction of Theorem 103 in `OrderReduction/` and
the output of the construction of Theorem 107 (`BMO/`, `Modified/`), the recursion on the
dimension closing the loop (`Stage/`).
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

namespace AnalyticTriple

/-- The class of the marked order-reduction functors `BMO_{n,m}` ([Kol07, Theorem 69] and
[Kol07, Theorem 107]: "defined on triples `(X, I, m, E)` with `dim X = n`"): `1 ≤ m` and only
finitely many members of the boundary are nonempty. There is no order bound: `BOClass m` is the
subclass with `ord 𝓘 ≤ m` everywhere. -/
def BMOClass (m : ℕ) : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop :=
  fun T => 1 ≤ m ∧ Finite {j // T.F.hyp j ≠ ∅}

variable {m : ℕ} {M : AnalyticManifold.{u} 𝕜 E} {T : AnalyticTriple ψ₀ M}

/-- The class's mark is positive. -/
theorem BMOClass.one_le (hT : BMOClass m T) : 1 ≤ m := hT.1

/-- Only finitely many members of a triple of the class are nonempty. -/
theorem BMOClass.finite (hT : BMOClass m T) : Finite {j // T.F.hyp j ≠ ∅} := hT.2

/-- A triple whose boundary has no member lies in the marked class at mark `1`. -/
theorem bmoClass_one_of_isEmpty (T : AnalyticTriple ψ₀ M) (h : IsEmpty T.F.ι) : BMOClass 1 T :=
  ⟨le_rfl, Subtype.finite⟩

/-- `(M, 𝓘, ∅)` lies in the marked class at mark `1`. -/
theorem bmoClass_one_empty (I : AnalyticManifold.IdealSheaf M) (hI : I.IsNonzeroEverywhere) :
    BMOClass 1 (⟨I, hI, HypersurfaceFamily.empty M, HypersurfaceFamily.isSnc_empty⟩ :
      AnalyticTriple ψ₀ M) :=
  bmoClass_one_of_isEmpty _ ⟨fun j => PEmpty.elim j⟩

/-- The class of `BO_{n,m}` lies in the class of `BMO_{n,m}` (Theorem 107 (3),
`BMO_{n,m}(X, I, m, E) = BO_{n,m}(X, I, E)` when `max-ord I = m`, presupposes it). -/
theorem BOClass.bmoClass (hT : BOClass m T) : BMOClass m T := ⟨hT.1, hT.2.2⟩

end AnalyticTriple

/-- The data of Kollár's marked order-reduction functor `BMO_{n,m}` ([Kol07, Theorem 107 (1)–(2)])
on analytic manifolds modelled on `𝕜ⁿ`: a blow-up sequence functor on the marked class `BMOClass m`
at the standard model such that its values are smooth blow-up sequences of order `≥ m` starting
with `(M, 𝓘, m, E)` ([Kol07, Definition 66 (1′)–(4′)]), the controlled transform at the last stage
has order `< m` at every point, the functor commutes with local analytic isomorphisms
([Kol07, 34.1]) and is indifferent to empty boundary members. Theorem 107 (3) and item 108 are
not fields.

The functor is valued in finite blow-up sequences on the whole manifold, which need not be
compact; since the class puts no bound on the order of `𝓘`, which may grow without bound towards
infinity, no finite sequence reduces it everywhere, and this structure has no inhabitant in
dimension `n ≥ 1` (an observation, not proved in this library). The compatible-family structure
`BMOanFam` (`Functor/Family.lean`) is the one
the main theorems use. -/
structure _root_.Hironaka.Manifold.BMOanData (𝕜 : Type) [RCLike 𝕜] (n m : ℕ) where
  /-- The functor `BMO_{n,m}` on the marked class at the standard model `𝕜ⁿ`. -/
  functor : AnalyticBlowUpSequenceAssignment (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
    (AnalyticTriple.BMOClass m)
  /-- The values are smooth blow-up sequences of order `≥ m` starting with `(M, 𝓘, m, E)`
  ([Kol07, Definition 66 (1′)–(4′)]). -/
  isOfOrderGe : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T),
    (functor.seq T hT).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf
  /-- Theorem 107 (1), `max-ord I_r < m`, pointwise: the controlled transform at the last stage has
  order `< m` at every point. -/
  ord_lt : ∀ {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (hT : AnalyticTriple.BMOClass m T) (x : (functor.seq T hT).toSuccession.stage (Fin.last _)),
    ((functor.seq T hT).toSuccession.markedTransformSeq T.I m (Fin.last _)).ord x < (m : ℕ∞)
  /-- Theorem 107 (2), "commutes with smooth morphisms": the functor commutes with local analytic
  isomorphisms, both clauses of [Kol07, 34.1]. -/
  commutesWithLocalIsos : functor.CommutesWithLocalIsos
  /-- The functor is indifferent to empty boundary members (`IndifferentToEmptyMembers`). -/
  indifferentToEmptyMembers : functor.IndifferentToEmptyMembers

end Manifold

end
