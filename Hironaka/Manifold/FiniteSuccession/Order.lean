/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Basic
public import Hironaka.Manifold.Snc.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Blow-up sequences of order `m` and of order `≥ m`

Kollár's smooth blow-up sequences of order `m` and of order `≥ m` [Kol07, Definition 66], on
analytic manifolds. A smooth blow-up sequence of order `m` starting with `(X, I, E)` is a smooth
blow-up sequence `Π : (X_r, I_r, E_r) → ⋯ → (X_0, I_0, E_0) = (X, I, E)` where (1)
`(X_{i+1}, I_{i+1}, E_{i+1}) := (B_{Z_i} X_i, (π_i)^{-1}_* I_i, (π_i)^{-1}_{tot} E_i)`, (2) each
`π_i` is a smooth blow-up with centre `Z_i ⊂ X_i`, (3) `Z_i` has simple normal crossings with
`E_i`, and (4) `ord_{Z_i} I_i = m`; a sequence of order `≥ m` starting with `(X, I, m, E)` has
(1′) the marked transforms `(π_i)^{-1}_*(I_i, m)` in the recursion and (4′) `ord_{Z_i} I_i ≥ m`.
On a finite sequence of monoidal transformations `AnalyticManifold.FiniteSuccession`:

* (1) and (1′) are the recursions `weakTransformSeq` and `markedTransformSeq`: Kollár's
  birational transform `(π)^{-1}_* I = 𝒪(νF) · π^*I` with `ν = ord_Z I` [Kol07, Definition 48] is
  the weak transform, and `(π)^{-1}_*(I, m) = 𝒪(mF) · π^*I` [Kol07, Definition 60] is the marked
  transform; `E_i` is `boundarySeq`, the total transforms accumulating the exceptional divisors;
* (2) is built into the structure: every step of a `FiniteSuccession` is a monoidal
  transformation with a closed-submanifold centre (`isMonoidal`), so no smoothness clause is
  stated;
* (3) is `HasOnlyNormalCrossingsWith E_i C_i`, Hironaka's normal crossings [Hir64, Definition 2]
  read on the stalks: coordinates at every point of `Z_i` in which the branches of `E_i` through
  the point and `Z_i` itself are coordinate subspaces, the analytic reading of
  [Kol07, Definition 24 (4)];
* (4) and (4′) are the order along the centre, `ordAlongIdeal C_i I_i a`, at every point `a` of
  `Z_i`: the order at the generic point of the component of `Z_i` through `a`
  [Kol07, Definition 47], stated componentwise on the connected components.

The algebraic counterparts are `IsOrderSeq` and `IsOrderGeSeq` of
`AlgebraicGeometry.Scheme.BlowUpSequence`. The constructor lemmas and the comparison of the two
recursions are in
`Hironaka/Manifold/FiniteSuccession/OrderLemmas.lean`; sequences of order `≥ m` are what the
order-reduction theorems produce.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- `S` is a **smooth blow-up sequence of order `m` starting with `(M, I, E₀)`**
[Kol07, Definition 66 (1)–(4)]: for every step `i`, with `I_i := weakTransformSeq I i` (the
birational transforms, clause (1)) and `E_i := boundarySeq E₀ i` (the total transforms, clause
(1)), (3) the centre `Z_i = cosupp C_i` has normal crossings with `E_i`, and (4)
`ord_{Z_i} I_i = m` at every point of `Z_i` (the order along the centre, i.e. the order at the
generic point of the component through the point). Clause (2), "each `π_i` is a smooth blow-up
with centre `Z_i`", is the structure's `isMonoidal`. The hypothesis `max-ord I = m` of Kollár's
preamble is carried by the statements that use it, as for the algebraic `IsOrderSeq`. -/
def IsOfOrder (I E₀ : IdealSheaf M) (m : ℕ) : Prop :=
  ∀ i : Fin S.length,
    (S.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith (S.center i) ∧
      ∀ a ∈ (S.center i).support,
        IdealSheaf.ordAlongIdeal (S.center i) (S.weakTransformSeq I i.castSucc) a = (m : ℕ∞)

/-- `S` is a **smooth blow-up sequence of order `≥ m` starting with `(M, I, m, E₀)`**
[Kol07, Definition 66 (1′)–(4′)]: with `(I_i, m) := markedTransformSeq I m i` (the marked
transforms, clause (1′)) and `E_i := boundarySeq E₀ i`, (3′) `Z_i` has normal crossings with
`E_i`, and (4′) `ord_{Z_i} I_i ≥ m` at every point of `Z_i`. -/
def IsOfOrderGe (I : IdealSheaf M) (m : ℕ) (E₀ : IdealSheaf M) : Prop :=
  ∀ i : Fin S.length,
    (S.boundarySeq E₀ i.castSucc).HasOnlyNormalCrossingsWith (S.center i) ∧
      ∀ a ∈ (S.center i).support,
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i) (S.markedTransformSeq I m i.castSucc) a

end AnalyticManifold.FiniteSuccession

end
