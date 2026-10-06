/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Submanifold.Defs
public import Hironaka.Algebra.Local.Defs
public import Hironaka.Manifold.StructureSheaf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Simple normal crossings divisors on an analytic manifold

Kollár's simple normal crossing divisors [Kol07, Definition 24] on analytic manifolds: a divisor
`E = ∑ E^j` is an ordered family of closed smooth hypersurfaces, and it has simple normal
crossings when every point has a chart in which each component through the point is a coordinate
hyperplane, with distinct coordinates for distinct components; a submanifold `Y` has simple normal
crossings with `E` when such a chart can be taken adapted to `Y` [Kol07, Definition 24 (4)]. The
data — an ordered countable family of subsets, `HypersurfaceFamily` — and the predicates `IsSnc`,
`HasSncWith` are separated, so that constructions on the data (Kollár's total transform
[Kol07, Definition 25], the restriction to a hypersurface) need no snc hypothesis. The index set is
ordered, as Kollár's algorithm requires of the boundary [Kol07, 72]. The reduced ideal sheaf of the
divisor (Hironaka's `red`, [Hir64, Main Theorem II'(N) (iii), p. 156]; the reduced space of
[BM97, Remark 3.14]) is the ideal sheaf of the germs vanishing on the support (`vanishingStalk`),
when those stalks have local generators — which `Hironaka/Manifold/Snc/Coherence.lean` proves for
an snc divisor.

The boundary predicates of the analytic main theorems, on the ideal sheaves of a bundled analytic
manifold, are stated through these notions: `IsSncBoundary B` says that `B` is the reduced ideal
sheaf of an snc hypersurface family, `IsSncBoundaryWith B D` that the family moreover has simple
normal crossings with the closed subspace `D`; `IsSncBoundaryTransversalTo B Y` that a closed
subspace `Y`, of possibly varying codimension, has simple normal crossings with it transversally,
and `IsMulBoundaryMonomial J Y B` that `J` is `Y` times a monomial in the components of the
family at every point (Włodarczyk's embedded desingularization, [Wlo09, Theorem 2.0.2 (3) and
(6)]). Hironaka's normal crossings [Hir64, Definition 2, p. 141] quantifies over the global
irreducible components of `E`; read on the minimal primes of the stalk (the local branches), the
condition is weaker on analytic spaces — the real nodal cubic `y² = x²(1 + x)` has two smooth
branches at the node but one singular global component — so the main theorems state their boundary
clauses through the global components, as Kollár's and Włodarczyk's simple normal crossings
[Kol07, Definition 24; Wlo09, Definition 3.2.4].

`IsNormalCrossingsDivisor J` is Bierstone–Milman's normal-crossings divisor [BM97, Theorem 1.10]:
a principal ideal sheaf generated at every point by a monomial in a regular system of parameters of
the stalk, spelled out as generators of the maximal ideal, as many as the Krull dimension. It is
the form of the conclusions of the principalization theorem on `σ^*(I)` and on the Jacobian ideal.
-/

@[expose] public section

open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

open TopologicalSpace

/-- An ordered, countable family of subsets of `M`: the components `E^j` of a divisor `E = ∑ E^j`
[Kol07, Definition 24]. The snc property is the predicate `HypersurfaceFamily.IsSnc`. -/
structure HypersurfaceFamily (M : Type u) : Type (u + 1) where
  /-- The index set of the components, countable and linearly ordered. -/
  ι : Type u
  [countable : Countable ι]
  [linearOrder : LinearOrder ι]
  /-- The component `E^j`. -/
  hyp : ι → Set M

attribute [instance] HypersurfaceFamily.countable HypersurfaceFamily.linearOrder

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

namespace HypersurfaceFamily

variable (F : HypersurfaceFamily M)

/-- The chart `φ` of the maximal atlas is an **snc chart** of `F` at `a ∈ φ.source` with coordinate
indices `c` — a function on the components through `a` — when every component through `a` is, on
the source of `φ`, the coordinate hyperplane `{z_{c j} = 0}`, and distinct components through `a`
have distinct indices [Kol07, Definition 24 (1)–(3)]. -/
def IsSncChartAt (φ : OpenPartialHomeomorph M E) (a : M) (c : {j // a ∈ F.hyp j} → Fin n) : Prop :=
  φ ∈ maximalAtlas 𝓘(𝕜, E) ω M ∧ a ∈ φ.source ∧
    (∀ j : {j // a ∈ F.hyp j}, ∀ x ∈ φ.source, x ∈ F.hyp j.1 ↔ ψ (φ x) (c j) = 0) ∧
    Function.Injective c

/-- `F` is a **simple normal crossings divisor** [Kol07, Definition 24]: each component is a closed
smooth hypersurface, the family is locally finite, and every point of `M` has an snc chart.
Hironaka's "`E` has only normal crossings" [Hir64, Definition 2, p. 141], read on the global
components. -/
def IsSnc : Prop :=
  (∀ j, IsClosedSubmanifold ψ (F.hyp j) 1) ∧ LocallyFinite F.hyp ∧
    ∀ a : M, ∃ (φ : OpenPartialHomeomorph M E) (c : {j // a ∈ F.hyp j} → Fin n),
      F.IsSncChartAt ψ φ a c

/-- `Y` **has simple normal crossings with** `F` [Kol07, Definition 24 (4)]: at every point of `Y`
there is a chart adapted to `Y` which is an snc chart of `F` there. Some components of `F` may
contain `Y` (Hironaka's "the ideal of `D` is generated by some of the `z_i`"
[Hir64, Definition 2, p. 141]; Bierstone–Milman's "`C_i` and `E_i` simultaneously have only normal
crossings" [BM97, (1.2)]). -/
def HasSncWith (Y : Set M) (c : ℕ) : Prop :=
  ∀ a ∈ Y, ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n)
    (cidx : {j // a ∈ F.hyp j} → Fin n), IsAdaptedChart ψ Y φ σ ∧ F.IsSncChartAt ψ φ a cidx

/-- The support `|F| = ⋃_j E^j` of the family. -/
def support : Set M := ⋃ j, F.hyp j

open Classical in
/-- **The reduced ideal sheaf of the divisor** (Hironaka's `red`,
[Hir64, Main Theorem II'(N) (iii), p. 156]; [BM97, Remark 3.14]): the ideal sheaf whose stalks are
the vanishing ideals of the support (`vanishingStalk`), when these have local generators (they do
for an snc divisor: the product of the coordinate equations of the components through the point,
`Hironaka/Manifold/Snc/Coherence.lean`); the unit ideal sheaf otherwise. -/
noncomputable def idealSheaf : IdealSheaf (structureSheaf 𝕜 E M) :=
  if h : IdealSheaf.HasLocalGenerators fun x => vanishingStalk (E := E) F.support x then
    IdealSheaf.ofStalks _ _ h
  else ⊤

end HypersurfaceFamily

end Manifold

namespace AnalyticManifold

section NormalCrossings

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

namespace IdealSheaf

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- Bierstone–Milman's **normal-crossings divisor**: a principal ideal sheaf generated locally by a
monomial in suitable analytic coordinates [BM97, Theorem 1.10] — at every point, by a monomial
`∏ z_i^{α_i}` in a regular system of parameters (generators of the maximal ideal, as many as the
Krull dimension). The form of the conclusions on `σ^*(I)` and on the Jacobian ideal in the
principalization theorem. -/
def IsNormalCrossingsDivisor (J : IdealSheaf M) : Prop :=
  ∀ x : M, ∃ (n : ℕ) (z : Fin n → stalkRing M x) (α : Fin n → ℕ),
    IsLocalRing.IsRegularSystemOfParameters z ∧ J.stalkIdeal x = Ideal.span {∏ i, z i ^ α i}

end IdealSheaf

end NormalCrossings

section Snc

/- The field is `RCLike` from here on: the snc charts of `HypersurfaceFamily.IsSnc` are charts over
`K ∈ {ℝ, ℂ}` (the main theorems instantiate `ℝ`). -/
variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace IdealSheaf

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- The boundary predicate of the analytic main theorems: `B` is **the reduced ideal sheaf of a
simple normal crossings hypersurface family** — for some coordinates `ψ : E ≃ 𝕜ⁿ` there is a
locally finite family `G` of closed smooth hypersurfaces with a simple normal crossings chart at
every point (`HypersurfaceFamily.IsSnc`; [Kol07, Definition 24; Wlo09, Definition 3.2.4]) whose
reduced ideal sheaf (`HypersurfaceFamily.idealSheaf`) is `B`. The coordinates are existential
inside the predicate, as in `AnalyticMap.IsMonoidalTransformation`: the statements carry no model
isomorphism, and Kollár names local coordinates at each point.

Relation to the source.
* **Translation.** `IsSncBoundary B` is Hironaka's "$E$ has only normal crossings"
  [Hir64, Definition 2, p. 141] and Włodarczyk's "$E_U^i$ has only simple normal crossings"
  [Wlo09, Theorem 2.0.3 (2)].
* **Interpretation.** Hironaka's normal crossings is read, as he writes it, on the global
  irreducible components: it is simple normal crossings [Kol07, Definition 24], where the
  stalk-local `HasOnlyNormalCrossings` reads the local branches. -/
def IsSncBoundary (B : IdealSheaf M) : Prop :=
  ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (G : Manifold.HypersurfaceFamily M),
    G.IsSnc ψ ∧ G.idealSheaf = B

/-- The boundary-with-centre predicate of the analytic main theorems: `B` is the reduced ideal
sheaf of a simple normal crossings hypersurface family `G` **having simple normal crossings with**
the closed subspace `D` — at every point of `D` a chart adapted to the set of points of `D` (a
closed submanifold of some codimension `c`) which is a simple normal crossings chart of `G` there
(`HypersurfaceFamily.HasSncWith`; [Kol07, Definition 24 (4)], "some of the `E^i` are allowed to
contain `Z`"; [Wlo09, Definition 3.2.4 (2)] and [Wlo09, Theorem 2.0.3 (2)], "`C_i` has simple
normal crossings with `E_i`"). The coordinates and the codimension are existential inside the
predicate, as in `AnalyticMap.IsMonoidalTransformation`.

The predicate thus asserts simple normal crossings of `B` at every point of `M` (it implies
`IsSncBoundary B`), and simple normal crossings with `D` at the points of `D`. The scheme
predicate of the same name (`AlgebraicGeometry.Scheme.IdealSheafData.IsSncBoundaryWith`) asserts
only the condition at the points of `D`, and nothing about its boundary elsewhere: for `D = ⊤`
the scheme predicate always holds, while this one is `IsSncBoundary B`.

Relation to the source.
* **Translation.** `IsSncBoundaryWith B D` is Hironaka's "$E$ has only normal crossings" together
  with "$E$ has only normal crossings with $D$" [Hir64, Definition 2, p. 141], the latter a
  condition at the points of $D$ only, both read on the global components. -/
def IsSncBoundaryWith (B D : IdealSheaf M) : Prop :=
  ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (G : Manifold.HypersurfaceFamily M) (c : ℕ),
    G.IsSnc ψ ∧ G.idealSheaf = B ∧ G.HasSncWith ψ D.support c

/-- The boundary-with-subspace predicate of Włodarczyk's embedded desingularization: `B` is the
reduced ideal sheaf of a simple normal crossings hypersurface family `G` with which the closed
subspace `Y` **has simple normal crossings transversally** — at every point `a` of `Y` a chart
adapted to the set of points of `Y` (a closed submanifold near `a`, of a codimension `c` read at
`a`) which is a simple normal crossings chart of `G` at `a`: simple normal crossings in the sense
of [Kol07, Definition 24 (4)]. Moreover, and this is an addition to Kollár's definition, which
allows components to contain `Y`, the coordinates cutting out `Y` are distinct from those of the
components of `G` through `a`, so that no component through `a` contains `Y` near `a` (Kollár's
case "`E` does not contain `Z`"). This is the reading of [Wlo09, Theorem 2.0.2 (3)], "`Ỹ` has
only simple normal crossings with the exceptional divisor `E_r`", for the strict transform.
Unlike `IsSncBoundaryWith`, the codimension may vary from point to point, as it does for the
strict transform of a subspace that is not equidimensional. -/
def IsSncBoundaryTransversalTo (B Y : IdealSheaf M) : Prop :=
  ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (G : Manifold.HypersurfaceFamily M),
    G.IsSnc ψ ∧ G.idealSheaf = B ∧
      ∀ a ∈ Y.support, ∃ (c : ℕ) (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n)
        (cidx : {j // a ∈ G.hyp j} → Fin n),
        Manifold.IsAdaptedChart ψ Y.support φ σ ∧ G.IsSncChartAt ψ φ a cidx ∧
          ∀ j, cidx j ∉ Set.range σ

/-- The factorization predicate of Włodarczyk's embedded desingularization: `J = I_Y · I_Ẽ` for a
divisor `Ẽ` that is, near every point, an effective combination of the components of a simple
normal crossings hypersurface family `G` whose reduced ideal sheaf is `B` — at every point `x` the
stalk `J_x` is the product of `(I_Y)_x` with a monomial `∏_{j ∈ s} (I_{G^j})_x^{α_j}` in the
vanishing ideals of finitely many components `G^j` through `x`, the exponents read at `x`
([Wlo09, Theorem 2.0.2 (6)], "`σ^*(I_Y) = I_Ỹ I_Ẽ`, where `I_Ỹ` is the sheaf of ideals of the
subvariety `Ỹ ⊂ M̃` and `I_Ẽ` is the sheaf of ideals of a simple normal crossing divisor `Ẽ`
which is a locally finite combination of the irreducible components of the divisor `E_{U_r}`";
the strengthening of Bravo–Villamayor). For `Y = ⊤` it says that `J` is, near every point, the
ideal of an effective combination of the hypersurfaces of `G` [Wlo09, Theorem 2.0.3 (3)]. -/
def IsMulBoundaryMonomial (J Y B : IdealSheaf M) : Prop :=
  ∃ (n : ℕ) (ψ : E ≃L[𝕜] (Fin n → 𝕜)) (G : Manifold.HypersurfaceFamily M),
    G.IsSnc ψ ∧ G.idealSheaf = B ∧
      ∀ x, ∃ (s : Finset G.ι) (α : G.ι → ℕ), (∀ j ∈ s, x ∈ G.hyp j) ∧
        J.stalkIdeal x = Y.stalkIdeal x * ∏ j ∈ s, Manifold.vanishingStalk (G.hyp j) x ^ α j

end IdealSheaf

end Snc

end AnalyticManifold
