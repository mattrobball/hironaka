/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.ClosedSubspaceAnalytic
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Closed analytic subspaces

Hironaka gives a closed analytic subspace of an analytic `K`-space `X` by a coherent sheaf of
ideals `𝓘 ⊆ 𝒪_X` [Hir64, Ch. 0, §1 and §5]; Bierstone and Milman spell the space out
[BM97, §3]: a closed subspace `Y` of `X` is given by a sheaf of ideals `𝓘_Y` of finite type in
`𝒪_X`, with `|Y| = supp 𝒪_X/𝓘_Y` and `𝒪_Y` the restriction of `𝒪_X/𝓘_Y` to `|Y|`. Here
"coherent" is read as locally finitely generated, so a closed subspace **is** an `IdealSheaf` on
the locally ringed space `X`, and the space `Y` is the quotient `KLocallyRingedSpace.quotient`,
which exists for every finite-type ideal sheaf on every locally ringed space and has
`𝒪_{Y,y} ≅ 𝒪_{X,y}/𝓘_y` (`QuotientSpace.stalkEquiv`).

## Main definitions

* `ClosedSubspace X := IdealSheaf X.𝒪`: the closed subspaces of `X`, given by their ideal sheaves.
* `closedSubspace X 𝒥`: the closed subspace defined by a finite-type ideal sheaf `𝒥`, as an
  analytic `K`-space [Hir64, Ch. 0, §1], [BM97, §3]: the quotient `X.quotient 𝒥` with Hironaka's
  clauses (i)–(iii). Its local models are `V(f₁, …, f_k, g₁, …, g_l)`, the ambient model of `X` cut
  out further by ambient lifts of local generators of `𝒥` (`quotient_locallyModel`); Hausdorff and
  countable at infinity are inherited by the closed subset `S(𝓘)` (`IdealSheaf.isClosed_support`).
  Its canonical morphism into `X` is `closedSubspaceι X 𝒥`, the quotient's `quotientι`.
* `IsSncBoundaryWith E D`, `IsSncBoundary E`: Kollár's Definition 24 [Kol07, Definition 24] at
  the stalk level on GLOBAL components — a locally finite family of closed subspaces (the
  components) such that at every point some regular system of parameters cuts out each component
  through the point by one member, distinct components by distinct members, `E` by their product
  and `D` (at its points) by some of the members. This is Hironaka's Definition 2 read, as he
  writes it, on "each irreducible component (i.e., a maximal reduced irreducible … analytic
  subspace)", and it is the boundary predicate of the resolution theorem for analytic spaces
  (`AnalyticSpace.exists_functorial_resolution`). The stalk-local `HasOnlyNormalCrossingsWith` reads
  the local branches instead; the two differ on the real nodal cubic `y² = x²(1 + x)`, whose two
  branches at the origin belong to one global component.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- A closed analytic subspace of the analytic `K`-space `X` [Hir64, Ch. 0, §1], [BM97, §3],
given by its ideal sheaf of finite type: an `IdealSheaf` on the locally ringed space `X`. The
subspace's ideal sheaf `𝓘_Y` is the subspace itself. -/
abbrev ClosedSubspace (X : AnalyticSpace.{u} K) : Type u := IdealSheaf X.toLocallyRingedSpace.𝒪

namespace ClosedSubspace

variable {X : AnalyticSpace.{u} K}

/-- Kollár's Definition 24 [Kol07, Definition 24] on an analytic space, at the stalk level, on
GLOBAL components: `E` is **the reduced divisor of a simple normal crossings family having simple
normal crossings with `D`** — there is a locally finite family `H` of closed subspaces of `X` (the
components `E^j`) such that at every point `x` some regular system of parameters `(z_1, …, z_n)`
of `𝒪_{X,x}` (`n` generators of the maximal ideal, `n` the Krull dimension) cuts out each
component through `x` by one member (so each component is a smooth hypersurface), distinct
components by distinct members, `E` by the product of those members (clauses (1)–(3) of the
definition), and, when `x ∈ D`, `D` by some of the members (clause (4):
`Z = (z_{j_1} = ⋯ = z_{j_s} = 0)`; "some of the `E^i` are allowed to contain `Z`"). This is
Hironaka's "`E` has only normal crossings with `D`" [Hir64, Ch. 0, §5, Definition 2] read on his
GLOBAL irreducible components, where `HasOnlyNormalCrossingsWith` reads the local branches (the
minimal primes of the stalk; the two differ on the real nodal cubic). The same notion on a
manifold is `AnalyticManifold.IdealSheaf.IsSncBoundaryWith`. Like it, and unlike the scheme
predicate of the same name (`AlgebraicGeometry.Scheme.IdealSheafData.IsSncBoundaryWith`, a
condition at the points of `D` only), it asserts simple normal crossings of `E` at every point of
`X` and implies `IsSncBoundary E`. -/
def IsSncBoundaryWith (E D : ClosedSubspace X) : Prop :=
  ∃ (ι : Type u) (H : ι → ClosedSubspace X), LocallyFinite (fun j => (H j).support) ∧
    ∀ x : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x),
      (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        (n : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x)) ∧
      (∃ (c : {j // x ∈ (H j).support} → Fin n) (s : Finset (Fin n)),
        Function.Injective c ∧ Set.range c = ↑s ∧
        (∀ j, (H j.1).stalkIdeal x = Ideal.span {z (c j)}) ∧
        E.stalkIdeal x = Ideal.span {∏ i ∈ s, z i}) ∧
      (x ∈ D.support → ∃ t : Finset (Fin n), D.stalkIdeal x = Ideal.span (z '' ↑t))

/-- Kollár's Definition 24 with `D = X` [Kol07, Definition 24]: `E` is the reduced divisor of a
simple normal crossings family — `IsSncBoundaryWith E ⊥`, the zero ideal sheaf `⊥` being the ideal
of `X` itself (as in `HasOnlyNormalCrossings`). Hironaka's "`E` has only normal crossings"
[Hir64, Ch. 0, §5, Definition 2] on his global components. This is the boundary predicate of the
resolution theorem `AnalyticSpace.exists_functorial_resolution`; the same notion on a manifold is
`AnalyticManifold.IdealSheaf.IsSncBoundary`. -/
def IsSncBoundary (E : ClosedSubspace X) : Prop := IsSncBoundaryWith E ⊥

end ClosedSubspace

/-! ### The closed subspace as an analytic space -/

section

open KLocallyRingedSpace QuotientSpace

variable (X : AnalyticSpace.{u} K)

/-- The closed analytic subspace defined by a finite-type ideal sheaf on an analytic `K`-space,
as an analytic `K`-space [Hir64, Ch. 0, §1], [BM97, §3]: the quotient `(S(𝓘), (𝒪_X/𝓘)|_{S(𝓘)})`
with Hironaka's clauses (i)–(iii). -/
def closedSubspace (J : IdealSheaf X.toLocallyRingedSpace.𝒪) : AnalyticSpace.{u} K where
  toKLocallyRingedSpace := X.toKLocallyRingedSpace.quotient J
  locallyModel := quotient_locallyModel X J
  t2 := by
    have : T2Space X.toLocallyRingedSpace.toTopCat := X.t2
    exact inferInstanceAs (T2Space J.support)
  sigmaCompact := by
    have : SigmaCompactSpace X.toLocallyRingedSpace.toTopCat := X.sigmaCompact
    exact isSigmaCompact_iff_sigmaCompactSpace.mp
      (isSigmaCompact_univ.of_isClosed_subset (IdealSheaf.isClosed_support J) (Set.subset_univ _))

/-- The canonical morphism of the closed subspace into `X`, a `K`-morphism of analytic
`K`-spaces: the quotient's `quotientι`. -/
def closedSubspaceι (J : IdealSheaf X.toLocallyRingedSpace.𝒪) : closedSubspace X J ⟶ X :=
  quotientι X.toKLocallyRingedSpace J

end

end AnalyticSpace
