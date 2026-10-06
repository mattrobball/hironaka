/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Defs
public import Hironaka.Manifold.BlowUp.Transform.Basic
import Hironaka.Manifold.BlowUp.Transform.Strict
import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Simple normal crossings divisors: constructions and the elementary lemmas

The constructions on the data of a hypersurface family — the empty family
(`HypersurfaceFamily.empty`), Kollár's total transform under a blowing-up
(`HypersurfaceFamily.totalTransform`: the strict transforms of the components,
`strictTransformSet`, followed by the exceptional divisor, appended last in the order
[Kol07, Definition 25]; Włodarczyk's exceptional divisor of a composite of blow-ups
[Wlo09, Remark (1) after Theorem 2.0.3]) and the restriction to a subset
(`HypersurfaceFamily.restrict`, Kollár's `E|_Z` [Kol07, Definition 24]) — and the elementary
lemmas: the projections of `IsSnc` and `IsSncChartAt` (the clauses of Kollár's definition of a
simple normal crossing divisor, [Kol07, Definition 24]), the closedness of the support and the
finiteness of the components meeting a compact set (local finiteness), the empty divisor (snc, and
every closed submanifold has simple normal crossings with it), the components of the total
transform [Kol07, Definition 25] and of the restriction, the position of the exceptional divisor in
the order, the support of the total transform (the set of points of Hironaka's
`red(f⁻¹(E) ∪ f⁻¹(D))` is `f⁻¹(E) ∪ f⁻¹(D)`, [Hir64, Main Theorem II'(N) (iii), p. 156]), from the
inclusions between the strict transform and the preimage, and the restriction of an snc chart to an
open set. These are the lemmas the rest of `Hironaka/Manifold/Snc/` and the boundary bookkeeping of
the blow-up sequences rest on.

It also states Hironaka's normal crossings [Hir64, Definition 2, p. 141] at the level of stalks,
`HasOnlyNormalCrossingsWith` and `HasOnlyNormalCrossings`, which read the irreducible components
through the minimal primes of the stalk (the local branches); the analytic main theorems state
their boundary clauses through the global components instead (`IdealSheaf.IsSncBoundary`).
-/

@[expose] public section

open TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

/-! ### The empty family, the total transform, the restriction -/

/-- The empty divisor `E = ∅` (no components). -/
def HypersurfaceFamily.empty (M : Type u) : HypersurfaceFamily M where
  ι := PEmpty.{u + 1}
  hyp := fun j => j.elim

section Constructions

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **The total transform** of the family `F` under the blowing-up `π : M' → M` with centre `Y`
([Kol07, Definition 25]; [Wlo09, Remark (1) after Theorem 2.0.3]): the strict transforms of the
components (`strictTransformSet`) followed by the exceptional divisor `π⁻¹(Y)`, appended last in
the order. -/
def HypersurfaceFamily.totalTransform {M' : Type u} [TopologicalSpace M'] (π : M' → M) (Y : Set M)
    (F : HypersurfaceFamily M) : HypersurfaceFamily M' where
  ι := F.ι ⊕ₗ PUnit.{u + 1}
  countable := inferInstanceAs (Countable (F.ι ⊕ PUnit.{u + 1}))
  hyp := Sum.elim (fun j => strictTransformSet π Y (F.hyp j)) (fun _ => π ⁻¹' Y) ∘ ofLex

/-- The **restriction** `F|_H = (E^j ∩ H)_j` of the family to a subset `H`, as a family on the
subspace `H` (Kollár's `E|_Z`, [Kol07, Definition 24]). -/
def HypersurfaceFamily.restrict (F : HypersurfaceFamily M) (H : Set M) : HypersurfaceFamily H where
  ι := F.ι
  hyp j := Subtype.val ⁻¹' F.hyp j

end Constructions

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u}

namespace HypersurfaceFamily

/-! ### The components of the total transform and of the restriction -/

section Data

variable {M' : Type u} [TopologicalSpace M'] (π : M' → M) (Y : Set M) (F : HypersurfaceFamily M)

/-- The components of the total transform indexed by `F` are the strict transforms of the
components of `F` [Kol07, Definition 25]. -/
theorem totalTransform_hyp_inl (j : F.ι) :
    (F.totalTransform π Y).hyp (toLex (Sum.inl j)) = strictTransformSet π Y (F.hyp j) :=
  rfl

/-- The last component of the total transform is the exceptional divisor `π⁻¹(Y)`
[Kol07, Definition 25]. -/
theorem totalTransform_hyp_inr :
    (F.totalTransform π Y).hyp (toLex (Sum.inr PUnit.unit)) = π ⁻¹' Y :=
  rfl

/-- The exceptional divisor comes after every strict transform in the order of the total
transform. -/
theorem totalTransform_inl_lt_inr (j : F.ι) :
    toLex (Sum.inl j) < (toLex (Sum.inr PUnit.unit) : F.ι ⊕ₗ PUnit.{u + 1}) :=
  Sum.Lex.inl_lt_inr _ _

/-- The components of the restriction are the traces of the components. -/
theorem restrict_hyp (H : Set M) (j : F.ι) : (F.restrict H).hyp j = Subtype.val ⁻¹' F.hyp j :=
  rfl

end Data

variable [TopologicalSpace M] [ChartedSpace E M] {F : HypersurfaceFamily M}

/-! ### The projections of `IsSnc` and `IsSncChartAt` -/

/-- The components of an snc divisor are closed smooth hypersurfaces [Kol07, Definition 24]. -/
theorem IsSnc.isClosedSubmanifold (hF : F.IsSnc ψ) (j : F.ι) : IsClosedSubmanifold ψ (F.hyp j) 1 :=
  hF.1 j

/-- The components of an snc divisor form a locally finite family. -/
theorem IsSnc.locallyFinite (hF : F.IsSnc ψ) : LocallyFinite F.hyp :=
  hF.2.1

/-- Every point has an snc chart [Kol07, Definition 24 (1)–(3)]. -/
theorem IsSnc.exists_isSncChartAt (hF : F.IsSnc ψ) (a : M) :
    ∃ (φ : OpenPartialHomeomorph M E) (c : {j // a ∈ F.hyp j} → Fin n), F.IsSncChartAt ψ φ a c :=
  hF.2.2 a

/-- An snc chart lies in the maximal analytic atlas. -/
theorem IsSncChartAt.mem_maximalAtlas {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (h : F.IsSncChartAt ψ φ a c) : φ ∈ maximalAtlas 𝓘(𝕜, E) ω M :=
  h.1

/-- An snc chart at `a` contains `a` in its source. -/
theorem IsSncChartAt.mem_source {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (h : F.IsSncChartAt ψ φ a c) : a ∈ φ.source :=
  h.2.1

/-- On the source of an snc chart at `a`, a component through `a` is the coordinate hyperplane of
its index [Kol07, Definition 24 (2)]. -/
theorem IsSncChartAt.mem_iff {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (h : F.IsSncChartAt ψ φ a c) (j : {j // a ∈ F.hyp j}) {x : M}
    (hx : x ∈ φ.source) :
    x ∈ F.hyp j.1 ↔ ψ (φ x) (c j) = 0 :=
  h.2.2.1 j x hx

/-- Distinct components through `a` have distinct coordinate indices
[Kol07, Definition 24 (3)]. -/
theorem IsSncChartAt.injective {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (h : F.IsSncChartAt ψ φ a c) : Function.Injective c :=
  h.2.2.2

/-- The support of an snc divisor is closed: a locally finite union of closed sets. -/
theorem IsSnc.isClosed_support (hF : F.IsSnc ψ) : IsClosed F.support :=
  hF.2.1.isClosed_iUnion fun j => (hF.1 j).isClosed

/-- Only finitely many components meet a compact set (local finiteness). -/
theorem IsSnc.finite_of_isCompact (hF : F.IsSnc ψ) {K : Set M} (hK : IsCompact K) :
    {j | (F.hyp j ∩ K).Nonempty}.Finite :=
  hF.2.1.finite_nonempty_inter_compact hK

/-! ### The empty divisor -/

/-- The empty family is a simple normal crossings divisor. -/
theorem isSnc_empty [IsManifold 𝓘(𝕜, E) ω M] : (HypersurfaceFamily.empty M).IsSnc ψ := by
  refine ⟨fun j => j.elim, fun x => ⟨Set.univ, Filter.univ_mem,
    Set.finite_empty.subset fun j _ => j.elim⟩, fun a =>
    ⟨chartAt E a, fun j => j.1.elim, IsManifold.chart_mem_maximalAtlas a, mem_chart_source E a,
      fun j => j.1.elim, fun j => j.1.elim⟩⟩

/-- Every closed submanifold has simple normal crossings with the empty divisor. -/
theorem hasSncWith_empty {Y : Set M} {c : ℕ} (hY : IsClosedSubmanifold ψ Y c) :
    (HypersurfaceFamily.empty M).HasSncWith ψ Y c := fun a ha => by
  obtain ⟨φ, σ, haφ, hφ⟩ := hY.exists_adaptedChart a ha
  exact ⟨φ, σ, fun j => j.1.elim, hφ, hφ.1, haφ, fun j => j.1.elim, fun j => j.1.elim⟩

/-! ### Simple normal crossings with a submanifold -/

/-- At every point of `Y` there is a chart adapted to `Y` which is an snc chart of `F`
[Kol07, Definition 24 (4)]. -/
theorem HasSncWith.exists_chart {Y : Set M} {c : ℕ} (h : F.HasSncWith ψ Y c) {a : M} (ha : a ∈ Y) :
    ∃ (φ : OpenPartialHomeomorph M E) (σ : Fin c ↪ Fin n) (cidx : {j // a ∈ F.hyp j} → Fin n),
      IsAdaptedChart ψ Y φ σ ∧ F.IsSncChartAt ψ φ a cidx :=
  h a ha

/-! ### The support of the total transform -/

section TotalTransform

variable {M' : Type u} [TopologicalSpace M'] (π : M' → M) (Y : Set M) (F : HypersurfaceFamily M)

/-- For a continuous `π` and closed components, the support of the total transform is the preimage
of the support together with the exceptional divisor: the set of points of Hironaka's
`red(f⁻¹(E) ∪ f⁻¹(D))` [Hir64, Main Theorem II'(N) (iii), p. 156] (from the inclusions between the
strict transform of a closed set and its preimage). -/
theorem support_totalTransform (hπ : Continuous π) (hF : ∀ j, IsClosed (F.hyp j)) :
    (F.totalTransform π Y).support = π ⁻¹' F.support ∪ π ⁻¹' Y := by
  ext p
  simp only [HypersurfaceFamily.support, Set.mem_iUnion, Set.mem_union, Set.mem_preimage]
  constructor
  · rintro ⟨k, hk⟩
    obtain j | u := k
    · exact Or.inl ⟨j, strictTransform_subset_preimage hπ (hF j) hk⟩
    · exact Or.inr hk
  · rintro (⟨j, hj⟩ | hp)
    · rcases preimage_subset_strictTransform_union (π := π) (Y := Y) (H := F.hyp j) hj with h | h
      · exact ⟨toLex (Sum.inl j), h⟩
      · exact ⟨toLex (Sum.inr PUnit.unit), h⟩
    · exact ⟨toLex (Sum.inr PUnit.unit), hp⟩

end TotalTransform

end HypersurfaceFamily

/-! ### Restricting an snc chart to an open set -/

namespace HypersurfaceFamily

open Set

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The restriction of an snc chart at `a` to an open set containing `a` is an snc chart at `a`
(the analogue of `IsAdaptedChart.restrOpen'`). -/
theorem IsSncChartAt.restrOpen
    {F : HypersurfaceFamily M} {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ₀ φ a c) {s : Set M} (hs : IsOpen s)
    (has : a ∈ s) : F.IsSncChartAt ψ₀ (φ.restrOpen s hs) a c := by
  refine ⟨?_, ?_, fun j x hx => ?_, hc.injective⟩
  · rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ hc.mem_maximalAtlas hs
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hc.mem_source, has⟩
  · rw [OpenPartialHomeomorph.restrOpen_source] at hx
    exact hc.mem_iff j hx.1

end HypersurfaceFamily

end Manifold

/-! ### Hironaka's normal crossings at the level of stalks -/

namespace AnalyticManifold

open scoped Manifold ContDiff

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

namespace IdealSheaf

variable {M : AnalyticManifold.{u} 𝕜 E}

/-- Hironaka's normal crossings [Hir64, Definition 2, p. 141] at the level of stalks: at every
point `x` of the subspace `D`, some regular system of parameters `(z_1, …, z_n)` of `𝒪_{M,x}`
(`n` generators of the maximal ideal, `n` the Krull dimension — the two clauses of the `Hironaka`
library's regular systems of parameters, spelled out as in `IsNormalCrossingsDivisor`) contains an
equation of each minimal prime of `E_x` and equations for `D_x`.

This body is stalk-local: "each irreducible component of `E` through `x`" is read as a minimal
prime of the analytic stalk `E_x`, a local branch, whereas Hironaka quantifies over the global
irreducible components of `E` containing `x`, so that his normal crossings is simple normal
crossings (every global component smooth). The two readings differ on analytic spaces: the real
nodal cubic `y² = x²(1 + x)` in `ℝ²` satisfies this body at every point (two smooth branch
parameters at the node) while its one global component is singular there. On schemes they
coincide, which is why the scheme form of this body is named
`AlgebraicGeometry.Scheme.IdealSheafData.IsSncBoundary`
(`Hironaka.Sequence.isSncBoundary_iff_isSnc_componentFamily`: Zariski-local components are the
global ones). The analytic main theorems use `IdealSheaf.IsSncBoundary` and
`IdealSheaf.IsSncBoundaryWith` instead; the ideal sheaf of a simple normal crossings family
does satisfy this body (`Hironaka/Manifold/Snc/Dictionary.lean`). -/
def HasOnlyNormalCrossingsWith (E D : IdealSheaf M) : Prop :=
  ∀ x ∈ D.support, ∃ (n : ℕ) (z : Fin n → stalkRing M x),
    (Ideal.span (Set.range z) = IsLocalRing.maximalIdeal (stalkRing M x) ∧
      (n : WithBot ℕ∞) = ringKrullDim (stalkRing M x)) ∧
    (∀ P ∈ (E.stalkIdeal x).minimalPrimes, ∃ i, P = Ideal.span {z i}) ∧
    ∃ s : Finset (Fin n), D.stalkIdeal x = Ideal.span (z '' ↑s)

/-- Hironaka's Definition 2 with `D = M` ("we simply say that `E` has only normal crossings"):
`HasOnlyNormalCrossingsWith E ⊥`, the zero ideal sheaf `⊥` being the ideal of `M` itself. The
stalk-local caveat of `HasOnlyNormalCrossingsWith` applies; the analytic main theorems use
`IdealSheaf.IsSncBoundary` instead. -/
def HasOnlyNormalCrossings (E : IdealSheaf M) : Prop := HasOnlyNormalCrossingsWith E ⊥

end IdealSheaf

end AnalyticManifold
