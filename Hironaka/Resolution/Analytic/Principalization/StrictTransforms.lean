/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Principalization.MeetLocus
import Hironaka.Manifold.Snc.TotalTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The strict transforms of a family under a blowing-up

Kollár's disjoining [Kol07, 72] blows up the `m`-fold meet locus and continues with "the
`(π_0 ⋯ π_{t-1})^{-1}_* E_i`", the strict transforms of the components — the total transform of
[Kol07, Definition 25] without its exceptional member, indexed by the original index set. This
module defines that family, `HypersurfaceFamily.strictTransforms π Y F`, and proves what the
disjoining needs of it: it is a simple normal crossings divisor when the total transform is (a
subfamily), a point of a strict transform lies over the component, off the centre the strict
transforms are the preimages, and a point on `m` strict transforms lies over a point on the `m`
components. The key statement of [Kol07, 72] — after blowing up the `m`-fold locus no point lies
on `m` strict transforms — is proved with the adapted chart of the meet locus in `Disjoin.lean` of
this directory.
-/

@[expose] public section

universe u

open Set
open scoped Manifold ContDiff

namespace Manifold.HypersurfaceFamily

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M']

/-- Kollár's "the `(π_0 ⋯ π_{t-1})^{-1}_* E_i`" [Kol07, 72]: the family of the strict transforms of
the components of `F` under `π` with centre `Y`, indexed by the components of `F` — the total
transform of [Kol07, Definition 25] without its exceptional member. -/
def strictTransforms (π : M' → M) (Y : Set M) (F : HypersurfaceFamily M) :
    HypersurfaceFamily M' where
  ι := F.ι
  countable := F.countable
  linearOrder := F.linearOrder
  hyp j := strictTransformSet π Y (F.hyp j)

variable (π : M' → M) (Y : Set M) (F : HypersurfaceFamily M)

omit [TopologicalSpace M] in
@[simp] theorem strictTransforms_hyp (j : F.ι) :
    (F.strictTransforms π Y).hyp j = strictTransformSet π Y (F.hyp j) :=
  rfl

omit [TopologicalSpace M] in
/-- The strict transforms are the `inl` components of the total transform. -/
theorem strictTransforms_hyp_eq_totalTransform_hyp (j : F.ι) :
    (F.strictTransforms π Y).hyp j = (F.totalTransform π Y).hyp (toLex (Sum.inl j)) :=
  rfl

variable {π Y F}

section BlowUp

variable [IsManifold 𝓘(𝕜, E) ω M'] [T2Space M'] [SecondCountableTopology M'] {c : ℕ}

/-- A point of a strict transform lies over the component. -/
theorem mem_hyp_of_mem_strictTransforms (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'}
    {j : F.ι} (hp : p ∈ (F.strictTransforms π Y).hyp j) : π p ∈ F.hyp j :=
  mem_hyp_of_mem_strictTransform h hF hp

/-- Off the centre a strict transform is the preimage of its component. -/
theorem mem_strictTransforms_iff_of_notMem (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) {p : M'}
    (hpY : π p ∉ Y) (j : F.ι) : p ∈ (F.strictTransforms π Y).hyp j ↔ π p ∈ F.hyp j :=
  mem_strictTransform_iff_of_notMem h hF hpY j

/-- A point lying on `m` strict transforms lies over a point lying on the `m` components: the
meet loci of the strict transforms map into the meet loci of `F`. -/
theorem mem_meetLocus_of_mem_meetLocus_strictTransforms (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ)
    {m : ℕ} {p : M'} (hp : p ∈ (F.strictTransforms π Y).meetLocus m) : π p ∈ F.meetLocus m := by
  obtain ⟨s, hs, hps⟩ := hp
  exact ⟨s, hs, fun j hj => mem_hyp_of_mem_strictTransforms h hF (hps j hj)⟩

/-- Off the centre the meet loci of the strict transforms are the preimages of the meet loci. -/
theorem mem_meetLocus_strictTransforms_iff_of_notMem (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ)
    {m : ℕ} {p : M'} (hpY : π p ∉ Y) :
    p ∈ (F.strictTransforms π Y).meetLocus m ↔ π p ∈ F.meetLocus m := by
  constructor
  · exact mem_meetLocus_of_mem_meetLocus_strictTransforms h hF
  · rintro ⟨s, hs, hps⟩
    exact ⟨s, hs, fun j hj => (mem_strictTransforms_iff_of_notMem h hF hpY j).mpr (hps j hj)⟩

/-- The strict transforms form a simple normal crossings divisor when the centre has simple normal
crossings with `F` ([Kol07, Definition 25]): they are a subfamily of the total transform
(`isSnc_totalTransform`) — closed smooth hypersurfaces, locally finite, and at every point the snc
chart of the total transform serves with its indices restricted to the strict transforms through
the point. -/
theorem isSnc_strictTransforms (hY : IsClosedSubmanifold ψ Y c)
    (h : IsBlowUp ψ Y c π) (hF : F.IsSnc ψ) (hsnc : F.HasSncWith ψ Y c) :
    (F.strictTransforms π Y).IsSnc ψ := by
  have hT : (F.totalTransform π Y).IsSnc ψ := isSnc_totalTransform hY h hF hsnc
  refine ⟨fun j => hT.1 (toLex (Sum.inl j)), ?_, fun a => ?_⟩
  · have hlf := hT.2.1
    have hcomp : (F.strictTransforms π Y).hyp =
        (F.totalTransform π Y).hyp ∘ fun j : F.ι => (toLex (Sum.inl j) : F.ι ⊕ₗ PUnit.{u + 1}) :=
      rfl
    rw [hcomp]
    exact hlf.comp_injective fun j j' hjj' => Sum.inl.inj (toLex.injective hjj')
  · obtain ⟨φ, cT, hφ⟩ := hT.2.2 a
    refine ⟨φ, fun j => cT ⟨toLex (Sum.inl j.1), j.2⟩, hφ.mem_maximalAtlas, hφ.mem_source,
      fun j x hx => ?_, fun j j' hjj' => ?_⟩
    · exact hφ.mem_iff ⟨toLex (Sum.inl j.1), j.2⟩ hx
    · have h' := hφ.injective hjj'
      have h'' : toLex (Sum.inl j.1) = (toLex (Sum.inl j'.1) : F.ι ⊕ₗ PUnit.{u + 1}) :=
        Subtype.mk.inj h'
      exact Subtype.ext (Sum.inl.inj (toLex.injective h''))

end BlowUp

end Manifold.HypersurfaceFamily
