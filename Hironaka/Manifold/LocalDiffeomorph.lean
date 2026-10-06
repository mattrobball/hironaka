/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# A local diffeomorphism at a point is a partial diffeomorphism near it

Mathlib defines `IsLocalDiffeomorphAt I J n f x` as the existence of a partial diffeomorphism
`Φ` with `x ∈ Φ.source` on whose source `f` agrees with `Φ`, but does not expose the definition
to importing modules, so a proof cannot destructure it.
`IsLocalDiffeomorphAt.exists_partialDiffeomorph` recovers the witness from Mathlib's
`IsLocalDiffeomorphAt.localInverse`: the inverse of an arbitrary local inverse of `f` at `x`. The
converse is Mathlib's `PartialDiffeomorph.isLocalDiffeomorphAt`.
-/

@[expose] public section

open Set Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H₁ : Type*} [TopologicalSpace H₁]
  {H₂ : Type*} [TopologicalSpace H₂]
  {I : ModelWithCorners 𝕜 E H₁} {J : ModelWithCorners 𝕜 F H₂}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H₁ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] {n : WithTop ℕ∞}
  {f : M → N} {x : M}

/-- A local diffeomorphism `f` at `x` agrees with a partial diffeomorphism `Φ` on the source of
`Φ`, a neighbourhood of `x`: the definition of `IsLocalDiffeomorphAt`, which Mathlib does not
expose; the witness is the inverse of `hf.localInverse`. -/
theorem IsLocalDiffeomorphAt.exists_partialDiffeomorph (hf : IsLocalDiffeomorphAt I J n f x) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source := by
  refine ⟨hf.localInverse.symm, hf.localInverse_mem_target, fun y hy => ?_⟩
  have hy' : hf.localInverse.toPartialEquiv.symm y ∈ hf.localInverse.source :=
    hf.localInverse.map_target hy
  change f y = hf.localInverse.toPartialEquiv.symm y
  conv_lhs => rw [← hf.localInverse.right_inv hy]
  exact hf.localInverse_right_inv hy'

/-- The converse: `f` is a local diffeomorphism at `x` when it agrees on the source of a partial
diffeomorphism `Φ`, a neighbourhood of `x`, with `Φ`. Mathlib's
`PartialDiffeomorph.isLocalDiffeomorphAt` is the case `f = Φ`; here `f` replaces `Φ` as the
forward map of `Φ`, which changes nothing on `Φ.source`. -/
theorem IsLocalDiffeomorphAt.of_eqOn (Φ : PartialDiffeomorph I J M N n) (hx : x ∈ Φ.source)
    (h : EqOn f Φ Φ.source) : IsLocalDiffeomorphAt I J n f x :=
  PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ (x := x)
    { toFun := f
      invFun := Φ.invFun
      source := Φ.source
      target := Φ.target
      map_source' := fun y hy => by rw [h hy]; exact Φ.map_source hy
      map_target' := fun _ hy => Φ.map_target hy
      left_inv' := fun y hy => by rw [h hy]; exact Φ.left_inv hy
      right_inv' := fun y hy => (h (Φ.map_target hy)).trans (Φ.right_inv hy)
      open_source := Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.congr h
      contMDiffOn_invFun := Φ.contMDiffOn_invFun } hx

/-- A diffeomorphism as a partial diffeomorphism with source and target everything: Mathlib's
`Diffeomorph.toPartialDiffeomorph`, exposed, so that in an importing module its source and target
reduce to `univ` and its maps to those of the diffeomorphism (Mathlib exposes neither and has no
lemmas about it). -/
def Diffeomorph.toPartialDiffeomorphUniv (g : Diffeomorph I J M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := g.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := g.contMDiff_toFun x
  contMDiffOn_invFun _ _ := g.symm.contMDiffWithinAt

/-- A bijective local diffeomorphism as a diffeomorphism, with `f` as its forward map: Mathlib's
`IsLocalDiffeomorph.diffeomorphOfBijective`, exposed, so that an importing module sees that the
forward map is `f` (Mathlib exposes neither the definition nor this fact). The inverse is a
right inverse `g` of `f`, which agrees with the inverse of each local inverse of `f`. -/
noncomputable def IsLocalDiffeomorph.toDiffeomorphOfBijective (hf : IsLocalDiffeomorph I J n f)
    (hf' : Bijective f) : Diffeomorph I J M N n := by
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  choose Φ hyp using fun x => (hf x).exists_partialDiffeomorph
  have aux (x) : EqOn g (Φ x).symm (Φ x).target :=
    eqOn_of_leftInvOn_of_rightInvOn (fun x' _ => hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toOpenPartialHomeomorph).rightInvOn
        ((Φ x).toOpenPartialHomeomorph).mapsTo_symm (hyp x).2.symm)
      (fun _y hy => (Φ x).map_target hy)
  exact {
    toFun := f
    invFun := g
    left_inv := hgInverse.1
    right_inv := hgInverse.2
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := by
      intro y
      let x := g y
      obtain ⟨hx, hfx⟩ := hyp x
      apply ((Φ x).symm.contMDiffOn.congr (aux x)).contMDiffAt (((Φ x).open_target).mem_nhds ?_)
      have : y = (Φ x) x := ((hgInverse.2 y).congr (hfx hx)).mp rfl
      exact this ▸ (Φ x).map_source hx }
