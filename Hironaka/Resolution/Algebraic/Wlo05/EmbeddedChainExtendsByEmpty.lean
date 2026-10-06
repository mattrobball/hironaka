/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainTransport
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The chain form under empty members and along an isomorphism

Two elementary transports of the chain form
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) used when the empty blow-ups of a run
are deleted ([Kol07, 34.1]; `cp1For_eraseEmpty` in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1EraseEmpty`): the chain form ignores members that
are the unit ideal — for families related by an extension by empty members (`ExtendsByEmpty`) the
two forms agree, the members through the point corresponding under the injection; and the chain form
pulls back along a morphism whose stalk map at the point is an isomorphism (the converse of
`chainRelativeAt_of_comap_of_isIso_stalkMap`, obtained from it along the inverse).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-- The members through `p` of a family and of its extension by empty members correspond: a member
of the extension through `p` is not the unit ideal, hence in the range of the injection. -/
theorem ExtendsByEmpty.mem_range_of_mem_support {E₁ E₂ : DivisorFamily X} {ι : E₁.ι → E₂.ι}
    (htop : ∀ j, j ∉ Set.range ι → E₂.component j = ⊤) {p : X} {j : E₂.ι}
    (hj : p ∈ (E₂.component j).support) : j ∈ Set.range ι := by
  by_contra hjr
  rw [htop j hjr, IdealSheafData.support_top] at hj
  exact hj

/-- The chain form ignores empty members — for `E₂` an extension of `E₁` by unit members, the chain
forms along `Γ` at `p` agree. -/
theorem chainRelativeAt_of_extendsByEmpty {E₁ E₂ : DivisorFamily X}
    (hext : ExtendsByEmpty E₁ E₂)
    {I Γ : X.IdealSheafData} {p : X} :
    ChainRelativeAt E₁ I Γ p ↔ ChainRelativeAt E₂ I Γ p := by
  classical
  obtain ⟨ι, hinj, hcomp, htop⟩ := hext
  -- the correspondence of the members through `p`
  let θ : {i : E₁.ι // p ∈ (E₁.component i).support} →
      {j : E₂.ι // p ∈ (E₂.component j).support} :=
    fun i => ⟨ι i.1, by rw [hcomp]; exact i.2⟩
  have hpre : ∀ j : {j : E₂.ι // p ∈ (E₂.component j).support},
      ∃ i : {i : E₁.ι // p ∈ (E₁.component i).support}, θ i = j := by
    intro j
    obtain ⟨i, hi⟩ := ExtendsByEmpty.mem_range_of_mem_support htop j.2
    refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
    rw [← hcomp, hi]
    exact j.2
  let θ' : {j : E₂.ι // p ∈ (E₂.component j).support} →
      {i : E₁.ι // p ∈ (E₁.component i).support} := fun j => Classical.choose (hpre j)
  have hθθ' : ∀ j, θ (θ' j) = j := fun j => Classical.choose_spec (hpre j)
  have hθinj : Function.Injective θ := fun i i' h =>
    Subtype.ext (hinj (Subtype.mk.inj h))
  have hθ'θ : ∀ i, θ' (θ i) = i := fun i => hθinj (hθθ' (θ i))
  have hθ'inj : Function.Injective θ' := fun j j' h => by
    rw [← hθθ' j, ← hθθ' j', h]
  have hcompθ : ∀ i : {i : E₁.ι // p ∈ (E₁.component i).support},
      E₂.component (θ i).1 = E₁.component i.1 := fun i => hcomp i.1
  constructor
  · rintro ⟨n, z, c, r, σ, a, b, ⟨hz, hcinj, hcmem, hσinj, hσc, ha, hΓ⟩, hb, hI⟩
    refine ⟨n, z, c ∘ θ', r, σ, a, b, ⟨hz, hcinj.comp hθ'inj, fun j => ?_, hσinj,
      fun i j => hσc i (θ' j), fun i k hk => ?_, hΓ⟩, fun k hk => ?_, hI⟩
    · have h1 := hcmem (θ' j)
      rw [← hcompθ (θ' j), hθθ' j] at h1
      exact h1
    · obtain ⟨i, hi⟩ := ha i k hk
      exact ⟨θ i, by rw [Function.comp_apply, hθ'θ, hi]⟩
    · obtain ⟨i, hi⟩ := hb k hk
      exact ⟨θ i, by rw [Function.comp_apply, hθ'θ, hi]⟩
  · rintro ⟨n, z, c, r, σ, a, b, ⟨hz, hcinj, hcmem, hσinj, hσc, ha, hΓ⟩, hb, hI⟩
    refine ⟨n, z, c ∘ θ, r, σ, a, b, ⟨hz, hcinj.comp hθinj, fun i => ?_, hσinj,
      fun i j => hσc i (θ j), fun i k hk => ?_, hΓ⟩, fun k hk => ?_, hI⟩
    · rw [← hcompθ i]
      exact hcmem (θ i)
    · obtain ⟨j, hj⟩ := ha i k hk
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ', hj]⟩
    · obtain ⟨j, hj⟩ := hb k hk
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ', hj]⟩

/-- The chain form pulls back along a morphism whose stalk map at the point is an isomorphism —
`chainRelativeAt_of_comap_of_isIso_stalkMap` applied to the inverse. -/
theorem chainRelativeAt_comap_of_isIso_stalkMap (φ : Y ⟶ X) [IsIso φ] {E : DivisorFamily X}
    {I Γ : X.IdealSheafData} (q : Y) (h : ChainRelativeAt E I Γ (φ q)) :
    ChainRelativeAt (E.comap φ) (I.comap φ) (Γ.comap φ) q := by
  have hq : q = (inv φ) (φ q) := by
    change q = (φ ≫ inv φ) q
    rw [IsIso.hom_inv_id]
    rfl
  have h' : ChainRelativeAt ((E.comap φ).comap (inv φ)) ((I.comap φ).comap (inv φ))
      ((Γ.comap φ).comap (inv φ)) (φ q) := by
    rw [← DivisorFamily.comap_comp, ← IdealSheafData.comap_comp, ← IdealSheafData.comap_comp,
        IsIso.inv_hom_id,
      DivisorFamily.comap_id, IdealSheafData.comap_id, IdealSheafData.comap_id]
    exact h
  rw [hq]
  exact chainRelativeAt_of_comap_of_isIso_stalkMap (inv φ) h'

end Hironaka.Resolution
