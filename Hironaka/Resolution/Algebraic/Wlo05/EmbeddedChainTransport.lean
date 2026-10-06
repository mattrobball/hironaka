/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Hironaka.Resolution.Algebraic.Wlo05.ChainRelativeLift
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport of the chain form along a stalk isomorphism

The chain-relative form (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) is a statement
about one stalk; it transports along a morphism whose stalk map at the point is an isomorphism — the
pieces of the local cover of [Kol07, Theorem 105], `openImmersionCoprods`
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCoverTools`): the form of `I.comap φ` along
`Γ.comap φ` at `q` gives the form of `I` along `Γ` at `φ q`, with the coordinates pulled back along
the inverse isomorphism and the same exponents. The members through `q` of the pulled-back family
are the members through `φ q` (`AlgebraicGeometry.mem_support_comap_iff_apply`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Cover`
and `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainExtendsByEmpty`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Scheme.IdealSheafData Ideal

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-- The chain-relative form transports along a morphism whose stalk map at the point is an
isomorphism. -/
theorem chainRelativeAt_of_comap_of_isIso_stalkMap (φ : Y ⟶ X) {E : DivisorFamily X}
    {I Γ : X.IdealSheafData} {q : Y} [IsIso (φ.stalkMap q)]
    (h : ChainRelativeAt (E.comap φ) (I.comap φ) (Γ.comap φ) q) : ChainRelativeAt E I Γ (φ q) := by
  obtain ⟨n, w, c, r, σ, a, b, ⟨hw, hcinj, hcmem, hσinj, hσc, ha, hΓ'⟩, hb, hI'⟩ := h
  set e : X.presheaf.stalk (φ q) ≃+* Y.presheaf.stalk q :=
    (asIso (φ.stalkMap q)).commRingCatIsoToRingEquiv with he
  have heφ : (e : X.presheaf.stalk (φ q) →+* Y.presheaf.stalk q) = (φ.stalkMap q).hom := rfl
  -- `Hironaka.Sequence.Ideal.eq_map_symm_of_map_eq` in the ring-homomorphism form
  have hsymm : ∀ {A : Ideal (X.presheaf.stalk (φ q))} {B : Ideal (Y.presheaf.stalk q)},
      A.map (e : X.presheaf.stalk (φ q) →+* Y.presheaf.stalk q) = B →
        A = B.map (e.symm : Y.presheaf.stalk q →+* X.presheaf.stalk (φ q)) := fun h => by
    rw [← h, Ideal.map_map]
    simp
  have hmem : ∀ j : {j : E.ι // φ q ∈ (E.component j).support},
      q ∈ ((E.comap φ).component j.1).support :=
    fun j => (mem_support_comap_iff_apply _ _ _).mpr j.2
  have hrange : ∀ k : Fin n, k ∈ Set.range c → k ∈ Set.range
      fun j : {j : E.ι // φ q ∈ (E.component j).support} => c ⟨j.1, hmem j⟩ := by
    rintro k ⟨⟨j, hj⟩, rfl⟩
    exact ⟨⟨j, (mem_support_comap_iff_apply _ _ _).mp hj⟩, rfl⟩
  refine ⟨n, (e.symm : Y.presheaf.stalk q →+* X.presheaf.stalk (φ q)) ∘ w,
    fun j => c ⟨j.1, hmem j⟩, r, σ, a, b,
    ⟨Hironaka.Sequence.isRegularSystemOfParameters_comp_ringEquiv e.symm hw, ?_, ?_, hσinj,
      fun i j => hσc i ⟨j.1, hmem j⟩, fun i k hk => hrange k (ha i k hk), ?_⟩,
    fun k hk => hrange k (hb k hk), ?_⟩
  · intro j j' hjj
    exact Subtype.ext (Subtype.mk.inj (hcinj hjj))
  · intro j
    have h1 := hcmem ⟨j.1, hmem j⟩
    change ((E.component j.1).comap φ).stalkIdeal q = _ at h1
    rw [IdealSheafData.stalkIdeal_comap, ← heφ] at h1
    rw [hsymm h1, map_span, Set.image_singleton]
    rfl
  · rw [IdealSheafData.stalkIdeal_comap, ← heφ] at hΓ'
    rw [hsymm hΓ', map_span, ← Set.range_comp, Function.comp_assoc]
  · rw [IdealSheafData.stalkIdeal_comap, ← heφ] at hI'
    have hM : ((e.symm : Y.presheaf.stalk q →+* X.presheaf.stalk (φ q)) ∘
        fun i => monomialOf w (a i)) =
        fun i => monomialOf ((e.symm : Y.presheaf.stalk q →+* X.presheaf.stalk (φ q)) ∘ w) (a i) :=
      funext fun i => by rw [Function.comp_apply, monomialOf_map]
    rw [hsymm hI', Ideal.map_mul, map_span, Set.image_singleton, monomialOf_map,
      ← chainIdeal_comp, Function.comp_assoc, hM]

end Hironaka.Resolution
