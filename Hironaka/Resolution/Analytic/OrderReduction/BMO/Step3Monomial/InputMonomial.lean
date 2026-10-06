/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Input
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Ideal
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Split
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1Comap
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.TransformStalk
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial ideal of the input family is the monomial part of the restricted triple

The monomial part `M(𝓘|_U)` of the restricted triple is indexed by the connected components of the
restricted members (`BMO/MonomialPart.lean`), while the input piece family of the monomial procedure
(`BMO/Step3Monomial/Input.lean`) has as pieces the traces on `U` of the ambient components meeting
`closure U`. The two products agree (`monomialIdeal_inputFamily`): stalk by stalk, both are the
product, over the members through the point, of the vanishing stalk of the member raised to the
exponent of the ambient component through the point. On one side the pieces through `x` are the
traces of the ambient components through `x`, one per member through `x`; on the other the active
components of `E|_U` at `x` are one per member through `x`, each with the stalk of its member and
with the exponent of the ambient component (the exponent transports along the open inclusion). The
two products are matched member by member.
-/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M) (U : Opens M) (hU : IsCompact (closure (U : Set M)))

/-- The monomial ideal of the input family is the monomial part of the restricted triple: every
component of a trace carries the exponent of its ambient component, and the locally finite product
over the components of the restricted members regroups into the finite product over the traces. -/
theorem monomialIdeal_inputFamily :
    (inputFamily T U hU).monomialIdeal
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
        (inputFamily_realizes T U hU) =
      monomialPart (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I := by
  classical
  have hΦ := inputFamily_realizes T U hU
  refine IdealSheaf.ext fun x => ?_
  rw [(inputFamily T U hU).stalkIdeal_monomialIdeal
    (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).isSnc hΦ x,
    stalkIdeal_monomialPart]
  -- a piece through `x` lies in its member
  have hmem : ∀ c : {c : Fin (inputFamily T U hU).nextComp // x ∈ (inputFamily T U hU).piece c},
      x ∈ (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp
        (inputEmb T U hU ⟨(inputFamily T U hU).label c.1,
          (inputFamily T U hU).label_lt c.1 c.1.2⟩) :=
    fun c => hΦ.piece_subset_hyp c.1.2 c.2
  -- the matching: a piece through `x` ↦ the component of `x` in the piece's member
  refine Finset.prod_bij (fun c _ =>
    (⟨inputEmb T U hU ⟨(inputFamily T U hU).label c.1, (inputFamily T U hU).label_lt c.1 c.1.2⟩,
      ConnectedComponents.mk ⟨x, hmem c⟩⟩ :
        ComponentIndex (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F))
    ?_ ?_ ?_ ?_
  · -- the component of `x` is active at `x`
    intro c _
    rw [IdealSheaf.mem_activeFinset]
    exact mem_componentSet_mk _ _ (hmem c)
  · -- injective: same member, both through `x`, hence the same piece
    intro c₁ _ c₂ _ heq
    have hj := congrArg Sigma.fst heq
    have hl : (inputFamily T U hU).label c₁.1 = (inputFamily T U hU).label c₂.1 :=
      congrArg Fin.val ((inputEmb T U hU).injective hj)
    exact Subtype.ext (Fin.ext (hΦ.eq_of_label_eq_of_mem c₁.1.2 c₂.1.2 hl c₁.2 c₂.2))
  · -- surjective: an active component's member is nonempty on `U`, hence embedded, and `x` lies
    -- on one of its pieces
    intro i' hi'
    rw [IdealSheaf.mem_activeFinset] at hi'
    have hx : x ∈ (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F.hyp i'.1 :=
      Subtype.coe_image_subset _ _ hi'
    have hrange : i'.1 ∈ Set.range (inputEmb T U hU) := by
      by_contra hnot
      rw [hΦ.hyp_eq_empty i'.1 hnot] at hx
      exact (Set.mem_empty_iff_false x).mp hx
    obtain ⟨ℓ, hℓ⟩ := hrange
    rw [← hℓ] at hx
    obtain ⟨c, hc, hlc, hxc⟩ := (hΦ.mem_hyp_iff ℓ x).mp hx
    refine ⟨⟨⟨c, hc⟩, hxc⟩, Finset.mem_univ _, ?_⟩
    apply componentIndex_ext_of_mem (mem_componentSet_mk _ _ (hmem _)) hi'
    change inputEmb T U hU ⟨(inputFamily T U hU).label c, _⟩ = i'.1
    rw [← hℓ]
    congr 1
    exact Fin.ext hlc
  · -- the factor: the member's vanishing stalk (component-to-member bridge) to the ambient
    -- exponent (transport along the inclusion)
    intro c _
    have hib := mem_componentSet_mk
      (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).F _ (hmem c)
    rw [componentFactor, IdealSheaf.stalkIdeal_pow,
      componentIdeal_stalkIdeal_eq _ _ _ hib,
      IsClosedSubmanifold.stalkIdeal_idealSheaf_eq_vanishingStalk]
    congr 1
    have hxc : (M.inclusion U) x ∈ componentSet T.F (meetingPiece T U hU c.1) := by
      have h := c.2
      rw [inputFamily_piece T U hU c.1] at h
      exact h
    rw [inputFamily_a T U hU c.1]
    exact (componentExponent_comap (M.inclusion U) (isLocalDiffeomorph_inclusion M U) T.F T.isSnc
      T.I (meetingPiece T U hU c.1) _ hib hxc (inputEmb_label T U hU c.1)).symm

end Hironaka.Manifold.BMO
