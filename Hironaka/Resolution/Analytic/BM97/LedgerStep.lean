/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.BM97.Ledger
public import Hironaka.Manifold.Snc.Basic
import Hironaka.Manifold.BlowUp.Divisor
import Hironaka.Manifold.Jacobian.BlowUp
import Hironaka.Manifold.Jacobian.Comp
import Hironaka.Manifold.Jacobian.Units
import Hironaka.Manifold.Snc.TotalTransform
import Hironaka.Resolution.Analytic.BM97.LedgerBlowUp
import Hironaka.Resolution.Analytic.IdealSheaf.VanishingPreimage
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Principalization.MonomialStep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The step of the Jacobian ledger along one blow-up

From a Jacobian ledger for `f : M' → M` relative to a simple normal crossings family `F` with
exceptional members `exc`, a centre `Z ⊆ M'` having simple normal crossings with `F`, and the
blowing-up `π : M'' → M'` of `Z`, a ledger for `f ∘ π` relative to the total transform
`F.totalTransform π Z`, the exceptional members being the strict transforms of `exc` together with
the new exceptional divisor `π⁻¹(Z)` (`JacobianLedger.step`; the condition on the centres is
Kollár's "the centers `Z_i` have simple normal crossings with `E`" [Kol07, Definition 25]).

The proof is the chain rule at the stalks (`jacobianStalk_comp` of
`Hironaka/Manifold/Jacobian/Comp.lean`:
`jacobianStalk (f ∘ π) p = (jacobianStalk f (π p)).map (germMap π p) · jacobianStalk π p`) with the
two factors read at `p`. **On the centre** (`π p ∈ Z`): the simple normal crossings hypothesis
gives an adapted chart of `Z` at `π p` that is a simple normal crossings chart of `F`,
`IsBlowUp.cover` a blow-up chart through `p`; `germMap_prod_vanishingStalk_pow_totalTransform`
(`Hironaka/Resolution/Analytic/BM97/LedgerBlowUp.lean`) transports the old monomial to the strict
transforms with the exceptional exponent `∑ e_j` over the members through the block, and
`jacobianStalk_blowUp` reads `jacobianStalk π p = (u_{σ i})^{c-1}`, the vanishing stalk of `π⁻¹(Z)`
at `p` to the power `c − 1` (`IsClosedSubmanifold.vanishingStalk_eq_span_coord` on the adapted
chart `IsBlowUpChart.isAdaptedChart_preimage`). **Off the centre**: `π` is a local analytic
isomorphism at `p` (`IsBlowUp.isLocalDiffeomorphOn_compl`), so `jacobianStalk π p = ⊤`
(`jacobianStalk_eq_top_of_isLocalDiffeomorphAt`) and the strict transforms coincide with the
preimages near `p` (`HypersurfaceFamily.mem_strictTransform_iff_of_notMem`);
`vanishingStalk_preimage_of_isLocalDiffeomorphAt'` carries each member's vanishing stalk at `π p`
to the strict transform's at `p`. In both cases the members whose strict transform misses `p`
contribute the unit ideal (`vanishingStalk_eq_top_of_notMem`) and are dropped from the index set
(`Finset.prod_filter_of_ne`), so the ledger's clause "`x ∈ F.hyp j` for `j ∈ s`" holds; the
exponent of a strict transform is the member's, that of the exceptional divisor is the block sum
plus `c − 1`; positivity of an exponent puts the member in `exc` or it is the exceptional divisor.
This is the inductive step of `Hironaka/Resolution/Analytic/BM97/LedgerSequence.lean`; the
one-blow-up computation it rests on is Bierstone–Milman's `f'(w', z') = (z'_1)^{-d} f(…)` in a
blow-up chart [BM97, §3, "The strict transform"].
-/

public section

open Set TopologicalSpace Filter Topology
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

namespace Hironaka.Manifold

open _root_.Manifold

universe u

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜))

section

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(𝕜, E) ω M]
  {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  {M'' : Type u} [TopologicalSpace M''] [ChartedSpace E M''] [IsManifold 𝓘(𝕜, E) ω M'']
  [T2Space M''] [SecondCountableTopology M'']

open scoped Classical in
/-- **The step of the Jacobian ledger along one blow-up** ([Kol07, Definition 25]): a ledger for
`f` relative to `(F, exc)`, a centre `Z` having simple normal crossings with `F` and the blowing-up
`π` of `Z` give a ledger for `f ∘ π` relative to `F.totalTransform π Z`, the exceptional members
being the strict transforms of `exc` and the new exceptional divisor. Chain rule
(`jacobianStalk_comp`), then on the centre `germMap_prod_vanishingStalk_pow_totalTransform` at a
blow-up chart through `p` with `jacobianStalk_blowUp`, off it the local-isomorphism transport
(`vanishingStalk_preimage_of_isLocalDiffeomorphAt'`) with `jacobianStalk π p = ⊤`. -/
theorem JacobianLedger.step {f : M' → M} (hf : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω f)
    {F : HypersurfaceFamily M'} (hF : F.IsSnc ψ) {exc : Set F.ι} (hL : JacobianLedger ψ f F exc)
    {Z : Set M'} {c : ℕ} (hZ : IsClosedSubmanifold ψ Z c) (hsnc : F.HasSncWith ψ Z c)
    {π : M'' → M'} (h : IsBlowUp ψ Z c π) :
    JacobianLedger ψ (f ∘ π) (F.totalTransform π Z)
      ((fun j : F.ι => toLex (Sum.inl j)) '' exc ∪ {toLex (Sum.inr PUnit.unit)}) := by
  have hFT : (F.totalTransform π Z).IsSnc ψ :=
    HypersurfaceFamily.isSnc_totalTransform hZ h hF hsnc
  intro p
  refine ⟨hFT.exists_isSncChartAt p, ?_⟩
  obtain ⟨-, s, e, hs, hpos, hJ⟩ := hL (π p)
  have hchain := jacobianStalk_comp h.contMDiff hf p
  have hclosedT : ∀ k, IsClosed ((F.totalTransform π Z).hyp k) := fun k => (hFT.1 k).isClosed
  -- the members through `π p` whose strict transforms pass through `p`
  set sT : Finset F.ι :=
    s.filter (fun j => p ∈ (F.totalTransform π Z).hyp (toLex (Sum.inl j))) with hsT
  have hprodT : ∀ e' : F.ι → ℕ,
      ∏ j ∈ s, (vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Z).hyp (toLex (Sum.inl j))) p) ^ e' j =
        ∏ j ∈ sT, (vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Z).hyp (toLex (Sum.inl j))) p) ^ e' j := by
    intro e'
    rw [hsT]
    refine (Finset.prod_filter_of_ne fun j _ hne => ?_).symm
    by_contra hj
    exact hne (by
      rw [vanishingStalk_eq_top_of_notMem (hclosedT _) hj, Ideal.top_pow, Ideal.one_eq_top])
  have hinj : ∀ x ∈ sT, ∀ y ∈ sT,
      toLex (Sum.inl x : F.ι ⊕ PUnit) = toLex (Sum.inl y : F.ι ⊕ PUnit) → x = y :=
    fun x _ y _ hxy => Sum.inl_injective (toLex_inj.mp hxy)
  have hmemT : ∀ j ∈ sT, p ∈ (F.totalTransform π Z).hyp (toLex (Sum.inl j)) ∧ j ∈ s := by
    intro j hj
    rw [hsT, Finset.mem_filter] at hj
    exact ⟨hj.2, hj.1⟩
  by_cases hpZ : π p ∈ Z
  · -- on the centre: the blow-up chart from `hsnc` and `h.cover`
    obtain ⟨φ, σ, cidx, hφ, hc⟩ := hsnc (π p) hpZ
    obtain ⟨i, Φ, hΦ, hpΦ⟩ := h.cover φ σ hφ p hc.mem_source
    have hb := germMap_prod_vanishingStalk_pow_totalTransform ψ hZ h hF hφ hc hΦ hpΦ s e hs
    have hexc : vanishingStalk (𝕜 := 𝕜) (E := E)
        ((F.totalTransform π Z).hyp (toLex (Sum.inr PUnit.unit))) p =
          Ideal.span {coord E ψ Φ hΦ.mem_maximalAtlas hpΦ (σ i)} :=
      (h.isClosedSubmanifold_preimage hZ).vanishingStalk_eq_span_coord
        (hΦ.isAdaptedChart_preimage hφ) hpΦ
    have hJπ : jacobianStalk (𝕜 := 𝕜) (E := E) π p =
        (vanishingStalk (𝕜 := 𝕜) (E := E)
          ((F.totalTransform π Z).hyp (toLex (Sum.inr PUnit.unit))) p) ^ (c - 1) := by
      rw [jacobianStalk_blowUp h hφ hΦ hpΦ, hexc, Ideal.span_singleton_pow]
    let e' : (F.totalTransform π Z).ι → ℕ := fun k =>
      Sum.elim (fun j => e j)
        (fun _ =>
          (∑ j ∈ s.attach, if ∃ k, σ k = cidx ⟨j.1, hs j.1 j.2⟩ then e j.1 else 0) + (c - 1))
        (ofLex k)
    have hdisj : Disjoint (sT.image fun j : F.ι => toLex (Sum.inl j))
        {toLex (Sum.inr PUnit.unit)} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_image]
      rintro ⟨j, -, hj⟩
      exact Sum.inl_ne_inr (toLex_inj.mp hj)
    refine ⟨sT.image (fun j : F.ι => toLex (Sum.inl j)) ∪ {toLex (Sum.inr PUnit.unit)}, e',
      ?_, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.mp hk with hk | hk
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        exact (hmemT j hj).1
      · obtain rfl := Finset.mem_singleton.mp hk
        exact hpZ
    · intro k hk hpos'
      rcases Finset.mem_union.mp hk with hk | hk
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
        exact Or.inl ⟨j, hpos j (hmemT j hj).2 hpos', rfl⟩
      · obtain rfl := Finset.mem_singleton.mp hk
        exact Or.inr rfl
    · rw [hchain, hJ, hb, hJπ, hprodT e, mul_assoc, ← pow_add]
      refine Eq.trans ?_ (Finset.prod_union hdisj).symm
      rw [Finset.prod_image hinj, Finset.prod_singleton]
      rfl
  · -- off the centre: `π` is a local diffeomorphism at `p` and the strict transforms are preimages
    have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω π p :=
      h.isLocalDiffeomorphOn_compl ⟨p, hpZ⟩
    rw [jacobianStalk_eq_top_of_isLocalDiffeomorphAt h.contMDiff hloc, Ideal.mul_top, hJ,
      Ideal.map_finset_prod] at hchain
    have hU : π ⁻¹' Zᶜ ∈ 𝓝 p :=
      (hZ.isClosed.isOpen_compl.preimage h.contMDiff.continuous).mem_nhds hpZ
    have hfac : ∀ j ∈ s, Ideal.map (germMap π h.contMDiff p)
        ((vanishingStalk (𝕜 := 𝕜) (E := E) (F.hyp j) (π p)) ^ e j) =
          (vanishingStalk (𝕜 := 𝕜) (E := E)
            ((F.totalTransform π Z).hyp (toLex (Sum.inl j))) p) ^ e j := by
      intro j _
      have hset : π ⁻¹' F.hyp j ∩ π ⁻¹' Zᶜ =
          (F.totalTransform π Z).hyp (toLex (Sum.inl j)) ∩ π ⁻¹' Zᶜ := by
        ext q
        constructor
        · rintro ⟨hq, hqZ⟩
          exact ⟨(HypersurfaceFamily.mem_strictTransform_iff_of_notMem h hF hqZ j).mpr hq, hqZ⟩
        · rintro ⟨hq, hqZ⟩
          exact ⟨(HypersurfaceFamily.mem_strictTransform_iff_of_notMem h hF hqZ j).mp hq, hqZ⟩
      rw [Ideal.map_pow, ← vanishingStalk_preimage_of_isLocalDiffeomorphAt' h.contMDiff hloc,
        ← vanishingStalk_inter_of_mem_nhds hU, hset, vanishingStalk_inter_of_mem_nhds hU]
    rw [Finset.prod_congr rfl hfac, hprodT e] at hchain
    let e' : (F.totalTransform π Z).ι → ℕ := fun k => Sum.elim (fun j => e j) (fun _ => 0) (ofLex k)
    refine ⟨sT.image (fun j : F.ι => toLex (Sum.inl j)), e', ?_, ?_, ?_⟩
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact (hmemT j hj).1
    · intro k hk hpos'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      exact Or.inl ⟨j, hpos j (hmemT j hj).2 hpos', rfl⟩
    · rw [hchain]
      refine Eq.trans ?_ (Finset.prod_image hinj).symm
      rfl

end

end Hironaka.Manifold
