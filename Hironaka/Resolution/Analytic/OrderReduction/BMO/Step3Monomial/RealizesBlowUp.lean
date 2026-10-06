/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Basic
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.BlowUpPieces
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Center
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step3Monomial.Kernel
import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The piece family after a blow-up realises the transformed boundary

The piece family after the blow-up of a centre realises the total transform of the boundary family,
that is, the strict transforms of the members in their old order followed by the exceptional divisor
`π⁻¹(Z)` as the last member ([Kol07, Definition 65]), through the label embedding extended by the
exceptional member (`extendEmb`). An old member's strict transform is the union of the strict
transforms of its pieces (the strict transform of a finite union is the union of the strict
transforms), the exceptional divisor is the union of the new pieces (one per face of the centre,
the preimages of the loci), the members off the range are empty, and pieces with the same label
stay pairwise disjoint: strict transforms of disjoint pieces lie over disjoint pieces, and the new
pieces lie over the disjoint loci of the faces of the centre.
-/

public section

open Set Topology Hironaka.Monomial
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

/-- The strict transform of a finite union is the union of the strict transforms. -/
theorem strictTransformSet_biUnion {M : Type u} {M' : Type u}
    [TopologicalSpace M'] (π : M' → M) (Y : Set M) {ι : Type*} (s : Finset ι) (H : ι → Set M) :
    strictTransformSet π Y (⋃ i ∈ s, H i) = ⋃ i ∈ s, strictTransformSet π Y (H i) := by
  unfold strictTransformSet
  rw [← Finset.closure_biUnion]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_iUnion, exists_prop]
  tauto

/-- Strict transforms of disjoint closed sets are disjoint. -/
theorem disjoint_strictTransformSet_of_disjoint {M : Type u} [TopologicalSpace M] {M' : Type u}
    [TopologicalSpace M'] {π : M' → M} (hπ : Continuous π) (Y : Set M) {H₁ H₂ : Set M}
    (h₁ : IsClosed H₁) (h₂ : IsClosed H₂) (hd : Disjoint H₁ H₂) :
    Disjoint (strictTransformSet π Y H₁) (strictTransformSet π Y H₂) :=
  Set.disjoint_of_subset (strictTransform_subset_preimage hπ h₁)
    (strictTransform_subset_preimage hπ h₂) (hd.preimage π)

namespace BMO.PieceFamily

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {N : AnalyticManifold.{u} 𝕜 E} {Φ : PieceFamily N}
  {F : HypersurfaceFamily N} {e : Fin Φ.nextLabel ↪o F.ι} {m : ℕ} {hV : Φ.IsValid n m}
  {S : Finset (Finset ℕ)}

/-- The pieces of the transported family with an old label are the old pieces with that label. -/
theorem filter_label_blowUpPieces_of_lt {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r)
    {l : ℕ} (hl : l < Φ.nextLabel) :
    (Finset.range (Φ.blowUpPieces S m hZ).nextComp).filter
        (fun c => (Φ.blowUpPieces S m hZ).label c = l) =
      (Finset.range Φ.nextComp).filter (fun c => Φ.label c = l) := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_range, Φ.blowUpPieces_nextComp]
  constructor
  · rintro ⟨hc, hcl⟩
    by_cases h : c < Φ.nextComp
    · rw [Φ.blowUpPieces_label_of_lt S m hZ h] at hcl
      exact ⟨h, hcl⟩
    · rw [Φ.blowUpPieces_label_of_le S m hZ (not_lt.mp h)] at hcl
      exact absurd hcl (ne_of_gt hl)
  · rintro ⟨hc, hcl⟩
    exact ⟨hc.trans_le (Nat.le_add_right _ _), (Φ.blowUpPieces_label_of_lt S m hZ hc).trans hcl⟩

/-- The pieces with the new label are exactly the new pieces. -/
theorem mem_filter_label_blowUpPieces_nextLabel {r : ℕ}
    (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) {c : ℕ} :
    c ∈ (Finset.range (Φ.blowUpPieces S m hZ).nextComp).filter
        (fun c => (Φ.blowUpPieces S m hZ).label c = Φ.nextLabel) ↔
      Φ.nextComp ≤ c ∧ c < Φ.nextComp + S.card := by
  simp only [Finset.mem_filter, Finset.mem_range, Φ.blowUpPieces_nextComp]
  constructor
  · rintro ⟨hc, hcl⟩
    refine ⟨?_, hc⟩
    by_contra h
    rw [Φ.blowUpPieces_label_of_lt S m hZ (not_le.mp h)] at hcl
    exact absurd hcl (ne_of_lt (Φ.label_lt c (not_le.mp h)))
  · rintro ⟨hc, hc'⟩
    exact ⟨hc', Φ.blowUpPieces_label_of_le S m hZ hc⟩

/-- The union of the new pieces is the exceptional divisor. -/
theorem biUnion_piece_blowUpPieces_of_le {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) :
    ⋃ c ∈ (Finset.range (Φ.blowUpPieces S m hZ).nextComp).filter
        (fun c => (Φ.blowUpPieces S m hZ).label c = Φ.nextLabel),
      (Φ.blowUpPieces S m hZ).piece c = (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨c, hc, hp⟩
    obtain ⟨hc₁, -⟩ := (Φ.mem_filter_label_blowUpPieces_nextLabel hZ).mp hc
    obtain ⟨P, hP, -, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le hZ hc₁).mp hp
    exact Φ.faceSet_subset_centerOf hP hxP
  · intro hp
    obtain ⟨P, hP, hxP⟩ := Φ.mem_centerOf.mp hp
    refine ⟨Φ.newComp S P, (Φ.mem_filter_label_blowUpPieces_nextLabel hZ).mpr
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (MonomialState.rank_lt_card hP) _⟩, ?_⟩
    rw [Φ.blowUpPieces_piece_newComp S m hZ hP]
    exact hxP

/-- The family after the blow-up of a centre realises the total transform of the boundary family
through the extended label embedding ([Kol07, Definition 65]: the strict transforms of the members
in the old order, the exceptional divisor last). -/
theorem Realizes.realizes_blowUpPieces (hΦ : Φ.Realizes F e) (hS : (Φ.toState n m hV).IsCenter S)
    {r : ℕ} (hZ : IsClosedSubmanifold ψ₀ (Φ.centerOf S) r) :
    (Φ.blowUpPieces S m hZ).Realizes
      (F.totalTransform (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)) (extendEmb e) := by
  classical
  have hπ : Continuous (Manifold.blowUpπ ψ₀ hZ) := (isBlowUp_blowUpπ ψ₀ hZ).contMDiff.continuous
  refine ⟨fun ℓ => ?_, fun j hj => ?_, fun c c' hc hc' hcc hl => ?_⟩
  · -- the members
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp ℓ.2) with hℓ | hℓ
    · -- an old member: its strict transform is the union of its pieces' strict transforms
      have h1 : (F.totalTransform (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)).hyp (extendEmb e ℓ) =
          strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S) (F.hyp (e ⟨ℓ.1, hℓ⟩)) := by
        rw [extendEmb_apply_of_lt e hℓ]
        rfl
      refine h1.trans ?_
      rw [hΦ.hyp_eq ⟨ℓ.1, hℓ⟩, strictTransformSet_biUnion,
        Φ.filter_label_blowUpPieces_of_lt hZ hℓ]
      refine Set.iUnion₂_congr fun c hc => ?_
      rw [Φ.blowUpPieces_piece_of_lt S m hZ (Finset.mem_range.mp (Finset.mem_filter.mp hc).1)]
    · -- the exceptional member: the union of the new pieces
      have hlast : ℓ = Fin.last _ := Fin.ext hℓ
      subst hlast
      have h1 : (F.totalTransform (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)).hyp
          (extendEmb e (Fin.last _)) = (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S := by
        rw [extendEmb_last]
        rfl
      refine h1.trans ?_
      change (Manifold.blowUpπ ψ₀ hZ) ⁻¹' Φ.centerOf S =
        ⋃ c ∈ (Finset.range (Φ.blowUpPieces S m hZ).nextComp).filter
          (fun c => (Φ.blowUpPieces S m hZ).label c = Φ.nextLabel), (Φ.blowUpPieces S m hZ).piece c
      exact (Φ.biUnion_piece_blowUpPieces_of_le (m := m) hZ).symm
  · -- the members off the range are empty
    have hj' : (toLex (ofLex (j : F.ι ⊕ₗ PUnit.{u + 1})) :
        (F.totalTransform (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S)).ι) = j := toLex_ofLex _
    rcases hs : ofLex (j : F.ι ⊕ₗ PUnit.{u + 1}) with j₀ | u
    · rw [hs] at hj'
      have hj₀ : j₀ ∉ Set.range e := by
        rintro ⟨ℓ, hℓ⟩
        apply hj
        exact ⟨ℓ.castSucc, (extendEmb_castSucc e ℓ).trans
          ((congrArg (fun a => toLex (Sum.inl a)) hℓ).trans hj')⟩
      subst hj'
      change strictTransformSet (Manifold.blowUpπ ψ₀ hZ) (Φ.centerOf S) (F.hyp j₀) = ∅
      rw [hΦ.hyp_eq_empty j₀ hj₀, strictTransformSet_empty]
    · rw [hs] at hj'
      exact absurd ⟨Fin.last _, (extendEmb_last e).trans hj'⟩ hj
  · -- pieces of one label are disjoint
    rw [Φ.blowUpPieces_nextComp] at hc hc'
    by_cases h : c < Φ.nextComp
    · by_cases h' : c' < Φ.nextComp
      · rw [Φ.blowUpPieces_label_of_lt S m hZ h, Φ.blowUpPieces_label_of_lt S m hZ h'] at hl
        rw [Φ.blowUpPieces_piece_of_lt S m hZ h, Φ.blowUpPieces_piece_of_lt S m hZ h']
        exact disjoint_strictTransformSet_of_disjoint hπ _ (Φ.isClosed_piece c)
          (Φ.isClosed_piece c') (hΦ.disjoint c c' h h' hcc hl)
      · rw [Φ.blowUpPieces_label_of_lt S m hZ h, Φ.blowUpPieces_label_of_le S m hZ (not_lt.mp h')]
          at hl
        exact absurd hl (ne_of_lt (Φ.label_lt c h))
    · by_cases h' : c' < Φ.nextComp
      · rw [Φ.blowUpPieces_label_of_le S m hZ (not_lt.mp h), Φ.blowUpPieces_label_of_lt S m hZ h']
          at hl
        exact absurd hl.symm (ne_of_lt (Φ.label_lt c' h'))
      · -- two new pieces: over the disjoint loci of two faces of the centre
        rw [Set.disjoint_left]
        intro p hp hp'
        obtain ⟨P, hP, hPc, hxP⟩ := (Φ.mem_blowUpPieces_piece_of_le hZ (not_lt.mp h)).mp hp
        obtain ⟨Q, hQ, hQc, hxQ⟩ := (Φ.mem_blowUpPieces_piece_of_le hZ (not_lt.mp h')).mp hp'
        have hPQ : P = Q := hΦ.eq_of_mem_faceSet_of_isCenter hS hP hQ hxP hxQ
        exact hcc (hPc.symm.trans (hPQ ▸ hQc))

end BMO.PieceFamily

end Hironaka.Manifold
