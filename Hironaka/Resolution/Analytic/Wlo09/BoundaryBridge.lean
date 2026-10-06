/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Functor.ModifiedMarkedFam
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Wlo09.Components
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The empty-boundary bridge and the local Hadamard lemma

Two tools for the clauses of the embedded desingularization about its final strict transform
(`Hironaka/Resolution/Analytic/Wlo09/StrictTransformClauses.lean`,
`Hironaka/Resolution/Analytic/Wlo09/TotalTransformClause.lean`):

* **The empty-boundary bridge.** The shape of the final controlled transform of the modified
  marked resolution (`output_isSmoothSubmanifoldIdeal`, the output of the proof of
  [Wlo09, Theorem 7.4.1]) is stated on the family `totalTransformSeqFrom (T|U).F` grown from the
  restricted boundary, while the clauses of [Wlo09, Theorem 2.0.2] read the exceptional divisors as
  `totalTransformSeq`, grown from the empty family. On `DomBEDan` the boundary has no member, and
  the two families agree up to the order-preserving relabelling of their index types
  (`F.ι ⊕ₗ PUnit ⊕ₗ …` against `PEmpty ⊕ₗ PUnit ⊕ₗ …`); the simple-normal-crossing chart data and
  the predicate `IsSmoothTransversalIdealAt` transport along such a relabelling.
  (`totalTransformSeqFrom_empty` is the literal case `F = empty`, `rfl`.)
* **The local Hadamard lemma.** At a point of a chart of the maximal atlas, the vanishing ideal of
  the zero set of `c` of the chart's coordinates (a set closed in the chart's source, not in `M`) is
  the ideal spanned by those coordinates: the description of the vanishing ideal of a closed
  submanifold (`ker_restrictStalk_eq_vanishingStalk`) read on the open submanifold
  `M.restrict φ.source`, where the zero set is a closed submanifold
  (`IsClosedSubmanifoldOn.restrict`), transported back along the inclusion. Hence the stalk of an
  ideal sheaf that is a coordinate ideal on a chart's source is the vanishing ideal of its
  cosupport there (`vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord`).

Neither tool is in the sources; both are bookkeeping for the comparison of the final controlled
transform with the strict transform of `Y`.
-/

public section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Relabel

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- A relabelling of the index type of a family preserving the members: the data of
`IsSncChartAt` transports. -/
theorem _root_.Manifold.HypersurfaceFamily.IsSncChartAt.of_equiv {F₁ F₂ : HypersurfaceFamily M}
    (e : F₁.ι ≃ F₂.ι)
    (he : ∀ j, F₂.hyp (e j) = F₁.hyp j) {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {j // a ∈ F₁.hyp j} → Fin n} (h : F₁.IsSncChartAt ψ φ a c) :
    F₂.IsSncChartAt ψ φ a fun j => c ⟨e.symm j.1, by
      have := j.2
      rwa [← e.apply_symm_apply j.1, he] at this⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun j x hx => ?_, fun j j' hjj' => ?_⟩
  · have hj : F₂.hyp j.1 = F₁.hyp (e.symm j.1) := by
      rw [← he (e.symm j.1), e.apply_symm_apply]
    rw [hj]
    exact h3 ⟨e.symm j.1, by
      have := j.2
      rwa [← e.apply_symm_apply j.1, he] at this⟩ x hx
  · have := h4 hjj'
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val this))

/-- A relabelling of the index type of a family preserving the members: the predicate
`IsSmoothTransversalIdealAt` transports. -/
theorem _root_.Manifold.HypersurfaceFamily.IsSmoothTransversalIdealAt.of_equiv
    {F₁ F₂ : HypersurfaceFamily M}
    (e : F₁.ι ≃ F₂.ι) (he : ∀ j, F₂.hyp (e j) = F₁.hyp j) {J : Manifold.IdealSheaf
        (structureSheaf 𝕜 E M)}
    {x : M} (h : F₁.IsSmoothTransversalIdealAt ψ J x) : F₂.IsSmoothTransversalIdealAt ψ J x := by
  obtain ⟨c, φ, σ, cidx, hφ, hJ, hne⟩ := h
  exact ⟨c, φ, σ, _, hφ.of_equiv ψ e he, hJ, fun j i => hne _ i⟩

end Relabel

section Bridge

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The stage-indexed form of `exists_equiv_totalTransformSeqFrom_of_isEmpty`, by induction on the
stage: at stage `0` both index types are empty; at a successor the relabelling is the sum of the
previous one with the identity on the new exceptional member. -/
theorem exists_equiv_totalTransformSeqFromAux_of_isEmpty (F : HypersurfaceFamily M)
    [IsEmpty F.ι] :
    ∀ (i : ℕ) (h : i < S.length + 1),
      ∃ e : (S.totalTransformSeqFromAux F i h).ι ≃
          (S.totalTransformSeqFromAux (HypersurfaceFamily.empty M) i h).ι,
        ∀ j, (S.totalTransformSeqFromAux (HypersurfaceFamily.empty M) i h).hyp (e j) =
          (S.totalTransformSeqFromAux F i h).hyp j
  | 0, h =>
    haveI h₁ : IsEmpty (S.totalTransformSeqFromAux F 0 h).ι := inferInstanceAs (IsEmpty F.ι)
    haveI h₂ : IsEmpty (S.totalTransformSeqFromAux (HypersurfaceFamily.empty M) 0 h).ι :=
      ⟨fun j => PEmpty.elim j⟩
    ⟨Equiv.equivOfIsEmpty _ _, fun j => isEmptyElim j⟩
  | i + 1, h => by
    obtain ⟨e, he⟩ :=
      exists_equiv_totalTransformSeqFromAux_of_isEmpty F i (Nat.lt_of_succ_lt h)
    refine ⟨(ofLex.trans (Equiv.sumCongr e (Equiv.refl PUnit.{u + 1}))).trans toLex, ?_⟩
    intro j
    rcases j with j | j
    · exact congrArg (strictTransformSet _ _) (he j)
    · rfl

/-- The exceptional family grown from a family without members is the exceptional family grown
from the empty family, up to a relabelling of the index type preserving the members. -/
theorem exists_equiv_totalTransformSeqFrom_of_isEmpty (F : HypersurfaceFamily M) [IsEmpty F.ι]
    (i : Fin (S.length + 1)) :
    ∃ e : (S.totalTransformSeqFrom F i).ι ≃ (S.totalTransformSeq i).ι,
      ∀ j, (S.totalTransformSeq i).hyp (e j) = (S.totalTransformSeqFrom F i).hyp j :=
  exists_equiv_totalTransformSeqFromAux_of_isEmpty S F i.1 i.2

/-- The empty-boundary bridge for the predicate `IsSmoothTransversalIdealAt`: on a boundary without
members, the predicate on `totalTransformSeqFrom F i` is the predicate on `totalTransformSeq i`. -/
theorem isSmoothTransversalIdealAt_totalTransformSeqFrom_iff_of_isEmpty (F : HypersurfaceFamily M)
    [IsEmpty F.ι] (i : Fin (S.length + 1)) (J : Manifold.IdealSheaf (structureSheaf 𝕜 E
        (S.stage i)))
    (x : S.stage i) :
    (S.totalTransformSeqFrom F i).IsSmoothTransversalIdealAt ψ J x ↔
      (S.totalTransformSeq i).IsSmoothTransversalIdealAt ψ J x := by
  obtain ⟨e, he⟩ := exists_equiv_totalTransformSeqFrom_of_isEmpty S F i
  exact ⟨fun h => h.of_equiv ψ e he,
    fun h => h.of_equiv ψ e.symm fun j => by rw [← he (e.symm j), e.apply_symm_apply]⟩

end Bridge

section Hadamard

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {M : AnalyticManifold.{u} 𝕜 E}

/-- The local Hadamard lemma (the vanishing ideal of a closed submanifold, on the open submanifold
of a chart's source): at a point `x` of a chart `φ` of the maximal atlas where the coordinates
`z_σ` vanish, the vanishing ideal of the zero set `{z_σ = 0} ∩ φ.source` is spanned by those
coordinates. -/
theorem vanishingStalk_zeroSet_eq_span_coord {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M) {x : M} (hx : x ∈ φ.source) {c : ℕ}
    (σ : Fin c ↪ Fin n) (h0 : ∀ i, ψ (φ x) (σ i) = 0) :
    vanishingStalk (𝕜 := 𝕜) (E := E) (φ.source ∩ {y | ∀ i, ψ (φ y) (σ i) = 0}) x =
      Ideal.span (Set.range fun i => coord E ψ φ hφ hx (σ i)) := by
  set Z := φ.source ∩ {y | ∀ i, ψ (φ y) (σ i) = 0} with hZ
  let U : Opens M := ⟨φ.source, φ.open_source⟩
  let p : M.restrict U := ⟨x, hx⟩
  set g := (inclusionPartialDiffeomorph M U p).symm with hg
  set f := germMap ⇑(M.inclusion U) (M.inclusion U).contMDiff p with hf
  have hadapt : IsAdaptedChart ψ Z φ σ := isAdaptedChart_zeroSet' hφ σ
  have hZ' : IsClosedSubmanifold ψ (⇑(M.inclusion U) ⁻¹' Z : Set (M.restrict U)) c :=
    hadapt.isClosedSubmanifoldOn'.restrict
  have hpZ : p ∈ (⇑(M.inclusion U) ⁻¹' Z : Set (M.restrict U)) := ⟨hx, h0⟩
  have hφ' : IsAdaptedChart ψ (⇑(M.inclusion U) ⁻¹' Z) (transportChart g φ) σ :=
    isAdaptedChart_transportChart _ (image_inclusionInv_eq U p Z) hadapt
  have hpφ' : p ∈ (transportChart g φ).source := by
    rw [transportChart_source]
    exact ⟨Set.mem_univ _, hx⟩
  have h1 : vanishingStalk (𝕜 := 𝕜) (E := E) (⇑(M.inclusion U) ⁻¹' Z) p =
      Ideal.span (Set.range fun i => coord E ψ (transportChart g φ) hφ'.1 hpφ' (σ i)) := by
    rw [← hZ'.ker_restrictStalk_eq_vanishingStalk hpZ, hZ'.ker_restrictStalk_eq_span hpZ hφ' hpφ']
  have h2 : vanishingStalk (𝕜 := 𝕜) (E := E) (⇑(M.inclusion U) ⁻¹' Z) p =
      Ideal.map f (vanishingStalk (𝕜 := 𝕜) (E := E) Z x) :=
    vanishingStalk_preimage_of_isLocalDiffeomorphAt (M.inclusion U)
      (isLocalDiffeomorph_inclusion M U p) Z
  have h3 : ∀ i, f (coord E ψ φ hφ hx (σ i)) =
      coord E ψ (transportChart g φ) hφ'.1 hpφ' (σ i) := fun i =>
    germMap_coord_eq_coord_transportChart ψ (M.inclusion U) (inclusionPartialDiffeomorph M U p)
      (fun _ _ => rfl) (Set.mem_univ _) φ hφ hx hφ'.1 hpφ' (σ i)
  have hbij : Function.Bijective f :=
    germMap_bijective_of_isLocalDiffeomorphAt ⇑(M.inclusion U) (M.inclusion U).contMDiff
      (isLocalDiffeomorph_inclusion M U p)
  have h4 : Ideal.map f (Ideal.span (Set.range fun i => coord E ψ φ hφ hx (σ i))) =
      Ideal.span (Set.range fun i => coord E ψ (transportChart g φ) hφ'.1 hpφ' (σ i)) := by
    refine (Ideal.map_span f _).trans (congrArg Ideal.span (Set.ext fun y => ?_))
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (h3 i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨coord E ψ φ hφ hx (σ i), ⟨i, rfl⟩, h3 i⟩
  have h5 : Ideal.comap f (Ideal.map f (vanishingStalk (𝕜 := 𝕜) (E := E) Z x)) =
      Ideal.comap f (Ideal.map f (Ideal.span (Set.range fun i => coord E ψ φ hφ hx (σ i)))) := by
    rw [← h2, h1, ← h4]
  have e1 := Ideal.comap_map_of_bijective (f := f) (hf := hbij)
    (I := vanishingStalk (𝕜 := 𝕜) (E := E) Z x)
  have e2 := Ideal.comap_map_of_bijective (f := f) (hf := hbij)
    (I := Ideal.span (Set.range fun i => coord E ψ φ hφ hx (σ i)))
  exact e1.symm.trans (h5.trans e2)

/-- The stalk of an ideal sheaf which is a coordinate ideal on a chart's source equals the vanishing
ideal of its cosupport at every point of the source: the local Hadamard lemma for a smooth
submanifold ideal (the shape the final controlled transform has at a support point). -/
theorem vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord
    (J : Manifold.IdealSheaf (structureSheaf 𝕜 E M)) {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) ω M) {c : ℕ} (σ : Fin c ↪ Fin n)
    (hJ : ∀ a (ha : a ∈ φ.source),
      J.stalkIdeal a = Ideal.span (Set.range fun i => coord E ψ φ hφ ha (σ i)))
    {x : M} (hx : x ∈ φ.source) :
    vanishingStalk (𝕜 := 𝕜) (E := E) J.support x = J.stalkIdeal x := by
  by_cases hxJ : x ∈ J.support
  · have h0 : ∀ i, ψ (φ x) (σ i) = 0 := by
      have hne : J.stalkIdeal x ≠ ⊤ := hxJ
      rw [hJ x hx] at hne
      exact (span_coord_ne_top_iff ψ φ hφ hx σ).mp hne
    have hset : J.support ∩ φ.source = φ.source ∩ {y | ∀ i, ψ (φ y) (σ i) = 0} := by
      ext y
      constructor
      · rintro ⟨hyJ, hys⟩
        refine ⟨hys, ?_⟩
        have hne : J.stalkIdeal y ≠ ⊤ := hyJ
        rw [hJ y hys] at hne
        exact (span_coord_ne_top_iff ψ φ hφ hys σ).mp hne
      · rintro ⟨hys, hy0⟩
        refine ⟨?_, hys⟩
        change J.stalkIdeal y ≠ ⊤
        rw [hJ y hys]
        exact (span_coord_ne_top_iff ψ φ hφ hys σ).mpr hy0
    rw [← vanishingStalk_inter_of_mem_nhds (φ.open_source.mem_nhds hx), hset,
      vanishingStalk_zeroSet_eq_span_coord ψ hφ hx σ h0, hJ x hx]
  · rw [vanishingStalk_eq_top_of_notMem (IdealSheaf.isClosed_support J) hxJ]
    exact (not_not.mp hxJ).symm

end Hadamard

end Hironaka.Manifold
