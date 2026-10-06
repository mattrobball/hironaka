/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Restrict.StrictTransformSeq
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The maximal-contact theorem: a smooth hypersurface in `MC(I)` has maximal contact

For an ideal sheaf `I` with `m = max-ord I`, a smooth hypersurface `H` with
`𝒪(−H) ⊆ MC(I) = D^{m−1}(I)` and `I|_H ≠ 0` is a hypersurface of maximal contact
[Kol07, Theorem 80 (1)], in the sense of [Kol07, Definition 78]: the centres of every smooth
blow-up sequence of order `m` lie in the birational transforms of `H`. This module proves that
clause on the whole manifold (`IsOfOrder.centersIn_of_idealSheaf_le_iteratedDeriv`), the static
form of maximal contact that order reduction uses. Kollár's proof: being a hypersurface of
maximal contact is a local question; for a smooth blow-up sequence of order `m` starting with
`(X, I)`, his Corollary 77 at `j = m − 1` gives a smooth blow-up sequence of order
`≥ 1` starting with `(X, J_0 := MC(I), 1)`; with `H_i := (Π_i)_*^{-1} H ⊂ X_i` the birational
transform of `H`, `𝒪_{X_0}(−H_0) ⊂ J_0` and the smoothness of `H_0` give `𝒪_{X_i}(−H_i) ⊂ J_i` for
every `i`; since `ord_{Z_i} I_i ≥ m`, one has `ord_{Z_i} J_i ≥ ord_{Z_i} MC(I_i) ≥ 1` and hence
`ord_{Z_i} H_i ≥ 1`, i.e. `Z_i ⊂ H_i` for every `i`.

The proof here is an induction on the stage keeping the invariant "`H_i` is a smooth hypersurface
and `I_{H_i} ⊆ J_i`": the order clause of Corollary 77 (`isOfOrderGe_iteratedDeriv` at
`j = m − 1`) gives `ord_{Z_i} I_{H_i} ≥ 1`, i.e. `Z_i ⊆ H_i`
(`center_subset_strictTransformSeq_of_le`: at a point of `Z_i` off `H_i` the stalk of `I_{H_i}` is
the unit ideal, which would force the stalk of the centre to be the unit ideal); then `H_{i+1}` is
the strict transform of a smooth
hypersurface through the centre, a smooth hypersurface with
`I_{H_{i+1}} = π_*^{-1}(I_{H_i}, 1) ⊆ π_*^{-1}(J_i, 1) = J_{i+1}` (the ideal sheaf of the strict
transform of a smooth hypersurface through the centre is the marked transform of its ideal sheaf
with the mark `1`, the analytic form of Giraud's lemma [Wlo05, Lemma 2.7.4], and the marked
transform is monotone).

This theorem, with the local construction of maximal contact [Kol07, 51.2], supplies the
hypersurfaces on which order reduction is carried out by induction on the dimension.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}
  {S : FiniteSuccession M} {I E₀ : IdealSheaf M} {m : ℕ} {H : Set M}

omit [FiniteDimensional 𝕜 E] in
/-- One stage of the proof of [Kol07, Theorem 80]: along a sequence of order `≥ 1` for `(J, 1)`, a
smooth hypersurface `H_i` with `I_{H_i} ⊆ J_i` contains the centre `Z_i`
(`ord_{Z_i} I_{H_i} ≥ 1`; at a point of `Z_i` off `H_i` the stalk of `I_{H_i}` is the unit
ideal). -/
theorem center_subset_strictTransformSeq_of_le {J : IdealSheaf M} (hge : S.IsOfOrderGe J 1 E₀)
    (i : Fin S.length) {n' : ℕ} {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)}
    (hHi : IsClosedSubmanifold ψ' (S.strictTransformSeq H i.castSucc) 1)
    (hHle : hHi.idealSheaf ≤ S.markedTransformSeq J 1 i.castSucc) :
    (S.center i).support ⊆ S.strictTransformSeq H i.castSucc := by
  intro a ha
  by_contra haH
  have h1 : ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i) hHi.idealSheaf a :=
    IdealSheaf.le_ordAlongIdeal_of_le hHle (hge.le_ordAlong i ha)
  rw [IdealSheaf.le_ordAlongIdeal_iff, pow_one, hHi.stalkIdeal_idealSheaf_of_notMem haH,
    top_le_iff] at h1
  exact (IdealSheaf.mem_support (S.center i)).mp ha h1

/-- A smooth blow-up sequence of order `m ≥ 1` for `I` is a smooth blow-up sequence of order `≥ 1`
starting with `(X, J_0 := MC(I), 1)`: Kollár's Corollary 77 at `j = m − 1`, the first step of the
proof of [Kol07, Theorem 80]. -/
theorem IsOfOrder.isOfOrderGe_iteratedDeriv_pred (hm : 1 ≤ m) (h : S.IsOfOrder I E₀ m) :
    S.IsOfOrderGe (I.iteratedDeriv (m - 1)) 1 E₀ := by
  have := h.isOfOrderGe.isOfOrderGe_iteratedDeriv (Nat.sub_le m 1)
  rwa [Nat.sub_sub_self hm] at this

/-- The invariant of the induction in the proof of [Kol07, Theorem 80]: along a smooth blow-up
sequence of order `m ≥ 1` starting with `(M, I, E₀)`, for a smooth hypersurface `H` with
`I_H ⊆ D^{m−1}(I)`, every strict transform `H_i` is a smooth hypersurface whose ideal sheaf lies
in the marked transform `J_i` of `(D^{m−1}(I), 1)`. -/
theorem IsOfOrder.exists_isClosedSubmanifold_strictTransformSeq_idealSheaf_le (hm : 1 ≤ m)
    (h : S.IsOfOrder I E₀ m) (hH : IsClosedSubmanifold ψ H 1)
    (hle : hH.idealSheaf ≤ I.iteratedDeriv (m - 1)) (i : Fin (S.length + 1)) :
    ∃ hHi : IsClosedSubmanifold ψ (S.strictTransformSeq H i) 1,
      hHi.idealSheaf ≤ S.markedTransformSeq (I.iteratedDeriv (m - 1)) 1 i := by
  have hge := h.isOfOrderGe_iteratedDeriv_pred hm
  induction i using Fin.induction with
  | zero => exact ⟨hH, hle⟩
  | succ i ih =>
    obtain ⟨hHi, hHle⟩ := ih
    have hZH := center_subset_strictTransformSeq_of_le hge i hHi hHle
    have hHi' : IsClosedSubmanifold (S.chartAt i) (S.strictTransformSeq H i.castSucc) 1 :=
      hHi.congr_chart (S.chartAt i)
    have hnext : IsClosedSubmanifold (S.chartAt i) (S.strictTransformSeq H i.succ) 1 :=
      isClosedSubmanifold_strictTransform (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) hHi'
        hZH
    have e : hnext.idealSheaf = (MarkedIdealSheaf.birationalTransform
        (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) ⟨hHi'.idealSheaf, 1⟩).I :=
      idealSheaf_strictTransform_eq_markedTransform_one (S.isClosedSubmanifold_center i)
        (S.isBlowUp_map i) hHi' hZH
    have h1def : ∀ a ∈ (S.center i).support, ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf
        (S.markedTransformSeq (I.iteratedDeriv (m - 1)) 1 i.castSucc) a := by
      intro a ha
      rw [S.idealSheaf_center i]
      exact hge.le_ordAlong i ha
    refine ⟨hnext.congr_chart ψ, ?_⟩
    rw [markedTransformSeq_succ, (hnext.congr_chart ψ).idealSheaf_eq_of_chart hnext, e,
      hHi'.idealSheaf_eq_of_chart hHi]
    exact birationalTransform_mono (S.isClosedSubmanifold_center i) (S.isBlowUp_map i) hHle h1def

/-- Every strict transform `H_i` of a smooth hypersurface `H` with `I_H ⊆ D^{m−1}(I)` along a
smooth blow-up sequence of order `m ≥ 1` is a smooth hypersurface (the smoothness of `H_0`
carried along the sequence in the proof of [Kol07, Theorem 80]; cf. [Wlo05, Lemma 2.7.4 (2)]). -/
theorem IsOfOrder.isClosedSubmanifold_strictTransformSeq_of_le (hm : 1 ≤ m)
    (h : S.IsOfOrder I E₀ m) (hH : IsClosedSubmanifold ψ H 1)
    (hle : hH.idealSheaf ≤ I.iteratedDeriv (m - 1)) (i : Fin (S.length + 1)) :
    IsClosedSubmanifold ψ (S.strictTransformSeq H i) 1 := by
  obtain ⟨hHi, -⟩ := h.exists_isClosedSubmanifold_strictTransformSeq_idealSheaf_le hm hH hle i
  exact hHi

/-- The ideal sheaf of the strict transform `H_i` lies in the marked transform `J_i` of
`(MC(I), 1)` (Kollár's "`𝒪_{X_i}(−H_i) ⊂ J_i` for every `i`" in the proof of
[Kol07, Theorem 80]). -/
theorem IsOfOrder.idealSheaf_strictTransformSeq_le_markedTransformSeq (hm : 1 ≤ m)
    (h : S.IsOfOrder I E₀ m) (hH : IsClosedSubmanifold ψ H 1)
    (hle : hH.idealSheaf ≤ I.iteratedDeriv (m - 1)) (i : Fin (S.length + 1))
    (hHi : IsClosedSubmanifold ψ (S.strictTransformSeq H i) 1) :
    hHi.idealSheaf ≤ S.markedTransformSeq (I.iteratedDeriv (m - 1)) 1 i := by
  obtain ⟨hHi', hle'⟩ := h.exists_isClosedSubmanifold_strictTransformSeq_idealSheaf_le hm hH hle i
  exact hle'

/-- Every centre lies in the strict transform of `H` at its stage (Kollár's "thus `Z_i ⊂ H_i` for
every `i`" in the proof of [Kol07, Theorem 80]). -/
theorem IsOfOrder.centersIn_of_idealSheaf_le_iteratedDeriv (hm : 1 ≤ m) (h : S.IsOfOrder I E₀ m)
    (hH : IsClosedSubmanifold ψ H 1) (hle : hH.idealSheaf ≤ I.iteratedDeriv (m - 1)) :
    S.CentersIn H := fun i => by
  obtain ⟨hHi, hHle⟩ :=
    h.exists_isClosedSubmanifold_strictTransformSeq_idealSheaf_le hm hH hle i.castSucc
  exact center_subset_strictTransformSeq_of_le (h.isOfOrderGe_iteratedDeriv_pred hm) i hHi hHle

end AnalyticManifold.FiniteSuccession

namespace Manifold

open AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} {H : Set M}
  {m : ℕ}

section PullbackMono

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M] {N : Type u} [TopologicalSpace N]
  [ChartedSpace E N] (φ : N → M) (hφ : ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E) ω φ)

omit [FiniteDimensional 𝕜 E] in
/-- The pullback of ideal sheaves is monotone (stalkwise, `Ideal.map` is monotone): the same-model
case of `IdealSheaf.pullback_le_pullback`. -/
theorem IdealSheaf.pullback_mono {J K : IdealSheaf (structureSheaf 𝕜 E M)} (h : J ≤ K) :
    J.pullback φ hφ ≤ K.pullback φ hφ :=
  IdealSheaf.pullback_le_pullback φ hφ h

end PullbackMono

end Manifold

end
