/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.IdealSheaf.Deriv
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The derivative ideals along a blow-up sequence of order `≥ m`

For a smooth blow-up sequence of order `≥ m` starting with `(X, I, m)` and `j ≤ m`, the marked
transforms `J_i` of `(D^j(I), m − j)` along the same sequence satisfy `J_i ⊆ D^j(I_i)` for every
`i`, and the sequence is of order `≥ m − j` starting with `(X, D^j(I), m − j)`
[Kol07, Corollary 77]. Kollár's argument: `J_i = (Π_i)_*^{-1}(D^j I, m − j) ⊂ D^j (Π_i)_*^{-1}(I, m)
= D^j(I_i)`, the containment being his Theorem 76 for the composite, and `ord_{Z_i} I_i ≥ m` gives
`ord_{Z_i} D^j(I_i) ≥ m − j` since each derivative lowers the order by at most one. The proof here
is an induction on the stage: at each step Theorem 76 for one blowing-up
(`markedTransform_iteratedDeriv_le`) and the monotonicity of the marked transform in the ideal
sheaf (`birationalTransform_mono`; both marked transforms are defined because the order along the
centre is antitone in the ideal sheaf, `le_ordAlongIdeal_of_le`, and `ord_{Z_i} D^j(I_i) ≥ m − j`
by `le_ordAlongIdeal_iteratedDeriv`). The containment is also proved in a prefix-bounded form
(`markedTransformSeq_iteratedDeriv_le_of_forall_lt`) that needs the order clause only at the
steps before the stage considered.

Also here: the ideal sheaf of a closed submanifold does not depend on the chart `ψ : E ≃ 𝕜ⁿ`
carried by the submanifold predicate (`IsClosedSubmanifold.idealSheaf_eq_of_chart`), needed
because a sequence carries one chosen chart per step.

This is the step by which the maximal-contact theorem [Kol07, Theorem 80] passes from a sequence
of order `m` for `I` to a sequence of order `≥ 1` for `D^{m−1}(I)`.
-/

public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

section Generic

variable {X : TopCat} {𝒪 : TopCat.Sheaf CommRingCat X}

/-- The order along a centre is antitone in the ideal sheaf: `J ⊆ K` gives
`ord_D K ≤ ord_D J` at every point (in the form the marked transforms use). -/
theorem IdealSheaf.le_ordAlongIdeal_of_le {D J K : IdealSheaf 𝒪} (hJK : J ≤ K) {a : X} {p : ℕ}
    (hp : (p : ℕ∞) ≤ IdealSheaf.ordAlongIdeal D K a) :
    (p : ℕ∞) ≤ IdealSheaf.ordAlongIdeal D J a := by
  rw [IdealSheaf.le_ordAlongIdeal_iff] at hp ⊢
  exact (IdealSheaf.le_def.mp hJK a).trans hp

end Generic

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M] {Y : Set M} {c : ℕ}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The ideal sheaf of a closed submanifold does not depend on the chart `ψ` of the submanifold
predicate: at a point of `Y` a germ lies in it iff its section vanishes on `Y` nearby
(`germ_mem_stalkIdeal_idealSheaf_iff`), and off `Y` it is the unit ideal. The same-set case of
`IsClosedSubmanifold.idealSheaf_congr` (module `BlowUp.Transform.IdealSheafCongr`), which carries
the proof. -/
theorem IsClosedSubmanifold.idealSheaf_eq_of_chart {n' : ℕ} {ψ' : E ≃L[𝕜] (Fin n' → 𝕜)}
    (hY : IsClosedSubmanifold ψ Y c) (hY' : IsClosedSubmanifold ψ' Y c) :
    hY.idealSheaf = hY'.idealSheaf :=
  IsClosedSubmanifold.idealSheaf_congr hY hY' rfl

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(𝕜, E) ω M']
  [T2Space M'] [SecondCountableTopology M'] {π : M' → M}

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- The marked transform is monotone in the ideal sheaf (colon ideals are monotone in the
numerator), for a mark that is legitimate for the larger ideal sheaf (hence for the smaller one
too, the order along the centre being antitone). -/
theorem birationalTransform_mono (hY : IsClosedSubmanifold ψ Y c) (h : IsBlowUp ψ Y c π)
    {J K : IdealSheaf (structureSheaf 𝕜 E M)} (hJK : J ≤ K) {k : ℕ}
    (hk : ∀ a ∈ Y, (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf K a) :
    (MarkedIdealSheaf.birationalTransform hY h ⟨J, k⟩).I ≤
      (MarkedIdealSheaf.birationalTransform hY h ⟨K, k⟩).I := by
  have hkJ : ∀ a ∈ Y, (k : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hY.idealSheaf J a := fun a ha =>
    IdealSheaf.le_ordAlongIdeal_of_le hJK (hk a ha)
  rw [IdealSheaf.le_def]
  intro a'
  have h1 := isDivExceptional_birationalTransform hY h ⟨J, k⟩ hkJ a'
  have h2 := isDivExceptional_birationalTransform hY h ⟨K, k⟩ hk a'
  dsimp only at h1 h2
  rw [h1, h2]
  simp only [IdealSheaf.stalkIdeal_pullback]
  exact Submodule.colon_mono (Ideal.map_mono (IdealSheaf.le_def.mp hJK (π a'))) subset_rfl

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M}
  {I E₀ : IdealSheaf M} {m j : ℕ}

/-- The order clause of [Kol07, Corollary 77] at one stage: where `J_i ⊆ D^j(I_i)` holds and
`ord_{Z_i} I_i ≥ m` (the order clause (4′) at the step `i` alone), `ord_{Z_i} J_i ≥ m − j`, since
`ord_{Z_i} D^j(I_i) ≥ m − j`. -/
theorem le_ordAlong_iteratedDeriv_of_le_of_le_ordAlong (hj : j ≤ m) (i : Fin S.length)
    (h4 : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i)
      (S.markedTransformSeq I m i.castSucc) a)
    (hle : S.markedTransformSeq (I.iteratedDeriv j) (m - j) i.castSucc ≤
      (S.markedTransformSeq I m i.castSucc).iteratedDeriv j) :
    ∀ a ∈ (S.center i).support, ((m - j : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i)
      (S.markedTransformSeq (I.iteratedDeriv j) (m - j) i.castSucc) a := by
  intro a ha
  refine IdealSheaf.le_ordAlongIdeal_of_le hle ?_
  have h1 := le_ordAlongIdeal_iteratedDeriv (S.isClosedSubmanifold_center i)
    (S.markedTransformSeq I m i.castSucc) ha hj
    (by rw [S.idealSheaf_center i]; exact h4 a ha)
  rwa [S.idealSheaf_center i] at h1

/-- The order clause of [Kol07, Corollary 77] at one stage, for a sequence of order `≥ m`
(`le_ordAlong_iteratedDeriv_of_le_of_le_ordAlong` with the order clause (4′) of `h`). -/
theorem IsOfOrderGe.le_ordAlong_iteratedDeriv_of_le (h : S.IsOfOrderGe I m E₀) (hj : j ≤ m)
    (i : Fin S.length)
    (hle : S.markedTransformSeq (I.iteratedDeriv j) (m - j) i.castSucc ≤
      (S.markedTransformSeq I m i.castSucc).iteratedDeriv j) :
    ∀ a ∈ (S.center i).support, ((m - j : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i)
      (S.markedTransformSeq (I.iteratedDeriv j) (m - j) i.castSucc) a :=
  le_ordAlong_iteratedDeriv_of_le_of_le_ordAlong hj i (fun _ ha => h.le_ordAlong i ha) hle

/-- The containment `J_i ⊂ D^j(I_i)` of [Kol07, Corollary 77] in a prefix-bounded form: for
`j ≤ m` and a stage `i`, if the marked transforms of `(I, m)` have order `≥ m` along the centres
of the steps before `i` (the order clause (4′) of [Kol07, Definition 66] on the prefix, with no
normal-crossings clause), the marked transform of `(D^j(I), m − j)` at stage `i` lies in the
`j`-th derivative ideal sheaf of the marked transform of `(I, m)`. Induction on the stage with
Kollár's Theorem 76 for one blowing-up and the monotonicity of the marked transform; the step
`i` uses (4′) at step `i` only. -/
theorem markedTransformSeq_iteratedDeriv_le_of_forall_lt (hj : j ≤ m) (i : Fin (S.length + 1))
    (h4 : ∀ i' : Fin S.length, i'.1 < i.1 → ∀ a ∈ (S.center i').support,
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.center i') (S.markedTransformSeq I m i'.castSucc) a) :
    S.markedTransformSeq (I.iteratedDeriv j) (m - j) i ≤
      (S.markedTransformSeq I m i).iteratedDeriv j := by
  induction i using Fin.induction with
  | zero => exact le_rfl
  | succ i ih =>
    rw [markedTransformSeq_succ, markedTransformSeq_succ]
    have hmI : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq I m i.castSucc) a := by
      intro a ha
      rw [S.idealSheaf_center i]
      exact h4 i (by rw [Fin.val_succ]; exact Nat.lt_succ_self _) a ha
    have hmD : ∀ a ∈ (S.center i).support, ((m - j : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf
        ((S.markedTransformSeq I m i.castSucc).iteratedDeriv j) a := fun a ha =>
      le_ordAlongIdeal_iteratedDeriv (S.isClosedSubmanifold_center i) _ ha hj (hmI a ha)
    exact (birationalTransform_mono (S.isClosedSubmanifold_center i) (S.isBlowUp_map i)
      (ih fun i' hi' => h4 i' (by rw [Fin.val_succ]; rw [Fin.val_castSucc] at hi'; omega))
      hmD).trans (markedTransform_iteratedDeriv_le (S.isClosedSubmanifold_center i)
        (S.isBlowUp_map i) _ hmI hj)

/-- The containment `J_i ⊂ D^j(I_i)` for every `i` of [Kol07, Corollary 77]: along a smooth
blow-up sequence of order `≥ m` starting with `(M, I, m, E₀)` and for `j ≤ m`, the marked
transforms of `(D^j(I), m − j)` lie in the `j`-th derivative ideal sheaves of the marked
transforms of `(I, m)`, at every stage (`markedTransformSeq_iteratedDeriv_le_of_forall_lt` with
the order clause (4′) of `h`). -/
theorem IsOfOrderGe.markedTransformSeq_iteratedDeriv_le (h : S.IsOfOrderGe I m E₀) (hj : j ≤ m)
    (i : Fin (S.length + 1)) :
    S.markedTransformSeq (I.iteratedDeriv j) (m - j) i ≤
      (S.markedTransformSeq I m i).iteratedDeriv j :=
  markedTransformSeq_iteratedDeriv_le_of_forall_lt hj i fun i' _ _ ha => h.le_ordAlong i' ha

/-- A smooth blow-up sequence of order `≥ m` starting with `(M, I, m, E₀)` is a smooth blow-up
sequence of order `≥ m − j` starting with `(M, D^j(I), m − j, E₀)` [Kol07, Corollary 77]. -/
theorem IsOfOrderGe.isOfOrderGe_iteratedDeriv (h : S.IsOfOrderGe I m E₀) (hj : j ≤ m) :
    S.IsOfOrderGe (I.iteratedDeriv j) (m - j) E₀ := fun i =>
  ⟨(h i).1,
    h.le_ordAlong_iteratedDeriv_of_le hj i (h.markedTransformSeq_iteratedDeriv_le hj i.castSucc)⟩

end AnalyticManifold.FiniteSuccession

end
