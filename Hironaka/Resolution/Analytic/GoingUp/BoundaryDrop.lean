/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.Restrict.Bundle
import Hironaka.Manifold.FiniteSuccession.Restrict.CongrChart
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Manifold.Snc.TotalTransform
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Going up: dropping the boundary divisor

A sequence of order `≥ m` for `(I, m)` starting with a simple normal crossing boundary `E` is a
sequence of order `≥ m` for `(I, m)` starting with the empty boundary ([Kol07, Definition 66]
read with the chart-wise normal crossings of [Kol07, Definition 24 (4)]). Kollár's Theorem 84 and
Corollary 85 carry a boundary `E`, while the push-forward theorem of this library
(`pushforward_isOfOrderGe`) is stated with the empty boundary; this module bridges the two.

* `totalTransformSeqFrom F i` (defined in `Hironaka/Manifold/FiniteSuccession/BoundaryFamily.lean`):
  the boundary family at stage `i` starting from the family `F`, Kollár's family of exceptional
  divisors [Kol07, Definition 25] along the sequence from an arbitrary start.
* `isSnc_totalTransformSeqFrom_and_boundarySeq_eq`: from a simple normal crossing start `F`, under
  the normal-crossings clause (3′) for the boundary `red(π⁻¹E_i ∪ π⁻¹Z_i)` starting with
  `E = red F`, the family `F_i` is a simple normal crossing family at every stage and the boundary
  `E_i` is its reduced ideal sheaf, by the induction of
  `Hironaka/Manifold/FiniteSuccession/BoundaryFamily.lean`.
* `exceptionalEmb`, `hyp_exceptionalEmb`: the exceptional divisors `F_i^∅` (the family from the
  empty start) form a sub-family of `F_i^F`.
* `HypersurfaceFamily.HasSncWith.of_subfamily`: simple normal crossings with a family pass to a
  sub-family (the simple-normal-crossing chart with its component coordinates restricted).
* `IsOfOrderGe.unit_of_idealSheaf`: dropping the boundary. Clause (3′) for the boundary starting
  with `red F` gives (3′) for the boundary starting with `𝒪`, by a joint induction carrying the
  invariant for the exceptional family; the order clause (4′) does not mention the boundary.

Not in the sources as a separate statement; it is what allows the going-up theorem to be applied
to sequences with a boundary.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Simple normal crossings with a family pass to a sub-family: the simple-normal-crossing chart
of `G` at a point, with its component coordinates restricted along the embedding of the components
of `F`. -/
theorem HypersurfaceFamily.HasSncWith.of_subfamily {F G : HypersurfaceFamily M} (e : F.ι → G.ι)
    (he : Function.Injective e) (hhyp : ∀ k, G.hyp (e k) = F.hyp k) {Y : Set M} {c : ℕ}
    (h : G.HasSncWith ψ Y c) : F.HasSncWith ψ Y c := by
  intro a ha
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := h a ha
  refine ⟨φ, σ, fun j => cidx ⟨e j.1, by rw [hhyp]; exact j.2⟩, hφ, hc.1, hc.2.1, ?_, ?_⟩
  · intro j x hx
    rw [← hhyp j.1]
    exact hc.2.2.1 ⟨e j.1, _⟩ x hx
  · intro j j' hjj'
    exact Subtype.ext (he (congrArg Subtype.val (hc.2.2.2 hjj')))

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- The exceptional divisors (the family from the empty start) as components of the family from
the start `F`, by recursion on the stage. -/
def exceptionalEmb (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1),
      (S.totalTransformSeqAux i h).ι → (S.totalTransformSeqFromAux F i h).ι
  | 0, _ => fun k => k.elim
  | i + 1, h => fun k => toLex (Sum.map (exceptionalEmb F i (Nat.lt_of_succ_lt h)) id (ofLex k))

theorem exceptionalEmb_injective (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1), Function.Injective (S.exceptionalEmb F i h)
  | 0, _ => fun k => k.elim
  | i + 1, h => fun k k' hkk' => by
    have h1 := toLex.injective hkk'
    have h2 := ((exceptionalEmb_injective F i (Nat.lt_of_succ_lt h)).sumMap
      Function.injective_id) h1
    exact ofLex.injective h2

theorem hyp_exceptionalEmb (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1) (k : (S.totalTransformSeqAux i h).ι),
      (S.totalTransformSeqFromAux F i h).hyp (S.exceptionalEmb F i h k) =
        (S.totalTransformSeqAux i h).hyp k
  | 0, _ => fun k => k.elim
  | i + 1, h => fun k => by
    obtain ⟨k, rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
    rcases k with j | u
    · exact congrArg (strictTransformSet _ _) (hyp_exceptionalEmb F i (Nat.lt_of_succ_lt h) j)
    · rfl

/-- From a simple normal crossing start `F`: under the normal-crossings clause (3′) for the
boundary starting with `red F`, the family `F_i` from the start `F` is a simple normal crossing
family at every stage and the boundary `E_i` is its reduced ideal sheaf. Clause (3′) at stage `i`
says that `E_i` has only normal crossings with `Z_i`, which by the dictionary
`hasOnlyNormalCrossingsWith_idealSheaf_iff` is "`Z_i` has simple normal crossings with `F_i`";
`isSnc_totalTransform` makes `F_{i+1}` a simple normal crossing family and
`reducedTransform_eq_idealSheaf_totalTransform` identifies `red(π_i⁻¹E_i ∪ π_i⁻¹Z_i)` with the
reduced ideal sheaf of the total transform. -/
theorem isSnc_totalTransformSeqFrom_and_boundarySeq_eq {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ)
    (h3 : ∀ i : Fin S.length, (S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E))
      i.castSucc).HasOnlyNormalCrossingsWith (S.center i))
    (i : Fin (S.length + 1)) :
    (S.totalTransformSeqFrom F i).IsSnc ψ ∧
      S.boundarySeq (F.idealSheaf (𝕜 := 𝕜) (E := E)) i =
        (S.totalTransformSeqFrom F i).idealSheaf :=
  isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hF i fun i' _ => h3 i'

variable [FiniteDimensional 𝕜 E] {S} {I : IdealSheaf M} {m : ℕ} (F : HypersurfaceFamily M)

omit [FiniteDimensional 𝕜 E] in
/-- **Dropping the boundary**: a sequence of order `≥ m` for `(I, m)` starting with the simple
normal crossing boundary `E = red F` is of order `≥ m` for `(I, m)` starting with the empty
boundary ([Kol07, Definition 66] with [Kol07, Definition 24 (4)]). Clause (4′) does not mention
the boundary. For clause (3′): the boundary `E_i^F` is the reduced ideal sheaf of the boundary
family `F_i^F` from the start `F` (`isSnc_totalTransformSeqFrom_and_boundarySeq_eq`), `Z_i` has
simple normal crossings with `F_i^F`, hence with the sub-family `F_i^∅` of exceptional divisors
(`exceptionalEmb`), whose reduced ideal sheaf is the boundary `E_i^∅` from the empty start; this
last identification is carried along the same induction, since it needs (3′) for `𝒪` at the
earlier stages. -/
theorem IsOfOrderGe.unit_of_idealSheaf (B : FiniteSuccession M) (hF : F.IsSnc ψ)
    (hge : B.IsOfOrderGe I m (F.idealSheaf (𝕜 := 𝕜) (E := E))) :
    B.IsOfOrderGe I m (⊤) := by
  have hFsnc := B.isSnc_totalTransformSeqFrom_and_boundarySeq_eq hF fun i => (hge i).1
  -- the joint induction: the invariant for the exceptional family and (3′) for `𝒪` below `i`
  have key : ∀ i : Fin (B.length + 1), (B.totalTransformSeq i).IsSnc ψ ∧
      B.boundarySeq (⊤) i = (B.totalTransformSeq i).idealSheaf ∧
      ∀ i' : Fin B.length, i'.1 < i.1 →
        (B.boundarySeq (⊤) i'.castSucc).HasOnlyNormalCrossingsWith
          (B.center i') := by
    intro i
    induction i using Fin.induction with
    | zero =>
      exact ⟨HypersurfaceFamily.isSnc_empty (ψ := ψ),
        (HypersurfaceFamily.idealSheaf_empty (ψ := ψ)).symm,
        fun i' hi' => absurd hi' (Nat.not_lt_zero _)⟩
    | succ i ih =>
      obtain ⟨hsnc, heq, h3⟩ := ih
      have hZ : IsClosedSubmanifold ψ (B.center i).support (B.codim i) :=
        (B.isClosedSubmanifold_center i).congr_chart ψ
      have hπ : IsBlowUp ψ (B.center i).support (B.codim i) (B.map i) :=
        (B.isBlowUp_map i).congr_chart ψ
      have hZI : hZ.idealSheaf = B.center i :=
        (IsClosedSubmanifold.idealSheaf_congr hZ (B.isClosedSubmanifold_center i) rfl).trans
          (B.idealSheaf_center i)
      -- `Z_i` has simple normal crossings with the family from `F`, hence with the exceptional
      -- sub-family
      have hswF : (B.totalTransformSeqFrom F i.castSucc).HasSncWith ψ (B.center i).support
          (B.codim i) := by
        have h := (hge i).1
        rw [(hFsnc i.castSucc).2, ← hZI] at h
        exact (hasOnlyNormalCrossingsWith_idealSheaf_iff (hFsnc i.castSucc).1 hZ).mp h
      have hsw : (B.totalTransformSeq i.castSucc).HasSncWith ψ (B.center i).support
          (B.codim i) :=
        hswF.of_subfamily (B.exceptionalEmb F i.castSucc.1 i.castSucc.2)
          (B.exceptionalEmb_injective F _ _) (B.hyp_exceptionalEmb F _ _)
      have h3i : (B.boundarySeq (⊤) i.castSucc).HasOnlyNormalCrossingsWith
          (B.center i) := by
        rw [heq, ← hZI]
        exact (hasOnlyNormalCrossingsWith_idealSheaf_iff hsnc hZ).mpr hsw
      refine ⟨HypersurfaceFamily.isSnc_totalTransform hZ hπ hsnc hsw, ?_, fun i' hi' => ?_⟩
      · rw [B.boundarySeq_succ, heq, ← hZI]
        exact reducedTransform_eq_idealSheaf_totalTransform hZ hπ hsnc hsw
      · rw [Fin.val_succ] at hi'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | heq'
        · exact h3 i' hlt
        · have : i' = i := Fin.ext heq'
          subst this
          exact h3i
  intro i
  exact ⟨(key (Fin.last B.length)).2.2 i i.2, (hge i).2⟩

end AnalyticManifold.FiniteSuccession

end
