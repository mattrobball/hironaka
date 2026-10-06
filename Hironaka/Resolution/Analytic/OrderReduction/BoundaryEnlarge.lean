/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.GoingUp.BoundaryDrop
public import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.Snc.NormalCrossings
import Hironaka.Resolution.Analytic.Functor.LocalIsoTools
import Hironaka.Resolution.Analytic.OrderReduction.Step21Cosupp
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Enlarging the boundary by members missing the cosupport

After Step 2.1 of the proof of [Kol07, Theorem 103], "`cosupp(I_r, m)` is disjoint from
`Π^{-1}_* E`" ([Kol07, 104, Step 2.1.j]), so Step 2.2 may run with the boundary consisting of the
exceptional divisors and the transform `H_r` of the hypersurface of maximal contact, while the
sequence is of order `≥ m` for the full transformed boundary as well: the extra members, the
transforms of the original members of `E`, miss every centre, and a member missing the centre is
invisible to the normal-crossings condition at the points of the centre ([Kol07, Definition 24],
whose chart only constrains the members through the point).

The general form, not in the sources: a blow-up sequence of order `≥ m` for `(𝓘, m, red F)` is of
order `≥ m` for `(𝓘, m, red G)` whenever every member of `G` meeting the cosupport `{ord 𝓘 ≥ m}`
is a member of `F`, injectively (through a map `e : G.ι → F.ι`). The proof is the joint induction
of `BoundaryFamily.lean` on the stages: at every stage the boundary family from `G` is the family
from `F` with extra members missing the centre, because a member of `G_i` through a point of the
centre is either the strict transform of a member of `G` (which then meets the cosupport, the
cosupport at stage `i` lying over the cosupport at the start and the strict transform over the
member) or an exceptional divisor, shared by the two families.

* `HypersurfaceFamily.HasSncWith.of_forall_mem_exists` — simple normal crossings pass to a family
  whose members through the points of `Y` are, injectively, members of the first.
* `FiniteSuccession.originalIdxAux_or_exceptionalEmb`, `originalIdxAux_injective`,
  `originalIdxAux_ne_exceptionalEmb` — every member of the stage-`i` family is the transform of an
  original member or an exceptional divisor, and the two kinds are distinct.
* `FiniteSuccession.corrIdxAux`, `corrIdxAux_originalIdxAux`, `corrIdxAux_exceptionalEmb` — the
  correspondence of index sets at every stage induced by `e`.
* `FiniteSuccession.IsOfOrderGe.of_forall_hyp_eq_of_mem` — the enlargement.

The enlargement is applied in `Step22FamFull.lean`; the index correspondence is reused in
`Step21Indiff.lean` for the indifference to empty boundary members.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Simple normal crossings with `F` pass to a family `G` whose members through each point `a` of
`Y` are, injectively, members of `F` through `a` with the same hypersurface: the chart of `F` at
`a` serves, with its coordinate indices transported along the correspondence. -/
theorem HypersurfaceFamily.HasSncWith.of_forall_mem_exists {F G : HypersurfaceFamily M} {Y : Set M}
    {c : ℕ} (h : F.HasSncWith ψ Y c) (e : ∀ a ∈ Y, {k // a ∈ G.hyp k} → {j // a ∈ F.hyp j})
    (he_inj : ∀ a ha, Function.Injective (e a ha))
    (he_hyp : ∀ a ha k, G.hyp k.1 = F.hyp (e a ha k).1) : G.HasSncWith ψ Y c := by
  intro a ha
  obtain ⟨φ, σ, cidx, hφ, hc⟩ := h a ha
  refine ⟨φ, σ, fun k => cidx (e a ha k), hφ, hc.1, hc.2.1, ?_, hc.2.2.2.comp (he_inj a ha)⟩
  intro k x hx
  rw [he_hyp a ha k]
  exact hc.2.2.1 (e a ha k) x hx

end Manifold

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-! ### The two kinds of members of the stage-`i` family -/

/-- Every member of the boundary family at stage `i` is the transform of an original member or an
exceptional divisor. -/
theorem originalIdxAux_or_exceptionalEmb (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1) (a : (S.totalTransformSeqFromAux F i h).ι),
      (∃ j, a = S.originalIdxAux F i h j) ∨ ∃ k, a = S.exceptionalEmb F i h k
  | 0, _, a => Or.inl ⟨a, rfl⟩
  | i + 1, h, a => by
    obtain ⟨a', rfl⟩ : ∃ a', toLex a' = a := ⟨ofLex a, rfl⟩
    rcases a' with a' | u
    · rcases originalIdxAux_or_exceptionalEmb F i (Nat.lt_of_succ_lt h) a' with
        ⟨j, rfl⟩ | ⟨k, rfl⟩
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨toLex (Sum.inl k), rfl⟩
    · exact Or.inr ⟨toLex (Sum.inr u), rfl⟩

/-- The transforms of distinct original members are distinct members. -/
theorem originalIdxAux_injective (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1), Function.Injective (S.originalIdxAux F i h)
  | 0, _ => fun _ _ hjj' => hjj'
  | i + 1, h => fun _ _ hjj' =>
    originalIdxAux_injective F i (Nat.lt_of_succ_lt h) (Sum.inl_injective (toLex.injective hjj'))

/-- The transform of an original member is never an exceptional divisor. -/
theorem originalIdxAux_ne_exceptionalEmb (F : HypersurfaceFamily M) :
    ∀ (i : ℕ) (h : i < S.length + 1) (j : F.ι) (k : (S.totalTransformSeqAux i h).ι),
      S.originalIdxAux F i h j ≠ S.exceptionalEmb F i h k
  | 0, _, _, k => k.elim
  | i + 1, h, j, k => by
    obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
    rcases k' with k' | u
    · intro heq
      exact originalIdxAux_ne_exceptionalEmb F i (Nat.lt_of_succ_lt h) j k'
        (Sum.inl_injective (toLex.injective heq))
    · intro heq
      exact Sum.inl_ne_inr (toLex.injective heq)

/-! ### The correspondence of index sets induced by a map of the starts -/

variable {F G : HypersurfaceFamily M} (e : G.ι → F.ι)

/-- The map of index sets at stage `i` induced by a map `e : G.ι → F.ι` of the starting index sets:
transforms of original members along `e`, exceptional divisors to themselves. -/
def corrIdxAux : ∀ (i : ℕ) (h : i < S.length + 1),
    (S.totalTransformSeqFromAux G i h).ι → (S.totalTransformSeqFromAux F i h).ι
  | 0, _ => e
  | i + 1, h => fun a => toLex (Sum.map (corrIdxAux i (Nat.lt_of_succ_lt h)) id (ofLex a))

theorem corrIdxAux_originalIdxAux : ∀ (i : ℕ) (h : i < S.length + 1) (j : G.ι),
    S.corrIdxAux e i h (S.originalIdxAux G i h j) = S.originalIdxAux F i h (e j)
  | 0, _, _ => rfl
  | i + 1, h, j => by
    change toLex (Sum.inl (S.corrIdxAux e i _ (S.originalIdxAux G i _ j))) = _
    rw [corrIdxAux_originalIdxAux i (Nat.lt_of_succ_lt h) j]
    rfl

theorem corrIdxAux_exceptionalEmb : ∀ (i : ℕ) (h : i < S.length + 1)
    (k : (S.totalTransformSeqAux i h).ι),
    S.corrIdxAux e i h (S.exceptionalEmb G i h k) = S.exceptionalEmb F i h k
  | 0, _, k => k.elim
  | i + 1, h, k => by
    obtain ⟨k', rfl⟩ : ∃ k', toLex k' = k := ⟨ofLex k, rfl⟩
    rcases k' with k' | u
    · change toLex (Sum.inl (S.corrIdxAux e i _ (S.exceptionalEmb G i _ k'))) = _
      rw [corrIdxAux_exceptionalEmb i (Nat.lt_of_succ_lt h) k']
      rfl
    · rfl

/-! ### The enlargement -/

variable [FiniteDimensional 𝕜 E] {J : IdealSheaf M} {m : ℕ}

/-- A member of the stage-`i` family from `G` through a point of the cosupport of the marked
transform is, under the correspondence, a member of the stage-`i` family from `F` with the same
hypersurface: the transform of an original member, which then meets the cosupport of `𝓘` (the
cosupport at stage `i` lies over the cosupport at the start, `le_ord_stageMap`, and the strict
transform over the member), or an exceptional divisor. -/
theorem hyp_corrIdxAux_of_mem (hG : G.IsSnc ψ) (hge : S.IsOfOrderGe J m F.idealSheaf)
    (hmem : ∀ k, (∃ a ∈ G.hyp k, (m : ℕ∞) ≤ J.ord a) → G.hyp k = F.hyp (e k))
    (i : Fin (S.length + 1)) (a : S.stage i) (hord : (m : ℕ∞) ≤ (S.markedTransformSeq J m i).ord a)
    (kk : (S.totalTransformSeqFrom G i).ι) (ha : a ∈ (S.totalTransformSeqFrom G i).hyp kk) :
    (S.totalTransformSeqFrom G i).hyp kk =
      (S.totalTransformSeqFrom F i).hyp (S.corrIdxAux e i.1 i.2 kk) := by
  rcases S.originalIdxAux_or_exceptionalEmb G i.1 i.2 kk with ⟨j, rfl⟩ | ⟨k, rfl⟩
  · rw [S.corrIdxAux_originalIdxAux]
    change (S.totalTransformSeqFrom G i).hyp (S.originalIdx G i j) =
      (S.totalTransformSeqFrom F i).hyp (S.originalIdx F i (e j))
    rw [hyp_originalIdx, hyp_originalIdx]
    have ha' : a ∈ S.strictTransformSeq (G.hyp j) i := by
      change a ∈ (S.totalTransformSeqFrom G i).hyp (S.originalIdx G i j) at ha
      rwa [hyp_originalIdx] at ha
    have hmemj : G.hyp j = F.hyp (e j) :=
      hmem j ⟨S.stageMap i a,
        S.strictTransformSeq_subset_preimage_stageMap (hG.1 j).isClosed i ha',
        hge.le_ord_stageMap i a hord⟩
    rw [hmemj]
  · rw [S.corrIdxAux_exceptionalEmb]
    change (S.totalTransformSeqFromAux G i.1 i.2).hyp (S.exceptionalEmb G i.1 i.2 k) =
      (S.totalTransformSeqFromAux F i.1 i.2).hyp (S.exceptionalEmb F i.1 i.2 k)
    rw [hyp_exceptionalEmb, hyp_exceptionalEmb]

/-- The correspondence is injective on the members through a point of the cosupport of the marked
transform. -/
theorem corrIdxAux_injOn_of_mem (hG : G.IsSnc ψ) (hge : S.IsOfOrderGe J m F.idealSheaf)
    (hinj : ∀ k k', (∃ a ∈ G.hyp k, (m : ℕ∞) ≤ J.ord a) → (∃ a ∈ G.hyp k', (m : ℕ∞) ≤ J.ord a) →
      e k = e k' → k = k')
    (i : Fin (S.length + 1)) (a : S.stage i) (hord : (m : ℕ∞) ≤ (S.markedTransformSeq J m i).ord a)
    (kk kk' : (S.totalTransformSeqFrom G i).ι) (ha : a ∈ (S.totalTransformSeqFrom G i).hyp kk)
    (ha' : a ∈ (S.totalTransformSeqFrom G i).hyp kk')
    (heq : S.corrIdxAux e i.1 i.2 kk = S.corrIdxAux e i.1 i.2 kk') : kk = kk' := by
  have hmeets : ∀ (j : G.ι), a ∈ (S.totalTransformSeqFrom G i).hyp (S.originalIdx G i j) →
      ∃ b ∈ G.hyp j, (m : ℕ∞) ≤ J.ord b := fun j hj => by
    rw [hyp_originalIdx] at hj
    exact ⟨S.stageMap i a, S.strictTransformSeq_subset_preimage_stageMap (hG.1 j).isClosed i hj,
      hge.le_ord_stageMap i a hord⟩
  rcases S.originalIdxAux_or_exceptionalEmb G i.1 i.2 kk with ⟨j, rfl⟩ | ⟨k, rfl⟩ <;>
    rcases S.originalIdxAux_or_exceptionalEmb G i.1 i.2 kk' with ⟨j', rfl⟩ | ⟨k', rfl⟩
  · rw [S.corrIdxAux_originalIdxAux, S.corrIdxAux_originalIdxAux] at heq
    have hjj' : e j = e j' := S.originalIdxAux_injective F i.1 i.2 heq
    rw [hinj j j' (hmeets j ha) (hmeets j' ha') hjj']
  · rw [S.corrIdxAux_originalIdxAux, S.corrIdxAux_exceptionalEmb] at heq
    exact absurd heq (S.originalIdxAux_ne_exceptionalEmb F i.1 i.2 _ _)
  · rw [S.corrIdxAux_exceptionalEmb, S.corrIdxAux_originalIdxAux] at heq
    exact absurd heq.symm (S.originalIdxAux_ne_exceptionalEmb F i.1 i.2 _ _)
  · rw [S.corrIdxAux_exceptionalEmb, S.corrIdxAux_exceptionalEmb] at heq
    rw [S.exceptionalEmb_injective F i.1 i.2 heq]

/-- A smooth blow-up sequence of order `≥ m` for `(𝓘, m, red F)` is of order `≥ m` for
`(𝓘, m, red G)` when every member of `G` meeting the cosupport `{ord 𝓘 ≥ m}` is, injectively, a
member of `F` (the general form of the observation in [Kol07, 104, Step 2.1.j] that the transforms
of the original boundary miss the cosupport after Step 2.1). The order clause of
[Kol07, Definition 66] does not see the boundary; the normal-crossings clause at every stage
follows by the joint induction of `BoundaryFamily.lean` and `HasSncWith.of_forall_mem_exists`, the
members of the family from `G` through a point of the centre corresponding to members of the
family from `F`. Not in the sources. -/
theorem IsOfOrderGe.of_forall_hyp_eq_of_mem (hF : F.IsSnc ψ) (hG : G.IsSnc ψ)
    (hge : S.IsOfOrderGe J m F.idealSheaf)
    (hmem : ∀ k, (∃ a ∈ G.hyp k, (m : ℕ∞) ≤ J.ord a) → G.hyp k = F.hyp (e k))
    (hinj : ∀ k k', (∃ a ∈ G.hyp k, (m : ℕ∞) ≤ J.ord a) → (∃ a ∈ G.hyp k', (m : ℕ∞) ≤ J.ord a) →
      e k = e k' → k = k') :
    S.IsOfOrderGe J m G.idealSheaf := by
  have key : ∀ (k : ℕ) (hk : k < S.length),
      (S.boundarySeq (G.idealSheaf (𝕜 := 𝕜) (E := E))
        (⟨k, hk⟩ : Fin S.length).castSucc).HasOnlyNormalCrossingsWith (S.center ⟨k, hk⟩) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    obtain ⟨hGsnc, hGeq⟩ := S.isSnc_totalTransformSeqFrom_and_boundarySeq_eq_of_forall_lt hG
      (⟨k, hk⟩ : Fin S.length).castSucc fun i' hi' => ih i'.1 hi' i'.2
    have hFsnc := S.hasSncWith_totalTransformSeqFrom_center_of_forall_lt hF ⟨k, hk⟩
      fun i' _ => (hge i').1
    have hZ : IsClosedSubmanifold ψ (S.center ⟨k, hk⟩).support (S.codim ⟨k, hk⟩) :=
      (S.isClosedSubmanifold_center ⟨k, hk⟩).congr_chart ψ
    have hZI : hZ.idealSheaf = S.center ⟨k, hk⟩ :=
      (IsClosedSubmanifold.idealSheaf_congr hZ (S.isClosedSubmanifold_center ⟨k, hk⟩) rfl).trans
        (S.idealSheaf_center ⟨k, hk⟩)
    rw [hGeq, ← hZI]
    refine (hasOnlyNormalCrossingsWith_idealSheaf_iff hGsnc hZ).mpr ?_
    -- a point of the centre lies in the cosupport of the controlled transform
    have hord : ∀ a ∈ (S.center ⟨k, hk⟩).support,
        (m : ℕ∞) ≤ (S.markedTransformSeq J m (⟨k, hk⟩ : Fin S.length).castSucc).ord a := by
      intro a ha
      have h1 := hge.le_ordAlong ⟨k, hk⟩ ha
      rw [← S.idealSheaf_center ⟨k, hk⟩] at h1
      exact h1.trans (ordAlong_le_ord _ _ ha)
    refine hFsnc.of_forall_mem_exists
      (fun a ha kk => ⟨S.corrIdxAux e _ _ kk.1, ?_⟩) (fun a ha => ?_) (fun a ha kk => ?_)
    · rw [← S.hyp_corrIdxAux_of_mem e hG hge hmem _ a (hord a ha) kk.1 kk.2]
      exact kk.2
    · intro kk kk' hkk'
      exact Subtype.ext (S.corrIdxAux_injOn_of_mem e hG hge hinj _ a (hord a ha) kk.1 kk'.1 kk.2
        kk'.2 (Subtype.mk.inj hkk'))
    · exact S.hyp_corrIdxAux_of_mem e hG hge hmem _ a (hord a ha) kk.1 kk.2
  exact fun i => ⟨key i.1 i.2, (hge i).2⟩

end AnalyticManifold.FiniteSuccession

end
