/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCard
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Resolution.Analytic.Functor.EraseEmptyLast
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Step21ErasePrep
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Empty rounds: the rounds over a region of low order erase to nothing

Kollár's remark after [Kol07, Theorem 68], that the order reduction `BO_m` does nothing when
`max-ord I < m`, for the rounds of the resolution family
(`Hironaka/Resolution/Analytic/Wlo09/Rounds.lean`). The round `BO_{n,d+1}` on a triple of its class
produces a sequence of order `≥ d + 1` (the field `isOfOrderGe`, [Kol07, Definition 66 (4′)]); over
a reading map into a region where the order of the ideal is `≤ d`, no centre can be met: stage by
stage the marked transform keeps order `≤ d`, the centre (which lies where that order is `≥ d + 1`)
has empty preimage, the blowing-up is an isomorphism there and the marked transform is the total
transform (`birationalTransform_I_of_eq_empty`). So the round's list pulled back along the reading
map erases to the empty list (`eraseEmpty_pullback_roundList_eq_nil`), and where the ideal is the
unit ideal every round does, whatever their number (`eraseEmpty_resolveFrom_eq_nil_of_ord_eq_zero`,
the case of an admissible chain with no round in
`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`).

* `FiniteSuccession.isEmptyAt_of_ord_le_of_lt`: the order bound read pointwise; a centre lying
  where the marked transform has order `≥ m` is empty when that order is `≤ b < m`.
* `ord_markedTransformSeq_pullback_le_of_lt`: the bound `≤ b` propagates along the pulled-back
  sequence (the recursion; `isOfOrderGe_pullback`).
* `BlowUpSequence.eraseEmpty_eq_nil_of_forall_isEmptyAt`: a list of empty centres erases to `nil`
  (the empty blow-up convention [Kol07, 32], via the count `length_eraseEmpty_add_emptyCount`).
* `IdealSheaf.ord_comap_of_isLocalDiffeomorphAt`: the order of an inverse image ideal sheaf at a
  point where the map is a local isomorphism, in the `comap` form.
-/

public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

section Core

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- The order bound of [Kol07, Definition 66 (4′)] read pointwise: a centre of a sequence of order
`≥ m` for `(I, m)` lies where the marked transform has order `≥ m` (`ordAlong_le_ord`); if that
order is `≤ b < m` at every point of the stage, the centre is empty. -/
theorem _root_.AnalyticManifold.FiniteSuccession.isEmptyAt_of_ord_le_of_lt
    (S : FiniteSuccession M)
    {I E₀ : AnalyticManifold.IdealSheaf M} {m b : ℕ} (hge : S.IsOfOrderGe I m E₀) (hb : b < m)
    (i : Fin S.length)
    (hlt : ∀ x : S.stage i.castSucc, (S.markedTransformSeq I m i.castSucc).ord x ≤ (b : ℕ∞)) :
    S.IsEmptyAt i := by
  refine (S.isEmptyAt_iff i).mpr (Set.eq_empty_iff_forall_notMem.mpr fun a ha => ?_)
  have h1 := hge.le_ordAlong i ha
  have h2 := ordAlong_le_ord (S.isClosedSubmanifold_center i)
    (S.markedTransformSeq I m i.castSucc) ha
  rw [S.idealSheaf_center i] at h2
  exact absurd (Nat.cast_le.mp (h1.trans (h2.trans (hlt a)))) (not_le.mpr hb)

/-- `ord_pullback_of_isLocalDiffeomorphAt` in the `comap` form: the order of the inverse image ideal
sheaf at a point where the map is a local isomorphism is the order of the ideal sheaf at the image
point. -/
theorem _root_.AnalyticManifold.IdealSheaf.ord_comap_of_isLocalDiffeomorphAt
    (J : AnalyticManifold.IdealSheaf M) (f : AnalyticMap N M) {b : N}
    (hf : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω f b) :
    (J.pullback f f.contMDiff).ord b = J.ord (f b) :=
  IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ J hf

/-- Along a pulled-back sequence: if `L` is of order `≥ m` for the triple `T` and `T.I` has order
`≤ b < m` on the image of the local analytic isomorphism `h`, every marked transform of
`(h^* T.I, m)` along `h^* L` has order `≤ b`. Stage by stage: the centre lies where the marked
transform has order `≥ m`, so it is empty (`isEmptyAt_of_ord_le_of_lt`), the blowing-up is then an
isomorphism and the marked transform is the total transform (`birationalTransform_I_of_eq_empty`),
whose order at a point is the order below it. -/
theorem ord_markedTransformSeq_pullback_le_of_lt (T : AnalyticTriple ψ₀ M) (L : BlowUpSequence ψ₀ M)
    {m : ℕ} (hge : L.toSuccession.IsOfOrderGe T.I m T.F.idealSheaf) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) {b : ℕ} (hb : b < m)
    (hlow : ∀ y, T.I.ord (h y) ≤ (b : ℕ∞)) (i : Fin ((L.pullback h hh).length + 1))
    (x : (L.pullback h hh).stage i) :
    ((L.pullback h hh).toSuccession.markedTransformSeq
        (T.I.pullback h h.contMDiff) m
      i).ord x ≤ (b : ℕ∞) := by
  have := finiteDimensional_of_chartIso ψ₀
  have hge' := AnalyticTriple.isOfOrderGe_pullback T m L hge h hh
  induction i using Fin.induction with
  | zero =>
    rw [FiniteSuccession.markedTransformSeq_zero]
    exact (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt T.I h (hh x)).trans_le (hlow x)
  | succ i ih =>
    have hY₀ : (((L.pullback h hh).toSuccession).center i).support = ∅ :=
      ((L.pullback h hh).toSuccession.isEmptyAt_iff i).mp
        ((L.pullback h hh).toSuccession.isEmptyAt_of_ord_le_of_lt hge' hb i ih)
    rw [FiniteSuccession.markedTransformSeq_succ,
      MarkedIdealSheaf.birationalTransform_I_of_eq_empty
        ((L.pullback h hh).toSuccession.isClosedSubmanifold_center i) hY₀
        ((L.pullback h hh).toSuccession.isBlowUp_map i),
      IdealSheaf.ord_comap_of_isLocalDiffeomorphAt _ _ (b := x)
        (((L.pullback h hh).toSuccession.isBlowUp_map i).isLocalDiffeomorphOn_compl
          ⟨x, fun hx => Set.notMem_empty _ (hY₀ ▸ hx)⟩)]
    exact ih _

/-- A list all of whose centres are empty erases to the empty list ([Kol07, 32]: the count of
empty centres is the length, `length_eraseEmpty_add_emptyCount`). -/
theorem _root_.AnalyticManifold.BlowUpSequence.eraseEmpty_eq_nil_of_forall_isEmptyAt
    (L : BlowUpSequence ψ₀ M)
    (h : ∀ i, L.toSuccession.IsEmptyAt i) : L.eraseEmpty = BlowUpSequence.nil M := by
  have hc : L.emptyCount = L.length := by
    classical
    unfold BlowUpSequence.emptyCount
    rw [Finset.filter_true_of_mem fun i _ => h i, Finset.card_univ, Fintype.card_fin]
  have hlen : L.eraseEmpty.length = 0 := by
    have := BlowUpSequence.length_eraseEmpty_add_emptyCount L
    omega
  revert hlen
  generalize L.eraseEmpty = L₀
  intro hlen
  cases L₀ with
  | nil => rfl
  | cons hY rest => exact absurd hlen (Nat.succ_ne_zero _)

end Core

section Rounds

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)

/-- **The empty round over the reading image** (the remark after [Kol07, Theorem 68]). The list of
the round `BO_{n,d+1}` at `O`, pulled back along a reading map `ι'` into `O` on whose image the
order is `≤ d`, erases to the empty list: every centre lies in `{ord ≥ d + 1}` of the current marked
transform (the field `isOfOrderGe`, [Kol07, Definition 66 (4′)]), which the image never meets, along
the list, stage by stage. -/
theorem eraseEmpty_pullback_roundList_eq_nil {d : ℕ} {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hcls : AnalyticTriple.BOClass (d + 1) cur) (O : Opens X)
    (hO : IsCompact (closure (O : Set X))) {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (ι' : AnalyticMap N (X.restrict O))
    (hι' : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι')
    (hlow : ∀ y, (cur.pullback (X.inclusion O) (isLocalDiffeomorph_inclusion X O)).I.ord (ι' y) ≤
      (d : ℕ∞)) :
    ((roundList bo cur hcls O hO).pullback ι' hι').eraseEmpty = BlowUpSequence.nil N :=
  BlowUpSequence.eraseEmpty_eq_nil_of_forall_isEmptyAt _ fun i =>
    ((roundList bo cur hcls O hO).pullback ι' hι').toSuccession.isEmptyAt_of_ord_le_of_lt
      (AnalyticTriple.isOfOrderGe_pullback _ (d + 1) (roundList bo cur hcls O hO)
        ((bo (d + 1)).isOfOrderGe cur hcls O hO) ι' hι')
      (Nat.lt_succ_self d) i
      (ord_markedTransformSeq_pullback_le_of_lt _ (roundList bo cur hcls O hO)
        ((bo (d + 1)).isOfOrderGe cur hcls O hO) ι' hι' (Nat.lt_succ_self d) hlow i.castSucc)

/-- **No rounds over a region where the ideal is the unit ideal.** If the order is `0` on the
reading image, the rounds read through `ι` erase to the empty list, whatever their number: every
round's centres miss the image (`eraseEmpty_pullback_roundList_eq_nil`), and the marked transforms
over it stay the unit ideal. The case of an admissible chain with no round in
`Hironaka/Resolution/Analytic/Wlo09/Canonicity.lean`. -/
theorem eraseEmpty_resolveFrom_eq_nil_of_ord_eq_zero (d : ℕ)
    {X : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (cur : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) X)
    (hord : ∀ x, cur.I.ord x ≤ (d : ℕ∞)) (hfin : Finite {j // cur.F.hyp j ≠ ∅})
    (Ω : ℕ → Opens X) (hΩ : ∀ k, k < d → IsCompact (closure (Ω k : Set X)))
    (hΩsub : ∀ k, k + 1 < d → closure (Ω k : Set X) ⊆ Ω (k + 1))
    {N : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)} (ι : AnalyticMap N X)
    (hι : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω ι) (hrange : Set.range ι ⊆ Ω 0)
    (hzero : ∀ y, cur.I.ord (ι y) ≤ ((0 : ℕ) : ℕ∞)) :
    (resolveFrom bo d cur hord hfin Ω hΩ hΩsub ι hι hrange).eraseEmpty = BlowUpSequence.nil N := by
  induction d generalizing X N with
  | zero => simp only [resolveFrom, BlowUpSequence.eraseEmpty_nil]
  | succ d ih =>
    have hr : Set.range ι ⊆ Ω d := range_subset_chain hΩsub hrange
    have hge := (bo (d + 1)).isOfOrderGe cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
      (hΩ d (Nat.lt_succ_self d))
    -- the order of the restricted ideal on the corestricted image is `0`
    have hlow : ∀ y, (cur.pullback (X.inclusion (Ω d))
        (isLocalDiffeomorph_inclusion X (Ω d))).I.ord (AnalyticMap.corestrict ι (Ω d) hr y) ≤ ((0 :
        ℕ) : ℕ∞) := fun y => by
      change (cur.I.pullback (X.inclusion (Ω d)) (X.inclusion (Ω d)).contMDiff).ord _ ≤ _
      rw [IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ cur.I
        (isLocalDiffeomorph_inclusion X (Ω d) _)]
      exact hzero y
    -- the top round erases to `nil` over the image (`eraseEmpty_pullback_roundList_eq_nil`)
    have hA := eraseEmpty_pullback_roundList_eq_nil bo cur (boClass_succ_of_ord_le cur hord hfin)
      (Ω d) (hΩ d (Nat.lt_succ_self d)) (AnalyticMap.corestrict ι (Ω d) hr)
      (isLocalDiffeomorph_corestrict ι (Ω d) hι hr)
      (fun y => (hlow y).trans (Nat.cast_le.mpr (Nat.zero_le d)))
    -- the derived ideal has order `0` on the lifted image
    have hzero' : ∀ q, (derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).I.ord
        ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
          (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hr)
          (isLocalDiffeomorph_corestrict ι (Ω d) hι hr) q) ≤ ((0 : ℕ) : ℕ∞) := fun q => by
      have h1 := ord_markedTransformSeq_pullback_le_of_lt _
        (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
        hge (AnalyticMap.corestrict ι (Ω d) hr) (isLocalDiffeomorph_corestrict ι (Ω d) hι hr)
        (Nat.succ_pos d) hlow (Fin.last _) q
      rw [BlowUpSequence.markedTransformSeq_last_pullbackLiftLast
        (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d) (hΩ d (Nat.lt_succ_self d)))
        _ _ _ _ _ hge,
        IdealSheaf.ord_comap_of_isLocalDiffeomorphAt _ _
          (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _ q)] at h1
      exact h1
    -- the rounds below erase to `nil` (the induction hypothesis)
    have hB := ih (derivedTriple bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d)))
      (derivedTriple_ord_le bo cur _ (Ω d) _) (derivedTriple_finite bo cur _ (Ω d) _)
      (liftChain (roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))) Ω)
      (liftChain_isCompact _ hΩ hΩsub rfl) (liftChain_closure_subset _ hΩsub)
      ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullbackLiftLast (AnalyticMap.corestrict ι (Ω d) hr)
        (isLocalDiffeomorph_corestrict ι (Ω d) hι hr))
      (BlowUpSequence.isLocalDiffeomorph_pullbackLiftLast _ _ _)
      (range_pullbackLiftLast_subset_liftOpens _ ι hι (Ω 0) hrange hr) hzero'
    rw [resolveFrom, BlowUpSequence.eraseEmpty_concat, BlowUpSequence.eraseEmpty_map]
    refine (congrArg (fun L => BlowUpSequence.concat
      ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback (AnalyticMap.corestrict ι (Ω d) hr)
        (isLocalDiffeomorph_corestrict ι (Ω d) hι hr)).eraseEmpty
      (BlowUpSequence.map ((roundList bo cur (boClass_succ_of_ord_le cur hord hfin) (Ω d)
        (hΩ d (Nat.lt_succ_self d))).pullback (AnalyticMap.corestrict ι (Ω d) hr)
        (isLocalDiffeomorph_corestrict ι (Ω d) hι hr)).eraseEmptyLast L)) hB).trans ?_
    rw [BlowUpSequence.map_nil, BlowUpSequence.concat_nil_right]
    exact hA

end Rounds

end Hironaka.Manifold

end
