/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.CoverData
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.FiniteSuccession.DerivTransform
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackCover
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Manifold.FiniteSuccession.Functor.SigmaTriple
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Functors and local analytic isomorphisms: general tools

Tools for the passage from local to global in the proof of [Kol07, Theorem 103], placed here,
downstream of the pull-back, deletion-of-empty-members and order-along-a-centre modules, because
they need all of them:

* the two-summand disjoint union `N ⊔ M` (`sumFamily`, `sumDesc`, `sumInl` and their lemmas), the
  device by which an arbitrary local analytic isomorphism `h : N → M` becomes the composite of an
  open embedding with a surjective local isomorphism, and the two-piece union `f ⊔ g` of two maps
  (`sumDesc₂`), the cover used for the functoriality clauses of the descended functor;
* [Kol07, 34.1] for an arbitrary local analytic isomorphism, up to the deletion of empty blow-ups
  (`CommutesWithLocalIsos.seq_pullback_eq_eraseEmpty`), the analytic counterpart of
  `etaleEquivSeq_of_functor` for schemes
  (`Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeqFunctor`);
* the lifts of a local isomorphism along a centre list
  (`BlowUpSequence.mem_range_pullbackLift_of_stageMap_mem`,
  `BlowUpSequence.noEmptyCenters_pullback_of_subset_range`, the counterpart of
  `noEmptyCenters_pullback_of_centersInRange` for schemes, and
  `BlowUpSequence.centers_subset_range_pullbackLiftAux`);
* along a sequence of order `≥ m`: points of order `≥ m` lie over points of order `≥ m`
  (`IsOfOrderGe.le_ord_stageMap`, the counterpart of `le_ord_stageMap_of_mem_center` for schemes)
  and the sequence is of order `≥ 1` for the marked maximal-contact ideal
  (`IsOfOrderGe.isMarkedOne`).
-/

@[expose] public noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### The two-summand disjoint union `N ⊔ M` -/

section DisjointUnion

variable (N M : AnalyticManifold.{u} 𝕜 E)

/-- The two-summand family `N ⊔ M`, indexed by the lifted booleans (`true ↦ N`, `false ↦ M`). -/
abbrev sumFamily : ULift.{u} Bool → AnalyticManifold.{u} 𝕜 E := fun b => cond b.down N M

end DisjointUnion

/-! ### The two-piece union `f ⊔ g` (general tools) -/

section TwoPieces

variable {N₁ N₂ M : AnalyticManifold.{u} 𝕜 E}

/-- The map `f ⊔ g : N₁ ⊔ N₂ → M` on the summands of `sumFamily N₁ N₂` (`true ↦ N₁`,
`false ↦ N₂`; `sumDesc` with two maps). -/
def sumDesc₂ (f : AnalyticMap N₁ M) (g : AnalyticMap N₂ M) :
    ∀ b : ULift.{u} Bool, AnalyticMap (sumFamily N₁ N₂ b) M :=
  fun b => Bool.rec (motive := fun c => AnalyticMap (cond c N₁ N₂) M) g f b.down

/-- The first piece of the two-piece coproduct map is `f`. -/
theorem sumDesc₂_true (f : AnalyticMap N₁ M) (g : AnalyticMap N₂ M) :
    sumDesc₂ f g ⟨true⟩ = f := rfl

/-- The two-piece coproduct map of two local analytic isomorphisms is a family of
local analytic isomorphisms (the hypothesis of `isSigmaOf_pullback_sigmaDescMap`). -/
theorem isLocalDiffeomorph_sumDesc₂ {f : AnalyticMap N₁ M} {g : AnalyticMap N₂ M}
    (hf : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω f) (hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω g) :
    ∀ b, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sumDesc₂ f g b) := by
  rintro ⟨_ | _⟩
  · exact hg
  · exact hf

open Function in
/-- The two pieces cover `M` as soon as the second does (the cover `g` of the
triple is surjective). -/
theorem iUnion_range_sumDesc₂ (f : AnalyticMap N₁ M) {g : AnalyticMap N₂ M}
    (hgs : Surjective g) : (⋃ b, range (sumDesc₂ f g b)) = univ :=
  eq_univ_of_forall fun y => by
    obtain ⟨x, rfl⟩ := hgs y
    exact mem_iUnion.mpr ⟨⟨false⟩, x, rfl⟩

end TwoPieces

section DisjointUnion

variable {N M : AnalyticManifold.{u} 𝕜 E}

/-- The map `h ⊔ id_M : N ⊔ M → M` on the summands.
The body is the instance `sumDesc₂ h ContMDiffMap.id` of the two-map form, definitionally
`Bool.rec (motive := fun c => AnalyticMap (cond c N M) M) ContMDiffMap.id h b.down`. -/
def sumDesc (h : AnalyticMap N M) : ∀ b : ULift.{u} Bool, AnalyticMap (sumFamily N M b) M :=
  sumDesc₂ h ContMDiffMap.id

theorem isLocalDiffeomorph_sumDesc {h : AnalyticMap N M}
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    ∀ b, IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sumDesc h b) := by
  rintro ⟨_ | _⟩
  · exact AnalyticManifold.BlowUpSequence.isLocalDiffeomorph_id M
  · exact hh

theorem iUnion_range_sumDesc (h : AnalyticMap N M) :
    (⋃ b, Set.range (sumDesc h b)) = Set.univ :=
  Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨⟨false⟩, y, rfl⟩

theorem sumDesc_true (h : AnalyticMap N M) : sumDesc h ⟨true⟩ = h := rfl

/-- The inclusion of the summand `N` into `N ⊔ M`. -/
abbrev sumInl : AnalyticMap N (sigmaManifold (sumFamily N M)) :=
  sigmaMk (sumFamily N M) (ULift.up true)

end DisjointUnion

end Hironaka.Manifold

namespace Manifold.AnalyticBlowUpSequenceAssignment

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### [Kol07, 34.1] for a local isomorphism, from the two clauses of `CommutesWithLocalIsos` -/

variable {Dom : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop}
  {B : AnalyticBlowUpSequenceAssignment ψ₀ Dom} {M N : AnalyticManifold.{u} 𝕜 E}

/-- A functor commuting with surjective local isomorphisms and with open
embeddings commutes with `h` up to the deletion of empty blow-ups, whenever the pull-backs along `h`
and along `h ⊔ id_M : N ⊔ M → M` lie in its class — `h = (h ⊔ id_M) ∘ inl` with `inl` an open
embedding and `h ⊔ id_M` a surjective local isomorphism; the analytic counterpart of
`etaleEquivSeq_of_functor` for schemes
(`Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeqFunctor`). -/
theorem CommutesWithLocalIsos.seq_pullback_eq_eraseEmpty (hB : B.CommutesWithLocalIsos)
    (T : AnalyticTriple ψ₀ M) (hT : Dom T) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hT' : Dom (T.pullback h hh))
    (hTsum : Dom (T.pullback (sigmaDescMap (sumDesc h))
      (isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hh)))) :
    B.seq (T.pullback h hh) hT' = ((B.seq T hT).pullback h hh).eraseEmpty := by
  have hg : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (sigmaDescMap (sumDesc h)) :=
    isLocalDiffeomorph_sigmaDescMap _ (isLocalDiffeomorph_sumDesc hh)
  have hk : IsAnalyticOpenEmbedding (sumInl (N := N) (M := M)) :=
    isAnalyticOpenEmbedding_sigmaMk _ _
  have hgs : Function.Surjective (sigmaDescMap (sumDesc h)) :=
    surjective_sigmaDescMap _ (iUnion_range_sumDesc h)
  have hgk : (sigmaDescMap (sumDesc h)).comp sumInl = h :=
    sigmaDescMap_comp_sigmaMk (sumDesc h) (ULift.up true)
  have hfun : ⇑(sigmaDescMap (sumDesc h)) ∘ ⇑(sumInl (N := N) (M := M)) = ⇑h := by
    funext x
    rw [Function.comp_apply, ← ContMDiffMap.comp_apply, hgk]
  -- the pull-back along `h` is the pull-back along `inl` of the pull-back along `h ⊔ id`
  have hpb : (T.pullback h hh).IsPullbackOf (T.pullback (sigmaDescMap (sumDesc h)) hg) sumInl := by
    refine ⟨?_, ?_⟩
    · change T.I.pullback h h.contMDiff = (T.I.pullback _ (sigmaDescMap (sumDesc
        h)).contMDiff).pullback sumInl sumInl.contMDiff
      rw [AnalyticManifold.IdealSheaf.pullback_comp, hgk]
    · change T.F.comap ⇑h =
        (T.F.comap ⇑(sigmaDescMap (sumDesc h))).comap ⇑(sumInl (N := N) (M := M))
      rw [HypersurfaceFamily.comap_comap, hfun]
  -- the two commutation clauses
  have h1 : B.seq (T.pullback (sigmaDescMap (sumDesc h)) hg) hTsum =
      (B.seq T hT).pullback (sigmaDescMap (sumDesc h)) hg :=
    CommutesWithSurjectiveLocalIsos.commutesWith hB.1 hg hgs (T.isPullbackOf_pullback _ _) hT hTsum
  have h2 := CommutesWithOpenEmbeddings.seq_eq hB.2 hk hpb hTsum hT'
  rw [h2, h1, AnalyticManifold.BlowUpSequence.pullback_comp _ _ hg _ hk.1,
    AnalyticManifold.BlowUpSequence.pullback_congr _ hgk _ hh]

end Manifold.AnalyticBlowUpSequenceAssignment

namespace AnalyticManifold.BlowUpSequence

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-! ### Centres of a sequence of order `≥ m` lie over the cosupport, and the lifts cover -/

variable {M N : AnalyticManifold.{u} 𝕜 E}

/-- A point of a stage of `L` whose composite blow-down
lies in the image of the local isomorphism `h` lies in the image of the lift of `h` to that stage
— `exists_liftStep_eq` at each step. -/
theorem mem_range_pullbackLift_of_stageMap_mem : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)
    (i : ℕ) (hi : i < L.length + 1) (hi' : i < (L.pullback h hh).length + 1)
    (p : L.toSuccession.stage ⟨i, hi⟩),
    L.toSuccession.stageMapAux i hi p ∈ Set.range h →
      p ∈ Set.range (L.pullbackLiftAux h hh i hi hi')
  | _, _, nil _, h, hh, 0, _, _, p, hp => hp
  | _, _, cons _ _, h, hh, 0, _, _, p, hp => hp
  | _, _, cons hY rest, h, hh, i + 1, hi, hi', p, hp => by
    rw [stageMapAux_cons_succ hY rest i hi p] at hp
    obtain ⟨b, hb⟩ := hp
    obtain ⟨q, hq⟩ := exists_liftStep_eq h hh hY _ hb
    exact mem_range_pullbackLift_of_stageMap_mem rest (liftStep h hh hY)
      (isLocalDiffeomorph_liftStep h hh hY) i (Nat.lt_of_succ_lt_succ hi)
      (Nat.lt_of_succ_lt_succ hi') p ⟨q, hq⟩
  | _, _, nil _, _, _, i + 1, hi, _, _, _ => absurd hi (by change ¬ i + 1 < 0 + 1; omega)

/-- The pull-back of a list with no
empty centre along a local analytic isomorphism whose lifts cover the centres has no empty
centre — the counterpart of `noEmptyCenters_pullback_of_centersInRange`
(`Hironaka.Scheme.BlowUpSequence.CentersCosupport`). -/
theorem noEmptyCenters_pullback_of_subset_range : ∀ {M N : AnalyticManifold.{u} 𝕜 E}
    (L : BlowUpSequence ψ₀ M) (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h),
    L.NoEmptyCenters →
    (∀ (i : ℕ) (hi : i < L.length) (hi' : i < (L.pullback h hh).length + 1),
      (L.toSuccession.center ⟨i, hi⟩).support ⊆
        Set.range (L.pullbackLiftAux h hh i (Nat.lt_succ_of_lt hi) hi')) →
    (L.pullback h hh).NoEmptyCenters
  | _, _, nil _, _, _, _, _ => noEmptyCenters_nil
  | _, _, cons hY rest, h, hh, hL, hsub => by
    rw [pullback_cons, noEmptyCenters_cons_iff]
    obtain ⟨hne, hrest⟩ := (noEmptyCenters_cons_iff hY rest).mp hL
    refine ⟨fun h0 => ?_, noEmptyCenters_pullback_of_subset_range rest _ _ hrest
      fun i hi hi' => hsub (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi')⟩
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hyr : y ∈ Set.range h := hsub 0 (Nat.succ_pos _) (Nat.succ_pos _) (by
      change y ∈ hY.idealSheaf.support
      rw [hY.cosupport_idealSheaf]
      exact hy)
    obtain ⟨x, rfl⟩ := hyr
    exact (Set.eq_empty_iff_forall_notMem.mp h0) x hy

end AnalyticManifold.BlowUpSequence

namespace AnalyticManifold.FiniteSuccession

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} {S : FiniteSuccession M}
  {I E₀ : IdealSheaf M} {m : ℕ}

/-- As in the proof of [Kol07, Theorem 97]: along a smooth blow-up sequence of order `≥ m` for
`(𝓘, m)`, a point of order `≥ m` for the marked transform at stage `i`
lies over a point of order `≥ m` for `𝓘` — over the centre the order along the centre is `≥ m`, off
the centre the marked transform is the pull-back of the previous one along a local isomorphism —
the analytic counterpart of `le_ord_stageMap_of_mem_center` for schemes
(`Hironaka.Scheme.BlowUpSequence.CentersCosupport`). -/
theorem IsOfOrderGe.le_ord_stageMap (hge : S.IsOfOrderGe I m E₀) (i : Fin (S.length + 1))
    (x : S.stage i) (hx : (m : ℕ∞) ≤ (S.markedTransformSeq I m i).ord x) :
    (m : ℕ∞) ≤ I.ord (S.stageMap i x) := by
  have _hfd := hfd
  induction i using Fin.induction with
  | zero => exact hx
  | succ i ih =>
    rw [markedTransformSeq_succ] at hx
    change (m : ℕ∞) ≤ I.ord (S.stageMap i.castSucc (S.map i x))
    refine ih (S.map i x) ?_
    have hk : ∀ a ∈ (S.center i).support, (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal
        (S.isClosedSubmanifold_center i).idealSheaf (S.markedTransformSeq I m i.castSucc) a := by
      rw [S.idealSheaf_center]
      exact fun a ha => hge.le_ordAlong i ha
    by_cases hmem : S.map i x ∈ (S.center i).support
    · refine (hge.le_ordAlong i hmem).trans ?_
      rw [← S.idealSheaf_center i]
      exact ordAlong_le_ord (S.isClosedSubmanifold_center i) _ hmem
    · have hst := birationalTransform_stalkIdeal_of_notMem (S.isClosedSubmanifold_center i)
        (S.isBlowUp_map i) hk hmem
      have h1 : (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center i)
          (S.isBlowUp_map i) ⟨S.markedTransformSeq I m i.castSucc, m⟩).I.ord x =
          ((S.markedTransformSeq I m i.castSucc).pullback (S.map i)
            (S.isBlowUp_map i).contMDiff).ord x := by
        unfold Manifold.IdealSheaf.ord
        rw [hst]
      have h2 : ((S.markedTransformSeq I m i.castSucc).pullback (S.map i)
          (S.isBlowUp_map i).contMDiff).ord x =
          (S.markedTransformSeq I m i.castSucc).ord (S.map i x) :=
        IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ _
          ((S.isBlowUp_map i).isLocalDiffeomorphOn_compl ⟨x, hmem⟩)
      exact hx.trans_eq (h1.trans h2)

/-- By the derivative inequality of [Kol07, Corollary 77]
(`markedTransformSeq_iteratedDeriv_le_of_forall_lt` with `j = m − 1`): a smooth blow-up sequence
of order `≥ m` for `(𝓘, m)` is of order `≥ 1` for `(MC(𝓘), 1)` in the containment form — each centre
lies in `cosupp(𝓘_i, m) = supp D^{m-1}(𝓘_i)`, which lies in the support of the marked transform
of `(MC(𝓘), 1)`. -/
theorem IsOfOrderGe.isMarkedOne (hm : 1 ≤ m) (hge : S.IsOfOrderGe I m E₀) :
    S.IsMarkedOne (I.iteratedDeriv (m - 1)) := by
  have _hfd := hfd
  intro i a ha
  have hle := markedTransformSeq_iteratedDeriv_le_of_forall_lt (S := S) (I := I)
    (Nat.sub_le m 1) i.castSucc fun i' _ a ha => hge.le_ordAlong i' ha
  rw [Nat.sub_sub_self hm] at hle
  have hmem : a ∈ ((S.markedTransformSeq I m i.castSucc).iteratedDeriv (m - 1)).support := by
    rw [IdealSheaf.support_iteratedDeriv _ hm]
    refine (hge.le_ordAlong i ha).trans ?_
    rw [← S.idealSheaf_center i]
    exact ordAlong_le_ord (S.isClosedSubmanifold_center i) _ ha
  exact (IdealSheaf.mem_support _).mpr fun hA =>
    (IdealSheaf.mem_support _).mp hmem (top_le_iff.mp (hA ▸ IdealSheaf.le_def.mp hle a))

end AnalyticManifold.FiniteSuccession

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The centres of a list of order `≥ m` for `(𝓘, m)` lie in the images
of the lifts of a local analytic isomorphism whose image contains `cosupp(𝓘, m)`. -/
theorem _root_.AnalyticManifold.BlowUpSequence.centers_subset_range_pullbackLiftAux
    {N : AnalyticManifold.{u} 𝕜 E}
    (L : AnalyticManifold.BlowUpSequence ψ₀ M) {I : AnalyticManifold.IdealSheaf M}
        {E₀ : AnalyticManifold.IdealSheaf M} {m : ℕ}
    (hge : L.toSuccession.IsOfOrderGe I m E₀) (h : AnalyticMap N M)
    (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) (hcov : {x | (m : ℕ∞) ≤ I.ord x} ⊆ Set.range h)
    (i : ℕ) (hi : i < L.length) (hi' : i < (L.pullback h hh).length + 1) :
    (L.toSuccession.center ⟨i, hi⟩).support ⊆
      Set.range (L.pullbackLiftAux h hh i (Nat.lt_succ_of_lt hi) hi') := by
  have := finiteDimensional_of_chartIso ψ₀
  intro a ha
  refine AnalyticManifold.BlowUpSequence.mem_range_pullbackLift_of_stageMap_mem L h hh i _ hi' a
      (hcov ?_)
  change (m : ℕ∞) ≤ I.ord (L.toSuccession.stageMap ⟨i, Nat.lt_succ_of_lt hi⟩ a)
  refine hge.le_ord_stageMap ⟨i, Nat.lt_succ_of_lt hi⟩ a ?_
  refine (hge.le_ordAlong ⟨i, hi⟩ ha).trans ?_
  rw [← L.toSuccession.idealSheaf_center ⟨i, hi⟩]
  exact ordAlong_le_ord (L.toSuccession.isClosedSubmanifold_center ⟨i, hi⟩) _ ha

end Manifold
