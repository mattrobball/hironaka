/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFirstCenterEq
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining
import Hironaka.Resolution.Algebraic.Wlo05.FirstCenterLocalIso
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.StalkProdDisjointSupport
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The isolated state is protected for the absorbed member

At the first absorbing stage `Nat.find h` of the loop, the strict transform `Γ = c̃` of an absorbed
member is: smooth over `k` and integral (the stalks of the centre are those of `Γ` at every point
of `Γ`, `stalkIdeal_center_eq_strictTransformSeq_of_first` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedFirstCenterEq`, and the centre has simple normal
crossings with the boundary by clause (3′) of [Kol07, Definition 66], so `Γ` has snc and is smooth;
integrality by `isIntegral_strictTransformSeq_of_le_firstCenterIndex`); disjoint from the strict
transforms of the remaining members (CP1, `disjoint_strictTransformSeq_of_absorbed`); and the
isolated ideal `I_n : I_Γ` has the K-shape along `Γ` (CP1 gives the chain form of `I_n`, CP2
`chainRelativeKAt_colon` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainColon` the K-shape of
the colon by `Γ`, and at a point of `Γ` the reduced ideal `I_Γ` of the absorbed strict transforms
has the stalk of `Γ`, the absorbed strict transforms being integral and pairwise disjoint by CP1).
This is `protectedState_isolatedTriple_of_absorbed`, the entry into the invariant CP5
(`ProtectedState`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`). It replaces,
without the false hypothesis `ClaimKC`, the isolation step of the proof of [Wlo05, Theorem 4.7.1].
Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCPBridge`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

/-! ### Bookkeeping -/

variable {X : Scheme.{u}}

/-- The K-shape depends on `K` only through its stalk at `p`. -/
theorem chainRelativeKAt_congr_stalkIdeal_K {E : DivisorFamily X} {K K' Γ : X.IdealSheafData}
    {p : X} (h : K.stalkIdeal p = K'.stalkIdeal p) :
    ChainRelativeKAt E K Γ p ↔ ChainRelativeKAt E K' Γ p := by
  unfold ChainRelativeKAt
  rw [h]

/-- Integrality of the closed subscheme transports across an equality of schemes. -/
theorem isIntegral_of_heq {Y Y' : Scheme.{u}} (h : Y = Y') {I : Y.IdealSheafData}
    {I' : Y'.IdealSheafData} (hI : HEq I I') (hint : IsIntegral I'.subscheme) :
    IsIntegral I.subscheme := by
  subst h
  rw [eq_of_heq hI]
  exact hint

variable {k : Type u} [Field k] [CharZero k]

/-- The strict transform of `c̄` has simple normal crossings with the boundary at a stage whose
centre contains it while no earlier centre does (clause (c) of [Wlo05, Theorem 1.0.2] at a first
containing stage; the unconditional form of `hasSncWith_strictTransformSeq_of_absorbed`):
[Kol07, Definition 24 (4)] read at its points, where its stalks are those of the centre
(`stalkIdeal_center_eq_strictTransformSeq_of_first`) and the centre has snc with the boundary
([Kol07, Definition 66 (3′)]). -/
theorem hasSncWith_strictTransformSeq_of_first [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f] {S : BlowUpSequence X} {I : X.IdealSheafData}
    {E : DivisorFamily X} (hS : S.IsOrderGeSeq f I 1 E) {η : X} (hη : η ∈ I.support.genericPoints)
    (hηE : ∀ i, η ∉ (E.component i).support)
    (hIc : I.stalkIdeal η = (IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η)
        (j : Fin S.length)
    (hle : S.center j ≤ S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) j.castSucc)
    (hmin : ∀ l < j.val, ¬ CenterContains S (IdealSheafData.vanishingIdeal (Closeds.closure
        {η})) l) :
    (S.totalTransformSeq E j.castSucc).HasSncWith
      (S.strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η})) j.castSucc) := by
  intro p hp
  obtain ⟨m, z, hsncAt, s, hDs⟩ := (hS.2 j).1 p (IdealSheafData.support_antitone hle hp)
  refine ⟨m, z, hsncAt, s, ?_⟩
  rw [← stalkIdeal_center_eq_strictTransformSeq_of_first f n hS le_rfl hη hηE hIc j hle hmin p hp]
  exact hDs

section Entry

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (hinv : InvCE T.I T.E C) (h : ∃ n, HasAbsorptionAt T hm C n)

open Classical in
include hinv in
/-- At the loop's stage, the truncated strict transform of every member is integral (no centre
before the stage contains it, `isIntegral_strictTransformSeq_of_le_firstCenterIndex`). -/
theorem isIntegral_take_strictTransformSeq_of_mem {c : T.X.left.IdealSheafData} (hc : c ∈ C) :
    IsIntegral
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).subscheme := by
  obtain ⟨η, -, rfl, -, -, hmin⟩ := remaining_spec (T := T) (hm := hm) (C := C) (h := h) hinv hc
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hlt : Nat.find h < (bmoOneRun T hm).length := find_lt_length T hm C h
  have := isIntegral_subscheme_vanishingIdeal_closure η
  refine isIntegral_of_heq (stage_take_last _ hlt.le) (strictTransformSeq_take_last_heq _ _ hlt.le)
    (isIntegral_strictTransformSeq_of_le_firstCenterIndex (bmoOneRun T hm)
      (IdealSheafData.vanishingIdeal (Closeds.closure {η})) ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ ?_)
  exact le_firstCenterIndex_of_forall_lt_not _ _ hlt.le hmin

open Classical in
include hinv in
/-- The truncated strict transforms of the members absorbed at the stage of the loop are pairwise
disjoint (CP1). -/
theorem pairwise_disjoint_take_strictTransformSeq_absorbed :
    (((C.filter fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)) :
        Finset T.X.left.IdealSheafData) : Set T.X.left.IdealSheafData).Pairwise fun a b =>
      Disjoint (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq a (Fin.last _)).support
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq b (Fin.last _)).support := by
  intro a ha b hb hab
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  exact disjoint_strictTransformSeq_of_absorbed T hm C hinv h hb.1 hb.2 ha.1 hab

open Classical in
include hinv in
/-- At a point of an absorbed member's truncated strict transform `Γ`, the reduced ideal of the
union of the absorbed strict transforms has `Γ`'s stalk (integral, pairwise disjoint). -/
theorem stalkIdeal_vanishingIdeal_absorbed_of_mem {c : T.X.left.IdealSheafData} (hcC : c ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) c (Nat.find h))
    {p : ((bmoOneRun T hm).take (Nat.find h)).stage (Fin.last _)}
    (hp : p ∈ (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support) :
    (IdealSheafData.vanishingIdeal (⨆ c' ∈ C.filter (fun c' => CenterContains (bmoOneRun T hm) c'
        (Nat.find h)),
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c'
          (Fin.last _)).support)).stalkIdeal p =
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).stalkIdeal p := by
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hLN' : IsLocallyNoetherian (((bmoOneRun T hm).take (Nat.find h)).stage (Fin.last _)) :=
    ((stageTriple T hm (Nat.find h)).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  rw [IdealSheafData.vanishingIdeal_iSup_support_eq_prod _ _ (fun c' hc' => ?_)
    (pairwise_disjoint_take_strictTransformSeq_absorbed T hm C hinv h)]
  · exact IdealSheafData.stalkIdeal_finset_prod_eq_of_mem_of_pairwise_disjoint _ _
      (pairwise_disjoint_take_strictTransformSeq_absorbed T hm C hinv h)
      (Finset.mem_filter.mpr ⟨hcC, hcc⟩) hp
  · have := isIntegral_take_strictTransformSeq_of_mem T hm C hinv h (Finset.mem_filter.mp hc').1
    rw [IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]

open Classical in
include hinv in
/-- **The entry into the protected state**: the isolated state at the first absorbing stage of the
loop is protected for the absorbed member — its strict transform is smooth and integral, has snc
with the boundary, misses the strict transforms of the remaining members, and the isolated ideal
has the K-shape along it. -/
theorem protectedState_isolatedTriple_of_absorbed {c : T.X.left.IdealSheafData} (hcC : c ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) c (Nat.find h)) :
    ProtectedState (isolatedTriple T hm C (Nat.find h)) (remainingComponents T hm C (Nat.find h))
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) := by
  obtain ⟨η, hη, rfl, hηE, hIc, hmin⟩ :=
    remaining_spec (T := T) (hm := hm) (C := C) (h := h) hinv hcC
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hNS : NoetherianSpace T.X.left := Hironaka.BD.noetherianSpace_triple T.toTriple
  have hN : IsNoetherian T.X.left :=
    { toIsLocallyNoetherian := hLN, toCompactSpace := inferInstance }
  have hPF : PerfectField k := PerfectField.ofCharZero
  obtain ⟨d, hd⟩ := T.smoothOfRelativeDimension
  have hsmd : SmoothOfRelativeDimension d (T.X.left ↘ Spec (.of k)) := hd
  have hlt : Nat.find h < (bmoOneRun T hm).length := find_lt_length T hm C h
  have hrun : (bmoOneRun T hm).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E := by
    have h0 := isOrderGeSeq_bmoOneRun T hm
    rwa [hm] at h0
  have hle : (bmoOneRun T hm).center ⟨Nat.find h, hlt⟩ ≤
      (bmoOneRun T hm).strictTransformSeq (IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        (⟨Nat.find h, hlt⟩ : Fin (bmoOneRun T hm).length).castSucc := hcc.2
  -- the structure map of the stage and the truncation
  have hLN' : IsLocallyNoetherian (((bmoOneRun T hm).take (Nat.find h)).stage (Fin.last _)) :=
    ((stageTriple T hm (Nat.find h)).X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hsm : Smooth (((bmoOneRun T hm).take (Nat.find h)).stageMap (Fin.last _) ≫
      (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := d)
      (isOrderGeSeq_take _ _ _ _ (isOrderGeSeq_bmoOneRun T hm) (Nat.find h)).1
      (Fin.last _)
  -- the snc of the strict transform at the stage, transported to the truncation
  have hsnc : (((bmoOneRun T hm).take (Nat.find h)).totalTransformSeq T.E (Fin.last _)).HasSncWith
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})) (Fin.last _)) :=
    hasSncWith_of_heq (stage_take_last _ hlt.le).symm
      (totalTransformSeq_take_last_heq _ T.E hlt.le).symm
      (strictTransformSeq_take_last_heq _ _ hlt.le).symm
      (hasSncWith_strictTransformSeq_of_first (T.X.left ↘ Spec (.of k)) d hrun hη hηE hIc
        ⟨Nat.find h, hlt⟩ hle hmin)
  refine ⟨?_, isIntegral_take_strictTransformSeq_of_mem T hm C hinv h hcC, hsnc, ?_, ?_⟩
  · -- smooth
    exact HasSncWith.smooth (((bmoOneRun T hm).take (Nat.find h)).stageMap (Fin.last _) ≫
      (T.X.left ↘ Spec (.of k))) hsnc
  · -- disjoint from the remaining members
    intro c' hc'
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc'
    rw [Finset.mem_filter] at hc₀
    have hne : c₀ ≠ IdealSheafData.vanishingIdeal (Closeds.closure {η}) := fun heq => hc₀.2
        (heq ▸ hcc)
    exact disjoint_strictTransformSeq_of_absorbed T hm C hinv h hcC hcc hc₀.1 hne
  · -- the K-shape of the isolated ideal along `Γ`
    intro p hp
    have hchain := chainRelativeAt_of_absorbed T hm C hinv h hcC hcc p hp
    have hK := chainRelativeKAt_colon (((bmoOneRun T hm).take (Nat.find h)).stageMap (Fin.last _) ≫
      (T.X.left ↘ Spec (.of k))) hchain
    refine (chainRelativeKAt_congr_stalkIdeal_K ?_).mp hK
    have hLN'' : IsLocallyNoetherian (stageTriple T hm (Nat.find h)).X.left := hLN'
    have e1 := IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian (X := (stageTriple T hm
        (Nat.find h)).X.left)
      (stageTriple T hm (Nat.find h)).I
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq
        (IdealSheafData.vanishingIdeal (Closeds.closure {η})) (Fin.last _)) p
    have e2 := IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian (X := (stageTriple T hm
        (Nat.find h)).X.left)
      (stageTriple T hm (Nat.find h)).I
      (IdealSheafData.vanishingIdeal (⨆ c' ∈ C.filter (fun c' => CenterContains (bmoOneRun T hm) c'
          (Nat.find h)),
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c' (Fin.last _)).support)) p
    have hA := stalkIdeal_vanishingIdeal_absorbed_of_mem T hm C hinv h hcC hcc hp
    change ((stageTriple T hm (Nat.find h)).I.colon
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq
          (IdealSheafData.vanishingIdeal (Closeds.closure {η})) (Fin.last _))).stalkIdeal p =
      ((stageTriple T hm (Nat.find h)).I.colon
        (IdealSheafData.vanishingIdeal (⨆ c' ∈ C.filter
            (fun c' => CenterContains (bmoOneRun T hm) c' (Nat.find h)),
          (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c'
            (Fin.last _)).support))).stalkIdeal p
    rw [e1, e2]
    exact congrArg (fun J : Ideal ((stageTriple T hm (Nat.find h)).X.left.presheaf.stalk p) =>
      Submodule.colon ((stageTriple T hm (Nat.find h)).I.stalkIdeal p) (J : Set _)) hA.symm

end Entry

end Hironaka.Resolution
