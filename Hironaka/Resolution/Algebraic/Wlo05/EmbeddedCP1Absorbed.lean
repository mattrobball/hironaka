/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1For
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealCorners
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedClaimCoverTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedComponentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.TakeLast
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP1 at the absorbing stage of the loop

The loop `bedAux` of the embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`)
truncates the run of `BMO_1` before its first absorbing blow-up, the stage `Nat.find h` at which
some member `c ∈ C` has its strict transform contained in the centre. For such a member, the
statement CP1 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) along the run
(`cp1For_bmoOneRun_of_cp1BMOAt`, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Tower`) gives the
chain form of the marked transform along the strict transform `c̃` at that stage; carried to the
last stage of the truncation (whose data are those of the run at that stage), this is
`chainRelativeAt_of_absorbed_of_cp1For`. And the chain form forces the strict transforms of the
other members off `c̃` at that stage (`disjoint_strictTransformSeq_of_absorbed_of_chainRelativeAt`):
at a common point `p`, the prime `(c̃')_p` contains `I_p = M⁰ · chainIdeal` and none of the
monomials (the lifted generic points of the members lie on no member of the boundary), hence every
chain equation (`span_range_le_of_mul_chainIdeal_le_prime`), hence `(c̃)_p`; so the generic point of
`c̃'` lies on `c̃`, and both being generic points of `V(I)` at that stage (the proof of [Kol07,
Corollary 22]) they coincide, giving `c' = c` (`eq_of_strictTransformSeq_eq`). This is the absorbing
moment of the proof of [Wlo05, Theorem 4.7.1], with the chain form in place of Włodarczyk's Claim.
Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Main`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData IsLocalRing

namespace Hironaka.Resolution

/-! ### Bookkeeping across the truncation's stage identification -/

/-- Heterogeneous equality of ideal sheaves gives heterogeneous equality of their supports. -/
theorem heq_support {Y Y' : Scheme.{u}} (h : Y = Y') {I : Y.IdealSheafData} {I' : Y'.IdealSheafData}
    (hI : HEq I I') : HEq I.support I'.support := by
  subst h
  rw [eq_of_heq hI]

/-- Disjointness of closed sets transports across an equality of schemes. -/
theorem disjoint_of_heq {Y Y' : Scheme.{u}} (h : Y = Y') {A B : Closeds Y} {A' B' : Closeds Y'}
    (hA : HEq A A') (hB : HEq B B') (hd : Disjoint A' B') : Disjoint A B := by
  subst h
  rw [eq_of_heq hA, eq_of_heq hB]
  exact hd

variable {k : Type u} [Field k] [CharZero k]

open Classical in
/-- From CP1 along `bmoOneRun` for the generic points of the members to the chain form at the
absorbing stage of the loop: `Nat.find h` is the first containing index, and the data of the
truncation at its last stage are the data of the run at that stage. -/
theorem chainRelativeAt_of_absorbed_of_cp1For (T : MarkedTriple k) (hm : T.m = 1)
    (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C)
    (h : ∃ n, HasAbsorptionAt T hm C n)
    {c : T.X.left.IdealSheafData} (hcC : c ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) c (Nat.find h))
    (hcp : ∀ η ∈ T.I.support.genericPoints, (∀ i, η ∉ (T.E.component i).support) →
      T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η →
      CP1For (bmoOneRun T hm) T.I T.E η) :
    ∀ p ∈ (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support,
      ChainRelativeAt (stageTriple T hm (Nat.find h)).E (stageTriple T hm (Nat.find h)).I
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) p := by
  obtain ⟨η, hη, rfl, hηE, hIc, hmin⟩ :=
    remaining_spec (T := T) (hm := hm) (C := C) (h := h) hinv hcC
  have hlt : Nat.find h < (bmoOneRun T hm).length := find_lt_length T hm C h
  have hstage := hcp η hη hηE hIc ⟨Nat.find h, hlt⟩ hcc hmin
  have hI' : (bmoOneRun T hm).markedTransformSeq T.I T.m ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ =
      (bmoOneRun T hm).markedTransformSeq T.I 1 ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ := by
    rw [hm]
  exact forall_chainRelativeAt_of_heq (stage_take_last _ hlt.le)
    (totalTransformSeq_take_last_heq _ T.E hlt.le)
    ((markedTransformSeq_take_last_heq _ T.I T.m hlt.le).trans (heq_of_eq hI'))
    (strictTransformSeq_take_last_heq _ _ hlt.le) hstage

open Classical in
/-- **The disjointness of the other members from the absorbed one**, from the local chain form at
every point of the strict transform `c̃` of the absorbed member: at a common point `p` the prime
`(c̃')_p ⊇ I_p = M⁰ · chainIdeal` with the monomials not in the prime (the lifted generic point of
`c'` lies on no member of the boundary) contains the equations of the chain, hence `(c̃)_p`, so the
generic point of `c̃'` lies on `c̃`; both are generic points of `V(I)` at that stage (the proof of
[Kol07, Corollary 22]), so they coincide and `c' = c`. -/
theorem disjoint_strictTransformSeq_of_absorbed_of_chainRelativeAt (T : MarkedTriple k)
    (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData) (hinv : InvCE T.I T.E C)
    (h : ∃ n, HasAbsorptionAt T hm C n) {c : T.X.left.IdealSheafData} (hcC : c ∈ C)
    (hcc : CenterContains (bmoOneRun T hm) c (Nat.find h))
    (hloc : ∀ p ∈ (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support,
      ChainRelativeAt (stageTriple T hm (Nat.find h)).E (stageTriple T hm (Nat.find h)).I
        (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)) p)
    {c' : T.X.left.IdealSheafData} (hc'C : c' ∈ C) (hne : c' ≠ c) :
    Disjoint (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c' (Fin.last _)).support
      (((bmoOneRun T hm).take (Nat.find h)).strictTransformSeq c (Fin.last _)).support := by
  obtain ⟨η, hη, rfl, hηE, hIc, hmin⟩ :=
    remaining_spec (T := T) (hm := hm) (C := C) (h := h) hinv hcC
  obtain ⟨η', hη', rfl, hη'E, hI'c, hmin'⟩ :=
    remaining_spec (T := T) (hm := hm) (C := C) (h := h) hinv hc'C
  have hlt : Nat.find h < (bmoOneRun T hm).length := find_lt_length T hm C h
  have hLN : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  -- the generic lifts of both members at the absorbing stage
  obtain ⟨ξ, hξ⟩ := exists_genericLift (bmoOneRun T hm) T.I T.E 1 hη hηE hIc
    ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ hmin
  obtain ⟨ξ', hξ'⟩ := exists_genericLift (bmoOneRun T hm) T.I T.E 1 hη' hη'E hI'c
    ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ hmin'
  -- the chain form at the stage itself
  have hI' : (bmoOneRun T hm).markedTransformSeq T.I T.m ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ =
      (bmoOneRun T hm).markedTransformSeq T.I 1 ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ := by
    rw [hm]
  have hloc' : ∀ p ∈ ((bmoOneRun T hm).strictTransformSeq (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {η}))
      ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩).support,
      ChainRelativeAt
        ((bmoOneRun T hm).totalTransformSeq T.E ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩)
        ((bmoOneRun T hm).markedTransformSeq T.I 1 ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩)
        ((bmoOneRun T hm).strictTransformSeq (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            {η}))
          ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩) p :=
    forall_chainRelativeAt_of_heq (stage_take_last _ hlt.le).symm
      (totalTransformSeq_take_last_heq _ T.E hlt.le).symm
      ((markedTransformSeq_take_last_heq _ T.I T.m hlt.le).trans (heq_of_eq hI')).symm
      (strictTransformSeq_take_last_heq _ _ hlt.le).symm hloc
  -- disjointness at the stage, transported to the truncation
  refine disjoint_of_heq (stage_take_last _ hlt.le)
    (heq_support (stage_take_last _ hlt.le) (strictTransformSeq_take_last_heq _ _ hlt.le))
    (heq_support (stage_take_last _ hlt.le) (strictTransformSeq_take_last_heq _ _ hlt.le)) ?_
  rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot,
    Set.eq_empty_iff_forall_notMem]
  rintro p ⟨hp', hp⟩
  rw [hξ'.strict_eq] at hp'
  -- the chain form at `p`
  obtain ⟨n₀, z, cE, r, σ, a, b, ⟨_, _, hcmem, _, _, ha, hΓ⟩, hb, hI⟩ := hloc' p hp
  -- the prime `(c̃')_p`, containing `I_p` and none of the boundary coordinates
  have hξ'p : ξ' ⤳ p := by
    rw [← hξ'.strict_eq] at hp'
    exact hξ'.isGenericPoint_strictTransformSeq.specializes hp'
  have hP : ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ'})).stalkIdeal p).IsPrime :=
    isPrime_stalkIdeal_vanishingIdeal_closure hξ'p
  have hIle : (bmoOneRun T hm).markedTransformSeq T.I 1 ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ ≤
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ'}) := by
    apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
    rw [← SetLike.coe_subset_coe, Closeds.coe_closure]
    exact ((bmoOneRun T hm).markedTransformSeq T.I 1 _).support.isClosed.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hξ'.mem_genericPoints.1)
  have hIP := Scheme.IdealSheafData.stalkIdeal_mono hIle p
  have hzP : ∀ j, z (cE j) ∉ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      {ξ'})).stalkIdeal p := by
    intro j hj
    have hEle : (((bmoOneRun T hm).totalTransformSeq T.E
        ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩).component j.1).stalkIdeal p ≤
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ'})).stalkIdeal p := by
      rw [hcmem j]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hj
    exact notContainedInMembers_vanishingIdeal_closure _ hξ'.notMem p hp' j.1 j.2 hEle
  have hmono : ∀ e : Fin n₀ → ℕ, (∀ i, e i ≠ 0 → i ∈ Set.range cE) →
      monomialOf z e ∉ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
          {ξ'})).stalkIdeal p := by
    intro e he hmem
    unfold monomialOf at hmem
    have := hP
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    have hei : e i ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hi
      exact hP.ne_top ((Ideal.eq_top_iff_one _).mpr hi)
    obtain ⟨j, rfl⟩ := he i hei
    exact hzP j (hP.mem_of_pow_mem _ hi)
  -- the ring core: `(c̃)_p ⊆ (c̃')_p`
  have hle : ((bmoOneRun T hm).strictTransformSeq (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {η}))
      ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩).stalkIdeal p ≤
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ'})).stalkIdeal p := by
    rw [hΓ]
    refine span_range_le_of_mul_chainIdeal_le_prime hP (z ∘ σ) (fun i => monomialOf z (a i))
      (fun i => hmono (a i) (ha i)) (monomialOf z b) (hmono b hb) ?_
    rw [← hI]
    exact hIP
  -- so the generic point of `c̃'` lies on `c̃`, and the two generic points coincide
  have hξ'c : ξ' ∈ ((bmoOneRun T hm).strictTransformSeq (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure {η}))
      ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩).support := by
    rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
        Scheme.IdealSheafData.stalkIdeal_specializes _ hξ'p]
    calc _ ≤ ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ'})).stalkIdeal p).map
          (((bmoOneRun T hm).stage ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩).presheaf.stalkSpecializes
            hξ'p).hom := Ideal.map_mono hle
      _ = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ'})).stalkIdeal ξ' :=
          (Scheme.IdealSheafData.stalkIdeal_specializes _ hξ'p).symm
      _ = maximalIdeal _ := Hironaka.BMO.stalkIdeal_vanishingIdeal_closure_self ξ'
  have hsp : ξ ⤳ ξ' := hξ.isGenericPoint_strictTransformSeq.specializes hξ'c
  have heq : ξ = ξ' := hξ'.mem_genericPoints.2 hξ.mem_genericPoints.1 hsp
  apply hne
  refine eq_of_strictTransformSeq_eq (T := T) (hm := hm) (C := C) (h := h) hinv hc'C hcC ?_
  change (bmoOneRun T hm).strictTransformSeq _ ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩ =
    (bmoOneRun T hm).strictTransformSeq _ ⟨Nat.find h, Nat.lt_succ_of_lt hlt⟩
  rw [hξ'.strict_eq, hξ.strict_eq, heq]

end Hironaka.Resolution
