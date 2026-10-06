/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.OrderSeq
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Realize
import Hironaka.Resolution.Algebraic.Snc.ComponentStalks
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Split
import Hironaka.Scheme.BlowUpSequence.DerivativeSequence
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.MarkedMono
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 along Step 3 at the mark `1`

Step 3 of the proof of [Kol07, Theorem 107] (item 111, Step 3) reduces the order of the monomial
part `M(I) = 𝒪(−∑ a_j E^j)`; here it is run at the mark `1`. Each centre of the geometric Step 3
(`PieceFamily.realize`, `Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces`) is, at each of
its points `q`, the face of the stage family through `q` selected by the rule of Step 3 — an
intersection of members of total exponent `≥ 1` (`realizeAux_center`, `exists_center_realize_eq`,
`realize_invariant`, `stalkIdeal_centerOf_eq_faceIdeal`, `m_le_total_of_mem_choice`). For the
statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`): in any chain coordinates `(z, c, σ,
a, b)` at `q` ([Kol07, Definition 24]) the stalk of the face is `(z_s)` with `s` a set of
coordinates of members (`exists_stalkIdeal_faceIdeal_eq_span`, `stalkIdeal_vanishingIdeal_piece`: a
piece through `q` is its member near `q`, whose coordinate is `z_{c j}`), which is the stratum of
level `0`. Its admissibility condition (★) — some `z_k`, `k ∈ s`, carries `b_k ≠ 0` — is read at the
piece `c₀` of positive exponent: the stage monomial has order `a_{c₀}` at the generic point `η₀` of
`c₀` (`ord_monomial_eq_total`, `faceAt_eq_singleton_of_mem_genericPoints`); the marked transform of
the current ideal lies below the stage monomial (`markedTransformSeq_mono`,
`markedTransformSeq_realize`), so it has order `≥ a_{c₀} ≥ 1` there, and finite order
(`ord_ne_top_of_isNonzeroEverywhere`); and the exponent `b_{c j}` of either chain shape at the
coordinate of a member is the order of the current ideal at that member's generic point — the fine
split `I = M(I) · N(I)` of [Kol07, Definition–Lemma 110] read exponent by exponent
(`toNat_ord_eq_of_stalkIdeal_eq_span_mul`, from `stalkIdeal_monomialPart_eq_span_prod` and the
uniqueness `eq_of_span_prod_pow_mul_eq` of `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Split`,
with the chain part `stalkIdeal_nonmonomialPart_of_kShape` or
`stalkIdeal_nonmonomialPart_of_iShape`). The same stratum serves both shapes, so the I-shape clause
is the first alternative.

The general form `cp3For_realize_of_le` is stated for any piece family realizing the boundary and
any nonzero ideal below the marked monomial ideal; `cp3For_step3Seq` is its instance through the
bridge `monomial_exponentAt_step3Family`
(`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Input`) and `I ⊆ M(I)`. This argument is
not in the literature. Used in `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData Hironaka Scheme
  IsLocalRing BlowUpSequence Hironaka.BMO Hironaka.BMO.Snc Hironaka.Monomial
  Hironaka.Monomial.PieceFamily

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Exponent

variable {X : Scheme.{u}}

/-- The fine split of [Kol07, Definition–Lemma 110] read exponent by exponent: the exponent of a
chain shape at the coordinate of a member is the order of the ideal at the generic point of that
member through the point — `M(K)_p` is the monomial in the coordinates of the members with the
orders as exponents, `N(K)_p` is the chain part, and the monomial factor is unique. -/
theorem toNat_ord_eq_of_stalkIdeal_eq_span_mul [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
    (n₀ : ℕ) [SmoothOfRelativeDimension n₀ f] {E : DivisorFamily X} (hE : E.IsSnc)
    {K : X.IdealSheafData} (hK0 : IsNonzeroEverywhere K) {p : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk p} {c : {j : E.ι // p ∈ (E.component j).support} → Fin n}
    (hz : IsRegularSystemOfParameters z) (hcinj : Function.Injective c)
    (hcmem : ∀ j, (E.component j.1).stalkIdeal p = Ideal.span {z (c j)}) {b : Fin n → ℕ}
    (hb : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c) {C : Ideal (X.presheaf.stalk p)}
    (hNC : (nonmonomialPart K E).stalkIdeal p = C)
    (hK : K.stalkIdeal p = Ideal.span {monomialOf z b} * C)
    (j : {j : E.ι // p ∈ (E.component j).support}) {η : X}
    (hη : η ∈ (E.component j.1).support.genericPoints) (hηp : η ⤳ p) :
    (K.ord η).toNat = b (c j) := by
  classical
  have hsm : Smooth f := SmoothOfRelativeDimension.smooth n₀ f
  have hreg := isRegularLocalRing_stalk f p
  have hex : ∀ j : {j : E.ι // p ∈ (E.component j).support},
      ∃ η ∈ (E.component j.1).support.genericPoints, η ⤳ p :=
    fun j => exists_genericPoint_specializes _ j.2
  choose η' hη' hη'p using hex
  have hsplit : K.stalkIdeal p =
      (monomialPart K E).stalkIdeal p * (nonmonomialPart K E).stalkIdeal p := by
    rw [← stalkIdeal_mul, Snc.monomialPart_mul_nonmonomialPart f E hE K]
  rw [stalkIdeal_monomialPart_eq_span_prod f n₀ hE K hcmem η' hη' hη'p, hNC] at hsplit
  rw [monomialOf_eq_prod_of_forall_mem_range z hcinj hb] at hK
  have hprime : ∀ j, (Ideal.span {z (c j)}).IsPrime := fun j => by
    rw [← hcmem j]
    exact isPrime_stalkIdeal_component_of_isSnc f E hE j.2
  have hN : ∀ j, ¬ C ≤ Ideal.span {z (c j)} := by
    intro j hle
    have h0 := Snc.ord_nonmonomialPart_eq_zero f E hE hK0 (hη' j)
    rw [IdealSheafData.ord_eq_zero_iff, mem_support_iff_stalkIdeal_le_maximalIdeal] at h0
    apply h0
    rw [stalkIdeal_specializes _ (hη'p j), maximalIdeal_eq_stalkIdeal_component E hE (hη' j),
      stalkIdeal_specializes (E.component j.1) (hη'p j), hNC]
    exact Ideal.map_mono (hle.trans_eq (hcmem j).symm)
  have he := (eq_of_span_prod_pow_mul_eq hz hcinj hprime _ _ hN hN (hsplit.symm.trans hK)).1
  have hηη : η = η' j :=
    Hironaka.Sequence.eq_of_specializes_of_isRegular _ (hE.1 j.1) hη (hη' j) hηp (hη'p j)
  rw [hηη]
  exact congrFun he j

end Exponent

section Step3

variable {X : Scheme.{u}}

/-- **CP3 along the geometric Step 3 of a piece family** ([Kol07, 111, Step 3]), for any nonzero
ideal below the marked monomial ideal (the general form; `cp3For_step3Seq` is its instance): each
centre is, at each of its points, the face of the stage family through the point, of total
exponent `≥ 1`; in any chain coordinates the face is `(z_s)` with `s` the coordinates of members,
and the exponent of the current ideal along a member through the point is `b` at that member —
the condition (★) at level `0`; the same stratum serves the I-shape. -/
theorem cp3For_realize_of_le (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
    (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}
    {n : ℕ} (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n 1)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) {I : X.IdealSheafData}
    (hI0 : IsNonzeroEverywhere I) (hle : I ≤ E.monomial Φ.exponentAt) :
    CP3For (Φ.realize n 1 hV) I E := by
  classical
  obtain ⟨n₀, -, hsm₀⟩ := id hn
  have hge : (Φ.realize n 1 hV).IsOrderGeSeq f I 1 E :=
    isOrderGeSeq_of_le f (Φ.realize_isOrderGeSeq f hE hΦ hV hn) hle
  have hK0 : ∀ i, IsNonzeroEverywhere ((Φ.realize n 1 hV).markedTransformSeq I 1 i) := fun i =>
    IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq f n₀ hge hI0 i
  have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  intro i q hq
  set L₀ := (MonomialState.step3 (Φ.toState n 1 hV)).2 with hL₀
  -- the stage family, its data and the instances at stage `i`
  set Φi : PieceFamily ((Φ.realize n 1 hV).stage i.castSucc) := stagePieces Φ 1 L₀ i.castSucc
    with hΦi
  set ei : ((Φ.realize n 1 hV).totalTransformSeq E i.castSucc).ι ≃o Fin Φi.nextLabel :=
    stageIso Φ 1 E e L₀ i.castSucc with hei
  have hV' : Φi.IsValid n 1 := Φ.valid_stagePieces f hE hΦ hV hn i.castSucc
  have hinv : Φi.toState n 1 hV' =
      (L₀.take i).foldl MonomialState.blowUp (Φ.toState n 1 hV) := by
    have h := Φ.realize_invariant f hE hΦ hV hn i.castSucc hV'
    rw [Fin.val_castSucc] at h
    exact h
  have hΦir : Φi.Realizes ((Φ.realize n 1 hV).totalTransformSeq E i.castSucc) ei :=
    Φ.realizes_stagePieces f hE hΦ hV hn i.castSucc
  have hEi : ((Φ.realize n 1 hV).totalTransformSeq E i.castSucc).IsSnc :=
    Φ.isSnc_totalTransformSeq_realize f hE hΦ hV hn i.castSucc
  obtain ⟨n', -, hsm'⟩ := Φ.exists_smoothOfRelativeDimension_stageMap_realize f hE hΦ hV hn
    i.castSucc
  set fi := (Φ.realize n 1 hV).stageMap i.castSucc ≫ f with hfi
  have hsmi : Smooth fi := SmoothOfRelativeDimension.smooth n' fi
  have hprop : IsProper ((Φ.realize n 1 hV).stageMap i.castSucc) := isProper_stageMap _ _
  have hNi : IsNoetherian ((Φ.realize n 1 hV).stage i.castSucc) := fi.isNoetherian_of_field
  have hreg := isRegularLocalRing_stalk fi q
  -- the centre is the centre selected by the rule of Step 3 on the stage family
  obtain ⟨r, -, -, hget⟩ := Φ.exists_center_realize_eq hV i
  have hcenter : (Φ.realize n 1 hV).center i =
      Φi.centerOf (L₀.get (Fin.cast (realizeAux_length Φ 1 L₀) i)) :=
    realizeAux_center Φ 1 L₀ i
  -- the centre is a centre of the stage state, and `q` lies on one of its faces
  have hSc : (Φi.toState n 1 hV').IsCenter (L₀.get (Fin.cast (realizeAux_length Φ 1 L₀) i)) := by
    rw [hget, hinv]
    exact MonomialState.isCenter_choice _ r
  rw [hcenter] at hq
  obtain ⟨P, hP, hqP⟩ := (Φi.mem_support_centerOf_iff _ q).mp hq
  have hPlt : ∀ c' ∈ P, c' < Φi.nextComp := fun c' hc' =>
    Φi.lt_nextComp_of_mem_nerve (hSc.1 hP) hc'
  have hZ : ((Φ.realize n 1 hV).center i).stalkIdeal q = (Φi.faceIdeal P).stalkIdeal q := by
    rw [hcenter]
    exact Φi.stalkIdeal_centerOf_eq_faceIdeal hSc hP hqP
  -- the face has total `≥ 1`: some piece through `q` has a positive exponent
  have htot : 1 ≤ Φi.total P := by
    have hP' := hP
    rw [hget] at hP'
    have h := MonomialState.m_le_total_of_mem_choice _ hP'
    rw [← hinv] at h
    exact h
  obtain ⟨c₀, hc₀P, hac₀⟩ : ∃ c₀ ∈ P, Φi.a c₀ ≠ 0 := by
    refine Finset.exists_ne_zero_of_sum_ne_zero ?_
    change Φi.total P ≠ 0
    omega
  -- the marked transform of the monomial ideal is the stage monomial
  have hMreal : (Φ.realize n 1 hV).markedTransformSeq (E.monomial Φ.exponentAt) 1 i.castSucc =
      ((Φ.realize n 1 hV).totalTransformSeq E i.castSucc).monomial Φi.exponentAt :=
    Φ.markedTransformSeq_realize f hE hΦ hV hn i.castSucc
  have hmono : (Φ.realize n 1 hV).markedTransformSeq I 1 i.castSucc ≤
      (Φ.realize n 1 hV).markedTransformSeq (E.monomial Φ.exponentAt) 1 i.castSucc :=
    markedTransformSeq_mono _ hle 1 i.castSucc
  -- the classification
  intro nq z c r' σ a b hfree hb
  obtain ⟨hz, hcinj, hcmem, -, -, -⟩ := id hfree
  have hzsnc : ((Φ.realize n 1 hV).totalTransformSeq E i.castSucc).IsSncAt q z :=
    ⟨hz, c, hcinj, hcmem⟩
  obtain ⟨s, hs, hPs, hsP⟩ := Φi.exists_stalkIdeal_faceIdeal_eq_span hEi hΦir hPlt hqP hzsnc
  -- a piece of the face through `q` has the coordinate of its member
  have hkey : ∀ c' (hc' : c' ∈ P) (j : Fin nq),
      (vanishingIdeal (Φi.piece c')).stalkIdeal q = Ideal.span {z j} →
      ∃ hmem : q ∈ (((Φ.realize n 1 hV).totalTransformSeq E i.castSucc).component
        (Φi.memberOf ei c' (hPlt c' hc'))).support, j = c ⟨_, hmem⟩ := by
    intro c' hc' j hj
    have hqc' : q ∈ Φi.piece c' := Φi.mem_faceSet.mp hqP c' hc'
    have hmem := Φi.mem_support_component_of_mem_piece hΦir (hPlt c' hc') hqc'
    refine ⟨hmem, ?_⟩
    have h1 := Φi.stalkIdeal_vanishingIdeal_piece hEi hΦir (hPlt c' hc') hqc'
    have hcm := hcmem ⟨Φi.memberOf ei c' (hPlt c' hc'), hmem⟩
    rw [hj, hcm] at h1
    by_contra hne
    exact notMem_span_singleton_of_ne hz (Ne.symm hne)
      (by rw [h1]; exact Ideal.subset_span (Set.mem_singleton _))
  have hsub : ↑s ⊆ Set.range c := by
    intro j hj
    obtain ⟨c', hc', hj'⟩ := hsP j (Finset.mem_coe.mp hj)
    obtain ⟨hmem, hjc⟩ := hkey c' hc' j hj'
    exact ⟨_, hjc.symm⟩
  have hZs : ((Φ.realize n 1 hV).center i).stalkIdeal q =
      Ideal.span ((z ∘ σ) '' {i : Fin (r' + 1) | i.val < 0}) ⊔ Ideal.span (z '' ↑s) := by
    rw [hZ, hs]
    have hempty : ((z ∘ σ) '' {i : Fin (r' + 1) | i.val < 0}) = ∅ :=
      Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun i hi => Nat.not_lt_zero _ hi)
    rw [hempty, Ideal.span_empty, bot_sup_eq]
  -- (★) at level `0`: the coordinate of the piece `c₀` carries a positive exponent of `K`
  obtain ⟨j₀, hj₀s, hj₀⟩ := hPs c₀ hc₀P
  obtain ⟨hmem₀, hj₀c⟩ := hkey c₀ hc₀P j₀ hj₀
  obtain ⟨η₀, hη₀, hη₀q⟩ := exists_genericPoint_specializes _ hmem₀
  -- the order of the stage monomial at `η₀` is the exponent of `c₀`
  have hord₀ : ((Φi.a c₀ : ℕ) : ℕ∞) ≤
      ((Φ.realize n 1 hV).markedTransformSeq I 1 i.castSucc).ord η₀ := by
    refine le_trans ?_ (IdealSheafData.ord_anti hmono η₀)
    rw [hMreal, Φi.ord_monomial_eq_total fi hEi hΦir η₀]
    obtain ⟨c₁, hc₁, hlab₁, hη₀c₁, hface₁, -⟩ :=
      Φi.faceAt_eq_singleton_of_mem_genericPoints fi hEi hΦir hη₀
    have hc₁₀ : c₁ = c₀ := by
      by_contra hne
      have hqc₁ : q ∈ Φi.piece c₁ := hη₀q.mem_closed (Φi.piece c₁).isClosed hη₀c₁
      refine Φi.not_mem_piece_of_label_eq hΦir hc₁ (hPlt c₀ hc₀P) hne ?_ hqc₁
        (Φi.mem_faceSet.mp hqP c₀ hc₀P)
      rw [hlab₁, Φi.coe_apply_memberOf]
    rw [hface₁, hc₁₀]
    change ((Φi.a c₀ : ℕ) : ℕ∞) ≤ ((∑ c ∈ ({c₀} : Finset ℕ), Φi.a c : ℕ) : ℕ∞)
    rw [Finset.sum_singleton]
  have hne0 : ((Φ.realize n 1 hV).markedTransformSeq I 1 i.castSucc).ord η₀ ≠ 0 := by
    intro h0
    rw [h0] at hord₀
    exact hac₀ (by exact_mod_cast nonpos_iff_eq_zero.mp hord₀)
  have hnetop : ((Φ.realize n 1 hV).markedTransformSeq I 1 i.castSucc).ord η₀ ≠ ⊤ :=
    ord_ne_top_of_isNonzeroEverywhere (hK0 _) η₀
  -- the common stratum for both shapes
  have hstrat : ∀ C : Ideal (((Φ.realize n 1 hV).stage i.castSucc).presheaf.stalk q),
      (nonmonomialPart ((Φ.realize n 1 hV).markedTransformSeq I 1 i.castSucc)
        ((Φ.realize n 1 hV).totalTransformSeq E i.castSucc)).stalkIdeal q = C →
      ((Φ.realize n 1 hV).markedTransformSeq I 1 i.castSucc).stalkIdeal q =
        Ideal.span {monomialOf z b} * C →
      StratumIn z (Set.range c) σ a b (((Φ.realize n 1 hV).center i).stalkIdeal q) := by
    intro C hNC hK
    refine ⟨0, Nat.zero_le _, s, hsub, hZs, fun _ => ⟨j₀, hj₀s, ?_⟩,
      fun h => absurd h (lt_irrefl 0)⟩
    have hexp := toNat_ord_eq_of_stalkIdeal_eq_span_mul fi n' hEi (hK0 _) hz hcinj hcmem hb hNC hK
      ⟨_, hmem₀⟩ hη₀ hη₀q
    rw [hj₀c, ← hexp]
    intro h
    exact (ENat.toNat_eq_zero.mp h).elim hne0 hnetop
  refine ⟨fun hK => hstrat _ ?_ hK, fun hI => Or.inl (hstrat _ ?_ hI)⟩
  · exact stalkIdeal_nonmonomialPart_of_kShape fi n' hEi (hK0 _) hfree hb hK
  · exact stalkIdeal_nonmonomialPart_of_iShape fi n' hEi (hK0 _) hfree hb hI

variable {n : ℕ}

/-- **CP3 along Step 3** ([Kol07, 111, Step 3] at the mark `1`): each centre is, at each of its
points, the face of the stage family through the point (`centerOf`), of total exponent `≥ 1`; in
any chain coordinates a face is `(z_s)` with `s` the coordinates of members, and the exponent of
the current ideal along a member through the point is `b` at that member — the condition (★) at
level `0`. An I-shape at a centre of Step 3 is classified by the same stratum. From the general
form through the bridge `monomial_exponentAt_step3Family` and `I ⊆ M(I)`. -/
theorem cp3For_step3Seq (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n 1 T) :
    CP3For (step3Seq T hT) T.I T.E := by
  have := T.smooth
  have hle : T.I ≤ monomialPart T.I T.E :=
    calc T.I = monomialPart T.I T.E * nonmonomialPart T.I T.E :=
          (BMO.monomialPart_mul_nonmonomialPart T.toTriple).symm
      _ ≤ monomialPart T.I T.E := mul_le_self_left _ _
  rw [← monomial_exponentAt_step3Family T] at hle
  exact cp3For_realize_of_le (T.X.left ↘ Spec (CommRingCat.of k)) (step3Family T) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1 T.isNonzeroEverywhere hle

end Step3

end Hironaka.Resolution
