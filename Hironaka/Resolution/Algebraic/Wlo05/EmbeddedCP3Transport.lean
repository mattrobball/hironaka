/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealColon
import Hironaka.Resolution.Algebraic.Wlo05.ChainRelativeLift
import Hironaka.Scheme.BlowUpSequence.ConcatIndex
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Snc.ParameterSubset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The transport lemmas of CP3, part 1

The statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) is proved in the form universal over
the chain-coordinate systems at a point (`CenterClassifiedAt`, `CP3For` of
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates`). Like the predicate `CP1For` of CP1, it
must travel with the bookkeeping of the algorithm: along a morphism that is an isomorphism on the
stalk (charts, the pull-backs of covers, the deletion of empty blow-ups), between two divisor
families whose members through the point correspond, and along a concatenation of runs. This module
holds those transports:

* `centerClassifiedAt_of_comap_of_isIso_stalkMap` and its converse
  `centerClassifiedAt_comap_of_isIso_stalkMap` — the stalk isomorphism carries chain coordinates,
  monomials and chain ideals both ways (`isRegularSystemOfParameters_comp_ringEquiv`,
  `monomialOf_map`, `chainIdeal_comp`, `chainKIdeal_comp`), and the strata and terminal strata as
  well (`stratumIn_map_ringEquiv`, `terminalIn_map_ringEquiv`);
* `centerClassifiedAt_iff_of_embeds` — the classification sees the family only through its members
  through the point;
* `cp3For_concat` — `CP3For` along `S.concat T` from `CP3For` on `S` and on `T` for the data
  induced at the end of `S` (the concatenation of [Kol07, Definition 29]), by the stage, centre and
  transform identities of `Hironaka.Scheme.BlowUpSequence.ConcatIndex`
  (`forall_centerClassifiedAt_of_heq` carries the pointwise statement across the casts);
* the order bounds `ord_le_one_of_stalkIdeal_eq_chainKIdeal` and
  `ord_le_one_of_stalkIdeal_eq_chainIdeal` — the K-shape and the un-isolated form have order at
  most one at the point (they contain a parameter or are the unit ideal). This is the observation
  that makes CP3 hold trivially along the rounds of order `≥ 2` of Step 1
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1`).

These transports are not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step21`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IsLocalRing BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.Resolution

section Ring

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S]

/-- A stratum in given coordinates transports along a ring equivalence. -/
theorem stratumIn_map_ringEquiv (e : R ≃+* S) {n : ℕ} {z : Fin n → R} {C : Set (Fin n)} {r : ℕ}
    {σ : Fin (r + 1) → Fin n} {a : Fin (r + 1) → Fin n → ℕ} {b : Fin n → ℕ} {Z : Ideal R}
    (h : StratumIn z C σ a b Z) :
    StratumIn (fun i => e (z i)) C σ a b (Z.map (e : R →+* S)) := by
  obtain ⟨l, hl, s, hsC, hZ, h0, hpos⟩ := h
  refine ⟨l, hl, s, hsC, ?_, h0, hpos⟩
  rw [hZ, Ideal.map_sup, Ideal.map_span, Ideal.map_span, ← Set.image_comp, ← Set.image_comp]
  rfl

/-- A terminal stratum in given coordinates transports along a ring equivalence. -/
theorem terminalIn_map_ringEquiv (e : R ≃+* S) {n : ℕ} {z : Fin n → R} {C : Set (Fin n)} {r : ℕ}
    {σ : Fin (r + 1) → Fin n} {Z : Ideal R} (h : TerminalIn z C σ Z) :
    TerminalIn (fun i => e (z i)) C σ (Z.map (e : R →+* S)) := by
  obtain ⟨s, hsC, hne, hZ⟩ := h
  refine ⟨s, hsC, hne, ?_⟩
  rw [hZ, Ideal.map_sup, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.image_comp]
  rfl

/-- The image of the span of the range of a composite along a ring equivalence. -/
theorem map_span_range_comp (e : R ≃+* S) {n : ℕ} (z : Fin n → R) {r : ℕ}
    (σ : Fin (r + 1) → Fin n) :
    (Ideal.span (Set.range (z ∘ σ))).map (e : R →+* S) =
      Ideal.span (Set.range ((fun i => e (z i)) ∘ σ)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

end Ring

variable {X : Scheme.{u}}

/-- The classification transports along a morphism inducing an isomorphism on the stalk at the
point: the pulled-back data at `q'` classify when the data at `φ q'` do (the counterpart of
`chainRelativeAt_of_comap_of_isIso_stalkMap` for the universal predicate). -/
theorem centerClassifiedAt_of_comap_of_isIso_stalkMap {Y : Scheme.{u}} (φ : Y ⟶ X)
    {E : DivisorFamily X} {K Z : X.IdealSheafData} {q' : Y} [IsIso (φ.stalkMap q')]
    (h : CenterClassifiedAt E K Z (φ q')) :
    CenterClassifiedAt (E.comap φ) (K.comap φ) (Z.comap φ) q' := by
  intro n w c r σ a b ⟨hw, hcinj, hcmem, hσinj, hσc, ha⟩ hb
  set e : X.presheaf.stalk (φ q') ≃+* Y.presheaf.stalk q' :=
    (asIso (φ.stalkMap q')).commRingCatIsoToRingEquiv with he
  have heφ : (e : X.presheaf.stalk (φ q') →+* Y.presheaf.stalk q') = (φ.stalkMap q').hom := rfl
  have hsymm : ∀ {A : Ideal (X.presheaf.stalk (φ q'))} {B : Ideal (Y.presheaf.stalk q')},
      A.map (e : X.presheaf.stalk (φ q') →+* Y.presheaf.stalk q') = B →
        A = B.map (e.symm : Y.presheaf.stalk q' →+* X.presheaf.stalk (φ q')) := fun h => by
    rw [← h, Ideal.map_map]
    simp
  have hmem : ∀ j : {j : E.ι // φ q' ∈ (E.component j).support},
      q' ∈ ((E.comap φ).component j.1).support :=
    fun j => (mem_support_comap_iff_apply _ _ _).mpr j.2
  set c' : {j : E.ι // φ q' ∈ (E.component j).support} → Fin n := fun j => c ⟨j.1, hmem j⟩
    with hc'
  have hrange : Set.range c' = Set.range c := by
    ext k
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.1, hmem j⟩, rfl⟩
    · rintro ⟨⟨j, hj⟩, rfl⟩
      exact ⟨⟨j, (mem_support_comap_iff_apply _ _ _).mp hj⟩, rfl⟩
  set z : Fin n → X.presheaf.stalk (φ q') :=
    (e.symm : Y.presheaf.stalk q' →+* X.presheaf.stalk (φ q')) ∘ w with hz
  have hez : (fun i => e (z i)) = w := funext fun i => by simp [hz]
  have hfree : ChainCoordsFree E (φ q') z c' σ a := by
    refine ⟨Hironaka.Sequence.isRegularSystemOfParameters_comp_ringEquiv e.symm hw, ?_, ?_, hσinj,
      fun i j => hσc i ⟨j.1, hmem j⟩, fun i k hk => hrange ▸ ha i k hk⟩
    · intro j j' hjj
      exact Subtype.ext (Subtype.mk.inj (hcinj hjj))
    · intro j
      have h1 := hcmem ⟨j.1, hmem j⟩
      change ((E.component j.1).comap φ).stalkIdeal q' = _ at h1
      rw [IdealSheafData.stalkIdeal_comap, ← heφ] at h1
      rw [hsymm h1, Ideal.map_span, Set.image_singleton]
      rfl
  have hb' : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c' := fun κ hκ => hrange ▸ hb κ hκ
  have hM : ((e.symm : Y.presheaf.stalk q' →+* X.presheaf.stalk (φ q')) ∘
      fun i => monomialOf w (a i)) = fun i => monomialOf z (a i) :=
    funext fun i => by rw [Function.comp_apply, monomialOf_map]
  have hZ' : (Z.comap φ).stalkIdeal q' = (Z.stalkIdeal (φ q')).map (e : _ →+* _) := by
    rw [IdealSheafData.stalkIdeal_comap, heφ]
  obtain ⟨hK, hI⟩ := h z c' σ a b hfree hb'
  refine ⟨fun hKq => ?_, fun hIq => ?_⟩
  · have hKz : K.stalkIdeal (φ q') =
        Ideal.span {monomialOf z b} * chainKIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
      rw [IdealSheafData.stalkIdeal_comap, ← heφ] at hKq
      rw [hsymm hKq, Ideal.map_mul, Ideal.map_span, Set.image_singleton, monomialOf_map,
        ← chainKIdeal_comp, Function.comp_assoc, hM]
    have hs := stratumIn_map_ringEquiv e (hK hKz)
    rw [hez, hrange, ← hZ'] at hs
    exact hs
  · have hIz : K.stalkIdeal (φ q') =
        Ideal.span {monomialOf z b} * chainIdeal (z ∘ σ) (fun i => monomialOf z (a i)) := by
      rw [IdealSheafData.stalkIdeal_comap, ← heφ] at hIq
      rw [hsymm hIq, Ideal.map_mul, Ideal.map_span, Set.image_singleton, monomialOf_map,
        ← chainIdeal_comp, Function.comp_assoc, hM]
    rcases hI hIz with hs | hs | hs
    · have := stratumIn_map_ringEquiv e hs
      rw [hez, hrange, ← hZ'] at this
      exact Or.inl this
    · have := terminalIn_map_ringEquiv e hs
      rw [hez, hrange, ← hZ'] at this
      exact Or.inr (Or.inl this)
    · refine Or.inr (Or.inr ?_)
      rw [hZ', hs, map_span_range_comp e z σ, hez]

/-- The classification depends on the family only through its members through `q`: two families
whose members through `q` correspond classify alike (`chainRelativeAt_iff_of_embeds` for the
universal predicate). -/
theorem centerClassifiedAt_iff_of_embeds {E₁ E₂ : DivisorFamily X} (e : E₁.ι → E₂.ι)
    (he : Function.Injective e) (hcomp : ∀ a, E₂.component (e a) = E₁.component a)
    {K Z : X.IdealSheafData} {q : X} (hmiss : ∀ b ∉ Set.range e, q ∉ (E₂.component b).support) :
    CenterClassifiedAt E₁ K Z q ↔ CenterClassifiedAt E₂ K Z q := by
  classical
  let θ : {i : E₁.ι // q ∈ (E₁.component i).support} →
      {j : E₂.ι // q ∈ (E₂.component j).support} :=
    fun i => ⟨e i.1, by rw [hcomp]; exact i.2⟩
  have hpre : ∀ j : {j : E₂.ι // q ∈ (E₂.component j).support},
      ∃ i : {i : E₁.ι // q ∈ (E₁.component i).support}, θ i = j := by
    intro j
    obtain ⟨i, hi⟩ : j.1 ∈ Set.range e := by
      by_contra hj
      exact hmiss j.1 hj j.2
    refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
    rw [← hcomp, hi]
    exact j.2
  let θ' : {j : E₂.ι // q ∈ (E₂.component j).support} →
      {i : E₁.ι // q ∈ (E₁.component i).support} := fun j => Classical.choose (hpre j)
  have hθθ' : ∀ j, θ (θ' j) = j := fun j => Classical.choose_spec (hpre j)
  have hθinj : Function.Injective θ := fun i i' h => Subtype.ext (he (Subtype.mk.inj h))
  have hθ'θ : ∀ i, θ' (θ i) = i := fun i => hθinj (hθθ' (θ i))
  have hθ'inj : Function.Injective θ' := fun j j' h => by rw [← hθθ' j, ← hθθ' j', h]
  have hcompθ : ∀ i : {i : E₁.ι // q ∈ (E₁.component i).support},
      E₂.component (θ i).1 = E₁.component i.1 := fun i => hcomp i.1
  have hrange₁ : ∀ {n : ℕ} (c : {j : E₂.ι // q ∈ (E₂.component j).support} → Fin n),
      Set.range (c ∘ θ) = Set.range c := fun c => by
    ext k
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨θ i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨θ' j, by rw [Function.comp_apply, hθθ']⟩
  have hrange₂ : ∀ {n : ℕ} (c : {i : E₁.ι // q ∈ (E₁.component i).support} → Fin n),
      Set.range (c ∘ θ') = Set.range c := fun c => by
    ext k
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨θ' j, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨θ i, by rw [Function.comp_apply, hθ'θ]⟩
  constructor
  · intro h n z c r σ a b hfr hb
    obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := hfr
    have hfree : ChainCoordsFree E₁ q z (c ∘ θ) σ a := by
      refine ⟨hz, hcinj.comp hθinj, ?_, hσinj, fun i j => hσc i (θ j), ?_⟩
      · intro i
        rw [← hcompθ i]
        exact hcmem (θ i)
      · intro i k hk
        rw [hrange₁ c]
        exact ha i k hk
    have hb' : ∀ κ, b κ ≠ 0 → κ ∈ Set.range (c ∘ θ) := by
      intro κ hκ
      rw [hrange₁ c]
      exact hb κ hκ
    obtain ⟨hK, hI⟩ := h z (c ∘ θ) σ a b hfree hb'
    rw [hrange₁ c] at hK hI
    exact ⟨hK, hI⟩
  · intro h n z c r σ a b hfr hb
    obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := hfr
    have hfree : ChainCoordsFree E₂ q z (c ∘ θ') σ a := by
      refine ⟨hz, hcinj.comp hθ'inj, ?_, hσinj, fun i j => hσc i (θ' j), ?_⟩
      · intro j
        have h1 := hcmem (θ' j)
        rw [← hcompθ (θ' j), hθθ' j] at h1
        exact h1
      · intro i k hk
        rw [hrange₂ c]
        exact ha i k hk
    have hb' : ∀ κ, b κ ≠ 0 → κ ∈ Set.range (c ∘ θ') := by
      intro κ hκ
      rw [hrange₂ c]
      exact hb κ hκ
    obtain ⟨hK, hI⟩ := h z (c ∘ θ') σ a b hfree hb'
    rw [hrange₂ c] at hK hI
    exact ⟨hK, hI⟩

/-- The K-shape has order `≤ 1`: it contains the parameter `f₀`, or is the unit ideal. -/
theorem ord_le_one_of_stalkIdeal_eq_chainKIdeal {N : X.IdealSheafData} {p : X}
    [IsRegularLocalRing (X.presheaf.stalk p)] {n : ℕ}
    {z : Fin n → X.presheaf.stalk p} (hz : IsRegularSystemOfParameters z) {r : ℕ}
    {σ : Fin (r + 1) → Fin n} (M : Fin (r + 1) → X.presheaf.stalk p)
    (hN : N.stalkIdeal p = chainKIdeal (z ∘ σ) M) : N.ord p ≤ 1 := by
  by_contra h
  have h2 : ((2 : ℕ) : ℕ∞) ≤ N.ord p := by
    have := not_le.mp h
    exact Order.add_one_le_of_lt this
  rw [IdealSheafData.le_ord_iff, hN] at h2
  cases r with
  | zero =>
    have h1 : (1 : X.presheaf.stalk p) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ 2 := by
      refine h2 ?_
      unfold chainKIdeal chainIdeal
      refine Ideal.subset_span ⟨0, ?_⟩
      simp
    have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = ⊤ :=
      (Ideal.eq_top_iff_one _).mpr (Ideal.pow_le_self two_ne_zero h1)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm
  | succ r =>
    have hf : z (σ 0) ∈ chainKIdeal (z ∘ σ) M := by
      unfold chainKIdeal chainIdeal
      refine Ideal.subset_span ⟨0, ?_⟩
      simp
    have hnot := notMem_sq_sup_span_image hz.1.symm hz.2 (s := ∅)
      (Finset.notMem_empty (σ 0))
    simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty, sup_bot_eq] at hnot
    exact hnot (h2 hf)

/-- The un-isolated form has order `≤ 1`: it contains the parameter `f₀`. -/
theorem ord_le_one_of_stalkIdeal_eq_chainIdeal {N : X.IdealSheafData} {p : X}
    [IsRegularLocalRing (X.presheaf.stalk p)] {n : ℕ}
    {z : Fin n → X.presheaf.stalk p} (hz : IsRegularSystemOfParameters z) {r : ℕ}
    {σ : Fin (r + 1) → Fin n} (M : Fin (r + 1) → X.presheaf.stalk p)
    (hN : N.stalkIdeal p = chainIdeal (z ∘ σ) M) : N.ord p ≤ 1 := by
  by_contra h
  have h2 : ((2 : ℕ) : ℕ∞) ≤ N.ord p := by
    have := not_le.mp h
    exact Order.add_one_le_of_lt this
  rw [IdealSheafData.le_ord_iff, hN] at h2
  have hf : z (σ 0) ∈ chainIdeal (z ∘ σ) M := by
    unfold chainIdeal
    refine Ideal.subset_span ⟨0, ?_⟩
    simp
  have hnot := notMem_sq_sup_span_image hz.1.symm hz.2 (s := ∅)
    (Finset.notMem_empty (σ 0))
  simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty, sup_bot_eq] at hnot
  exact hnot (h2 hf)

/-- The pointwise classification along a stage transports across equal schemes with
heterogeneously equal data. -/
theorem forall_centerClassifiedAt_of_heq {Y₁ Y₂ : Scheme.{u}} (e : Y₁ = Y₂)
    {E₁ : DivisorFamily Y₁} {E₂ : DivisorFamily Y₂} (hE : HEq E₁ E₂) {K₁ Z₁ : Y₁.IdealSheafData}
    {K₂ Z₂ : Y₂.IdealSheafData} (hK : HEq K₁ K₂) (hZ : HEq Z₁ Z₂)
    (h : ∀ q ∈ Z₁.support, CenterClassifiedAt E₁ K₁ Z₁ q) :
    ∀ q ∈ Z₂.support, CenterClassifiedAt E₂ K₂ Z₂ q := by
  subst e
  rw [eq_of_heq hE, eq_of_heq hK, eq_of_heq hZ] at h
  exact h

/-- `CP3For` along a concatenation ([Kol07, Definition 29]) from `CP3For` on the two pieces, the
second for the data induced at the end of the first (the stage, centre and transform identities
of `Hironaka.Scheme.BlowUpSequence.ConcatIndex`). -/
theorem cp3For_concat (S : BlowUpSequence X) (T : BlowUpSequence S.last) (I : X.IdealSheafData)
    (E : DivisorFamily X) (hS : CP3For S I E)
    (hT : CP3For T (S.markedTransformSeq I 1 (Fin.last _)) (S.totalTransformSeq E (Fin.last _))) :
    CP3For (S.concat T) I E := by
  rintro ⟨j, hj⟩ q hq
  by_cases hjS : j < S.length
  · have hst := stage_concat_mk_of_le S T j (Nat.lt_succ_of_lt hj) (Nat.lt_succ_of_lt hjS)
    have hc := center_concat_heq_mk_of_lt S T j hj hjS
    have hm := markedTransformSeq_concat_heq_mk_of_le S T I 1 j (Nat.lt_succ_of_lt hj)
      (Nat.lt_succ_of_lt hjS)
    have ht := totalTransformSeq_concat_heq_mk_of_le S T E j (Nat.lt_succ_of_lt hj)
      (Nat.lt_succ_of_lt hjS)
    exact forall_centerClassifiedAt_of_heq hst.symm ht.symm hm.symm hc.symm
      (fun q' hq' => hS ⟨j, hjS⟩ q' hq') q hq
  · have hjT : j - S.length < T.length := by
      rw [length_concat] at hj
      omega
    have hjeq : j = S.length + (j - S.length) := by omega
    have hst := stage_concat_mk S T j (j - S.length) (Nat.lt_succ_of_lt hj)
      (Nat.lt_succ_of_lt hjT) hjeq
    have hc := center_concat_heq_mk S T j (j - S.length) hj hjT hjeq
    have hm := markedTransformSeq_concat_heq_mk S T I 1 j (j - S.length) (Nat.lt_succ_of_lt hj)
      (Nat.lt_succ_of_lt hjT) hjeq
    have ht := totalTransformSeq_concat_heq_mk S T E j (j - S.length) (Nat.lt_succ_of_lt hj)
      (Nat.lt_succ_of_lt hjT) hjeq
    exact forall_centerClassifiedAt_of_heq hst.symm ht.symm hm.symm hc.symm
      (fun q' hq' => hT ⟨j - S.length, hjT⟩ q' hq') q hq

/-- The converse of `centerClassifiedAt_of_comap_of_isIso_stalkMap`: the data at `φ q'` classify
when the pulled-back data at `q'` do. -/
theorem centerClassifiedAt_comap_of_isIso_stalkMap {Y : Scheme.{u}} (φ : Y ⟶ X)
    {E : DivisorFamily X} {K Z : X.IdealSheafData} {q' : Y} [IsIso (φ.stalkMap q')]
    (h : CenterClassifiedAt (E.comap φ) (K.comap φ) (Z.comap φ) q') :
    CenterClassifiedAt E K Z (φ q') := by
  intro n z c r σ a b ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ hb
  set e : X.presheaf.stalk (φ q') ≃+* Y.presheaf.stalk q' :=
    (asIso (φ.stalkMap q')).commRingCatIsoToRingEquiv with he
  have heφ : (e : X.presheaf.stalk (φ q') →+* Y.presheaf.stalk q') = (φ.stalkMap q').hom := rfl
  have hmem : ∀ j : {j : E.ι // φ q' ∈ (E.component j).support},
      q' ∈ ((E.comap φ).component j.1).support :=
    fun j => (mem_support_comap_iff_apply _ _ _).mpr j.2
  have hmem' : ∀ j : {j : (E.comap φ).ι // q' ∈ ((E.comap φ).component j).support},
      φ q' ∈ (E.component j.1).support :=
    fun j => (mem_support_comap_iff_apply _ _ _).mp j.2
  set c' : {j : (E.comap φ).ι // q' ∈ ((E.comap φ).component j).support} → Fin n :=
    fun j => c ⟨j.1, hmem' j⟩ with hc'
  have hrange : Set.range c' = Set.range c := by
    ext k
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.1, hmem' j⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨j.1, hmem j⟩, rfl⟩
  set w : Fin n → Y.presheaf.stalk q' := (e : X.presheaf.stalk (φ q') →+* Y.presheaf.stalk q') ∘ z
    with hw
  have hfree : ChainCoordsFree (E.comap φ) q' w c' σ a := by
    refine ⟨Hironaka.Sequence.isRegularSystemOfParameters_comp_ringEquiv e hz, ?_, ?_, hσinj,
      fun i j => hσc i ⟨j.1, hmem' j⟩, fun i k hk => hrange ▸ ha i k hk⟩
    · intro j j' hjj
      exact Subtype.ext (Subtype.mk.inj (hcinj hjj))
    · intro j
      change ((E.component j.1).comap φ).stalkIdeal q' = _
      rw [IdealSheafData.stalkIdeal_comap, ← heφ, hcmem ⟨j.1, hmem' j⟩, Ideal.map_span,
          Set.image_singleton]
      rfl
  have hb' : ∀ κ, b κ ≠ 0 → κ ∈ Set.range c' := fun κ hκ => hrange ▸ hb κ hκ
  have hM : ((e : X.presheaf.stalk (φ q') →+* Y.presheaf.stalk q') ∘
      fun i => monomialOf z (a i)) = fun i => monomialOf w (a i) :=
    funext fun i => by rw [Function.comp_apply, monomialOf_map]
  have hZ' : (Z.comap φ).stalkIdeal q' = (Z.stalkIdeal (φ q')).map (e : _ →+* _) := by
    rw [IdealSheafData.stalkIdeal_comap, heφ]
  have hback : ∀ {J : Ideal (X.presheaf.stalk (φ q'))},
      (J.map (e : X.presheaf.stalk (φ q') →+* Y.presheaf.stalk q')).map
        (e.symm : Y.presheaf.stalk q' →+* X.presheaf.stalk (φ q')) = J := fun {J} => by
    rw [Ideal.map_map, RingEquiv.symm_comp, Ideal.map_id]
  obtain ⟨hK, hI⟩ := h w c' σ a b hfree hb'
  refine ⟨fun hKq => ?_, fun hIq => ?_⟩
  · have hKw : (K.comap φ).stalkIdeal q' =
        Ideal.span {monomialOf w b} * chainKIdeal (w ∘ σ) (fun i => monomialOf w (a i)) := by
      rw [IdealSheafData.stalkIdeal_comap, ← heφ, hKq, Ideal.map_mul, Ideal.map_span,
          Set.image_singleton,
        monomialOf_map, ← chainKIdeal_comp, Function.comp_assoc, hM]
    have hs := stratumIn_map_ringEquiv e.symm (hK hKw)
    rw [hrange, hZ', hback] at hs
    have hez : (fun i => e.symm (w i)) = z := funext fun i => by simp [hw]
    rw [hez] at hs
    exact hs
  · have hIw : (K.comap φ).stalkIdeal q' =
        Ideal.span {monomialOf w b} * chainIdeal (w ∘ σ) (fun i => monomialOf w (a i)) := by
      rw [IdealSheafData.stalkIdeal_comap, ← heφ, hIq, Ideal.map_mul, Ideal.map_span,
          Set.image_singleton,
        monomialOf_map, ← chainIdeal_comp, Function.comp_assoc, hM]
    have hez : (fun i => e.symm (w i)) = z := funext fun i => by simp [hw]
    rcases hI hIw with hs | hs | hs
    · have := stratumIn_map_ringEquiv e.symm hs
      rw [hrange, hZ', hback, hez] at this
      exact Or.inl this
    · have := terminalIn_map_ringEquiv e.symm hs
      rw [hrange, hZ', hback, hez] at this
      exact Or.inr (Or.inl this)
    · refine Or.inr (Or.inr ?_)
      have := congrArg
        (Ideal.map (e.symm : Y.presheaf.stalk q' →+* X.presheaf.stalk (φ q'))) hs
      rw [hZ', hback, map_span_range_comp e.symm w σ, hez] at this
      exact this

end Hironaka.Resolution
