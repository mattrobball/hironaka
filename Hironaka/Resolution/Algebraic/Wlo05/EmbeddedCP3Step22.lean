/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.OrderReduction.ClosedEmbedding
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Step22Tools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Subfamily
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Chain
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3EraseEmpty
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Transport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainDescentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedComponentTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep21Passage
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.Remark67
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 along Step 2.2

Step 2.2 of the proof of [Kol07, Theorem 103] (item 104, Step 2.2) applies [Kol07, Lemma 102] at
the position of `H_r` on the Step 2.2 triple `(X_r, I_r, F_r + H_r)`, through the re-tuning at the
mark `1` (the identity). The statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) along it for `(I_r, E_r)`, `E_r` the
FULL total transform of `E`:

* along the raw output of Lemma 102 over `H_r` for the family `F_r = (F_r + H_r) − H_r`
  (`cp3For_rawSeq_erase_of_le`): the first centre `Z₋₁` by the ring-level classification
  (`centerClassifiedAt_of_stalkIdeal_le_of_isSncAt_append`; `F_r + H_r` snc at `q` from
  `isSnc_erase_append`, the stalk of `Z₋₁` by `stalkIdeal_Zminus1_eq`, and `I_r ≤ H_r` at `q` from
  the order `1` of `I_r` at the generic point of the component of `H_r` through `q`,
  `mem_support_Zminus1_iff_ord_eq`, `stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor`); the
  later centres by the pointwise pass `centerClassifiedAt_of_comap_chain`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Chain`) with the identities of [Kol07, Lemma 62]
  as in `cp3For_rawSeq_member`, the snc of the transform of `F_r` with that of `H_r` from the snc of
  the transform of the full family (`isSncAt_of_injective`, `exists_embeds_totalTransformSeq'`), the
  maximal contact carried along (`strictTransformSeq_le_markedTransformSeq_MC`) and the stalk of
  `I_r` proper at a point of a centre (the centre has order `≥ 1`);
* the family bridge `cp3For_of_embeds` (`centerClassifiedAt_iff_of_embeds`): `F_r ↪ E_r`, the
  members of `E_r` outside `F_r` being the birational transforms of the original members, which
  miss `V(I_r)` at the end of Step 2.1 (`disjoint_support_markedTransformSeq_step21_final`,
  `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep21Passage`) and hence every later centre
  (`disjoint_support_markedTransformSeq_strictTransformSeq`; a centre lies in `V(I_i)`);
* the assembly (`cp3For_step22_aux`, `cp3For_step22`): below the mark the re-tuned Lemma 102 is
  empty (`step22Functor_seq_of_maxOrd_lt`); at the mark, `max-ord I = 1` too (below it Step 2.1 is
  empty and `I_r = I`), the value is the raw output with its empty blow-ups deleted
  (`step22Functor_seq_of_maxOrd_eq`, `functor_seq_congr_mark`, `dataFunctor_seq_of_maxOrd_eq`,
  `functor_seq`), `cp3For_eraseEmpty` deletes them, and the tuned ideal is `I_r`
  (`W_tuningParam_one`, [Kol07, Remark 67]).

This argument is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Tower`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BD Hironaka.BO Hironaka.Local IsLocalRing

namespace Hironaka.Resolution

variable {X : Scheme.{u}} {k : Type u} [Field k] [CharZero k]

/-- `CP3For` transports to a bigger family whose extra members miss every point of a centre (the
counterpart of `cp1For_of_embeds`). -/
theorem cp3For_of_embeds (S : BlowUpSequence X) (I : X.IdealSheafData) {E₁ E₂ : DivisorFamily X}
    (e₀ : E₁.ι → E₂.ι) (he₀ : Function.Injective e₀)
    (hcomp₀ : ∀ a, E₂.component (e₀ a) = E₁.component a)
    (hmiss : ∀ (i : Fin S.length) (q : S.stage i.castSucc), q ∈ (S.center i).support →
      ∀ a, a ∉ Set.range e₀ →
        q ∉ ((S.totalTransformSeq E₂ i.castSucc).component
          (S.originalIdx E₂ i.castSucc a)).support)
    (h : CP3For S I E₁) : CP3For S I E₂ := by
  intro i q hq
  obtain ⟨e, he, hcomp, hm⟩ := exists_embeds_totalTransformSeq S e₀ he₀ hcomp₀ i.castSucc
  have h1 : CenterClassifiedAt (S.totalTransformSeq E₂ i.castSucc)
      (S.markedTransformSeq I 1 i.castSucc) (S.center i) q := by
    refine (centerClassifiedAt_iff_of_embeds e he hcomp ?_).mp (h i q hq)
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hm b hb
    exact hmiss i q hq a ha
  intro n z c r σ a b hfree hb
  exact h1 z c σ a b hfree hb

section Raw

variable {N : ℕ}

/-- **The pass over a hypersurface of maximal contact, classified for the boundary without it**:
CP3 along the raw output of Lemma 102 over the member `Eʲ ⊆ V(I)` (i.e. `Eʲ ≤ I`) for the outer
data `(I, E − Eʲ)` from CP3 for the inductive run. -/
theorem cp3For_rawSeq_erase_of_le {Dom' : MarkedTriple k → Prop} (B' : OrderGeSeqAssignment k Dom')
    (T : Triple k) (j : T.E.ι) (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) 1)
    (hmax : T.I.maxOrd = 1) (hn : T.HasDimLE N)
    (hDom' : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (N - 1) → T'.m = 1 → Dom' T')
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom' T'), T'.m = 1 → CP3For (B'.seq T' hT') T'.I T'.E)
    (hHJ : T.E.component j ≤ T.I) :
    CP3For (rawSeq T 1 j hI hmax hn B' hDom') T.I (T.E.erase j) := by
  classical
  obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
  have hsm₀ : SmoothOfRelativeDimension n₀ (T.X.left ↘ Spec (CommRingCat.of k)) := hn₀
  have hsmf : Smooth (T.X.left ↘ Spec (CommRingCat.of k)) := SmoothOfRelativeDimension.smooth n₀ _
  have hLN : IsLocallyNoetherian T.X.left :=
    (T.X.left ↘ Spec (CommRingCat.of k)).isLocallyNoetherian_of_field
  have hN : IsNoetherian T.X.left := (T.X.left ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  have hker : (T.E.component j).subschemeι.ker = T.E.component j := IdealSheafData.ker_subschemeι _
  have hHsm : IsSmoothDivisor (T.E.component j) := isSmoothDivisor_component T j
  have hHdim : SmoothOfRelativeDimension (n₀ - 1)
      ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) :=
    smoothOfRelativeDimension_of_isSmoothDivisor (T.X.left ↘ Spec (CommRingCat.of k)) n₀ _ hHsm
  set T' := restrictedTriple T 1 j hI hmax with hT'def
  set hR : Dom' T' := hDom' _ (hasDimLE_restrictedTriple T 1 j hI hmax hn) rfl with hRdef
  set L' := B'.seq T' hR with hL'def
  set L : BlowUpSequence (T.E.component j).subscheme :=
    cons (T.E.component j).subscheme (centerS T 1 j) L' with hLdef
  have hraw : rawSeq T 1 j hI hmax hn B' hDom' = L.pushforward (T.E.component j).subschemeι := rfl
  have hL : L.IsOrderGeSeq ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
      (T.I.comap (T.E.component j).subschemeι) 1
      ((T.E.erase j).comap (T.E.component j).subschemeι) :=
    isOrderGeSeq_cons_centerS T 1 j hI hmax B' hR
  have hSord : (L.pushforward (T.E.component j).subschemeι).IsOrderSeq
      (T.X.left ↘ Spec (CommRingCat.of k)) T.I (T.E.erase j) 1 :=
    isOrderSeq_rawSeq_erase T 1 j hI hmax hn B' hDom'
  have hS : (L.pushforward (T.E.component j).subschemeι).IsOrderGeSeq
      (T.X.left ↘ Spec (CommRingCat.of k)) T.I 1 (T.E.erase j) :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) n₀ hSord
  have hSfull : (L.pushforward (T.E.component j).subschemeι).IsOrderGeSeq
      (T.X.left ↘ Spec (CommRingCat.of k)) T.I 1 T.E :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) n₀
      (isOrderSeq_rawSeq T 1 j hI hmax hn B' hDom')
  have hsm : (L.pushforward (T.E.component j).subschemeι).IsSmooth
      (T.X.left ↘ Spec (CommRingCat.of k)) := hS.1
  have hEH' : ((T.E.erase j).append (T.E.component j).subschemeι.ker).IsSnc := by
    rw [hker]
    exact DivisorFamily.isSnc_erase_append T.E j T.isSnc
  have hsnc : ∀ l : Fin (L.pushforward (T.E.component j).subschemeι).length,
      ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j)
        l.castSucc).HasSncWith ((L.pushforward (T.E.component j).subschemeι).center l) :=
    fun l => (hS.2 l).1
  have hZ : ∀ l : Fin (L.pushforward (T.E.component j).subschemeι).length,
      (L.pushforward (T.E.component j).subschemeι).strictTransformSeq
        (T.E.component j).subschemeι.ker l.castSucc ≤
        (L.pushforward (T.E.component j).subschemeι).center l := by
    intro l
    rw [hker]
    exact strictTransformSeq_le_center_pushforward_subschemeι (T.E.component j) L l
  have e : (L.pushforward (T.E.component j).subschemeι).pullback (T.E.component j).subschemeι = L :=
    pullback_pushforward L _
  obtain ⟨n₁, hn₁⟩ := T'.smoothOfRelativeDimension
  have hsm₁ : SmoothOfRelativeDimension n₁ (T'.X.left ↘ Spec (CommRingCat.of k)) := hn₁
  have hL' : L'.IsOrderGeSeq (T'.X.left ↘ Spec (CommRingCat.of k)) T'.I 1 T'.E :=
    B'.isOrderGeSeq T' hR
  have hcp : CP3For L' T'.I T'.E := hcp3 T' hR rfl
  have hle : T.E.component j ≤ IdealSheafData.MC (T.X.left ↘ Spec (CommRingCat.of k)) T.I 1 := hHJ
  rw [hraw]
  rintro ⟨i, hi⟩ q hq
  cases i with
  | zero =>
    -- the first centre `Z₋₁`: the current ideal lies in `Eʲ` there, so no K-shape and an I-shape
    -- is the absorption
    have hc0 : (L.pushforward (T.E.component j).subschemeι).center ⟨0, hi⟩ =
        Zminus1 T.I 1 (T.E.component j) := by
      change (centerS T 1 j).map (T.E.component j).subschemeι = _
      exact map_centerS T 1 j
    rw [hc0] at hq ⊢
    change CenterClassifiedAt (T.E.erase j) T.I (Zminus1 T.I 1 (T.E.component j)) q
    have hqj : q ∈ (T.E.component j).support := support_Zminus1_le T 1 j hq
    obtain ⟨η, hη, hord, hηq⟩ := (mem_support_Zminus1_iff_ord_eq T 1 j hmax q).mp hq
    have hZq : (Zminus1 T.I 1 (T.E.component j)).stalkIdeal q = (T.E.component j).stalkIdeal q :=
      stalkIdeal_Zminus1_eq T 1 j hq
    have hreg := isRegularLocalRing_stalk (T.X.left ↘ Spec (CommRingCat.of k)) q
    obtain ⟨m, w, hsnc0⟩ := (DivisorFamily.isSnc_erase_append T.E j T.isSnc).2 q
    have hηI : η ∈ T.I.support := by
      rw [← IdealSheafData.one_le_ord_iff, hord]
      exact le_of_eq Nat.cast_one.symm
    have hcl : Closeds.closure {η} ≤ T.I.support := by
      rw [← SetLike.coe_subset_coe, Closeds.coe_closure]
      exact T.I.support.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hηI)
    have hKH : T.I.stalkIdeal q ≤ (T.E.component j).stalkIdeal q := by
      rw [← stalkIdeal_vanishingIdeal_closure_eq_of_isSmoothDivisor hHsm hη hηq]
      exact IdealSheafData.stalkIdeal_mono (IdealSheafData.le_support_iff_le_vanishingIdeal.mp hcl)
          q
    have hmain : CenterClassifiedAt (T.E.erase j) T.I (Zminus1 T.I 1 (T.E.component j)) q :=
      centerClassifiedAt_of_stalkIdeal_le_of_isSncAt_append (E := T.E.erase j) hqj hsnc0 hZq hKH
    intro n z c r σ a b hfree hb
    exact hmain z c σ a b hfree hb
  | succ i =>
    have hiS : i + 1 < (L.pushforward (T.E.component j).subschemeι).length + 1 :=
      Nat.lt_succ_of_lt hi
    have hi' : i + 1 < L.length + 1 := by
      rw [← length_pushforward L (T.E.component j).subschemeι]
      exact hiS
    have hiL : i + 1 < L.length := by
      rw [← length_pushforward L (T.E.component j).subschemeι]
      exact hi
    have hiL' : i < L'.length := Nat.lt_of_succ_lt_succ hiL
    set g : L.stage ⟨i + 1, hi'⟩ ⟶
        (L.pushforward (T.E.component j).subschemeι).stage ⟨i + 1, hiS⟩ :=
      L.pushforwardStageHom (T.E.component j).subschemeι ⟨i + 1, hi'⟩ with hgdef
    have hgci : IsClosedImmersion g :=
      isClosedImmersion_pushforwardStageHom L (T.E.component j).subschemeι ⟨i + 1, hi'⟩
    have hgker : g.ker = (L.pushforward (T.E.component j).subschemeι).strictTransformSeq
        (T.E.component j) ⟨i + 1, hiS⟩ := by
      have := ker_pushforwardStageHom L (T.E.component j).subschemeι ⟨i + 1, hi'⟩
      rw [hker] at this
      exact this
    set Zc : (L.stage ⟨i + 1, hi'⟩).IdealSheafData := L.center ⟨i + 1, hiL⟩ with hZc
    have hcenter : (L.pushforward (T.E.component j).subschemeι).center ⟨i + 1, hi⟩ = Zc.map g :=
      center_pushforward_mk L (T.E.component j).subschemeι (i + 1) hiL
    rw [hcenter] at hq ⊢
    have hqimg : q ∈ g '' (Zc.support : Set (L.stage ⟨i + 1, hi'⟩)) := by
      have hcl : IsClosed (g '' (Zc.support : Set (L.stage ⟨i + 1, hi'⟩))) :=
        g.isClosedEmbedding.isClosedMap _ Zc.support.isClosed
      rw [IdealSheafData.support_map, ← SetLike.mem_coe, Closeds.coe_closure, hcl.closure_eq] at hq
      exact hq
    obtain ⟨q', hq', rfl⟩ := hqimg
    have hjP : i + 1 < ((L.pushforward (T.E.component j).subschemeι).pullback
        (T.E.component j).subschemeι).length + 1 := by
      rw [e]
      exact hi'
    have es : ((L.pushforward (T.E.component j).subschemeι).pullback
        (T.E.component j).subschemeι).stage ⟨i + 1, hjP⟩ = L.stage ⟨i + 1, hi'⟩ :=
      stage_congr e (i + 1) hjP hi'
    have hφ : HEq ((L.pushforward (T.E.component j).subschemeι).pullbackStageHom
        (T.E.component j).subschemeι ⟨i + 1, hiS⟩) g :=
      pullbackStageHom_pushforward_heq_mk L (T.E.component j).subschemeι (i + 1) hiS hi'
    have hEcomap : ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j)
        ⟨i + 1, hiS⟩).comap g =
        L.totalTransformSeq ((T.E.erase j).comap (T.E.component j).subschemeι) ⟨i + 1, hi'⟩ := by
      have hres := totalTransformSeq_comap_pullbackStageHom_of_forall_lt
        (T.X.left ↘ Spec (CommRingCat.of k)) (L.pushforward (T.E.component j).subschemeι)
        (T.E.component j).subschemeι (T.E.erase j) hsm hEH' (i + 1) (fun l _ => hsnc l) hZ hiS
      have h1 := comap_congr_heq es hφ
        ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j) ⟨i + 1, hiS⟩)
      have h2 := totalTransformSeq_congr_heq e ((T.E.erase j).comap (T.E.component j).subschemeι)
        (i + 1) hjP hi'
      exact eq_of_heq (h1.symm.trans ((heq_of_eq hres).trans h2))
    have hJcomap : ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1
        ⟨i + 1, hiS⟩).comap g =
        L.markedTransformSeq (T.I.comap (T.E.component j).subschemeι) 1 ⟨i + 1, hi'⟩ := by
      have hres := IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk
        (T.X.left ↘ Spec (CommRingCat.of k)) n₀ (T.E.component j).subschemeι hS (i + 1) hiS
      have h1 := heq_comap es hφ
        ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1 ⟨i + 1, hiS⟩)
      have h2 := markedTransformSeq_congr_heq e (T.I.comap (T.E.component j).subschemeι) 1 (i + 1)
        hjP hi'
      exact eq_of_heq (h1.symm.trans ((heq_of_eq hres.symm).trans h2))
    -- the outer boundary `E − Eʲ` with the transform of `Eʲ` appended is snc at `g q'`
    obtain ⟨em, hem, hcompm, -, hnotm⟩ := exists_embeds_totalTransformSeq' (E₁ := T.E.erase j)
      (E₂ := T.E) (L.pushforward (T.E.component j).subschemeι)
      (Subtype.val : (T.E.erase j).ι → T.E.ι) Subtype.val_injective (fun _ => rfl) ⟨i + 1, hiS⟩
    have hEi : ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq T.E
        ⟨i + 1, hiS⟩).IsSnc :=
      IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (CommRingCat.of k)) n₀ hSfull T.isSnc
        ⟨i + 1, hiS⟩
    obtain ⟨m, w, hsncE⟩ := hEi.2 (g q')
    have hjnot : (L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j ∉
        Set.range em :=
      hnotm j (fun ⟨a, ha⟩ => a.2 ha)
    have hsnc' : (((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j)
        ⟨i + 1, hiS⟩).append ((L.pushforward (T.E.component j).subschemeι).strictTransformSeq
          (T.E.component j) ⟨i + 1, hiS⟩)).IsSncAt (g q') w := by
      refine isSncAt_of_injective
        (fun b => Sum.elim em
          (fun _ => (L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j)
          (ofLex b)) ?_ ?_ hsncE
      · intro b₁ b₂ h12
        rcases b₁ with a₁ | u₁ <;> rcases b₂ with a₂ | u₂
        · have h12' : em a₁ = em a₂ := h12
          exact congrArg Sum.inl (hem h12')
        · have h12' : em a₁ =
              (L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j := h12
          exact absurd ⟨a₁, h12'⟩ hjnot
        · have h12' : em a₂ =
              (L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j :=
            h12.symm
          exact absurd ⟨a₂, h12'⟩ hjnot
        · cases u₁
          cases u₂
          rfl
      · intro b
        rcases b with a | u
        · exact hcompm a
        · exact component_originalIdx _ T.E ⟨i + 1, hiS⟩ j
    -- regular stalks, the maximal contact and the nonvanishing of the current ideal at `g q'`
    have hsmi : Smooth ((L.pushforward (T.E.component j).subschemeι).stageMap ⟨i + 1, hiS⟩ ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) := IsSmooth.smooth_stageMap' hsm ⟨i + 1, hiS⟩
    have hsmi' : SmoothOfRelativeDimension n₀
        ((L.pushforward (T.E.component j).subschemeι).stageMap ⟨i + 1, hiS⟩ ≫
          (T.X.left ↘ Spec (CommRingCat.of k))) :=
      IsSmooth.smoothOfRelativeDimension_stageMap hsm ⟨i + 1, hiS⟩
    have hregX := isRegularLocalRing_stalk
      ((L.pushforward (T.E.component j).subschemeι).stageMap ⟨i + 1, hiS⟩ ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) (g q')
    have hHsm' : Smooth ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) :=
      SmoothOfRelativeDimension.smooth (n₀ - 1) _
    have hLsmi : Smooth (L.stageMap ⟨i + 1, hi'⟩ ≫ (T.E.component j).subschemeι ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) := IsSmooth.smooth_stageMap' hL.1 ⟨i + 1, hi'⟩
    have hHK : ((L.pushforward (T.E.component j).subschemeι).strictTransformSeq (T.E.component j)
        ⟨i + 1, hiS⟩).stalkIdeal (g q') ≤
        ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1
          ⟨i + 1, hiS⟩).stalkIdeal (g q') := by
      have h := IsOrderSeq.strictTransformSeq_le_markedTransformSeq_MC
        (T.X.left ↘ Spec (CommRingCat.of k)) n₀ le_rfl hSord hHsm hle ⟨i + 1, hiS⟩
      rw [IdealSheafData.MC_one] at h
      exact IdealSheafData.stalkIdeal_mono h (g q')
    have hKq : ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1
        ⟨i + 1, hiS⟩).stalkIdeal (g q') ≠ ⊤ := by
      obtain ⟨ζ, hζ, hsp⟩ := Closeds.exists_mem_genericPoints_specializes _ hq
      have hcen := (hS.2 ⟨i + 1, hi⟩).2
      rw [hcenter] at hcen
      have h1 : (1 : ℕ∞) ≤ ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1
          ⟨i + 1, hiS⟩).ord (g q') :=
        (hcen ζ hζ).trans (IdealSheafData.ord_le_ord_of_specializes _
          ((L.pushforward (T.E.component j).subschemeι).stageMap ⟨i + 1, hiS⟩ ≫
            (T.X.left ↘ Spec (CommRingCat.of k))) n₀ hsp)
      have h2 := (IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
          ((IdealSheafData.one_le_ord_iff _ _).mp h1)
      intro htop
      rw [htop] at h2
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp h2)
    have hinner : CenterClassifiedAt
        (L.totalTransformSeq ((T.E.erase j).comap (T.E.component j).subschemeι) ⟨i + 1, hi'⟩)
        (L.markedTransformSeq (T.I.comap (T.E.component j).subschemeι) 1 ⟨i + 1, hi'⟩)
        Zc q' := hcp ⟨i, hiL'⟩ q' hq'
    rw [← hEcomap, ← hJcomap] at hinner
    have hK0 : (((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1
        ⟨i + 1, hiS⟩).comap g).stalkIdeal q' ≠ ⊥ := by
      rw [hJcomap]
      exact IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq
        (T'.X.left ↘ Spec (CommRingCat.of k)) n₁
        hL' T'.isNonzeroEverywhere ⟨i, Nat.lt_succ_of_lt hiL'⟩ q'
    have hmain : CenterClassifiedAt
        ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j) ⟨i + 1, hiS⟩)
        ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1 ⟨i + 1, hiS⟩)
        (Zc.map g) (g q') :=
      @centerClassifiedAt_of_comap_chain _ _ g hgci
        ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j) ⟨i + 1, hiS⟩)
        (((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j)
          ⟨i + 1, hiS⟩).comap g) id Function.injective_id (fun _ => rfl) Function.surjective_id
        _ hgker _ Zc q' hregX m w hsnc' hHK hKq hK0 hinner
    change CenterClassifiedAt
      ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j) ⟨i + 1, hiS⟩)
      ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1 ⟨i + 1, hiS⟩)
      (Zc.map g) (g q')
    intro n z c r σ a b hfree hb
    exact hmain z c σ a b hfree hb

/-- The pass with the mark carried as a variable (the mark of the tuned triple is
`tuningParam 1`). -/
theorem cp3For_rawSeq_erase_of_le_of_eq_one {Dom' : MarkedTriple k → Prop}
    (B' : OrderGeSeqAssignment k Dom') (T : Triple k) (j : T.E.ι) (m : ℕ) (hm1 : m = 1)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) (hn : T.HasDimLE N)
    (hDom' : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (N - 1) → T'.m = m → Dom' T')
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom' T'), T'.m = 1 → CP3For (B'.seq T' hT') T'.I T'.E)
    (hHJ : T.E.component j ≤ T.I) :
    CP3For (rawSeq T m j hI hmax hn B' hDom') T.I (T.E.erase j) := by
  subst hm1
  exact cp3For_rawSeq_erase_of_le B' T j hI hmax hn hDom' hcp3 hHJ

end Raw

section Step22

variable {N : ℕ} (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (N - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)
  (T : Triple k) (hn : T.HasDimLE N) (hmax : T.I.maxOrd ≤ 1) {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H) (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 H)

include hmax hH hle in
/-- CP3 along the re-tuned functor of Lemma 102 at the mark `1` on the Step 2.2 triple of an
arbitrary Step 2.1 run `S₁`, for `(I_r, E_r)` ([Kol07, 104, Step 2.2]; the proof of
[Kol07, Lemma 102]) — given CP3 for the inductive input `B` at the mark `1` and the passage fact
that the transforms of the original members miss `V(I_r)` when `max-ord I = 1`. -/
theorem cp3For_step22_aux (S₁ : BlowUpSequence T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E 1) (hne : S₁.NoEmptyCenters)
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hT₂ : Triple.BDClass N 1 (Fintype.card (S₁.exceptionalFamily T.E).ι)
      (step22TripleOfSeq T S₁ hS₁ hsnc))
    (hpass : T.I.maxOrd = 1 → ∀ (i : ℕ) (hi : i < Fintype.card T.E.ι),
      Disjoint (SetLike.coe (S₁.markedTransformSeq T.I 1 (Fin.last _)).support)
        (SetLike.coe (S₁.strictTransformSeq (T.E.nth ⟨i, hi⟩) (Fin.last _)).support))
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 →
      CP3For ((B k).seq T' hT') T'.I T'.E) :
    CP3For ((step22Functor (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) 1 _ le_rfl).seq
        (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂)
      (S₁.markedTransformSeq T.I 1 (Fin.last _)) (S₁.totalTransformSeq T.E (Fin.last _)) := by
  classical
  -- standing facts on the Step 2.1 run
  obtain ⟨n', hn'⟩ := T.smoothOfRelativeDimension
  have hsmn : SmoothOfRelativeDimension n' (T.X.left ↘ Spec (.of k)) := hn'
  have hge : S₁.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (.of k)) n' hS₁
  -- the Step 2.2 triple `T₂` (on `X_r`)
  set T₂ := step22TripleOfSeq T S₁ hS₁ hsnc with hT₂def
  obtain ⟨n₂, hn₂⟩ := T₂.smoothOfRelativeDimension
  have hsm₂ : SmoothOfRelativeDimension n₂ (T₂.X.left ↘ Spec (.of k)) := hn₂
  have hLN₂ : IsLocallyNoetherian T₂.X.left :=
    (T₂.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  have hle₂ : T₂.I.maxOrd ≤ ((1 : ℕ) : ℕ∞) := maxOrd_induced_last_le T hmax hS₁ hne
  by_cases h1 : T₂.I.maxOrd = ((1 : ℕ) : ℕ∞)
  swap
  · -- below the mark the re-tuned Lemma 102 is the empty sequence: nothing to classify
    rw [step22Functor_seq_of_maxOrd_lt _ 1 _ le_rfl T₂ hT₂ (lt_of_le_of_ne hle₂ h1)]
    intro i
    exact i.elim0
  -- at the mark: `max-ord I = 1` as well (below it Step 2.1 is empty and `I_r = I`)
  have hm1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞) := by
    by_contra hcon
    have hl : T.I.maxOrd < 1 := lt_of_le_of_ne hmax hcon
    have hnil := Hironaka.BO.eq_nil_of_isOrderSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k)) hS₁ hne hl
    subst hnil
    change T.I.maxOrd = ((1 : ℕ) : ℕ∞) at h1
    exact absurd h1 hcon
  have hm1' : T.I.maxOrd = 1 := by rwa [Nat.cast_one] at hm1
  have hmw : S₁.markedTransformSeq T.I 1 (Fin.last _) = S₁.weakTransformSeq T.I (Fin.last _) :=
    IsOrderGeSeq.markedTransformSeq_eq_weakTransformSeq (T.X.left ↘ Spec (.of k)) n' hm1 hge
      (Fin.last _)
  have hT₂I : T₂.I = S₁.markedTransformSeq T.I 1 (Fin.last _) := hmw.symm
  -- Lemma 102's functor at the mark `1` on `T₂`, then the raw output with its empty blow-ups
  -- deleted on the tuned triple `T₃`
  have e2 : (((fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) (tuningParam 1)
        (Fintype.card (S₁.exceptionalFamily T.E).ι)).functor k).seq (T₂.tuned 1 le_rfl)
        (bdClass_tuned hT₂ h1 le_rfl) =
      ((bdData N 1 (Fintype.card (S₁.exceptionalFamily T.E).ι) Dom B (hDom 1) hB hsm
        hbc).functor k).seq T₂ hT₂ :=
    functor_seq_congr_mark (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) _ T₂
      (tuningParam 1) tuningParam_one _ (IdealSheafData.W_tuningParam_one _ _) _ _ hT₂
  rw [step22Functor_seq_of_maxOrd_eq _ 1 _ le_rfl T₂ hT₂ h1, e2]
  change CP3For ((dataFunctor N 1 _ le_rfl (B k) (hDom 1 k)).seq T₂ hT₂) _ _
  rw [dataFunctor_seq_of_maxOrd_eq N 1 _ le_rfl (B k) (hDom 1 k) T₂ hT₂ h1,
    Hironaka.BD.functor_seq]
  set T₃ := T₂.tuned 1 le_rfl with hT₃
  have hdom₃ := domain_tuned (n := N) (m := 1) le_rfl hT₂ h1
  set j₃ := monoEquivOfFin T₃.E.ι rfl ⟨Fintype.card (S₁.exceptionalFamily T.E).ι, hdom₃.2.2.2⟩
    with hj₃
  have hsm₃ : SmoothOfRelativeDimension n₂ (T₃.X.left ↘ Spec (.of k)) := hn₂
  have hLN₃ : IsLocallyNoetherian T₃.X.left := hLN₂
  have hLN₁ : IsLocallyNoetherian (S₁.stage (Fin.last _)) := hLN₂
  have hI₃ : T₃.I = S₁.markedTransformSeq T.I 1 (Fin.last _) := by
    change IdealSheafData.W (T₂.X.left ↘ Spec (.of k)) T₂.I 1 (tuningParam 1) = _
    rw [IdealSheafData.W_tuningParam_one]
    exact hT₂I
  -- the member `H_r` at the appended position and the indices of `(F_r + H_r) − H_r`
  have hH₃ : T₃.E.component j₃ = S₁.strictTransformSeq H (Fin.last _) :=
    nth_append_last (S₁.exceptionalFamily T.E) (S₁.strictTransformSeq H (Fin.last _)) _
  have h7 : ∀ b : (T₃.E.erase j₃).ι, ∃ a : (S₁.exceptionalFamily T.E).ι,
      b.1 = toLex (Sum.inl a) :=
    exists_eq_inl_of_erase_append_last (S₁.exceptionalFamily T.E)
      (S₁.strictTransformSeq H (Fin.last _)) _
  -- `H_r` is a smooth hypersurface of maximal contact for `I_r` at the end of Step 2.1
  have hle' : H ≤ IdealSheafData.MC (T.X.left ↘ Spec (.of k)) T.I 1 := hle
  have hHJ₃ : T₃.E.component j₃ ≤ T₃.I := by
    rw [hH₃, hI₃]
    exact IsOrderSeq.strictTransformSeq_le_markedTransformSeq_MC (T.X.left ↘ Spec (.of k)) n' le_rfl
      hS₁ hH hle' (Fin.last _)
  -- the raw output's order property for the family `(F_r + H_r) − H_r`, at the mark `1`
  have hS₃ : (rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
      (hDom 1 k)).IsOrderGeSeq (T₃.X.left ↘ Spec (.of k)) T₃.I 1 (T₃.E.erase j₃) := by
    have h := IsOrderSeq.isOrderGeSeq (T₃.X.left ↘ Spec (.of k)) n₂
      (isOrderSeq_rawSeq_erase T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
        (hDom 1 k))
    exact (congrArg (fun m => (rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1
      (B k) (hDom 1 k)).IsOrderGeSeq (T₃.X.left ↘ Spec (.of k)) T₃.I m (T₃.E.erase j₃))
      tuningParam_one).mp h
  have hSE : (rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
      (hDom 1 k)).eraseEmpty.IsOrderGeSeq (T₃.X.left ↘ Spec (.of k)) T₃.I 1 (T₃.E.erase j₃) :=
    IsOrderGeSeq.eraseEmpty (T₃.X.left ↘ Spec (.of k)) n₂ hS₃
  -- the family bridge from `(F_r + H_r) − H_r` to the full `E_r`
  let e₀ : (T₃.E.erase j₃).ι → (S₁.totalTransformSeq T.E (Fin.last _)).ι :=
    fun b => (Classical.choose (h7 b)).1
  have he₀ : Function.Injective e₀ := by
    intro b b' hbb'
    have hb := Classical.choose_spec (h7 b)
    have hb' := Classical.choose_spec (h7 b')
    have h2 : Classical.choose (h7 b) = Classical.choose (h7 b') := Subtype.ext hbb'
    exact Subtype.ext (hb.trans (by rw [h2]; exact hb'.symm))
  have hcomp₀ : ∀ b, (S₁.totalTransformSeq T.E (Fin.last _)).component (e₀ b) =
      (T₃.E.erase j₃).component b := by
    intro b
    change _ = T₃.E.component b.1
    rw [Classical.choose_spec (h7 b)]
    rfl
  have hj₃inr : j₃ = toLex (Sum.inr PUnit.unit) := monoEquivOfFin_lex_inr_last _
  refine cp3For_of_embeds _ _ e₀ he₀ hcomp₀ ?_ ?_
  · -- the missing members are the originals' transforms; they miss `V(I_r)`, hence every centre
    intro i q hq a ha
    -- `a` is not exceptional: it is the transform of an original member `t`
    have horig : ∃ t : T.E.ι, a = S₁.originalIdx T.E (Fin.last _) t := by
      by_contra hcon
      have hex : ∀ t, a ≠ S₁.originalIdx T.E (Fin.last _) t := fun t ht => hcon ⟨t, ht⟩
      have hne : toLex (Sum.inl (⟨a, hex⟩ : (S₁.exceptionalFamily T.E).ι)) ≠ j₃ := by
        rw [hj₃inr]
        intro h
        exact absurd (toLex_inj.mp h) Sum.inl_ne_inr
      set b₀ : (T₃.E.erase j₃).ι :=
        ⟨toLex (Sum.inl (⟨a, hex⟩ : (S₁.exceptionalFamily T.E).ι)), hne⟩ with hb₀
      refine ha (Set.mem_range.mpr ⟨b₀, ?_⟩)
      change (Classical.choose (h7 b₀)).1 = a
      have hsp := Classical.choose_spec (h7 b₀)
      change toLex (Sum.inl (⟨a, hex⟩ : (S₁.exceptionalFamily T.E).ι)) = toLex (Sum.inl _) at hsp
      exact (congrArg Subtype.val (Sum.inl.inj (toLex_inj.mp hsp))).symm
    obtain ⟨t, rfl⟩ := horig
    -- the point lies on `V(I_i)` (the centre has order `≥ 1`), which misses the transform of `E^t`
    have hqI : q ∈ ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
        (hDom 1 k)).eraseEmpty.markedTransformSeq (S₁.markedTransformSeq T.I 1 (Fin.last _)) 1
        i.castSucc).support := by
      rw [← hI₃]
      obtain ⟨ζ, hζ, hsp⟩ := Closeds.exists_mem_genericPoints_specializes _ hq
      have hsmi : SmoothOfRelativeDimension n₂
          ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
            (hDom 1 k)).eraseEmpty.stageMap i.castSucc ≫ (T₃.X.left ↘ Spec (.of k))) :=
        IsSmooth.smoothOfRelativeDimension_stageMap hSE.1 i.castSucc
      have h1' : (1 : ℕ∞) ≤ ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
          (hDom 1 k)).eraseEmpty.markedTransformSeq T₃.I 1 i.castSucc).ord q :=
        ((hSE.2 i).2 ζ hζ).trans (IdealSheafData.ord_le_ord_of_specializes _
          ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
            (hDom 1 k)).eraseEmpty.stageMap i.castSucc ≫ (T₃.X.left ↘ Spec (.of k))) n₂ hsp)
      exact (IdealSheafData.one_le_ord_iff _ _).mp h1'
    -- the transform of `E^t` misses `V(I_r)`, hence `V(I_i)`
    obtain ⟨idx, hidx, hnth⟩ : ∃ (idx : ℕ) (hidx : idx < Fintype.card T.E.ι),
        T.E.nth ⟨idx, hidx⟩ = T.E.component t :=
      ⟨((monoEquivOfFin T.E.ι rfl).symm t).val, ((monoEquivOfFin T.E.ι rfl).symm t).isLt, by
        change T.E.component (monoEquivOfFin T.E.ι rfl ⟨_, _⟩) = _
        rw [Fin.eta, OrderIso.apply_symm_apply]⟩
    have hD : Disjoint (SetLike.coe (S₁.markedTransformSeq T.I 1 (Fin.last _)).support)
        (SetLike.coe (S₁.strictTransformSeq (T.E.component t) (Fin.last _)).support) := by
      rw [← hnth]
      exact hpass hm1' idx hidx
    have hdisj := disjoint_support_markedTransformSeq_strictTransformSeq _ _ _ hD i.castSucc
    rw [component_originalIdx ((rawSeq T₃ (tuningParam 1) j₃ hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (B k)
      (hDom 1 k)).eraseEmpty) (S₁.totalTransformSeq T.E (Fin.last _)) i.castSucc
      (S₁.originalIdx T.E (Fin.last _) t), component_originalIdx S₁ T.E (Fin.last _) t]
    exact Set.disjoint_left.mp hdisj hqI
  · -- CP3 along the raw output for the tuned data, then the empty blow-ups deleted
    rw [← hI₃]
    refine cp3For_eraseEmpty (T₃.X.left ↘ Spec (.of k)) n₂ _ T₃.I (T₃.E.erase j₃) hS₃ ?_
    exact cp3For_rawSeq_erase_of_le_of_eq_one (B k) T₃ j₃ (tuningParam 1) tuningParam_one
      hdom₃.2.1 hdom₃.2.2.1 hdom₃.1 (hDom 1 k) hcp3 hHJ₃

/-- **CP3 along Step 2.2** ([Kol07, 104, Step 2.2]; the proof of [Kol07, Lemma 102]) with the data
`bdData`, given CP3 for the inductive input `B` at the mark `1`: CP3 along Step 2.2 for
`(I_r, E_r)`, `E_r` the FULL total transform of `E`. -/
theorem cp3For_step22
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom k T'), T'.m = 1 →
      CP3For ((B k).seq T' hT') T'.I T'.E) :
    CP3For (step22 T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH hle)
      ((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
        (Fintype.card T.E.ι)).1.markedTransformSeq T.I 1 (Fin.last _))
      ((step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
        (Fintype.card T.E.ι)).1.totalTransformSeq T.E (Fin.last _)) :=
  cp3For_step22_aux Dom B hDom hB hsm hbc T hmax hH hle
    (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1
    (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).2.1
    (step21Seq T hn hmax (fun j => bdData N 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).2.2
    (step22Triple T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH
      hle).isSnc
    (bdClass_step22Triple T hn hmax (fun m j => bdData N m j Dom B (hDom m) hB hsm hbc) le_rfl hH
      hle)
    (fun hm1' _ hi => disjoint_support_markedTransformSeq_step21_final T hn hmax _ hm1' hi)
    hcp3

end Step22

end Hironaka.Resolution
