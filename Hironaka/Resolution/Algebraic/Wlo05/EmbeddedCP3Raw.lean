/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.Center
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.GoingUp
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Bookkeeping
import Hironaka.Resolution.Algebraic.MaximalContact.Sequence
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedBridge
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Subfamily
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Pass
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Split
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step3
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.RelativeDimension
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 along the raw output of Lemma 102 over a member

[Kol07, Lemma 102] on a triple `(X, I, E)` with `max-ord I = 1` and a member `Eʲ`: blow up `Z₋₁`,
the union of the components of `Eʲ` inside `V(I)`, then push forward the inductive run on the
strict transform of `Eʲ` (`rawSeq`, `Hironaka.Resolution.Algebraic.BoundaryClearing.Restriction`).
For the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) its centres are classified at every
point for the outer data `(I, E)` from the inductive classification:

* at a point `q` of `Z₋₁` (stage `0`; `map_centerS`) the stalk of the centre is the stalk of `Eʲ`
  (`stalkIdeal_Zminus1_eq`), the coordinate `z (c j)` of the member — the stratum of level `0`
  with `s = {c j}`, whose admissibility condition (★) `b (c j) ≠ 0` is the order of `I` at the
  generic point of the component of `Eʲ` through `q`, which is `1` because that component lies in
  `Z₋₁` (`mem_support_Zminus1_iff_ord_eq`) — read through the exponent identity
  `toNat_ord_eq_of_stalkIdeal_eq_span_mul` for either shape;
* at a point of a later centre — the push-forward of a centre of the inductive run along the stage
  inclusion `g` (`center_pushforward_mk`, `support_map`) — the identities of [Kol07, Lemma 62] read
  the outer boundary `E − Eʲ` and the outer marked transform on the strict transform of `Eʲ` as
  the data of the inductive run (`pullback_pushforward`, `pullbackStageHom_pushforward_heq_mk`,
  `totalTransformSeq_comap_pullbackStageHom_of_forall_lt` with `(E − Eʲ) + Eʲ` snc,
  `IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk`); the total transform of `E − Eʲ`
  embeds in that of `E` with the transform of `Eʲ` as the only member outside the range
  (`exists_embeds_totalTransformSeq`, `component_originalIdx` = the kernel of `g`); the family of
  the inductive run is snc (`isSnc_restrictedFamily`) and its marked ideal nonzero
  (`isNonzeroEverywhere_markedTransformSeq`); and the pointwise pass
  `centerClassifiedAt_of_comap_member` (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Pass`) lifts
  the inductive classification.

No smoothness of `Eʲ` and no inclusion `Eʲ ≤ I` is assumed: the passes of Step 2.1 of the proof of
[Kol07, Theorem 103] have neither. This argument is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step21` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step22`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BD Hironaka.BMO

namespace Hironaka.Resolution

section Raw

variable {k : Type u} [Field k] [CharZero k] {N : ℕ}

/-- **CP3 along the raw output of Lemma 102 over a member `Eʲ`** for the outer data `(I, E)`, from
CP3 for the values of the inductive functor `B'` at the mark `1` ([Kol07, Lemma 102] and
[Kol07, Lemma 62]): at a point of `Z₋₁` the stratum of level `0` given by the coordinate of `Eʲ`;
at a point of a later centre the pointwise pass `centerClassifiedAt_of_comap_member` on the stage
inclusion, with the identities of Lemma 62. -/
theorem cp3For_rawSeq_member {Dom' : MarkedTriple k → Prop} (B' : OrderGeSeqAssignment k Dom')
    (T : Triple k) (j : T.E.ι) (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) 1)
    (hmax : T.I.maxOrd = 1) (hn : T.HasDimLE N)
    (hDom' : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (N - 1) → T'.m = 1 → Dom' T')
    (hcp3 : ∀ (T' : MarkedTriple k) (hT' : Dom' T'), T'.m = 1 → CP3For (B'.seq T' hT') T'.I T'.E) :
    CP3For (rawSeq T 1 j hI hmax hn B' hDom') T.I T.E := by
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
  have hS : (L.pushforward (T.E.component j).subschemeι).IsOrderGeSeq
      (T.X.left ↘ Spec (CommRingCat.of k)) T.I 1 (T.E.erase j) :=
    IsOrderSeq.isOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) n₀
      (isOrderSeq_rawSeq_erase T 1 j hI hmax hn B' hDom')
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
  rw [hraw]
  rintro ⟨i, hi⟩ q hq
  cases i with
  | zero =>
    -- the first centre `Z₋₁`: the components of `Eʲ` inside `V(I)`
    have hc0 : (L.pushforward (T.E.component j).subschemeι).center ⟨0, hi⟩ =
        Zminus1 T.I 1 (T.E.component j) := by
      change (centerS T 1 j).map (T.E.component j).subschemeι = _
      exact map_centerS T 1 j
    rw [hc0] at hq ⊢
    change CenterClassifiedAt T.E T.I (Zminus1 T.I 1 (T.E.component j)) q
    have hqj : q ∈ (T.E.component j).support := support_Zminus1_le T 1 j hq
    obtain ⟨η, hη, hord, hηq⟩ := (mem_support_Zminus1_iff_ord_eq T 1 j hmax q).mp hq
    have hZq : (Zminus1 T.I 1 (T.E.component j)).stalkIdeal q = (T.E.component j).stalkIdeal q :=
      stalkIdeal_Zminus1_eq T 1 j hq
    have hreg := isRegularLocalRing_stalk (T.X.left ↘ Spec (CommRingCat.of k)) q
    intro n z c r σ a b hfree hb
    obtain ⟨hz, hcinj, hcmem, -, -, -⟩ := id hfree
    have hZs : (Zminus1 T.I 1 (T.E.component j)).stalkIdeal q =
        Ideal.span ((z ∘ σ) '' {i : Fin (r + 1) | i.val < 0}) ⊔
          Ideal.span (z '' ↑({c ⟨j, hqj⟩} : Finset (Fin n))) := by
      rw [hZq, hcmem ⟨j, hqj⟩]
      have hempty : ((z ∘ σ) '' {i : Fin (r + 1) | i.val < 0}) = ∅ :=
        Set.image_eq_empty.mpr (Set.eq_empty_iff_forall_notMem.mpr fun i hi => Nat.not_lt_zero _ hi)
      rw [hempty, Ideal.span_empty, bot_sup_eq, Finset.coe_singleton, Set.image_singleton]
    have hstrat : ∀ C : Ideal (T.X.left.presheaf.stalk q),
        (nonmonomialPart T.I T.E).stalkIdeal q = C →
        T.I.stalkIdeal q = Ideal.span {monomialOf z b} * C →
        StratumIn z (Set.range c) σ a b ((Zminus1 T.I 1 (T.E.component j)).stalkIdeal q) := by
      intro C hNC hK
      refine ⟨0, Nat.zero_le _, {c ⟨j, hqj⟩}, ?_, hZs,
        fun _ => ⟨c ⟨j, hqj⟩, Finset.mem_singleton_self _, ?_⟩, fun h => absurd h (lt_irrefl 0)⟩
      · rw [Finset.coe_singleton]
        exact Set.singleton_subset_iff.mpr ⟨_, rfl⟩
      · have hexp := toNat_ord_eq_of_stalkIdeal_eq_span_mul (T.X.left ↘ Spec (CommRingCat.of k)) n₀
          T.isSnc T.isNonzeroEverywhere hz hcinj hcmem hb hNC hK ⟨j, hqj⟩ hη hηq
        rw [← hexp, hord, ENat.toNat_natCast]
        exact one_ne_zero
    exact ⟨fun hK => hstrat _ (stalkIdeal_nonmonomialPart_of_kShape
        (T.X.left ↘ Spec (CommRingCat.of k)) n₀ T.isSnc T.isNonzeroEverywhere hfree hb hK) hK,
      fun hI' => Or.inl (hstrat _ (stalkIdeal_nonmonomialPart_of_iShape
        (T.X.left ↘ Spec (CommRingCat.of k)) n₀ T.isSnc T.isNonzeroEverywhere hfree hb hI') hI')⟩
  | succ i =>
    -- a later centre: the push-forward of an inner centre along the stage inclusion
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
    -- Lemma 62 at stage `i + 1`: the boundary and the marked transform restrict to `Eʲ`
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
    -- the erased family's total transform embeds in the full one, missing only `Eʲ`'s transform
    obtain ⟨em, hem, hcompm, hmissm⟩ := exists_embeds_totalTransformSeq (E₁ := T.E.erase j)
      (E₂ := T.E) (L.pushforward (T.E.component j).subschemeι)
      (Subtype.val : (T.E.erase j).ι → T.E.ι) Subtype.val_injective (fun _ => rfl) ⟨i + 1, hiS⟩
    -- regular stalks on both sides
    have hsmi : Smooth ((L.pushforward (T.E.component j).subschemeι).stageMap ⟨i + 1, hiS⟩ ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) := IsSmooth.smooth_stageMap' hsm ⟨i + 1, hiS⟩
    have hregX := isRegularLocalRing_stalk
      ((L.pushforward (T.E.component j).subschemeι).stageMap ⟨i + 1, hiS⟩ ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) (g q')
    have hHsm' : Smooth ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) :=
      SmoothOfRelativeDimension.smooth (n₀ - 1) _
    have hLsmi : Smooth (L.stageMap ⟨i + 1, hi'⟩ ≫ (T.E.component j).subschemeι ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) := IsSmooth.smooth_stageMap' hL.1 ⟨i + 1, hi'⟩
    have hregY := isRegularLocalRing_stalk
      (L.stageMap ⟨i + 1, hi'⟩ ≫ (T.E.component j).subschemeι ≫
        (T.X.left ↘ Spec (CommRingCat.of k))) q'
    -- the inner classification, in the closed-immersion form
    have hinner : CenterClassifiedAt
        (L.totalTransformSeq ((T.E.erase j).comap (T.E.component j).subschemeι) ⟨i + 1, hi'⟩)
        (L.markedTransformSeq (T.I.comap (T.E.component j).subschemeι) 1 ⟨i + 1, hi'⟩)
        Zc q' := hcp ⟨i, hiL'⟩ q' hq'
    rw [← hEcomap, ← hJcomap] at hinner
    have hF : (((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j)
        ⟨i + 1, hiS⟩).comap g).IsSnc := by
      rw [hEcomap]
      exact IsOrderGeSeq.isSnc_totalTransformSeq
        ((T.E.component j).subschemeι ≫ (T.X.left ↘ Spec (CommRingCat.of k))) (n₀ - 1) hL
        (isSnc_restrictedFamily T j) ⟨i + 1, hi'⟩
    have hK0 : (((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1
        ⟨i + 1, hiS⟩).comap g).stalkIdeal q' ≠ ⊥ := by
      rw [hJcomap]
      exact IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq
        (T'.X.left ↘ Spec (CommRingCat.of k)) n₁
        hL' T'.isNonzeroEverywhere ⟨i, Nat.lt_succ_of_lt hiL'⟩ q'
    have hmiss : ∀ b, b ∉ Set.range em →
        b = (L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j := by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := hmissm b hb
      have haj : a = j := by
        by_contra hne
        exact ha ⟨⟨a, hne⟩, rfl⟩
      rw [haj]
    have hkerE : g.ker = ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq T.E
        ⟨i + 1, hiS⟩).component
          ((L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j) := by
      rw [component_originalIdx, hgker]
    have hcomp' : ∀ a, (((L.pushforward (T.E.component j).subschemeι).totalTransformSeq
        (T.E.erase j) ⟨i + 1, hiS⟩).comap g).component a =
        (((L.pushforward (T.E.component j).subschemeι).totalTransformSeq T.E
          ⟨i + 1, hiS⟩).component (em a)).comap g := by
      intro a
      rw [hcompm a]
      rfl
    have hmain : CenterClassifiedAt
        ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq T.E ⟨i + 1, hiS⟩)
        ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1 ⟨i + 1, hiS⟩)
        (Zc.map g) (g q') :=
      @centerClassifiedAt_of_comap_member _ _ g hgci
        ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq T.E ⟨i + 1, hiS⟩)
        (((L.pushforward (T.E.component j).subschemeι).totalTransformSeq (T.E.erase j)
          ⟨i + 1, hiS⟩).comap g) em hem hcomp'
        ((L.pushforward (T.E.component j).subschemeι).originalIdx T.E ⟨i + 1, hiS⟩ j) hkerE hF
        hmiss ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1 ⟨i + 1, hiS⟩)
        Zc q' hregX hregY hK0 hinner
    change CenterClassifiedAt
      ((L.pushforward (T.E.component j).subschemeι).totalTransformSeq T.E ⟨i + 1, hiS⟩)
      ((L.pushforward (T.E.component j).subschemeι).markedTransformSeq T.I 1 ⟨i + 1, hiS⟩)
      (Zc.map g) (g q')
    intro n z c r σ a b hfree hb
    exact hmain z c σ a b hfree hb

end Raw

end Hironaka.Resolution
