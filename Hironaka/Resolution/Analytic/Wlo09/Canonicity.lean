/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Rounds
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyCommute
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackLemmas
import Hironaka.Manifold.FiniteSuccession.Functor.PullbackTriple
import Hironaka.Resolution.Analytic.OrderReduction.FamilyOrder
import Hironaka.Resolution.Analytic.OrderReduction.Finiteness
import Hironaka.Resolution.Analytic.OrderReduction.Step21Fam
import Hironaka.Resolution.Analytic.Wlo09.Comp
import Hironaka.Resolution.Analytic.Wlo09.EmptyRound
import Hironaka.Resolution.Analytic.Wlo09.TopRound
import Hironaka.Resolution.Analytic.Wlo09.Transport
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Canonicity of the rounds, compatibility, and the resolution family

The value of the rounds of the resolution family on a relatively compact open `U` does not depend
on the admissible chain along which they are read (`resolveSeqOnAlong_chain_indep`), the values on
`U ≤ V` are compatible under restriction up to empty blow-ups (`resolveSeqOn_compat`), and the
family `resolveFam : CompatibleFamily T` is assembled with that `compat` field. This is the
compatibility clause of Włodarczyk's locally finite principalization [Wlo09, Theorem 2.0.3 (4)];
on the side of the functors it is the behaviour of a blow-up sequence functor under smooth
morphisms [Kol07, 34.1] together with the remark after [Kol07, Theorem 68] that the rounds above
the order bound are empty.

The proof rests on `Resolve/{Comp,EmptyRound,Transport,TopRound,Indiff}.lean`. Two admissible
chains of the same length, one inside the other, have the same value: `eraseEmpty_resolveFrom_congr`
along the inclusion of the outermost opens, the identity on `U`, and `pullback_id`
(`resolveSeqOnAlong_eq_of_le`). A chain one round longer than a chain inside it has the same value:
its top round has no centre over the shorter chain's outermost open, where the order is below the
round's mark, so `eraseEmpty_resolveFrom_succ_eq_restrict` drops it (the low-order chain being the
shorter chain's opens traced on the longer one's outermost open), and `eraseEmpty_resolveFrom_congr`
along `restrictMap` carries the rounds from that region, an open of an open, to the shorter chain's
outermost open (`resolveSeqOnAlong_eq_of_succ`; the closure hypothesis comes from
`closure U ⊆ W 1 ⊆ W m`, so one round must remain). The bridge from an arbitrary chain `c` to the
canonical one is `c.shrunk`: `c` cut down by the iterated shrinks of `closure U` inside
`{ord ≤ d_U}` (`shrinkChain`), of any length `m` between `d_U` and `c.D`; every one of its opens
has order `≤ d_U`, so every truncation is admissible. Then (`resolveSeqOnAlong_eq_canonical`): a
chain with no round has the order vanishing on `U`, and both values are empty by
`eraseEmpty_resolveFrom_eq_nil_of_ord_eq_zero`; otherwise `d_U ≤ c.D` since `closure U` lies in
the outermost open, `c` equals its cut-down of full length, the cut-downs of consecutive lengths
agree (the same lemma at the last drop, from one round to none, when `d_U = 0`), and the cut-down
of length `d_U` lies inside the canonical chain. Canonicity is two applications; compatibility
reads the canonical chain of `V` as a chain for `U`, whose reading map is the reading map of `V`
after the inclusion `U ≤ V`: canonicity, `resolveFrom_congr_ι`, `resolveFrom_comp` and
`eraseEmpty_pullback_eraseEmpty`.

* `resolveSeqOnAlong_eq_of_le`, `resolveSeqOnAlong_eq_of_succ`: the two comparison lemmas.
* `ResolveChain.shrunk`, `ResolveChain.ord_le_maxOrdOn_of_mem_shrunk`, `maxOrdOn_le`,
  `resolveSeqOnAlong_eq_nil_of_ord_eq_zero`: the cut-down chain, the order bound, the empty value
  of a chain with no round.
* `resolveSeqOnAlong_eq_canonical`: every admissible chain has the canonical value.
* `resolveSeqOnAlong_chain_indep`, `resolveSeqOn_compat`, `resolveFam`.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace AnalyticManifold
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (bo : ∀ d : ℕ, BOanFam.{u} 𝕜 n d)
  {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  {T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M} {U : Opens M}

/-! ### Lemma A: nested chains of the same length -/

/-- **Two admissible chains of the same length, one inside the other, have the same value**
([Kol07, 34.1]; [Wlo09, Theorem 2.0.3 (4)]): `eraseEmpty_resolveFrom_congr` along the inclusion of
the outermost opens (`restrictLE`), the identity on `U`, and `pullback_id`. -/
theorem resolveSeqOnAlong_eq_of_le (c c' : ResolveChain T U) (hD : c.D = c'.D)
    (hW : ∀ k, k ≤ c.D → c.W k ≤ c'.W k) :
    resolveSeqOnAlong bo T U c = resolveSeqOnAlong bo T U c' := by
  obtain ⟨D, W, hWc, hWs, hU0, hord⟩ := c
  obtain ⟨D', W', hWc', hWs', hU0', hord'⟩ := c'
  obtain rfl : D = D' := hD
  set c₁ : ResolveChain T U := ⟨D, W, hWc, hWs, hU0, hord⟩ with hc₁
  set c₂ : ResolveChain T U := ⟨D, W', hWc', hWs', hU0', hord'⟩ with hc₂
  have hWD : W D ≤ W' D := hW D le_rfl
  have hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω (M.restrictLE hWD) :=
    isLocalDiffeomorph_restrictLE hWD
  -- the outer triple of `c₁` is the pull-back of the outer triple of `c₂` along the inclusion
  have hpb : c₁.outerTriple = c₂.outerTriple.pullback (M.restrictLE hWD) hg := by
    change T.pullback (M.inclusion (W D)) _ = (T.pullback (M.inclusion (W' D)) _).pullback _ hg
    rw [AnalyticTriple.pullback_pullback _ _ _ _ _]
    exact AnalyticTriple.pullback_eq_of_eq T (ContMDiffMap.ext fun _ => rfl) _ _
  have hΩg : ∀ k, k < D → ⇑(M.restrictLE hWD) '' (c₁.trace k : Set (M.restrict (W D))) ⊆
      c₂.trace k := by
    rintro k hk _ ⟨p, hp, rfl⟩
    exact hW k hk.le hp
  have h := eraseEmpty_resolveFrom_congr bo D (M.restrictLE hWD) hg c₂.outerTriple c₁.outerTriple
    (by rw [hpb]; exact AnalyticTriple.isPullbackOf_pullback _ _ _)
    c₂.outerTriple_ord_le c₂.outerTriple_finite c₁.outerTriple_ord_le c₁.outerTriple_finite
    c₂.trace c₂.isCompact_closure_trace c₂.closure_trace_subset
    c₁.trace c₁.isCompact_closure_trace c₁.closure_trace_subset hΩg
    (M.restrictLE c₂.le_outerOpen) (isLocalDiffeomorph_restrictLE _)
    c₂.range_restrictLE_subset_trace
    (M.restrictLE c₁.le_outerOpen) (isLocalDiffeomorph_restrictLE _)
    c₁.range_restrictLE_subset_trace
    (ContMDiffMap.id : AnalyticMap (M.restrict U) (M.restrict U))
    (BlowUpSequence.isLocalDiffeomorph_id _)
    (ContMDiffMap.ext fun _ => rfl)
  exact h.trans (congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_id _))

/-! ### Lemma B: dropping the top round of a chain one longer -/

/-- **A chain one round longer than a chain inside it has the same value** (the remark after
[Kol07, Theorem 68]). The top round has no centre over the shorter chain's outermost open, where
the order is below the round's mark: `eraseEmpty_resolveFrom_succ_eq_restrict` drops it (the
low-order chain is the shorter chain's opens traced on the longer one's outermost open; its
closure hypothesis is `closure U ⊆ W 1 ⊆ W m`, whence one round must remain), and
`eraseEmpty_resolveFrom_congr` along `restrictMap` carries the rounds from that region, an open of
an open, to the shorter chain's outermost open. -/
theorem resolveSeqOnAlong_eq_of_succ (c₁ c₂ : ResolveChain T U) (hD : c₁.D = c₂.D + 1)
    (hW : ∀ k, k ≤ c₂.D → c₂.W k ≤ c₁.W k) (h1 : 1 ≤ c₂.D) :
    resolveSeqOnAlong bo T U c₁ = resolveSeqOnAlong bo T U c₂ := by
  obtain ⟨D₁, W₁, hWc₁, hWs₁, hU₁, hord₁⟩ := c₁
  obtain ⟨m, W₂, hWc₂, hWs₂, hU₂, hord₂⟩ := c₂
  obtain rfl : D₁ = m + 1 := hD
  set c₁ : ResolveChain T U := ⟨m + 1, W₁, hWc₁, hWs₁, hU₁, hord₁⟩ with hc₁
  set c₂ : ResolveChain T U := ⟨m, W₂, hWc₂, hWs₂, hU₂, hord₂⟩ with hc₂
  have h1' : 1 ≤ m := h1
  /- ### The top round on `c₁`, and the low-order chain `ΩZ` inside it: the opens of `c₂` -/
  set X := M.restrict (W₁ (m + 1)) with hXdef
  set cur := c₁.outerTriple with hcur
  set ι := M.restrictLE c₁.le_outerOpen with hιdef
  set ΩZ : ℕ → Opens X := fun k => traceOn (W₁ (m + 1)) (W₂ k) with hΩZdef
  have hWm : ∀ k, k ≤ m → W₂ k ≤ W₁ (m + 1) := fun k hk =>
    ((hW k hk).trans (c₁.le_of_le (Nat.le_succ_of_le hk) le_rfl))
  have hcl : ∀ k, k ≤ m → closure (W₂ k : Set M) ⊆ W₁ (m + 1) := fun k hk =>
    (closure_mono ((c₂.le_of_le hk le_rfl).trans (hW m le_rfl))).trans
      (c₁.closure_subset m (Nat.lt_succ_self m))
  have hΩZ : ∀ k, k ≤ m → IsCompact (closure (ΩZ k : Set X)) := fun k hk =>
    isCompact_closure_preimage_val_of_closure_subset (c₂.isCompact_closure k hk) (hcl k hk)
  have hΩZsub : ∀ k, k < m → closure (ΩZ k : Set X) ⊆ ΩZ (k + 1) := fun k hk =>
    (continuous_subtype_val.closure_preimage_subset _).trans
      (Set.preimage_mono (c₂.closure_subset k hk))
  have hΩZle : ∀ k, k < m → ΩZ k ≤ c₁.trace k := fun k hk _ hx => hW k hk.le hx
  have hZord : ∀ x ∈ ΩZ m, cur.I.ord x ≤ (m : ℕ∞) := fun x hx =>
    (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt T.I (M.inclusion (W₁ (m + 1)))
      (isLocalDiffeomorph_inclusion M _ x)).trans_le (c₂.ord_le _ hx)
  have hrangeZ : Set.range ι ⊆ ΩZ 0 := by
    rintro _ ⟨y, rfl⟩
    exact c₂.le_zero y.2
  have hclosure : closure (Set.range ι) ⊆ ΩZ m := by
    rw [hιdef, range_restrictLE]
    exact (continuous_subtype_val.closure_preimage_subset _).trans (Set.preimage_mono
      ((closure_mono c₂.le_zero).trans (c₂.closure_subset_of_lt h1' le_rfl)))
  have hrZ : Set.range ι ⊆ ΩZ m := by
    rintro _ ⟨y, rfl⟩
    exact (c₂.le_zero.trans (c₂.le_outer 0 (Nat.zero_le _))) y.2
  have hordZ : ∀ x : X.restrict (ΩZ m),
      (cur.pullback (X.inclusion (ΩZ m)) (isLocalDiffeomorph_inclusion X _)).I.ord x ≤ (m : ℕ∞) :=
    fun x => (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt cur.I _
      (isLocalDiffeomorph_inclusion X (ΩZ m) x)).trans_le (hZord _ x.2)
  have hfinZ : Finite {j //
      (cur.pullback (X.inclusion (ΩZ m)) (isLocalDiffeomorph_inclusion X _)).F.hyp j ≠ ∅} :=
    HypersurfaceFamily.finite_nonempty_comap cur.F _ c₁.outerTriple_finite
  have hΩZ' : ∀ k, k < m → IsCompact (closure (traceOn (ΩZ m) (ΩZ k) : Set (X.restrict (ΩZ m)))) :=
    fun k hk => isCompact_closure_preimage_val_of_closure_subset (hΩZ k hk.le)
      ((continuous_subtype_val.closure_preimage_subset _).trans
        (Set.preimage_mono (c₂.closure_subset_of_lt hk le_rfl)))
  have hΩZsub' : ∀ k, k + 1 < m →
      closure (traceOn (ΩZ m) (ΩZ k) : Set (X.restrict (ΩZ m))) ⊆ traceOn (ΩZ m) (ΩZ (k + 1)) :=
    fun k hk => (continuous_subtype_val.closure_preimage_subset _).trans
      (Set.preimage_mono (hΩZsub k (Nat.lt_of_succ_lt hk)))
  have hrangeZ' : Set.range (AnalyticMap.corestrict ι (ΩZ m) hrZ) ⊆ traceOn (ΩZ m) (ΩZ 0) := by
    rintro _ ⟨y, rfl⟩
    exact c₂.le_zero y.2
  -- the top round dropped (`eraseEmpty_resolveFrom_succ_eq_restrict`): the rounds from `m` on the
  -- region `ΩZ m` of `X`
  have hH4 := eraseEmpty_resolveFrom_succ_eq_restrict bo m cur c₁.outerTriple_ord_le
    c₁.outerTriple_finite c₁.trace c₁.isCompact_closure_trace c₁.closure_trace_subset ι
    (isLocalDiffeomorph_restrictLE _) c₁.range_restrictLE_subset_trace ΩZ hΩZ hΩZsub hΩZle hZord
    hrangeZ hclosure hordZ hfinZ hΩZ' hΩZsub' hrZ hrangeZ'
  /- ### the transport from the region of `X` (an open of an open) to `M.restrict (W₂ m)` -/
  have hres : ⇑(M.inclusion (W₁ (m + 1))) '' (ΩZ m : Set X) ⊆ W₂ m := by
    rintro _ ⟨p, hp, rfl⟩
    exact hp
  set g := AnalyticMap.restrictMap (M.inclusion (W₁ (m + 1))) (ΩZ m) (W₂ m) hres with hgdef
  have hg : IsLocalDiffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω g :=
    AnalyticMap.isLocalDiffeomorph_restrictMap (isLocalDiffeomorph_inclusion M _) (ΩZ m) (W₂ m) hres
  have hpb : cur.pullback (X.inclusion (ΩZ m)) (isLocalDiffeomorph_inclusion X _) =
      c₂.outerTriple.pullback g hg := by
    change (T.pullback (M.inclusion (W₁ (m + 1))) _).pullback (X.inclusion (ΩZ m)) _ =
      (T.pullback (M.inclusion (W₂ m)) _).pullback g hg
    rw [AnalyticTriple.pullback_pullback _ _ _ _ _,
      AnalyticTriple.pullback_pullback _ _ _ _ _]
    exact AnalyticTriple.pullback_eq_of_eq T (ContMDiffMap.ext fun _ => rfl) _ _
  have hΩg : ∀ k, k < m → ⇑g '' (traceOn (ΩZ m) (ΩZ k) : Set (X.restrict (ΩZ m))) ⊆
      c₂.trace k := by
    rintro k _ _ ⟨p, hp, rfl⟩
    exact hp
  have hH3 := eraseEmpty_resolveFrom_congr bo m g hg c₂.outerTriple
    (cur.pullback (X.inclusion (ΩZ m)) (isLocalDiffeomorph_inclusion X _))
    (by rw [hpb]; exact AnalyticTriple.isPullbackOf_pullback _ _ _)
    c₂.outerTriple_ord_le c₂.outerTriple_finite hordZ hfinZ
    c₂.trace c₂.isCompact_closure_trace c₂.closure_trace_subset
    (fun k => traceOn (ΩZ m) (ΩZ k)) hΩZ' hΩZsub' hΩg
    (M.restrictLE c₂.le_outerOpen) (isLocalDiffeomorph_restrictLE _)
    c₂.range_restrictLE_subset_trace
    (AnalyticMap.corestrict ι (ΩZ m) hrZ) (isLocalDiffeomorph_corestrict ι (ΩZ m)
      (isLocalDiffeomorph_restrictLE _) hrZ) hrangeZ'
    (ContMDiffMap.id : AnalyticMap (M.restrict U) (M.restrict U))
    (BlowUpSequence.isLocalDiffeomorph_id _)
    (ContMDiffMap.ext fun _ => rfl)
  exact hH4.trans (hH3.trans (congrArg BlowUpSequence.eraseEmpty (BlowUpSequence.pullback_id _)))

/-! ### The chain cut down by the shrinks of `closure U` inside `{ord ≤ d_U}` -/

/-- **The chain `c` cut down by the iterated shrinks** of `closure U` inside `{ord ≤ d_U}` (the
`k`-th open is `c.W k ⊓ shrinkChain … (c.D - k)`), of any length `m` between `d_U` and `c.D`: the
compact closures and the shrinking are inherited, `U` lies in the innermost open, and every open
has order `≤ d_U`, so every truncation is admissible. The bridge from an arbitrary admissible chain
to the canonical one. -/
def ResolveChain.shrunk (c : ResolveChain T U) (hU : IsCompact (closure (U : Set M))) (m : ℕ)
    (hm : m ≤ c.D) (hdm : maxOrdOn T U hU ≤ m) : ResolveChain T U where
  D := m
  W k := c.W k ⊓ shrinkChain (closure (U : Set M)) (orderOpen T (maxOrdOn T U hU)) hU
    (closure_subset_orderOpen T U hU) (c.D - k)
  isCompact_closure k hk :=
    (c.isCompact_closure k (hk.trans hm)).of_isClosed_subset isClosed_closure
      (closure_mono inf_le_left)
  closure_subset k hk := by
    have h : c.D - k = (c.D - (k + 1)) + 1 := by omega
    refine (closure_inter_subset_inter_closure _ _).trans
      (Set.inter_subset_inter (c.closure_subset k (lt_of_lt_of_le hk hm)) ?_)
    rw [h]
    exact closure_shrinkChain_succ_subset hU _ _
  le_zero := le_inf c.le_zero fun _ hx => subset_shrinkChain hU _ _ (subset_closure hx)
  ord_le x hx :=
    (closure_shrinkChain_zero_subset hU _ (subset_closure
      (shrinkChain_antitone hU _ (Nat.zero_le _) hx.2))).trans (Nat.cast_le.mpr hdm)

/-- The order on every open of the cut-down chain is at most `d_U` (its opens lie in the shrinks,
which lie in `{ord ≤ d_U}`). -/
theorem ResolveChain.ord_le_maxOrdOn_of_mem_shrunk (c : ResolveChain T U)
    (hU : IsCompact (closure (U : Set M))) (m : ℕ) (hm : m ≤ c.D) (hdm : maxOrdOn T U hU ≤ m)
    (k : ℕ) (x : M) (hx : x ∈ (c.shrunk hU m hm hdm).W k) :
    T.I.ord x ≤ (maxOrdOn T U hU : ℕ∞) :=
  closure_shrinkChain_zero_subset hU _ (subset_closure
    (shrinkChain_antitone hU _ (Nat.zero_le _) hx.2))

open Classical in
/-- `d_U` is the least bound (`bddAbove_ord_on_compact`, `Nat.find`): any bound of the order on
`closure U` is at least `d_U`. -/
theorem maxOrdOn_le (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (hU : IsCompact (closure (U : Set M))) {m : ℕ}
    (h : ∀ x ∈ closure (U : Set M), T.I.ord x ≤ (m : ℕ∞)) : maxOrdOn T U hU ≤ m :=
  Nat.find_min' (IdealSheaf.bddAbove_ord_on_compact T.isNonzeroEverywhere hU) h

/-- The value along a chain is empty when the order vanishes on `U`
(`eraseEmpty_resolveFrom_eq_nil_of_ord_eq_zero` at the chain's outer triple; the remark after
[Kol07, Theorem 68]). -/
theorem resolveSeqOnAlong_eq_nil_of_ord_eq_zero (c : ResolveChain T U)
    (hz : ∀ y : M.restrict U, T.I.ord y.1 ≤ ((0 : ℕ) : ℕ∞)) :
    resolveSeqOnAlong bo T U c = BlowUpSequence.nil (M.restrict U) :=
  eraseEmpty_resolveFrom_eq_nil_of_ord_eq_zero bo c.D c.outerTriple c.outerTriple_ord_le
    c.outerTriple_finite c.trace c.isCompact_closure_trace c.closure_trace_subset
    (M.restrictLE c.le_outerOpen) (isLocalDiffeomorph_restrictLE _) c.range_restrictLE_subset_trace
    fun y => (IdealSheaf.ord_comap_of_isLocalDiffeomorphAt T.I
      (M.inclusion (c.W c.D)) (isLocalDiffeomorph_inclusion M _ _)).trans_le (hz y)

/-! ### Canonicity -/

/-- **Every admissible chain has the canonical chain's value** ([Wlo09, Theorem 2.0.3 (4)];
[Kol07, 34.1]). A chain with no round has the order vanishing on `U`, and both values are empty
(`resolveSeqOnAlong_eq_nil_of_ord_eq_zero`). Otherwise `d_U ≤ c.D`, since `closure U` lies in the
outermost open; the chain equals its cut-down of full length (`resolveSeqOnAlong_eq_of_le`), the
cut-downs of consecutive lengths agree (`resolveSeqOnAlong_eq_of_succ`; the empty value at the
last drop, from one round to none, when `d_U = 0`), and the cut-down of length `d_U` lies inside
the canonical chain. -/
theorem resolveSeqOnAlong_eq_canonical (c : ResolveChain T U)
    (hU : IsCompact (closure (U : Set M))) :
    resolveSeqOnAlong bo T U c = resolveSeqOnAlong bo T U (canonicalResolveChain T U hU) := by
  set dU := maxOrdOn T U hU with hdUdef
  rcases Nat.eq_zero_or_pos c.D with hD0 | hDpos
  · -- (i) no round at all: the order vanishes on `U`, both values are empty
    have hz : ∀ y : M.restrict U, T.I.ord y.1 ≤ ((0 : ℕ) : ℕ∞) := fun y => by
      have h0 : y.1 ∈ c.W c.D := by
        rw [hD0]
        exact c.le_zero y.2
      have := c.ord_le y.1 h0
      rwa [hD0] at this
    exact (resolveSeqOnAlong_eq_nil_of_ord_eq_zero bo c hz).trans
      (resolveSeqOnAlong_eq_nil_of_ord_eq_zero bo _ hz).symm
  · -- (ii) `d_U ≤ c.D`: the closure of `U` lies in the outermost open
    have hdUD : dU ≤ c.D := maxOrdOn_le T U hU fun x hx =>
      c.ord_le x ((c.closure_subset_of_lt hDpos le_rfl) ((closure_mono c.le_zero) hx))
    -- the chain cut down by the shrinks, of every length from `d_U` to `c.D`
    have key : ∀ m (hdm : dU ≤ m) (hm : m ≤ c.D),
        resolveSeqOnAlong bo T U (c.shrunk hU m hm hdm) =
          resolveSeqOnAlong bo T U (c.shrunk hU dU hdUD le_rfl) := by
      intro m hdm
      induction m, hdm using Nat.le_induction with
      | base => intro _; rfl
      | succ m hdm ih =>
        intro hm
        refine Eq.trans ?_ (ih (Nat.le_of_succ_le hm))
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · -- the last drop, from one round to none: `d_U = 0`, the order vanishes on `U`
          subst hm0
          have hdU0 : dU = 0 := Nat.le_zero.mp hdm
          have hz : ∀ y : M.restrict U, T.I.ord y.1 ≤ ((0 : ℕ) : ℕ∞) := fun y => by
            have := c.ord_le_maxOrdOn_of_mem_shrunk hU 0 (Nat.le_of_succ_le hm) hdm 0 y.1
              ((c.shrunk hU 0 (Nat.le_of_succ_le hm) hdm).le_zero y.2)
            rwa [← hdUdef, hdU0] at this
          exact (resolveSeqOnAlong_eq_nil_of_ord_eq_zero bo _ hz).trans
            (resolveSeqOnAlong_eq_nil_of_ord_eq_zero bo _ hz).symm
        · exact resolveSeqOnAlong_eq_of_succ bo _ _ rfl (fun k _ => le_rfl) hmpos
    -- assembly: `c` to its cut-down of full length, down to length `d_U`, to the canonical chain
    refine (resolveSeqOnAlong_eq_of_le bo (c.shrunk hU c.D le_rfl hdUD) c rfl
      fun k _ => inf_le_left).symm.trans ((key c.D hdUD le_rfl).trans ?_)
    refine resolveSeqOnAlong_eq_of_le bo _ _ rfl fun k _ => ?_
    exact inf_le_right.trans (shrinkChain_antitone hU _ (Nat.sub_le_sub_right hdUD k))

/-- **Canonicity** ([Wlo09, Theorem 2.0.3 (4)]; [Kol07, 34.1], with the remark after
[Kol07, Theorem 68] for the empty rounds above the order bound): the value on `U` does not depend
on the admissible chain; two chains for `U`, of any lengths, give the same list. Both have the
canonical chain's value (`resolveSeqOnAlong_eq_canonical`; `closure U` is compact, inside the
closure of a chain's innermost open). -/
theorem resolveSeqOnAlong_chain_indep
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (U : Opens M)
    (c₁ c₂ : ResolveChain T U) :
    resolveSeqOnAlong bo T U c₁ = resolveSeqOnAlong bo T U c₂ :=
  have hU : IsCompact (closure (U : Set M)) :=
    (c₁.isCompact_closure 0 (Nat.zero_le _)).of_isClosed_subset isClosed_closure
      (closure_mono c₁.le_zero)
  (resolveSeqOnAlong_eq_canonical bo c₁ hU).trans (resolveSeqOnAlong_eq_canonical bo c₂ hU).symm

/-! ### Compatibility and the resolution family -/

/-- The `compat` field of the resolution family ([Wlo09, Theorem 2.0.3 (4)]; the shape of
`CompatibleFamily.compat`): for `U ≤ V` the value on `U` is the pull-back of the value on `V` along
the open inclusion, with the empty blow-ups erased. The canonical chain of `V` is an admissible
chain for `U` whose reading map is the reading map of `V` after the inclusion `U ≤ V`: canonicity
(`resolveSeqOnAlong_chain_indep`), `resolveFrom_congr_ι`, `resolveFrom_comp` and
`eraseEmpty_pullback_eraseEmpty`. -/
theorem resolveSeqOn_compat (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (U V : Opens M) (hU : IsCompact (closure (U : Set M)))
    (hV : IsCompact (closure (V : Set M))) (hUV : U ≤ V) :
    resolveSeqOn bo T U hU =
      ((resolveSeqOn bo T V hV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
  set cV : ResolveChain T V := canonicalResolveChain T V hV with hcV
  -- the canonical chain of `V`, read as an admissible chain for `U`
  set cVU : ResolveChain T U :=
    ⟨cV.D, cV.W, cV.isCompact_closure, cV.closure_subset, hUV.trans cV.le_zero, cV.ord_le⟩ with hcVU
  have h1 : resolveSeqOn bo T U hU = resolveSeqOnAlong bo T U cVU :=
    resolveSeqOnAlong_chain_indep bo T U _ cVU
  -- the reading map of `cVU` is the reading map of `cV` after the inclusion `U ≤ V`
  have hι : M.restrictLE cVU.le_outerOpen =
      (M.restrictLE cV.le_outerOpen).comp (M.restrictLE hUV) := ContMDiffMap.ext fun _ => rfl
  have h2 : resolveSeqOnAlong bo T U cVU =
      ((resolveSeqOnAlong bo T V cV).pullback (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV)).eraseEmpty := by
    refine (congrArg BlowUpSequence.eraseEmpty ((resolveFrom_congr_ι bo cV.D cV.outerTriple
      cV.outerTriple_ord_le cV.outerTriple_finite cV.trace cV.isCompact_closure_trace
      cV.closure_trace_subset hι _ _ (BlowUpSequence.isLocalDiffeomorph_comp
        (isLocalDiffeomorph_restrictLE _) (isLocalDiffeomorph_restrictLE hUV))
      (by rw [← hι]; exact cVU.range_restrictLE_subset_trace)).trans
      (resolveFrom_comp bo cV.D cV.outerTriple cV.outerTriple_ord_le cV.outerTriple_finite cV.trace
        cV.isCompact_closure_trace cV.closure_trace_subset (M.restrictLE cV.le_outerOpen)
        (isLocalDiffeomorph_restrictLE _) cV.range_restrictLE_subset_trace (M.restrictLE hUV)
        (isLocalDiffeomorph_restrictLE hUV) _))).trans ?_
    exact (BlowUpSequence.eraseEmpty_pullback_eraseEmpty _ _ _).symm
  exact h1.trans h2

/-- **The resolution family** of the triple `T` ([Hir64, Main Theorem II(N), p. 176], order
reduction iterated at decreasing maximal order; [Wlo09, Theorem 2.0.3 (1), (4)]; the remark after
[BM97, Theorem 1.6] on non-compact spaces): the compatible family whose value on a relatively
compact open `U` is `resolveSeqOn bo T U hU`, without empty centres, with the `compat` field
`resolveSeqOn_compat`. -/
def resolveFam (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) :
    CompatibleFamily T where
  seqOn := resolveSeqOn bo T
  noEmptyCenters := noEmptyCenters_resolveSeqOn bo T
  compat := resolveSeqOn_compat bo T

end Hironaka.Manifold

end
