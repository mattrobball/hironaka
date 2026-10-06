/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BD
import Hironaka.Manifold.IdealSheaf.Identity
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Components
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The modified first step: the stopped locus and the restricted triple on `H⁺`

The modified first step of [Wlo09, Theorem 7.4.1]: if the transformed ideal `I′ = (u)` is the ideal
of a smooth hypersurface of maximal contact, the algorithm stops; otherwise it restricts `(I′, 1)`
to a hypersurface of maximal contact `V(u₁)` and recurses. At the mark `1` the element of
maximal contact lies in the ideal ([Wlo09, Lemma 5.5.1 (1)]: `H(I) = I` for `µ = 1`), so `I′ = (u)`
near `x` exactly when the restriction `I′|_{V(u)}` has zero stalk at `x`, and by the identity
theorem the zero-stalk locus of a restriction is a union of connected components of `V(u)`
(`isClopen_setOf_stalkIdeal_eq_bot`): **the stopped locus is Kollár's `Z_{-1}` at the mark `1`**
(`BD.Zminus1`, the components of the member inside `cosupp(𝓘, 1)`, from the proof of
[Kol07, Lemma 102]). The modification of the algorithm is precisely not to blow `Z_{-1}` up
(Kollár's isomorphic first blow-up) but to stop there.

This module builds the objects of the modified core: the stopped locus `stopLocus T j`; the closed
hypersurface **`hplus T j = E^j ∖ Z_{-1}`** (a union of connected components of the member, hence
closed in `M`: `isClosedSubmanifold_hplus`); the boundary `E − E^j`, in proper normal crossings
with it (`hasSncWithProper_hplus`); and **the restricted triple `restrictedTripleMod T j`** on the
bundled hypersurface `H⁺` (`toAnalyticManifold`, modelled on `𝕜^{n−1}`): the pull-back of `𝓘`,
nonzero everywhere by the identity theorem (`isNonzeroEverywhere_hplusIdeal`: a zero stalk of the
restriction at a point of `H⁺` would put its whole component into `cosupp(𝓘, 1)`, i.e. into
`Z_{-1}`), and the trace of `E − E^j`, with simple normal crossings as the trace of a proper family
with simple normal crossings. The restricted triple lies in the marked class `BMOClass 1`
(`bmoClass_restrictedTripleMod`), the domain of the modified functor one dimension down.
-/

@[expose] public section

noncomputable section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
  (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (j : T.F.ι)

/-! ### The stopped locus and `H⁺` -/

/-- **The stopped locus of the member `j` at the mark `1`**: Kollár's `Z_{-1}` (`BD.Zminus1`, the
proof of [Kol07, Lemma 102]), the points of `E^j` whose connected component in `E^j` lies in
`cosupp(𝓘, 1)`; at the mark `1` with maximal contact this is where `𝓘 = (u)` ("the algorithm is
stopped", [Wlo09, Theorem 7.4.1]). -/
abbrev stopLocus : Set M := BD.Zminus1 T.I 1 (T.F.hyp j)

theorem isClosed_stopLocus : IsClosed (stopLocus T j) :=
  (BD.isClosedSubmanifold_Zminus1 T 1 j).isClosed

/-- **`H⁺`, the member `E^j` without its stopped components**: the hypersurface on which the run one
dimension down is performed ("otherwise we restrict", [Wlo09, Theorem 7.4.1]). -/
def hplus : Set M := T.F.hyp j \ stopLocus T j

theorem hplus_subset : hplus T j ⊆ T.F.hyp j := fun _ hx => hx.1

theorem mem_hplus {x : M} : x ∈ hplus T j ↔ x ∈ T.F.hyp j ∧ x ∉ stopLocus T j := Iff.rfl

/-- The connected component in `E^j` of a point of `H⁺` lies in `H⁺` (`Z_{-1}` is a union of
components of `E^j`). -/
theorem connectedComponentIn_subset_hplus {x : M} (hx : x ∈ hplus T j) :
    connectedComponentIn (T.F.hyp j) x ⊆ hplus T j := by
  intro y hy
  refine ⟨connectedComponentIn_subset _ _ hy, fun hyZ => hx.2 ?_⟩
  refine BD.connectedComponentIn_subset_Zminus1 hyZ ?_
  rw [← connectedComponentIn_eq hy]
  exact mem_connectedComponentIn hx.1

/-- `H⁺` is closed in `M`: its complement in `E^j` is `Z_{-1}`, a union of components of `E^j`,
open in `E^j` (every point of `Z_{-1}` has an adapted chart of `E^j` meeting `E^j` only inside its
component). -/
theorem isClosed_hplus : IsClosed (hplus T j) := by
  have hY : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (T.F.hyp j) 1 :=
    T.isSnc.1 j
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  by_cases hxY : x ∈ T.F.hyp j
  · have hxZ : x ∈ stopLocus T j := by
      by_contra h
      exact hx ⟨hxY, h⟩
    obtain ⟨φ, σ, hxs, -, hsub⟩ := hY.exists_adaptedChart_source_inter_subset hxY
    refine Filter.mem_of_superset (φ.open_source.mem_nhds hxs) fun y hy hyH => ?_
    exact hyH.2 (BD.connectedComponentIn_subset_Zminus1 hxZ (hsub ⟨hy, hyH.1⟩))
  · exact Filter.mem_of_superset (hY.isClosed.isOpen_compl.mem_nhds hxY) fun y hy hyH => hy hyH.1

/-- An adapted chart of `E^j`, restricted to the complement of the stopped locus, is an adapted
chart of `H⁺`. -/
theorem isAdaptedChart_hplus_restrOpen {φ : OpenPartialHomeomorph M (Fin n → 𝕜)} {σ : Fin 1 ↪ Fin n}
    (h : IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (T.F.hyp j) φ σ) :
    IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (hplus T j)
      (φ.restrOpen (stopLocus T j)ᶜ (isClosed_stopLocus T j).isOpen_compl) σ := by
  refine ⟨(h.restrOpen' _ (isClosed_stopLocus T j).isOpen_compl).1, fun x hx => ?_⟩
  rw [OpenPartialHomeomorph.restrOpen_source] at hx
  change x ∈ hplus T j ↔ ∀ i, ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜) (φ x) (σ i) = 0
  rw [← h.2 x hx.1]
  exact ⟨fun hxp => hxp.1, fun hxH => ⟨hxH, hx.2⟩⟩

/-- **`H⁺` is a closed hypersurface of `M`** (its charts are `E^j`'s, restricted off `Z_{-1}`). -/
theorem isClosedSubmanifold_hplus :
    IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (hplus T j) 1 := by
  refine ⟨isClosed_hplus T j, fun b hb => ?_⟩
  obtain ⟨φ, σ, hbs, h⟩ := (T.isSnc.1 j).exists_adaptedChart b hb.1
  refine ⟨φ.restrOpen (stopLocus T j)ᶜ (isClosed_stopLocus T j).isOpen_compl, σ, ?_,
    isAdaptedChart_hplus_restrOpen T j h⟩
  rw [OpenPartialHomeomorph.restrOpen_source]
  exact ⟨hbs, hb.2⟩

/-- The boundary `E − E^j` has simple normal crossings with `H⁺` properly (Corollary 85's
hypothesis for the trace): `E^j`'s proper snc charts (`hasSncWithProper_emptyMember`), restricted
off `Z_{-1}`. -/
theorem hasSncWithProper_hplus :
    (T.F.emptyMember j).HasSncWithProper (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (hplus T j) 1 := by
  intro a ha
  obtain ⟨φ, σ, cidx, hφ, hc, hproper⟩ := T.isSnc.hasSncWithProper_emptyMember j a ha.1
  exact ⟨φ.restrOpen (stopLocus T j)ᶜ (isClosed_stopLocus T j).isOpen_compl, σ, cidx,
    isAdaptedChart_hplus_restrOpen T j hφ, hc.restrOpen _ ha.2, hproper⟩

/-! ### The restriction of `𝓘` to `H⁺` is nonzero everywhere -/

/-- The restriction of `𝓘` to the bundled hypersurface `H⁺` (the pull-back along the inclusion). -/
abbrev hplusIdeal :=
  T.I.pullback ⇑(isClosedSubmanifold_hplus T j).inclusionMap
    (isClosedSubmanifold_hplus T j).inclusionMap.contMDiff

/-- **The restriction of `𝓘` to `H⁺` is nonzero everywhere**: a zero stalk at a point `p` of `H⁺`
puts the whole connected component of `p` (in `H⁺`, which is its component in `E^j`) into the
zero-stalk locus (`isClopen_setOf_stalkIdeal_eq_bot`, the identity theorem), hence into
`cosupp(𝓘, 1)` (`cosupport_pullback`), so `p ∈ Z_{-1}`, against `p ∈ H⁺`. -/
theorem isNonzeroEverywhere_hplusIdeal : (hplusIdeal T j).IsNonzeroEverywhere := by
  intro p hp
  have hcomp : connectedComponent p ⊆
      {q : (isClosedSubmanifold_hplus T j).toAnalyticManifold |
        (hplusIdeal T j).stalkIdeal q = ⊥} :=
    (hplusIdeal T j).isClopen_setOf_stalkIdeal_eq_bot.connectedComponent_subset hp
  have hxH : (p : hplus T j).1 ∈ T.F.hyp j := (p : hplus T j).2.1
  have hxZ : (p : hplus T j).1 ∉ stopLocus T j := (p : hplus T j).2.2
  refine hxZ ⟨hxH, fun y hy => ?_⟩
  have hy' : y ∈ connectedComponentIn (hplus T j) (p : hplus T j).1 :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxH) (connectedComponentIn_subset_hplus T j (p : hplus T j).2) hy
  rw [connectedComponentIn_eq_image (p : hplus T j).2] at hy'
  obtain ⟨q, hq, rfl⟩ := hy'
  have hq' : (hplusIdeal T j).stalkIdeal q = ⊥ := hcomp hq
  have hqord : (hplusIdeal T j).ord q = ⊤ :=
    IdealSheaf.ord_eq_top_of_stalkIdeal_eq_bot (hplusIdeal T j) hq'
  have hqcos : q ∈ (hplusIdeal T j).support := by
    by_contra h
    exact ENat.top_ne_zero (hqord.symm.trans ((IdealSheaf.ord_eq_zero_iff _).mpr h))
  rw [IdealSheaf.support_pullback] at hqcos
  exact Order.one_le_iff_ne_zero.mpr fun h0 => ((IdealSheaf.ord_eq_zero_iff T.I).mp h0) hqcos

/-! ### The restricted triple on `H⁺` -/

/-- The restricted triple read on a closed hypersurface `S` propositionally equal to `H⁺`: the
data on `S`, the proofs transported by substitution (`restrictedTripleMod` is its instance at
`H⁺`). -/
def restrictedTripleModOf {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (hSeq : S = hplus T j) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hS.toAnalyticManifold where
  I := T.I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff
  isNonzeroEverywhere := by
    subst hSeq
    exact isNonzeroEverywhere_hplusIdeal T j
  F := hS.traceFamily (T.F.emptyMember j)
  isSnc := by
    subst hSeq
    exact (isClosedSubmanifold_hplus T j).isSnc_traceFamily (T.isSnc.emptyMember j)
      (hasSncWithProper_hplus T j)

/-- **The restricted triple on `H⁺`** ("we restrict `(I′, 1)` to a hypersurface of maximal contact
`V(u₁)`", [Wlo09, Theorem 7.4.1], on the components which are not stopped; the counterpart of
Kollár's `(S, I_0|_S, E_S)` of the proof of [Kol07, Lemma 102], `BD.restrictedTriple`, without the
first blow-up): the pull-back of `𝓘` to the bundled hypersurface `H⁺` (nonzero everywhere by
`isNonzeroEverywhere_hplusIdeal`) and the trace of `E − E^j` (with simple normal crossings as the
trace of a proper family, `isSnc_traceFamily`). -/
def restrictedTripleMod :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (isClosedSubmanifold_hplus T j).toAnalyticManifold :=
  restrictedTripleModOf T j (isClosedSubmanifold_hplus T j) rfl

@[simp] theorem restrictedTripleMod_I : (restrictedTripleMod T j).I = hplusIdeal T j := rfl

@[simp] theorem restrictedTripleMod_F :
    (restrictedTripleMod T j).F =
      (isClosedSubmanifold_hplus T j).traceFamily (T.F.emptyMember j) := rfl

/-- The restricted triple lies in the marked class `BMOClass 1` (the domain of the modified functor
one dimension down): only finitely many trace members are nonempty, a nonempty trace member coming
from a nonempty member of `E`. -/
theorem bmoClass_restrictedTripleMod (hT : AnalyticTriple.BMOClass 1 T) :
    AnalyticTriple.BMOClass 1 (restrictedTripleMod T j) := by
  refine ⟨hT.1, ?_⟩
  have hfin : Finite {k // T.F.hyp k ≠ ∅} := hT.2
  change Finite {k : T.F.ι // (restrictedTripleMod T j).F.hyp k ≠ ∅}
  have key : ∀ k : T.F.ι, T.F.hyp k = ∅ → (restrictedTripleMod T j).F.hyp k = ∅ := by
    intro k h
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    have hp' : (p : hplus T j).1 ∈ (T.F.emptyMember j).hyp k := hp
    have := HypersurfaceFamily.emptyMember_hyp_subset T.F j k hp'
    rw [h] at this
    exact this
  exact Finite.of_injective
    (fun k : {k : T.F.ι // (restrictedTripleMod T j).F.hyp k ≠ ∅} =>
      (⟨k.1, fun h => k.2 (key k.1 h)⟩ : {k // T.F.hyp k ≠ ∅}))
    fun k k' hkk' => Subtype.ext (Subtype.mk.inj hkk')

/-- The restricted triple on `S = H⁺` lies in the marked class `BMOClass 1`. -/
theorem bmoClass_restrictedTripleModOf (hT : AnalyticTriple.BMOClass 1 T) {S : Set M}
    (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S 1)
    (hSeq : S = hplus T j) :
    AnalyticTriple.BMOClass 1 (restrictedTripleModOf T j hS hSeq) := by
  subst hSeq
  exact bmoClass_restrictedTripleMod T j hT

end Hironaka.Manifold.BMOmod

end
