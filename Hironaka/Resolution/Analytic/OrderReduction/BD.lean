/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Tuned
public import Hironaka.Resolution.Analytic.OrderReduction.FirstStep
public import Hironaka.Manifold.Snc.Trace
public import Hironaka.Resolution.Analytic.OrderReduction.MarkedData
import Hironaka.Manifold.FiniteSuccession.Functor.EraseEmptyLemmas
import Hironaka.Manifold.Submanifold.Charts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Lemma 102 on analytic manifolds: the construction of the functor `BD`

Kollár's Lemma 102 ([Kol07, Lemma 102]) is the first ingredient of order reduction for ideals: for
a triple `(X, I, E)` with `max-ord I ≤ m` and a member `E^j` of the boundary, assuming order
reduction for marked ideals in dimension `n - 1`, it produces a smooth blow-up sequence functor
`BD_{n,m,j}` of order `m` after which the cosupport `cosupp(I_r, m)` is disjoint from the
birational transform of `E^j`. Its proof first replaces `I` by the D-balanced ideal `W_{m!}(I)`
([Kol07, Corollary 101]; here `W_s(𝓘)` with `s = tuningParam m`, `Tuned.lean`) and then, with `S
:= E^j`, blows up the union `Z_{-1}` of the components
of `E^j` contained in `cosupp(I, m)`, restricts the weak transform `I_0` and the boundary `E - E^j`
to `S`, applies the marked functor `BMO_{n-1,m}` to the restricted triple and pushes the result
forward ([Kol07, 30.3]): `BD_{n,m,j}(X, I, E) := τ_* BMO_{n-1,m}(S, I_0|_S, m, E_S) ∘ π_{-1}`.
This module carries the construction out on analytic manifolds, in two layers as in the proof: a
core on D-balanced triples, and the functor itself on the tuned triple.

* `HypersurfaceFamily.emptyMember F j` — Kollár's `E - E^j`, with the index set kept and the `j`-th
  member replaced by the empty hypersurface; `IsSnc.emptyMember`, and
  `IsSnc.hasSncWithProper_emptyMember`: the other members have simple normal crossings with `E^j`
  properly (at a point of `E^j`, the chart of the simple normal crossings has `E^j` as a coordinate
  hyperplane and the other members through the point on other coordinates).
* `HypersurfaceFamily.HasSncWithProper.comap` — proper simple normal crossings pull back along a
  local analytic isomorphism (the charts are transported along the local inverses).
* `isLocalDiffeomorph_blowUpπ_of_codimOne` — blowing up a hypersurface is a local analytic
  isomorphism ([Kol07, Warning 20]: a trivial blow-up is an isomorphism).
* `BDan.BDClass s` — the class of the core: the triples of `BOClass s` whose ideal sheaf is
  D-balanced at the mark `s`.
* `BDan.transformS`, `BDan.weakTransformI`, `BDan.boundaryMinus`, `BDan.restrictedTriple` — the
  transform `S_0 = π_{-1}^{-1}(E^j)` of `E^j`, the weak transform `I_0` of `𝓘`, the pulled-back
  `E - E^j`, and the triple `(S_0, I_0|_{S_0}, (E - E^j)|_{S_0})` on the hypersurface `S_0` regarded
  as a manifold modelled on `𝕜^{n-1}`; its ideal sheaf is nonzero everywhere because `I_0` is
  D-balanced, and its boundary has simple normal crossings as the trace of a family having proper
  simple normal crossings with `S_0`. It lies in the marked class `BMOClass s`. They are the
  instances at `Z_{-1}` of `BDan.transformSOf`, `BDan.weakTransformIOf`, `BDan.boundaryMinusOf`,
  `BDan.restrictedTripleOf`, over an arbitrary closed hypersurface `Z` (and `S'`).
* `BDan.coreOfListOf hZ hS' L` — the core over a sequence: the blow-up of a closed hypersurface
  `Z`, followed by the push-forward of a sequence `L` on a closed hypersurface `S'` of the blow-up,
  with empty blow-ups deleted ([Kol07, 32]); `BDan.core s T j inp hT` — the core: `coreOfListOf`
  at `Z_{-1}` and `S_0` over the value of the input functor `inp : BMOanData 𝕜 (n - 1) s` on the
  restricted triple (the first blow-up is empty when no component of `E^j` lies in `cosupp(𝓘, s)`).
* `BDan m inp T hT j` — **the functor `BD_{n,m,j}`** on the class `BOClass m`: the core at the mark
  `s = tuningParam m` on the tuned triple `(M, W_s(𝓘), E)` (`Tuned.lean`), the input being
  `BMO_{n-1,s}`.

The clauses of Lemma 102 for `BDan` — order `m` with respect to `E`, the disjointness (1) and the
functoriality (2) — are proved in `BDCore.lean`, `BDCosupp.lean`, `BDBridge.lean`, `BDOf.lean`,
`BDErase.lean` and `BDIndiff.lean`, and carried over to the compatible-family form of
`BDFam.lean`, whose data `bdanFamDataOfInput` (`BOanFamOfInput.lean`) is the input of Steps 2.1 and
2.2 of the proof of Theorem 103.

The push-forward inside the core is the push-forward of a list of centres; its identification
with the push-forward of the corresponding succession of blow-ups
(`BlowUpSequence.toSuccession_pushforward`) holds for lists without empty centres and is what makes
[Kol07, Corollary 85] available for the clauses.
-/

@[expose] public section

noncomputable section

open Set Topology IsLocalRing
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold.HypersurfaceFamily

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-! ### `E − E^j`: emptying a member -/

variable {M : Type u}

open Classical in
/-- Kollár's `E - E^j` (the proof of [Kol07, Lemma 102], "`E_S := (E - E^j)|_S`"): the family with
the same index set, the `j`-th member replaced by the empty hypersurface and the others unchanged.
Keeping the index set lets the member be named by its index throughout. -/
def emptyMember (F : HypersurfaceFamily M) (j : F.ι) : HypersurfaceFamily M where
  ι := F.ι
  hyp k := if k = j then ∅ else F.hyp k

open Classical in
@[simp] theorem emptyMember_hyp_self (F : HypersurfaceFamily M) (j : F.ι) :
    (F.emptyMember j).hyp j = ∅ := by
  simp [emptyMember]

open Classical in
theorem emptyMember_hyp_of_ne (F : HypersurfaceFamily M) {j k : F.ι} (h : k ≠ j) :
    (F.emptyMember j).hyp k = F.hyp k := by
  simp [emptyMember, h]

theorem emptyMember_hyp_subset (F : HypersurfaceFamily M) (j k : F.ι) :
    (F.emptyMember j).hyp k ⊆ F.hyp k := by
  by_cases h : k = j
  · subst h
    rw [emptyMember_hyp_self]
    exact empty_subset _
  · rw [emptyMember_hyp_of_ne F h]

theorem ne_of_mem_emptyMember {F : HypersurfaceFamily M} {j k : F.ι} {a : M}
    (ha : a ∈ (F.emptyMember j).hyp k) : k ≠ j := by
  rintro rfl
  rw [emptyMember_hyp_self] at ha
  exact ha

theorem mem_of_mem_emptyMember {F : HypersurfaceFamily M} {j k : F.ι} {a : M}
    (ha : a ∈ (F.emptyMember j).hyp k) : a ∈ F.hyp k :=
  emptyMember_hyp_subset F j k ha

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [TopologicalSpace M] [ChartedSpace E M]

/-- A chart of the simple normal crossings of `F` at `a` is one of `E - E^j` at `a`: the members
through `a` other than `E^j` keep their coordinates. -/
theorem IsSncChartAt.emptyMember {F : HypersurfaceFamily M} {φ : OpenPartialHomeomorph M E} {a : M}
    {c : {k // a ∈ F.hyp k} → Fin n} (h : F.IsSncChartAt ψ φ a c) (j : F.ι) :
    (F.emptyMember j).IsSncChartAt ψ φ a fun k => c ⟨k.1, mem_of_mem_emptyMember k.2⟩ := by
  refine ⟨h.1, h.2.1, fun k x hx => ?_, fun k k' hkk' => ?_⟩
  · rw [emptyMember_hyp_of_ne F (ne_of_mem_emptyMember k.2)]
    exact h.2.2.1 ⟨k.1, mem_of_mem_emptyMember k.2⟩ x hx
  · exact Subtype.ext (Subtype.mk.inj (h.2.2.2 hkk'))

/-- `E - E^j` has simple normal crossings when `E` does. -/
theorem IsSnc.emptyMember {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) (j : F.ι) :
    (F.emptyMember j).IsSnc ψ := by
  refine ⟨fun k => ?_, hF.2.1.subset (emptyMember_hyp_subset F j), fun a => ?_⟩
  · by_cases h : k = j
    · rw [h, emptyMember_hyp_self]
      exact isClosedSubmanifold_empty' ψ 1
    · rw [emptyMember_hyp_of_ne F h]
      exact hF.1 k
  · obtain ⟨φ, c, hφ⟩ := hF.2.2 a
    exact ⟨φ, _, hφ.emptyMember j⟩

/-- The members of `E` other than `E^j` have simple normal crossings with `E^j` properly: at a point
of `E^j`, a chart of the simple normal crossings of `E` has `E^j` as the coordinate hyperplane of
the `j`-th index and is adapted to `E^j`, while the other members through the point use other
coordinates (the indices are injective). This is the hypothesis "`E + H` has simple normal
crossings" of [Kol07, Corollary 85] for `H := E^j`, needed for the restriction of `E - E^j` to
`S = E^j` in the proof of [Kol07, Lemma 102]. -/
theorem IsSnc.hasSncWithProper_emptyMember {F : HypersurfaceFamily M} (hF : F.IsSnc ψ) (j : F.ι) :
    (F.emptyMember j).HasSncWithProper ψ (F.hyp j) 1 := by
  intro a ha
  obtain ⟨φ, c, hφ⟩ := hF.2.2 a
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 1 ↪ Fin n, ∀ i, σ i = c ⟨j, ha⟩ :=
    ⟨⟨fun _ => c ⟨j, ha⟩, fun i i' _ => Subsingleton.elim i i'⟩, fun _ => rfl⟩
  have hφY : IsAdaptedChart ψ (F.hyp j) φ σ := by
    refine ⟨hφ.1, fun x hx => ?_⟩
    rw [hφ.2.2.1 ⟨j, ha⟩ x hx]
    exact ⟨fun h i => by rw [hσ]; exact h, fun h => by have := h 0; rwa [hσ] at this⟩
  have hprop : ∀ k : {k // a ∈ (F.emptyMember j).hyp k},
      c ⟨k.1, mem_of_mem_emptyMember k.2⟩ ∉ Set.range σ := by
    rintro k ⟨i, hi⟩
    rw [hσ] at hi
    exact ne_of_mem_emptyMember k.2 (Subtype.mk.inj (hφ.2.2.2 hi)).symm
  exact ⟨φ, σ, _, hφY, hφ.emptyMember j, hprop⟩

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-! ### Proper simple normal crossings pull back along local analytic isomorphisms -/

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}

/-- Proper simple normal crossings pull back along a local analytic isomorphism `h : N → M`: the
adapted chart and the chart of the simple normal crossings at `h a` are transported along a local
inverse of `h`, with the same coordinate indices. -/
theorem _root_.Manifold.HypersurfaceFamily.HasSncWithProper.comap {M N : AnalyticManifold.{u} 𝕜 E}
    {F : HypersurfaceFamily M} {Y : Set M} {s : ℕ} (hFY : F.HasSncWithProper ψ₀ Y s)
    (h : AnalyticMap N M) (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h) :
    (F.comap h).HasSncWithProper ψ₀ (⇑h ⁻¹' Y) s := by
  intro a ha
  obtain ⟨Φ, haΦ, hΦ⟩ := (hh a).exists_partialDiffeomorph
  obtain ⟨φ, σ, cidx, hφY, hφ, hprop⟩ := hFY (h a) ha
  have hg : Φ.symm '' (Y ∩ Φ.symm.source) = ⇑h ⁻¹' Y ∩ Φ.symm.target :=
    image_symm_eq_of_image_eq Φ (image_preimage_eq_of_eqOn Φ hΦ)
  refine ⟨transportChart Φ.symm φ, σ, fun k => cidx ⟨k.1, k.2⟩,
    isAdaptedChart_transportChart Φ.symm hg hφY,
    ⟨transportChart_mem_maximalAtlas _ hφ.1, ?_, ?_, ?_⟩, fun k => hprop ⟨k.1, k.2⟩⟩
  · rw [transportChart_source]
    refine ⟨haΦ, ?_⟩
    change Φ a ∈ φ.source
    rw [← hΦ haΦ]
    exact hφ.2.1
  · intro k x hx
    rw [transportChart_source] at hx
    obtain ⟨hxΦ, hxφ⟩ := hx
    have hx' : h x ∈ φ.source := by
      rw [hΦ hxΦ]
      exact hxφ
    rw [transportChart_apply]
    change h x ∈ F.hyp k.1 ↔ ψ₀ (φ (Φ x)) (cidx ⟨k.1, k.2⟩) = 0
    rw [← hΦ hxΦ]
    exact hφ.2.2.1 ⟨k.1, k.2⟩ (h x) hx'
  · intro k k' hkk'
    exact Subtype.ext (Subtype.mk.inj (hφ.2.2.2 hkk'))

/-- Blowing up a closed hypersurface is a local analytic isomorphism ([Kol07, Warning 20]: the
blow-up of a Cartier divisor is an isomorphism): the blow-up map is a diffeomorphism
(`IsBlowUp.exists_diffeomorph_of_codim_one`). -/
theorem isLocalDiffeomorph_blowUpπ_of_codimOne {M : AnalyticManifold.{u} 𝕜 E} {Z : Set M}
    (hZ : IsClosedSubmanifold ψ₀ Z 1) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (Manifold.blowUpπ ψ₀ hZ) := by
  obtain ⟨g, hg⟩ := IsBlowUp.exists_diffeomorph_of_codim_one hZ (isBlowUp_blowUpπ ψ₀ hZ)
  have hπ : ⇑(Manifold.blowUpπ ψ₀ hZ) = ⇑g := funext fun p => (hg p).symm
  change IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω ⇑(Manifold.blowUpπ ψ₀ hZ)
  rw [hπ]
  exact g.isLocalDiffeomorph

/-! ### Lemma 102's core -/

namespace BDan

open _root_.Manifold

variable [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E}

/-- The class of the core of Lemma 102 (the proof of [Kol07, Lemma 102], "from now on we assume
that `I` is D-balanced"): the triples of `BOClass s` whose ideal sheaf is D-balanced at the mark
`s`; the tuned triples of `Tuned.lean` belong to it. -/
def BDClass (s : ℕ) : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop :=
  fun T => AnalyticTriple.BOClass s T ∧ T.I.IsDBalanced s

variable (T : AnalyticTriple ψ₀ M) (s : ℕ) (j : T.F.ι)

/-- The first blow-up `π_{-1} : X_0 → X` of the proof of [Kol07, Lemma 102], with centre `Z_{-1}`.
-/
abbrev piMinusOne : AnalyticMap (Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)) M :=
  Manifold.blowUpπ ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)

/-- `π_{-1}` is a local analytic isomorphism ([Kol07, Warning 20]; its centre is a hypersurface). -/
theorem isLocalDiffeomorph_piMinusOne :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω (piMinusOne T s j) :=
  isLocalDiffeomorph_blowUpπ_of_codimOne _

/-! ### The data of the core over an arbitrary closed hypersurface -/

section Of

variable {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1)

/-- The transform `π^{-1}(E^j)` of the member `E^j` under the blowing-up of a closed hypersurface
`Z` (`transformS` at `Z = Z_{-1}`). -/
def transformSOf : Set (Manifold.blowUp ψ₀ hZ) := ⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j

/-- The weak transform of `𝓘` under the blowing-up of a closed hypersurface `Z` (`weakTransformI`
at `Z = Z_{-1}`). -/
def weakTransformIOf : AnalyticManifold.IdealSheaf (Manifold.blowUp ψ₀ hZ) :=
  IdealSheaf.weakTransformOf hZ (isBlowUp_blowUpπ ψ₀ hZ) T.I

/-- `E - E^j` pulled back along the blowing-up of a closed hypersurface `Z` (`boundaryMinus` at
`Z = Z_{-1}`). -/
def boundaryMinusOf : HypersurfaceFamily (Manifold.blowUp ψ₀ hZ) :=
  (T.F.emptyMember j).comap (Manifold.blowUpπ ψ₀ hZ)

end Of

/-- The transform `S_0 = π_{-1}^{-1}(E^j)` of the member `E^j` under the isomorphism `π_{-1}`, the
hypersurface `S := E^j` of the proof of [Kol07, Lemma 102] read on `X_0`. -/
def transformS : Set (Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)) :=
  transformSOf T j (BD.isClosedSubmanifold_Zminus1 T s j)

/-- `S_0` is a closed hypersurface of the blown-up manifold. -/
theorem isClosedSubmanifold_transformS : IsClosedSubmanifold ψ₀ (transformS T s j) 1 :=
  (T.isSnc.1 j).preimage_of_isLocalDiffeomorph (isLocalDiffeomorph_piMinusOne T s j)

/-- The weak transform `I_0` of `𝓘` under `π_{-1}` (the proof of [Kol07, Lemma 102], "we get a new
ideal sheaf `I_0`"). -/
def weakTransformI :
    AnalyticManifold.IdealSheaf (Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j)) :=
  weakTransformIOf T (BD.isClosedSubmanifold_Zminus1 T s j)

/-- The family `E - E^j` pulled back along the isomorphism `π_{-1}` (the proof of
[Kol07, Lemma 102], "`E_S := (E - E^j)|_S`", before the restriction to `S`). -/
def boundaryMinus : HypersurfaceFamily (Manifold.blowUp ψ₀ (BD.isClosedSubmanifold_Zminus1 T s j))
    :=
  boundaryMinusOf T j (BD.isClosedSubmanifold_Zminus1 T s j)

/-- The pulled-back `E - E^j` has simple normal crossings. -/
theorem isSnc_boundaryMinus : (boundaryMinus T s j).IsSnc ψ₀ :=
  HypersurfaceFamily.isSnc_comap (T.isSnc.emptyMember j) _ (isLocalDiffeomorph_piMinusOne T s j)

/-- The pulled-back `E - E^j` has simple normal crossings with `S_0` properly (the hypothesis of
[Kol07, Corollary 85] on the boundary, for `H := S_0`). -/
theorem hasSncWithProper_boundaryMinus :
    (boundaryMinus T s j).HasSncWithProper ψ₀ (transformS T s j) 1 :=
  (T.isSnc.hasSncWithProper_emptyMember j).comap _ (isLocalDiffeomorph_piMinusOne T s j)

/-- The restricted triple `(S, I_0|_S, E_S)` of the proof of [Kol07, Lemma 102] over an arbitrary
closed hypersurface `Z` and an arbitrary closed hypersurface `S'` of its blow-up, with the
identifications `Z = Z_{-1}` and `S' = S_0` as hypotheses used only in the proof fields (the pulled
back centre and transform are only propositionally `Z_{-1}` and `S_0`): the restriction of the weak
transform of `𝓘`, nonzero everywhere because `𝓘` is D-balanced with `ord 𝓘 ≤ s`
(`BD.isNonzeroEverywhere_pullback_weakTransformOf`), and the trace of the pulled-back `E - E^j`,
with simple normal crossings as the trace of a family having proper simple normal crossings with
`S_0`. -/
def restrictedTripleOf {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set
    (Manifold.blowUp ψ₀ hZ)}
    (hS' : IsClosedSubmanifold ψ₀ S' 1) (hT : BDClass s T)
    (hZeq : Z = BD.Zminus1 T.I s (T.F.hyp j)) (hSeq : S' = transformSOf T j hZ) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜)) hS'.toAnalyticManifold where
  I := (weakTransformIOf T hZ).pullback ⇑hS'.inclusionMap hS'.inclusionMap.contMDiff
  isNonzeroEverywhere := by
    subst hZeq
    subst hSeq
    exact BD.isNonzeroEverywhere_pullback_weakTransformOf T s j hT.2 hT.1.2.1 hZ hS'
  F := hS'.traceFamily (boundaryMinusOf T j hZ)
  isSnc := by
    subst hZeq
    subst hSeq
    exact hS'.isSnc_traceFamily (isSnc_boundaryMinus T s j) (hasSncWithProper_boundaryMinus T s j)

/-- The restricted triple `(S, I_0|_S, E_S)` of the proof of [Kol07, Lemma 102], on the hypersurface
`S_0` regarded as a manifold modelled on `𝕜^{n-1}` with the standard chart: `restrictedTripleOf` at
`Z_{-1}` and `S_0`. -/
def restrictedTriple (hT : BDClass s T) :
    AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin (n - 1) → 𝕜))
      (isClosedSubmanifold_transformS T s j).toAnalyticManifold :=
  restrictedTripleOf T s j _ (isClosedSubmanifold_transformS T s j) hT rfl rfl

/-- The restricted triple lies in the marked class `BMOClass s`: only finitely many of its members
are nonempty, since a nonempty member of the trace comes from a nonempty member of `E`. -/
theorem bmoClass_restrictedTriple (hT : BDClass s T) :
    AnalyticTriple.BMOClass s (restrictedTriple T s j hT) := by
  refine ⟨hT.1.1, ?_⟩
  have hfin : Finite {k // T.F.hyp k ≠ ∅} := hT.1.2.2
  change Finite {k : T.F.ι // (restrictedTriple T s j hT).F.hyp k ≠ ∅}
  have key : ∀ k : T.F.ι, T.F.hyp k = ∅ → (restrictedTriple T s j hT).F.hyp k = ∅ := by
    intro k h
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    have hp' : piMinusOne T s j (p : transformS T s j).1 ∈ (T.F.emptyMember j).hyp k := hp
    have := HypersurfaceFamily.emptyMember_hyp_subset T.F j k hp'
    rw [h] at this
    exact this
  exact Finite.of_injective
    (fun k : {k : T.F.ι // (restrictedTriple T s j hT).F.hyp k ≠ ∅} =>
      (⟨k.1, fun h => k.2 (key k.1 h)⟩ : {k // T.F.hyp k ≠ ∅}))
    fun k k' hkk' => Subtype.ext (Subtype.mk.inj hkk')

/-- **The core over a sequence**, over an arbitrary closed hypersurface `Z` of `M` and a closed
hypersurface `S'` of its blowing-up: the blowing-up of `Z`, then the push-forward of a sequence of
centres `L` on `S'` regarded as a manifold ([Kol07, Definition 30 (3)]), with empty blow-ups
deleted ([Kol07, 32]). -/
def coreOfListOf {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) {S' : Set (Manifold.blowUp ψ₀ hZ)}
    (hS' : IsClosedSubmanifold ψ₀ S' 1)
    (L : AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin
        (n - 1) → 𝕜)) hS'.toAnalyticManifold) :
    AnalyticManifold.BlowUpSequence ψ₀ M :=
  (AnalyticManifold.BlowUpSequence.cons hZ (AnalyticManifold.BlowUpSequence.pushforward hS'
      L)).eraseEmpty

/-- The core of Lemma 102 (the proof of [Kol07, Lemma 102]: the value `BMO_{n-1,m}(S, I_0|_S, m,
(E - E^j)|_S)` is pushed forward ([Kol07, 30.3]) and composed "on the right with our first blow-up
`π_{-1}`"): the core over the value of the input functor on the restricted triple, at `Z_{-1}` and
`S_0` (the first blow-up is empty when no component of `E^j` lies in `cosupp(𝓘, s)`). -/
def core (inp : BMOanData 𝕜 (n - 1) s) (hT : BDClass s T) : AnalyticManifold.BlowUpSequence ψ₀ M :=
  coreOfListOf (BD.isClosedSubmanifold_Zminus1 T s j) (isClosedSubmanifold_transformS T s j)
    (inp.functor.seq (restrictedTriple T s j hT) (bmoClass_restrictedTriple T s j hT))

/-- The value of the core has no empty centres ([Kol07, 32]). -/
theorem noEmptyCenters_core (inp : BMOanData 𝕜 (n - 1) s) (hT : BDClass s T) :
    (core T s j inp hT).NoEmptyCenters :=
  AnalyticManifold.BlowUpSequence.noEmptyCenters_eraseEmpty _

end BDan

/-- **The functor `BD_{n,m,j}` of [Kol07, Lemma 102]** on analytic manifolds: on a triple of the
class `BOClass m`, the core at the mark `s = tuningParam m` applied to the tuned triple
`(M, W_s(𝓘), E)` (the proof's first step, the tuning to a D-balanced ideal with the same order
reduction,
[Kol07, Corollary 101], at the mark `s` in place of Kollár's `m!`), with the input functor
`BMO_{n-1,s}`,
a `BMOanData 𝕜 (n - 1) (tuningParam m)`. The member is named by its index `j : T.F.ι`, which
every pull-back keeps. -/
def BDan [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (m : ℕ)
    (inp : BMOanData 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) : AnalyticManifold.BlowUpSequence ψ₀ M :=
  BDan.core (T.tuned m hT.1) (tuningParam m) j inp
    ⟨AnalyticTriple.boClass_tuned hT, AnalyticTriple.isDBalanced_tuned hT⟩

/-- The value of `BD_{n,m,j}` has no empty centres ([Kol07, 32]). -/
theorem noEmptyCenters_BDan [FiniteDimensional 𝕜 E] {M : AnalyticManifold.{u} 𝕜 E} (m : ℕ)
    (inp : BMOanData 𝕜 (n - 1) (tuningParam m)) (T : AnalyticTriple ψ₀ M)
    (hT : AnalyticTriple.BOClass m T) (j : T.F.ι) :
    (BDan m inp T hT j).NoEmptyCenters :=
  BDan.noEmptyCenters_core _ _ _ _ _

end Hironaka.Manifold

end
