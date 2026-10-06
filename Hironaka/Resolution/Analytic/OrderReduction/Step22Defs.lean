/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Tuned
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Manifold.Snc.Proper
public import Hironaka.Manifold.FiniteSuccession.BoundaryFamily
import Hironaka.Resolution.Analytic.OrderReduction.Induced
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Order reduction on manifolds: Step 2.2 of the proof of Theorem 103

Step 2.2 of the proof of [Kol07, Theorem 103]: once `H + E` has simple normal crossings, "we
restrict everything to the birational transform of `H`" and obtain order reduction from Lemma 102
by the induction on the dimension. Two remarks of Kollár govern the construction: under a smooth
blow-up of order `m` the birational transform of a smooth hypersurface of maximal contact is again
one (Step 2 of the proof), and one should not pick new hypersurfaces of maximal contact after a
blow-up but stick with the birational transforms of the old ones (the Warning of [Kol07, 104]).
This module provides the vocabulary of the construction, which is made in the compatible-family
form in `Step22Fam.lean`.

* `HypersurfaceFamily.finite_nonempty_append`, `HypersurfaceFamily.appendIdx`,
  `HypersurfaceFamily.isSnc_append_of_hasSncWithProper` — appending a hypersurface having proper
  simple normal crossings with a family keeps the family with simple normal crossings (at a point
  of `H` the proper chart is a chart of the appended family, its indices those of the members of
  `F` through the point and the coordinate of `H`; away from `H` the family's own chart serves) and
  keeps the nonempty members finite. Not in the sources.
* `BO.stepHClass`, `BO.greatestIdx` — the class of triples of `BOClass s` whose boundary has a
  greatest member, and that member, at which Lemma 102 is applied (the greatest member of `F + H`
  is `H`); `stepHClass_tuned` — the class is kept by Kollár's re-tuning "we can again replace `I`
  by `W(I)`" ([Kol07, 104, Step 2.2]; Kollár re-tunes at `s!`; the library's mark is
  `tuningParam s`, as in `Tuned.lean`). Kollár declares `H` the first member of `H + E` (index
  `0`); the library appends it as the greatest member, a convention that only fixes the index at
  which Lemma 102 is applied.

The clauses of Theorem 103 for Step 2 in the compatible-family form are proved in
`Step22Fam*.lean`, `Step2Assembly*.lean` and `FamilyIndependence.lean`; Step 3 of the proof
assembles the local functors in `GlobalizeFam.lean`.
-/

@[expose] public section

noncomputable section

open Set Topology AnalyticManifold IsLocalRing
open scoped Manifold ContDiff

universe u

namespace Manifold.HypersurfaceFamily

open _root_.Manifold
open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-! ### Appending a hypersurface with proper simple normal crossings -/

variable {M : Type u}

/-- Appending one hypersurface keeps the nonempty members of a family finite. -/
theorem finite_nonempty_append (F : HypersurfaceFamily M) (H : Set M)
    (hF : Finite {j // F.hyp j ≠ ∅}) : Finite {k // (F.append H).hyp k ≠ ∅} := by
  change Finite {k : F.ι ⊕ₗ PUnit.{u + 1} // (F.append H).hyp k ≠ ∅}
  have hfin : Set.Finite {j : F.ι | F.hyp j ≠ ∅} := Set.finite_coe_iff.mp hF
  have hsub : {k : F.ι ⊕ₗ PUnit.{u + 1} | (F.append H).hyp k ≠ ∅} ⊆
      ((fun j : F.ι => toLex (Sum.inl j)) '' {j : F.ι | F.hyp j ≠ ∅}) ∪
        {toLex (Sum.inr PUnit.unit)} := by
    intro k hk
    rcases hk' : ofLex k with j | u
    · left
      refine ⟨j, fun hj => hk ?_, ?_⟩
      · change (Sum.elim F.hyp (fun _ => H) ∘ ofLex) k = ∅
        rw [Function.comp_apply, hk']
        exact hj
      · change toLex (Sum.inl j) = k
        rw [← hk']
        exact toLex_ofLex k
    · right
      rw [Set.mem_singleton_iff]
      calc k = toLex (ofLex k) := (toLex_ofLex k).symm
        _ = toLex (Sum.inr PUnit.unit) := by rw [hk']
  exact Set.finite_coe_iff.mpr (Set.Finite.subset ((hfin.image _).union (Set.finite_singleton _))
    hsub)

/-- Chart indices for `F + H` at a point `a`: the index `cF j` for a member `E^j` of `F` through
`a`, and the index `cH` for `H`. -/
def appendIdx (F : HypersurfaceFamily M) (H : Set M) (a : M) (cF : {j // a ∈ F.hyp j} → Fin n)
    (cH : Fin n) (k : {k // a ∈ (F.append H).hyp k}) : Fin n :=
  Sum.rec (motive := fun s => a ∈ Sum.elim F.hyp (fun _ => H) s → Fin n)
    (fun j h => cF ⟨j, h⟩) (fun _ _ => cH) (ofLex k.1 : F.ι ⊕ PUnit.{u + 1}) k.2

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} [TopologicalSpace M] [ChartedSpace E M]

/-- Appending a hypersurface `H` having proper simple normal crossings with `F` keeps the family
with simple normal crossings ([Kol07, Definition 24]; this is Kollár's observation in Step 2.1 of
the proof of [Kol07, Theorem 103] that the new exceptional divisors have simple normal crossings
with the transforms of `H`, so that `H_r + E_r` has simple normal crossings): at a point of `H` the
proper chart (adapted to `H`, a chart of `F` whose indices avoid the coordinate of `H`) is a chart
of `F + H`; away from `H` the chart of `F` serves. -/
theorem isSnc_append_of_hasSncWithProper {F : HypersurfaceFamily M} {H : Set M} (hF : F.IsSnc ψ)
    (hH : IsClosedSubmanifold ψ H 1) (hFH : F.HasSncWithProper ψ H 1) : (F.append H).IsSnc ψ := by
  refine ⟨fun k => ?_, ?_, fun a => ?_⟩
  · rcases k with j | u
    · exact hF.1 j
    · exact hH
  · change LocallyFinite (Sum.elim F.hyp (fun _ => H) ∘ ⇑ofLex)
    exact (hF.2.1.sumElim (locallyFinite_of_finite _)).comp_injective ofLex.injective
  · by_cases haH : a ∈ H
    · obtain ⟨φ, σ, cidx, hφH, hφ, hprop⟩ := hFH a haH
      refine ⟨φ, appendIdx F H a cidx (σ 0), hφ.1, hφ.2.1, ?_, ?_⟩
      · rintro ⟨k, hk⟩ x hx
        rcases k with j | u
        · exact hφ.2.2.1 ⟨j, hk⟩ x hx
        · change x ∈ H ↔ ψ (φ x) (σ 0) = 0
          rw [hφH.2 x hx]
          exact ⟨fun h => h 0, fun h i => by rw [Subsingleton.elim i 0]; exact h⟩
      · rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
        rcases k with j | u <;> rcases k' with j' | u'
        · have h' : cidx ⟨j, hk⟩ = cidx ⟨j', hk'⟩ := h
          have := Subtype.mk.inj (hφ.2.2.2 h')
          subst this
          rfl
        · have h' : cidx ⟨j, hk⟩ = σ 0 := h
          exact absurd (Set.mem_range.mpr ⟨0, h'.symm⟩) (hprop ⟨j, hk⟩)
        · have h' : σ 0 = cidx ⟨j', hk'⟩ := h
          exact absurd (Set.mem_range.mpr ⟨0, h'⟩) (hprop ⟨j', hk'⟩)
        · cases u
          cases u'
          rfl
    · obtain ⟨φ, c, hφ⟩ := hF.2.2 a
      rcases isEmpty_or_nonempty (Fin n) with hn | hn
      · -- no member of `F + H` passes through `a`: the chart of `F` with no indices to assign
        have hno : ∀ k : {k // a ∈ (F.append H).hyp k}, False := by
          rintro ⟨k, hk⟩
          rcases k with j | u
          · exact hn.false (c ⟨j, hk⟩)
          · exact haH hk
        exact ⟨φ, fun k => (hno k).elim, hφ.1, hφ.2.1, fun k => (hno k).elim,
          fun k => (hno k).elim⟩
      · refine ⟨φ, appendIdx F H a c hn.some, hφ.1, hφ.2.1, ?_, ?_⟩
        · rintro ⟨k, hk⟩ x hx
          rcases k with j | u
          · exact hφ.2.2.1 ⟨j, hk⟩ x hx
          · exact absurd hk haH
        · rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
          rcases k with j | u <;> rcases k' with j' | u'
          · have h' : c ⟨j, hk⟩ = c ⟨j', hk'⟩ := h
            have := Subtype.mk.inj (hφ.2.2.2 h')
            subst this
            rfl
          · exact absurd hk' haH
          · exact absurd hk haH
          · exact absurd hk haH

end Manifold.HypersurfaceFamily

namespace Hironaka.Manifold

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}

/-! ### Appending a member away from a hypersurface -/

section AppendAway

variable {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- Appending a member missing the hypersurface `S` keeps proper simple normal crossings with `S`:
the proper chart of `F` at a point of `S` serves, the appended member passing through no point of
`S`. -/
theorem _root_.Manifold.HypersurfaceFamily.hasSncWithProper_append_of_notMem
    {F : HypersurfaceFamily M}
    {S Z : Set M} (hFS : F.HasSncWithProper ψ S 1) (hZ : ∀ a ∈ S, a ∉ Z) :
    (F.append Z).HasSncWithProper ψ S 1 := by
  intro a ha
  obtain ⟨φ, σ, cidx, hφ, hc, hprop⟩ := hFS a ha
  refine ⟨φ, σ, HypersurfaceFamily.appendIdx F Z a cidx (σ 0), hφ, ⟨hc.1, hc.2.1, ?_, ?_⟩, ?_⟩
  · rintro ⟨k, hk⟩ x hx
    rcases k with j | u
    · exact hc.2.2.1 ⟨j, hk⟩ x hx
    · exact absurd hk (hZ a ha)
  · rintro ⟨k, hk⟩ ⟨k', hk'⟩ h
    rcases k with j | u <;> rcases k' with j' | u'
    · have h' : cidx ⟨j, hk⟩ = cidx ⟨j', hk'⟩ := h
      have := Subtype.mk.inj (hc.2.2.2 h')
      subst this
      rfl
    · exact absurd hk' (hZ a ha)
    · exact absurd hk (hZ a ha)
    · exact absurd hk (hZ a ha)
  · rintro ⟨k, hk⟩
    rcases k with j | u
    · exact hprop ⟨j, hk⟩
    · exact absurd hk (hZ a ha)

end AppendAway

/-- The appended member is the greatest index of `F + H` (the lexicographic sum puts the right
summand last). -/
theorem le_toLex_inr {ι : Type u} [LinearOrder ι] (k : ι ⊕ₗ PUnit.{u + 1}) :
    k ≤ toLex (Sum.inr PUnit.unit) := by
  rcases hk : ofLex k with j | u
  · rw [← toLex_ofLex k, hk]
    exact le_of_lt (Sum.Lex.inl_lt_inr j PUnit.unit)
  · rw [← toLex_ofLex k, hk]

/-- The family of exceptional divisors (from the empty start) has finitely many nonempty members at
every stage. -/
theorem finite_nonempty_totalTransformSeq {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)
    (i : Fin (S.length + 1)) : Finite {k // (S.totalTransformSeq i).hyp k ≠ ∅} :=
  finite_nonempty_totalTransformSeqFrom S (HypersurfaceFamily.empty M)
    (Finite.of_injective (β := PEmpty.{u + 1})
      (fun j : {j // (HypersurfaceFamily.empty M).hyp j ≠ ∅} => j.1) fun _ _ h => Subtype.ext h) i

namespace BO

open _root_.Manifold

variable {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E} {s : ℕ}

/-! ### The greatest member of the boundary -/

/-- The class of triples of `BOClass s` whose boundary has a greatest member: the triples
`(X, I, H + E)` to which Kollár applies `BD_{n,m,0}` in Step 2.2 of the proof of
[Kol07, Theorem 103], the appended `H` being the greatest member. -/
def stepHClass (s : ℕ) : ∀ {M : AnalyticManifold.{u} 𝕜 E}, AnalyticTriple ψ₀ M → Prop :=
  fun T => AnalyticTriple.BOClass s T ∧ ∃ j : T.F.ι, ∀ k, k ≤ j

/-- The greatest member of the boundary of a triple of the class. -/
def greatestIdx {T : AnalyticTriple ψ₀ M} (hT : stepHClass s T) : T.F.ι :=
  Classical.choose hT.2

theorem le_greatestIdx {T : AnalyticTriple ψ₀ M} (hT : stepHClass s T) (k : T.F.ι) :
    k ≤ greatestIdx hT :=
  Classical.choose_spec hT.2 k

/-- The greatest member is unique. -/
theorem greatestIdx_eq {T : AnalyticTriple ψ₀ M} (hT : stepHClass s T) {j : T.F.ι}
    (hj : ∀ k, k ≤ j) : greatestIdx hT = j :=
  le_antisymm (hj _) (le_greatestIdx hT j)

/-! ### Step 2.2 -/

variable [FiniteDimensional 𝕜 E]

/-- A triple of the class tunes into the class at the mark `tuningParam s`: the boundary and its
index set are
kept by the tuning. -/
theorem stepHClass_tuned {T : AnalyticTriple ψ₀ M} (hT : stepHClass s T) :
    stepHClass (tuningParam s) (T.tuned s hT.1.1) :=
  ⟨AnalyticTriple.boClass_tuned hT.1, hT.2⟩

end BO

end Hironaka.Manifold

end
