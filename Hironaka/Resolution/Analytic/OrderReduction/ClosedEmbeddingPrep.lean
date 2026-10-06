/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Step21Defs
public import Hironaka.Resolution.Analytic.LocalIsoEquiv
public import Hironaka.Resolution.Analytic.OrderReduction.Tuned
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.TuningLemmas
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sets.Opens
import Mathlib.CategoryTheory.Category.Preorder
public import Hironaka.Resolution.Algebraic.Tuning.Parameter

/-!
# Theorem 103 (3): preparatory lemmas

[Kol07, Theorem 103 (3)]: for a smooth hypersurface `τ : Y ↪ X` and an ideal sheaf `J ⊂ 𝒪_Y`
nonzero on every irreducible component of `Y` with `τ_*(𝒪_Y / J) = 𝒪_X / I`, one has
`BO_{n,1}(X, I, ∅) = τ_* BMO_{n-1,1}(Y, J, 1, ∅)`. Its proof is [Kol07, 104, Step 2.4]: `I` contains
the local equations of `Y`, so it has order `1` and equals its tuning; with `E = ∅` Step 2.1 does
nothing, and in Step 2.2 one may take `H = Y`, so that the clause follows from Lemma 102 (3). The
assembly of this argument for the analytic functor is `ClosedEmbedding.lean`; this module proves
the facts it needs:

* `BD.Zminus1_one_eq_empty_of_isNonzeroEverywhere` — the first centre `Z_{-1}` of the proof of
  [Kol07, Lemma 102] at the member `Y` and the mark `1` is empty when the restriction `I|_Y` is
  nonzero at every point. A connected component of `Y` contained in `cosupp(I, 1)` is open in `Y`
  (a manifold is locally connected); the generators of `I|_Y` vanish on it, so their germs at its
  points are zero and the stalk of `I|_Y` there is `⊥`, against the hypothesis. This is the
  analytic reading of Kollár's "`J` is nonzero on every irreducible component of `Y`".
* `HypersurfaceFamily.nonemptyList_empty` — the empty boundary has no nonempty member, so Step 2.1
  is idle.
* `HypersurfaceFamily.eq_toLex_inr_of_append_empty` — the boundary `∅ + Y` has the single member
  `Y`.
* `AnalyticTriple.tuned_one` — at the mark `1` the tuning is the identity on triples.
-/

public section

noncomputable section

open Set Topology Hironaka.Local TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-! ### The first centre at the mark `1` for a nonzero restriction -/

/-- The hypothesis "`J` is nonzero on every irreducible component of `Y`" of
[Kol07, Theorem 103 (3)], read for `J = 𝓘|_Y` as `IsNonzeroEverywhere`, makes the first centre
`Z_{-1}` of the proof of [Kol07, Lemma 102] at the member `Y` and the mark `1` empty. A connected
component of `Y` contained in `cosupp(𝓘, 1)` is open in `Y`, the generators of `𝓘|_Y` vanish on it,
so their germs at its points are `0` and the stalk of `𝓘|_Y` there is `⊥`, against the hypothesis.
Not in the sources as a separate statement. -/
theorem _root_.Hironaka.Manifold.BD.Zminus1_one_eq_empty_of_isNonzeroEverywhere {S : Set M}
    (hS : IsClosedSubmanifold ψ₀ S 1)
    (I : AnalyticManifold.IdealSheaf M)
    (hJ : (I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff).IsNonzeroEverywhere) :
    Hironaka.Manifold.BD.Zminus1 I 1 S = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨hxS, hsub⟩ := hx
  have _lc : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (Fin (n - 1) → 𝕜) hS.toAnalyticManifold
  obtain ⟨W, hW, hWeq⟩ := isOpen_induced_iff.mp
    (isOpen_connectedComponent (x := (⟨x, hxS⟩ : S)))
  set J := I.pullback ⇑hS.inclusionMap hS.inclusionMap.contMDiff with hJdef
  -- points of `Y` over `W` lie in the cosupport of `J`
  have hcos : ∀ p : S, p.1 ∈ W → p ∈ J.support := by
    intro p hp
    have hpC : p.1 ∈ connectedComponentIn S x := by
      rw [connectedComponentIn_eq_image hxS]
      refine ⟨p, ?_, rfl⟩
      rw [← hWeq]
      exact hp
    have h1 : (1 : ℕ∞) ≤ I.ord p.1 := hsub hpC
    have hne : I.ord p.1 ≠ 0 := Order.one_le_iff_ne_zero.mp h1
    have hpI : p.1 ∈ I.support :=
      not_not.mp fun h => hne ((IdealSheaf.ord_eq_zero_iff I).mpr h)
    rw [hJdef, IdealSheaf.support_pullback]
    exact hpI
  -- generators of `I` near `x`, pulled back to generators of `J` near `x`
  obtain ⟨U, hxU, k, f, -, hgen⟩ := I.exists_generators x
  have hgen' : ∀ b (hb : b ∈ preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff U),
      J.stalkIdeal b = Ideal.span (Set.range fun i =>
        (structureSheaf 𝕜 (Fin (n - 1) → 𝕜) hS.toAnalyticManifold).presheaf.germ
          (preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff U) b hb
          (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff (f i))) :=
    fun b hb => IdealSheaf.stalkIdeal_pullback_eq_span _ _ I hgen hb
  set U' := preimageOpens ⇑hS.inclusionMap hS.inclusionMap.contMDiff U with hU'
  set W' : Opens hS.toAnalyticManifold :=
    ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val⟩ with hW'
  have hxU' : (⟨x, hxS⟩ : S) ∈ U' := hxU
  have hxW' : (⟨x, hxS⟩ : S) ∈ W' := by
    change x ∈ W
    have : (⟨x, hxS⟩ : S) ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]
      exact mem_connectedComponent
    exact this
  -- the generators vanish on `U' ⊓ W'`
  have hzero : ∀ (a : S) (ha : a ∈ U' ⊓ W') (i : Fin k),
      comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff (f i) ⟨a, ha.1⟩ = 0 := fun a ha i =>
    (IdealSheaf.mem_support_iff_forall_eq_zero J hgen' ha.1).mp (hcos a ha.2) i
  -- so their germs at `x` are `0`, and the stalk of `J` at `x` is `⊥`
  have hgerm : ∀ i : Fin k, (structureSheaf 𝕜 (Fin (n - 1) → 𝕜) hS.toAnalyticManifold).presheaf.germ
      U' ⟨x, hxS⟩ hxU' (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff (f i)) = 0 := by
    intro i
    have hres := (structureSheaf 𝕜 (Fin (n - 1) → 𝕜) hS.toAnalyticManifold).presheaf.germ_res_apply
      (homOfLE inf_le_left : U' ⊓ W' ⟶ U') ⟨x, hxS⟩ ⟨hxU', hxW'⟩
      (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff (f i))
    have h0 : (structureSheaf 𝕜 (Fin (n - 1) → 𝕜) hS.toAnalyticManifold).presheaf.map
        (homOfLE inf_le_left : U' ⊓ W' ⟶ U').op
        (comapSection ⇑hS.inclusionMap hS.inclusionMap.contMDiff (f i)) = 0 := by
      exact ContMDiffMap.ext fun a => hzero a.1 a.2 i
    refine hres.symm.trans ?_
    rw [h0]
    exact map_zero ((structureSheaf 𝕜 (Fin (n - 1) → 𝕜) hS.toAnalyticManifold).presheaf.germ
      (U' ⊓ W') ⟨x, hxS⟩ ⟨hxU', hxW'⟩).hom
  have hbot : J.stalkIdeal ⟨x, hxS⟩ = ⊥ := by
    rw [hgen' _ hxU']
    refine Ideal.span_eq_bot.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hgerm i
  exact hJ ⟨x, hxS⟩ hbot

/-! ### The empty boundary and the boundary `∅ + Y` -/

/-- The empty boundary has no nonempty member, so Step 2.1 of the proof of [Kol07, Theorem 103] is
idle on it ("if `E = ∅` then Step 2.1 does nothing", [Kol07, 104, Step 2.4]). -/
theorem HypersurfaceFamily.nonemptyList_empty
    (hF : Finite {j // (HypersurfaceFamily.empty M).hyp j ≠ ∅}) :
    (HypersurfaceFamily.empty M).nonemptyList hF = [] := by
  unfold HypersurfaceFamily.nonemptyList
  have _e : IsEmpty (HypersurfaceFamily.empty M).ι := inferInstanceAs (IsEmpty PEmpty)
  rw [Finset.eq_empty_of_isEmpty ((HypersurfaceFamily.empty M).nonemptyFinset hF),
    Finset.sort_empty]

/-- The boundary `∅ + Y` has exactly one member, the appended one. -/
theorem HypersurfaceFamily.eq_toLex_inr_of_append_empty (Y : Set M)
    (k : ((HypersurfaceFamily.empty M).append Y).ι) : k = toLex (Sum.inr PUnit.unit) := by
  rcases hk : ofLex k with j | u
  · exact j.elim
  · rw [← toLex_ofLex k, hk]
    exact congrArg (fun v => toLex (Sum.inr v)) (Subsingleton.elim u PUnit.unit)

/-! ### The tuning at the mark `1` -/

/-- At the mark `1` the tuning is the identity on triples (`tuning_one_tuningParam`; Kollár's
"`I` has order `1`, in particular `I = W(I)`" in [Kol07, 104, Step 2.4]). -/
theorem AnalyticTriple.tuned_one [FiniteDimensional 𝕜 E] (T : AnalyticTriple ψ₀ M) :
    T.tuned 1 le_rfl = T :=
  AnalyticTriple.ext' (IdealSheaf.tuning_one_tuningParam T.I) rfl

end Manifold

end
