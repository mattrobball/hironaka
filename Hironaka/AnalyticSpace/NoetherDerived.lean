/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Coherent
import Hironaka.AnalyticSpace.CoherentColon
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Consequences of local Noetherianity on an analytic `K`-space

Three consequences of the local stationarity of increasing sequences of ideal sheaves of finite
type on an analytic `K`-space `X` — the property "`X` is locally Noetherian" of [BM97, (3.8)],
which Bierstone and Milman take as a standing property of their categories of spaces. Each theorem
takes that local stationarity as an explicit hypothesis `hloc`;
`Hironaka/AnalyticSpace/ModelTransport.lean` derives `hloc` from the Noether lemma on the models
`(G, 𝒜_G)`, itself taken as a hypothesis.

* `stabilizes_of_isCompact_closure_of_locallyStationary` ([BM97, 3.9]: "if `X` (respectively,
  `|X|`) is locally Noetherian and `|X|` is quasi-compact, then `X` (respectively, `|X|`) is
  Noetherian"): a finite subcover of the
  compact closure of `U` by the neighbourhoods of local stationarity and the maximum of their
  indices;
* `isNoetherian_of_compactSpace_of_locallyStationary` (one direction of "`X` is Noetherian iff
  `|X|` is compact", [BM97, 3.9]): the case `U = univ`, with `IdealSheaf.ext` turning stalkwise
  equality into equality of closed subspaces;
* `hasLocalGenerators_iSup_colon_pow_of_locallyStationary` (the saturation,
  [BM97, Proposition 3.13] and the sentence after it): the colon ideal sheaves `(J : I^k)`
  (`hasLocalGenerators_colon_idealSheaf`) form an increasing sequence, stationary near every
  point, so the stalkwise union is `(J : I^N)_x` near `x` — an ideal sheaf of finite type.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- Given local stationarity, on a set with compact closure the sequence stabilizes uniformly
[BM97, 3.9]. -/
theorem stabilizes_of_isCompact_closure_of_locallyStationary (X : AnalyticSpace.{u} K)
    (W : ℕ → ClosedSubspace X)
    (hloc : ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (N : ℕ), ∀ m ≥ N, ∀ y ∈ V,
      (W m).stalkIdeal y = (W N).stalkIdeal y)
    (U : Set X) (hU : IsCompact (closure U)) :
    ∃ N, ∀ m ≥ N, ∀ x ∈ U, (W m).stalkIdeal x = (W N).stalkIdeal x := by
  classical
  choose V hxV N hN using hloc
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    fun y _ => Set.mem_iUnion.mpr ⟨y, hxV y⟩
  refine ⟨t.sup N, fun m hm x hx => ?_⟩
  obtain ⟨x₀, hx₀t, hxV₀⟩ := Set.mem_iUnion₂.mp (ht (subset_closure hx))
  have h₀ : N x₀ ≤ t.sup N := Finset.le_sup hx₀t
  rw [hN x₀ m (h₀.trans hm) x hxV₀, hN x₀ (t.sup N) h₀ x hxV₀]

/-- A compact analytic `K`-space on which every increasing sequence of ideal sheaves of finite type
is locally stationary is Noetherian: one direction of [BM97, 3.9]. -/
theorem isNoetherian_of_compactSpace_of_locallyStationary (X : AnalyticSpace.{u} K) [CompactSpace X]
    (hloc : ∀ C : ℕ → IdealSheaf X.toLocallyRingedSpace.𝒪, (∀ m, C m ≤ C (m + 1)) →
      ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (N : ℕ), ∀ m ≥ N, ∀ y ∈ V,
        (C m).stalkIdeal y = (C N).stalkIdeal y) :
    X.IsNoetherian := by
  intro W hW
  obtain ⟨N, hN⟩ := stabilizes_of_isCompact_closure_of_locallyStationary X W (hloc W hW) Set.univ
    (by rw [closure_univ]; exact isCompact_univ)
  exact ⟨N, fun m hm => IdealSheaf.ext fun x => hN m hm x (Set.mem_univ x)⟩

/-- The saturation `⨆_k (J_x : I_x^k)` ([BM97, Proposition 3.13] and the sentence after it) has
local generators, given local stationarity of increasing sequences of ideal sheaves. -/
theorem hasLocalGenerators_iSup_colon_pow_of_locallyStationary (X : AnalyticSpace.{u} K)
    (J I : IdealSheaf X.toLocallyRingedSpace.𝒪)
    (hloc : ∀ C : ℕ → IdealSheaf X.toLocallyRingedSpace.𝒪, (∀ m, C m ≤ C (m + 1)) →
      ∀ x : X, ∃ (V : Opens X) (_ : x ∈ V) (N : ℕ), ∀ m ≥ N, ∀ y ∈ V,
        (C m).stalkIdeal y = (C N).stalkIdeal y) :
    IdealSheaf.HasLocalGenerators (𝒪 := X.toLocallyRingedSpace.𝒪)
      fun x : X => ⨆ k : ℕ,
        Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) := by
  intro a
  -- the increasing sequence of colon ideal sheaves `(J : I^k)`
  obtain ⟨C, hC⟩ : ∃ C : ℕ → IdealSheaf X.toLocallyRingedSpace.𝒪, C = fun k =>
      IdealSheaf.ofStalks _ (fun x => Submodule.colon (J.stalkIdeal x)
        (SetLike.coe ((I ^ k).stalkIdeal x)))
        (hasLocalGenerators_colon_idealSheaf X J (I ^ k)) := ⟨_, rfl⟩
  have hCs : ∀ k (x : X), (C k).stalkIdeal x =
      Submodule.colon (J.stalkIdeal x) (SetLike.coe (I.stalkIdeal x ^ k)) := by
    intro k x
    rw [hC]
    dsimp only
    rw [IdealSheaf.stalkIdeal_ofStalks, IdealSheaf.stalkIdeal_pow]
  have hmono : ∀ k, C k ≤ C (k + 1) := by
    intro k x
    rw [hCs, hCs]
    exact Submodule.colon_mono le_rfl
      (SetLike.coe_subset_coe.mpr (Ideal.pow_le_pow_right (Nat.le_succ k)))
  have hmono' : Monotone C := monotone_nat_of_le_succ hmono
  obtain ⟨V, haV, N, hN⟩ := hloc C hmono a
  obtain ⟨U', haU', l, g, -, hg⟩ := (C N).exists_generators a
  obtain ⟨U, hU⟩ : ∃ U, U = V ⊓ U' := ⟨_, rfl⟩
  have hUV : U ≤ V := hU ▸ inf_le_left
  have hUU' : U ≤ U' := hU ▸ inf_le_right
  have haU : a ∈ U := by
    rw [hU, ← SetLike.mem_coe, Opens.coe_inf]
    exact ⟨haV, haU'⟩
  refine ⟨U, haU, Fin l, inferInstance,
    fun i => X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU').op (g i), fun b hb => ?_⟩
  have hsup : (⨆ k : ℕ, Submodule.colon (J.stalkIdeal b) (SetLike.coe (I.stalkIdeal b ^ k))) =
      (C N).stalkIdeal b := by
    refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le N (hCs N b).le)
    rw [← hCs]
    rcases le_total k N with hk | hk
    · exact IdealSheaf.le_def.mp (hmono' hk) b
    · rw [hN k hk b (hUV hb)]
  have hgi : ∀ i, X.toLocallyRingedSpace.𝒪.presheaf.germ U b hb
      (X.toLocallyRingedSpace.𝒪.presheaf.map (homOfLE hUU').op (g i)) =
        X.toLocallyRingedSpace.𝒪.presheaf.germ U' b (hUU' hb) (g i) := fun i =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  dsimp only
  rw [hsup, hg b (hUU' hb)]
  congr 1
  ext s
  simp only [Set.mem_range, hgi]

end AnalyticSpace
