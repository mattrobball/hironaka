/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Wlo09.Saturation
public import Hironaka.Manifold.Submanifold.Defs
import Hironaka.Algebra.Local.Regular
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.Coherence
import Hironaka.Resolution.Analytic.MaximalContact.OneStepDescentLemmas
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Mathlib.RingTheory.Filtration

/-!
# The singular locus of a reduced subspace contains no smooth hypersurface

For a reduced closed analytic subspace `Y` with ideal sheaf `I`, the singular locus
`Sing(Y) = Y ∖ Reg(Y)` contains no nonempty closed smooth hypersurface `H`
(`IdealSheaf.not_subset_sing_of_isClosedSubmanifold_one`), and no nonempty open set
(`IdealSheaf.not_subset_sing_of_isOpen`). The hypersurface statement: at every point `q` of `H`
the stalk `I_q` lies in the ideal `(h)` of `H`, `h` an adapted coordinate (every germ of `I`
vanishes on `Y ⊇ H`), and `h ∉ I_q`, since otherwise `I_q = (h)` and `𝒪_q/I_q` would be regular,
against `q ∈ Sing(Y)`. So the saturation `(I : I_H^∞)` (`IdealSheaf.saturation`) is a proper ideal
at every point of `H`, hence its stalk at `a ∈ H` also lies in `(h)`. For `f ∈ I_a` this gives
`f ∈ (h²)`, and then `f ∈ (h^m)` for every `m` by induction, since `I_a` is radical: from
`f = h^m g`, `(hg)^m = f g^{m−1} ∈ I_a`, so `hg ∈ I_a ⊆ (h²)` and `g ∈ (h)`, the stalk being a
domain. Krull's intersection theorem (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) then gives
`f = 0`, so `I_a = 0` and `𝒪_a/I_a = 𝒪_a` is regular, against `a ∈ Sing(Y)`. The open-set
statement: a germ of `I_a` vanishing on a neighbourhood of `a` is zero, so `I_a = 0`.

These are the facts behind Włodarczyk's remark that the centres of the embedded
desingularization have codimension at least two [Wlo09, Remark (2) after Theorem 2.0.3]: a centre
of codimension at most one lies over `Sing(Y)`, so it meets the exceptional divisor everywhere
(`Hironaka/Resolution/Analytic/Wlo09/CenterCodim.lean`). The arguments are not in the sources.
-/

@[expose] public section

noncomputable section

open Set Filter Topology TopologicalSpace IsLocalRing
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.IdealSheaf

open Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (I : IdealSheaf M)

/-- **The singular locus of a reduced subspace contains no nonempty closed smooth
hypersurface.** -/
theorem not_subset_sing_of_isClosedSubmanifold_one (hI : I.IsReduced) {H : Set M}
    (hH : IsClosedSubmanifold ψ H 1) (hsub : H ⊆ I.support \ I.regularLocus) (hne : H.Nonempty) :
    False := by
  obtain ⟨a, ha⟩ := hne
  have hsupp : H ⊆ I.support := fun x hx => (hsub hx).1
  -- every germ of `I` vanishes on `H`
  have hle : ∀ q, I.stalkIdeal q ≤ vanishingStalk (𝕜 := 𝕜) (E := E) H q := fun q =>
    Hironaka.Manifold.stalkIdeal_le_vanishingStalk_of_subset_cosupport I hsupp q
  set B := hH.idealSheaf with hB
  -- the stalk of the ideal sheaf of `H` at a point of `H`, in an adapted chart
  have hBq : ∀ (q : M) (hq : q ∈ H) (φ : OpenPartialHomeomorph M E) (σ : Fin 1 ↪ Fin n)
      (hqφ : q ∈ φ.source) (hφ : IsAdaptedChart ψ H φ σ),
      B.stalkIdeal q = Ideal.span {coord E ψ φ hφ.1 hqφ (σ 0)} := by
    intro q hq φ σ hqφ hφ
    rw [hB, hH.isIdealSheafOf_idealSheaf.2 φ σ hφ q hqφ hq, Set.range_unique]
    rfl
  -- the equation of `H` is not in `I` at a point of `H`: the quotient would be regular
  have hnot : ∀ q ∈ H, ¬ B.stalkIdeal q ≤ I.stalkIdeal q := by
    intro q hq hBle
    obtain ⟨φ, σ, hqφ, hφ⟩ := hH.exists_adaptedChart q hq
    have hIq : I.stalkIdeal q = Ideal.span {coord E ψ φ hφ.1 hqφ (σ 0)} := by
      refine le_antisymm ?_ ((hBq q hq φ σ hqφ hφ) ▸ hBle)
      rw [← hH.vanishingStalk_eq_span_coord hφ hqφ]
      exact hle q
    have hreg : IsRegularLocalRing (stalkRing M q ⧸ I.stalkIdeal q) := by
      rw [hIq]
      exact (IsRegularLocalRing.quotient_span_singleton
        (coord_mem_maximalIdeal_of_eq_zero φ hφ.1 hqφ ((hφ.2 q hqφ).mp hq 0))
        (coord_notMem_maximalIdeal_sq φ hφ.1 hqφ)).1
    exact (hsub hq).2 hreg
  -- the saturation of `I` by the ideal sheaf of `H` is proper at every point of `H`
  have hsat_supp : H ⊆ (I.saturation B).support := by
    intro q hq htop
    rw [stalkIdeal_saturation] at htop
    have hmono : Monotone fun k : ℕ =>
        Submodule.colon (I.stalkIdeal q) (SetLike.coe (B.stalkIdeal q ^ k)) := by
      intro k l hkl
      exact Submodule.colon_mono le_rfl (Ideal.pow_le_pow_right hkl)
    have h1 : (1 : stalkRing M q) ∈ ⨆ k : ℕ,
        Submodule.colon (I.stalkIdeal q) (SetLike.coe (B.stalkIdeal q ^ k)) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp h1
    rw [Submodule.mem_colon] at hk
    refine hnot q hq fun x hx => ?_
    have hxk : x ^ k ∈ I.stalkIdeal q := by
      simpa using hk (x ^ k) (Ideal.pow_mem_pow hx k)
    exact hI q (Ideal.mem_radical_of_pow_mem (Ideal.le_radical hxk))
  have hsat_le : (I.saturation B).stalkIdeal a ≤ vanishingStalk (𝕜 := 𝕜) (E := E) H a :=
    Hironaka.Manifold.stalkIdeal_le_vanishingStalk_of_subset_cosupport _ hsat_supp a
  -- the coordinates at `a`
  obtain ⟨φ, σ, haφ, hφ⟩ := hH.exists_adaptedChart a ha
  set h := coord E ψ φ hφ.1 haφ (σ 0) with hh
  have hvan : vanishingStalk (𝕜 := 𝕜) (E := E) H a = Ideal.span {h} :=
    hH.vanishingStalk_eq_span_coord hφ haφ
  have hBa : B.stalkIdeal a = Ideal.span {h} := hBq a ha φ σ haφ hφ
  have hJle : I.stalkIdeal a ≤ Ideal.span {h} := hvan ▸ hle a
  have hmem : h ∈ maximalIdeal (stalkRing M a) :=
    coord_mem_maximalIdeal_of_eq_zero φ hφ.1 haφ ((hφ.2 a haφ).mp ha 0)
  have hne0 : h ≠ 0 := (prime_coord_of_eq_zero φ hφ.1 haφ ((hφ.2 a haφ).mp ha 0)).ne_zero
  -- every element of `I_a` is divisible by every power of `h`
  have hpow : ∀ f ∈ I.stalkIdeal a, ∀ m : ℕ, f ∈ Ideal.span {h ^ (m + 1)} := by
    intro f hf m
    induction m with
    | zero => simpa using hJle hf
    | succ m ih =>
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ih
      have h1 : (h * g) ^ (m + 1) ∈ I.stalkIdeal a := by
        have : (h * g) ^ (m + 1) = g * h ^ (m + 1) * g ^ m := by ring
        rw [this]
        exact Ideal.mul_mem_right _ _ hf
      have h2 : h * g ∈ I.stalkIdeal a :=
        hI a (Ideal.mem_radical_of_pow_mem (Ideal.le_radical h1))
      have h3 : g ∈ (I.saturation B).stalkIdeal a := by
        rw [stalkIdeal_saturation]
        refine Submodule.mem_iSup_of_mem 1 ?_
        rw [Submodule.mem_colon]
        intro s hs
        rw [pow_one, hBa] at hs
        obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
        change g * (t * h) ∈ _
        rw [show g * (t * h) = t * (h * g) by ring]
        exact Ideal.mul_mem_left _ _ h2
      obtain ⟨g', rfl⟩ := Ideal.mem_span_singleton'.mp (hvan ▸ hsat_le h3)
      exact Ideal.mem_span_singleton'.mpr ⟨g', by ring⟩
  -- Krull: `I_a = 0`
  have hbot : I.stalkIdeal a = ⊥ := by
    refine le_bot_iff.mp fun f hf => ?_
    have hmem' : f ∈ ⨅ m : ℕ, Ideal.span {h} ^ m := by
      rw [Submodule.mem_iInf]
      intro m
      rw [Ideal.span_singleton_pow]
      exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow h (Nat.le_succ m)) (hpow f hf m)
    exact (Submodule.mem_bot _).mp ((Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {h}) fun ht =>
      (IsLocalRing.notMem_maximalIdeal.mpr (Ideal.span_singleton_eq_top.mp ht)) hmem).le hmem')
  have hreg : IsRegularLocalRing (stalkRing M a ⧸ I.stalkIdeal a) := by
    rw [hbot]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot _).symm
  exact (hsub ha).2 hreg

/-- **The singular locus of a subspace contains no nonempty open set**: a germ vanishing on a
neighbourhood is zero, so the stalk of `I` at a point of the open set is zero and the quotient
is regular. -/
theorem not_subset_sing_of_isOpen {O : Set M} (hO : IsOpen O)
    (hsub : O ⊆ I.support \ I.regularLocus) (hne : O.Nonempty) : False := by
  obtain ⟨a, ha⟩ := hne
  have hle : I.stalkIdeal a ≤ vanishingStalk (𝕜 := 𝕜) (E := E) O a :=
    Hironaka.Manifold.stalkIdeal_le_vanishingStalk_of_subset_cosupport I (fun x hx => (hsub hx).1) a
  have hvan : vanishingStalk (𝕜 := 𝕜) (E := E) O a = ⊥ := by
    refine le_bot_iff.mp fun s hs => ?_
    rw [mem_vanishingStalk_iff] at hs
    apply stalkToGerm_injective 𝓘(𝕜, E) ω M a
    rw [map_zero]
    revert hs
    induction stalkToGerm 𝓘(𝕜, E) ω M a s using Filter.Germ.inductionOn with
    | h f =>
      intro hs
      rw [Germ.vanishesOn_coe, nhdsWithin_eq_nhds.mpr (hO.mem_nhds ha)] at hs
      exact Filter.Germ.coe_eq.mpr hs
  have hbot : I.stalkIdeal a = ⊥ := le_bot_iff.mp (hvan ▸ hle)
  have hreg : IsRegularLocalRing (stalkRing M a ⧸ I.stalkIdeal a) := by
    rw [hbot]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot _).symm
  exact (hsub ha).2 hreg

end AnalyticManifold.IdealSheaf

end

end
