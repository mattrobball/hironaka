/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Restrict
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Split
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
import Hironaka.Scheme.Snc.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Scheme
public import Hironaka.Resolution.Algebraic.Snc.SncOnTransport

/-!
# The pointwise pass over a member

Step 2.1 of the proof of [Kol07, Theorem 103] applies [Kol07, Lemma 102] to each member `Eʲ` of
the boundary: the centres of the output over `Eʲ` are push-forwards of centres of the inductive
run on the strict transform of `Eʲ`, whose data are the restrictions of the outer data
([Kol07, Lemma 62]). For the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) this means that the classification of
such a centre at a point `g q'` follows from the inductive classification at `q'`. This module holds
the pointwise statement `centerClassifiedAt_of_comap_member`: for a closed immersion `g : Y ⟶ X`
whose kernel is the member `Eʲ⁰` of `E`, and a family `F` on `Y` whose members are the
restrictions of the other members of `E`, every chain-coordinate system at `g q'` in which the
current ideal `K` has the K-shape or the I-shape restricts to one at `q'`. The coordinate `k₀` of
`Eʲ⁰` generates the kernel of the stalk map (`ker_stalkMap_of_isClosedImmersion`); the others
restrict to a regular system of parameters (`isRegularSystemOfParameters_comp_succAbove`); the
members of `F` through `q'` are the members of `E` through `g q'` other than `Eʲ⁰` (a member
restricting `Eʲ⁰` itself would have the zero stalk, against the snc of `F`); the exponent of `k₀`
in the top monomial is `0` (the restricted ideal is nonzero); and the shape restricts — either no
level below `r` kills `k₀` (`map_span_mul_chainKIdeal_of_forall`,
`map_span_mul_chainIdeal_of_forall`), or a first level `l₀` does (`exists_min_level`;
`map_span_mul_chainKIdeal_of_lt`, `map_span_mul_chainIdeal_of_lt`, the truncated un-isolated
form). The inductive classification, read at the restricted system (truncated in the second case,
`chainCoordsFree_castLE`), gives a stratum of the restricted centre, which lifts with `k₀`
adjoined (`stratumIn_comap_of_stratumIn`, `terminalIn_comap_of_terminalIn`,
`terminalIn_comap_of_eq_span`, `stratumIn_comap_of_stratumIn_castLE`) to the stalk of the
pushed-forward centre (`stalkIdeal_map_of_isClosedImmersion`). The chain coordinates are those of
[Kol07, Definition 24]. This argument is not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Raw`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IsLocalRing BlowUpSequence
  Scheme.IdealSheafData Hironaka.Snc

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The first level at which the exponent of a given coordinate is positive. -/
theorem exists_min_level {r : ℕ} (v : Fin (r + 1) → ℕ)
    (h : ¬ ∀ i : Fin (r + 1), i.val < r → v i = 0) :
    ∃ l₀ : ℕ, ∃ hl : l₀ < r, v ⟨l₀, by omega⟩ ≠ 0 ∧ ∀ i : Fin (r + 1), i.val < l₀ → v i = 0 := by
  classical
  have hex : ∃ l, ∃ hl : l < r, v ⟨l, by omega⟩ ≠ 0 := by
    by_contra hn
    apply h
    intro i hi
    by_contra hne
    exact hn ⟨i.val, hi, hne⟩
  obtain ⟨hl, h0⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, hl, h0, fun i hi => ?_⟩
  by_contra hne
  exact Nat.find_min hex hi ⟨by omega, hne⟩

/-- Chain coordinates truncated to the first `l + 1` levels are chain coordinates. -/
theorem chainCoordsFree_castLE {E : DivisorFamily X} {p : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk p} {c : {j : E.ι // p ∈ (E.component j).support} → Fin n}
    {r : ℕ} {σ : Fin (r + 1) → Fin n} {a : Fin (r + 1) → Fin n → ℕ}
    (h : ChainCoordsFree E p z c σ a) {l : ℕ} (hl : l + 1 ≤ r + 1) :
    ChainCoordsFree E p z c (fun i : Fin (l + 1) => σ (Fin.castLE hl i))
      (fun i : Fin (l + 1) => a (Fin.castLE hl i)) := by
  obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := h
  exact ⟨hz, hcinj, hcmem, fun i i' hii' => Fin.castLE_injective hl (hσinj hii'),
    fun i j => hσc _ j, fun i k hk => ha _ k hk⟩

/-- **The pointwise pass over a member** ([Kol07, Lemma 102] and [Kol07, Lemma 62]): for a closed
immersion `g : Y ⟶ X` whose kernel is the member `Eʲ⁰` of `E`, and a family `F` on `Y` whose
members are the restrictions of the other members of `E`, the classification of a centre `Z'` on
`Y` at `q'` for the restricted ideal gives the classification of its push-forward at `g q'` for
the ideal on `X`: the outer chain coordinates restrict to `Y` (killing the coordinate of `Eʲ⁰`),
the outer shape restricts to the inner shape, and the inner stratum lifts with the killed
coordinate adjoined. -/
theorem centerClassifiedAt_of_comap_member {Y : Scheme.{u}} (g : Y ⟶ X) [IsClosedImmersion g]
    (E : DivisorFamily X) (F : DivisorFamily Y) (e : F.ι → E.ι) (he : Function.Injective e)
    (hcomp : ∀ a, F.component a = (E.component (e a)).comap g) (j₀ : E.ι)
    (hker : g.ker = E.component j₀) (hF : F.IsSnc) (hmiss : ∀ b, b ∉ Set.range e → b = j₀)
    {K : X.IdealSheafData} {Z' : Y.IdealSheafData} {q' : Y}
    [IsRegularLocalRing (X.presheaf.stalk (g q'))] [IsRegularLocalRing (Y.presheaf.stalk q')]
    (hK0 : (K.comap g).stalkIdeal q' ≠ ⊥)
    (h : CenterClassifiedAt F (K.comap g) Z' q') : CenterClassifiedAt E K (Z'.map g) (g q') := by
  classical
  intro n z c r σ a b hfree hb
  obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := id hfree
  have hqj : g q' ∈ (E.component j₀).support := by
    rw [← hker, ← SetLike.mem_coe, Scheme.Hom.support_ker]
    exact subset_closure ⟨q', rfl⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Fin.pos (c ⟨j₀, hqj⟩))).symm⟩
  set k₀ : Fin (n' + 1) := c ⟨j₀, hqj⟩ with hk₀
  set φ : X.presheaf.stalk (g q') →+* Y.presheaf.stalk q' := (g.stalkMap q').hom with hφdef
  have hφs : Function.Surjective φ := g.stalkMap_surjective q'
  have hkerφ : RingHom.ker φ = Ideal.span {z k₀} := by
    rw [hφdef, ker_stalkMap_of_isClosedImmersion, hker]
    exact hcmem ⟨j₀, hqj⟩
  have hφk : φ (z k₀) = 0 := by
    rw [← RingHom.mem_ker, hkerφ]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hz' : IsRegularSystemOfParameters (fun i : Fin n' => φ (z (k₀.succAbove i))) :=
    isRegularSystemOfParameters_comp_succAbove hz k₀ φ hφs hkerφ
  -- the members of `F` through `q'` are the members of `E` through `g q'` other than `j₀`
  have hmemF : ∀ a : {a : F.ι // q' ∈ (F.component a).support},
      g q' ∈ (E.component (e a.1)).support := fun a => by
    have := a.2
    rw [hcomp] at this
    exact (mem_support_comap_iff_apply _ _ _).mp this
  -- no member of `F` restricts the member `j₀` (its restriction would have the zero stalk)
  have hne : ∀ a : {a : F.ι // q' ∈ (F.component a).support}, c ⟨e a.1, hmemF a⟩ ≠ k₀ := by
    intro a heq
    have hj : e a.1 = j₀ := Subtype.mk.inj (hcinj heq)
    have h1 : ((E.component j₀).comap g).stalkIdeal q' =
        ((E.component j₀).stalkIdeal (g q')).map φ := IdealSheafData.stalkIdeal_comap _ g q'
    have hbot : (F.component a.1).stalkIdeal q' = ⊥ := by
      rw [hcomp, hj, h1, hcmem ⟨j₀, hqj⟩, Ideal.map_span, Set.image_singleton, hφk,
        Ideal.span_singleton_eq_bot.mpr rfl]
    obtain ⟨m, w, hw, cF, -, hcF⟩ := hF.2 q'
    have h2 : (F.component a.1).stalkIdeal q' = Ideal.span {w (cF a)} := hcF a
    rw [hbot] at h2
    exact ne_zero_of_isRegularSystemOfParameters hw (cF a)
      (Ideal.span_singleton_eq_bot.mp h2.symm)
  choose c' hc' using fun a => Fin.exists_succAbove_eq (hne a)
  have hσne : ∀ i, σ i ≠ k₀ := fun i => hσc i ⟨j₀, hqj⟩
  choose σ' hσ' using fun i => Fin.exists_succAbove_eq (hσne i)
  have hback : ∀ j : {j : E.ι // g q' ∈ (E.component j).support}, c j ≠ k₀ →
      ∃ a : {a : F.ι // q' ∈ (F.component a).support}, c ⟨e a.1, hmemF a⟩ = c j := by
    intro j hj
    have hjne : j.1 ≠ j₀ := fun h0 => hj (congrArg c (Subtype.ext h0))
    obtain ⟨a₀, ha₀⟩ : j.1 ∈ Set.range e := by
      by_contra hn
      exact hjne (hmiss j.1 hn)
    have hmem : q' ∈ (F.component a₀).support := by
      rw [hcomp, mem_support_comap_iff_apply, ha₀]
      exact j.2
    exact ⟨⟨a₀, hmem⟩, congrArg c (Subtype.ext ha₀)⟩
  have hC : ∀ κ ∈ Set.range c', k₀.succAbove κ ∈ Set.range c := by
    rintro κ ⟨a, rfl⟩
    exact ⟨_, (hc' a).symm⟩
  have hCback : ∀ κ : Fin n', k₀.succAbove κ ∈ Set.range c → κ ∈ Set.range c' := by
    rintro κ ⟨j, hj⟩
    obtain ⟨a, ha⟩ := hback j (by rw [hj]; exact Fin.succAbove_ne k₀ κ)
    refine ⟨a, Fin.succAbove_right_injective (p := k₀) ?_⟩
    rw [hc' a, ha, hj]
  have hk₀C : k₀ ∈ Set.range c := ⟨_, rfl⟩
  -- the restricted chain coordinates
  have hfree' : ChainCoordsFree F q' (fun i => φ (z (k₀.succAbove i))) c' σ'
      (fun i => a i ∘ k₀.succAbove) := by
    refine ⟨hz', ?_, ?_, ?_, ?_, ?_⟩
    · intro a₁ a₂ h12
      have h3 := congrArg k₀.succAbove h12
      rw [hc' a₁, hc' a₂] at h3
      exact Subtype.ext (he (Subtype.mk.inj (hcinj h3)))
    · intro a
      have hst : (K.comap g).stalkIdeal q' = (K.stalkIdeal (g q')).map φ :=
          IdealSheafData.stalkIdeal_comap K g q'
      have h1 : ((E.component (e a.1)).comap g).stalkIdeal q' =
          ((E.component (e a.1)).stalkIdeal (g q')).map φ := IdealSheafData.stalkIdeal_comap _ g q'
      rw [hcomp, h1, hcmem ⟨e a.1, hmemF a⟩, Ideal.map_span, Set.image_singleton]
      dsimp only
      rw [hc' a]
    · intro i i' hii'
      exact hσinj (by rw [← hσ' i, ← hσ' i', hii'])
    · intro i a heq
      exact hσc i ⟨e a.1, hmemF a⟩ (by rw [← hσ' i, ← hc' a, heq])
    · intro i κ hκ
      exact hCback κ (ha i _ hκ)
  have hb' : ∀ κ, (b ∘ k₀.succAbove) κ ≠ 0 → κ ∈ Set.range c' := fun κ hκ => hCback κ (hb _ hκ)
  -- the stalks of the centre and of the ideal
  have hZ : (Z'.map g).stalkIdeal (g q') = (Z'.stalkIdeal q').comap φ :=
    stalkIdeal_map_of_isClosedImmersion g Z' q'
  have hK' : (K.comap g).stalkIdeal q' = (K.stalkIdeal (g q')).map φ :=
      IdealSheafData.stalkIdeal_comap K g q'
  rw [hZ]
  -- `b k₀ = 0`: otherwise `K_q ⊆ (z k₀) = ker φ` and the inner stalk vanishes
  have hbk : ∀ C : Ideal (X.presheaf.stalk (g q')),
      K.stalkIdeal (g q') = Ideal.span {monomialOf z b} * C → b k₀ = 0 := by
    intro C hKC
    by_contra hne0
    apply hK0
    have h0 : φ (monomialOf z b) = 0 := by
      rw [← RingHom.mem_ker, hkerφ]
      exact monomialOf_mem_span_singleton z b hne0
    rw [hK', hKC, Ideal.map_mul, Ideal.map_span, Set.image_singleton, h0,
      Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]
  refine ⟨fun hK => ?_, fun hI => ?_⟩
  · -- the K-shape
    have hb0 := hbk _ hK
    by_cases hcase : ∀ i : Fin (r + 1), i.val < r → a i k₀ = 0
    · have hres := map_span_mul_chainKIdeal_of_forall z k₀ φ σ σ' hσ' a b hb0 hcase
      have hK'' : (K.comap g).stalkIdeal q' =
          Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
            chainKIdeal ((fun i => φ (z (k₀.succAbove i))) ∘ σ')
              (fun i => monomialOf (fun i => φ (z (k₀.succAbove i))) (a i ∘ k₀.succAbove)) := by
        rw [hK', hK, hres]
      exact stratumIn_comap_of_stratumIn hφs hkerφ hk₀C hC hσ'
        ((h _ c' σ' _ _ hfree' hb').1 hK'')
    · obtain ⟨l₀, hl, h0, hlt⟩ := exists_min_level (fun i => a i k₀) hcase
      have hres := map_span_mul_chainKIdeal_of_lt z k₀ φ hφk σ σ' hσ' a b hb0 hl h0 hlt
      have hfree'' := chainCoordsFree_castLE hfree' (l := l₀) (by omega)
      have hK'' : (K.comap g).stalkIdeal q' =
          Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
            chainIdeal (fun i : Fin (l₀ + 1) => φ (z (k₀.succAbove (σ' (Fin.castLE (by omega) i)))))
              (fun i : Fin (l₀ + 1) => monomialOf (fun i => φ (z (k₀.succAbove i)))
                (a (Fin.castLE (by omega) i) ∘ k₀.succAbove)) := by
        rw [hK', hK, hres]
      exact stratumIn_comap_of_stratumIn_castLE hφs hkerφ hk₀C hC hσ' hl h0
        ((h _ c' _ _ _ hfree'' hb').2 hK'')
  · -- the I-shape
    have hb0 := hbk _ hI
    by_cases hcase : ∀ i : Fin (r + 1), i.val < r → a i k₀ = 0
    · have hres := map_span_mul_chainIdeal_of_forall z k₀ φ σ σ' hσ' a b hb0 hcase
      have hK'' : (K.comap g).stalkIdeal q' =
          Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
            chainIdeal ((fun i => φ (z (k₀.succAbove i))) ∘ σ')
              (fun i => monomialOf (fun i => φ (z (k₀.succAbove i))) (a i ∘ k₀.succAbove)) := by
        rw [hK', hI, hres]
      rcases (h _ c' σ' _ _ hfree' hb').2 hK'' with h1 | h2 | h3
      · exact Or.inl (stratumIn_comap_of_stratumIn hφs hkerφ hk₀C hC hσ' h1)
      · exact Or.inr (Or.inl (terminalIn_comap_of_terminalIn hφs hkerφ hk₀C hC hσ' h2))
      · exact Or.inr (Or.inl (terminalIn_comap_of_eq_span hφs hkerφ hk₀C hσ' h3))
    · obtain ⟨l₀, hl, h0, hlt⟩ := exists_min_level (fun i => a i k₀) hcase
      have hres := map_span_mul_chainIdeal_of_lt z k₀ φ hφk σ σ' hσ' a b hb0 hl h0 hlt
      have hfree'' := chainCoordsFree_castLE hfree' (l := l₀) (by omega)
      have hK'' : (K.comap g).stalkIdeal q' =
          Ideal.span {monomialOf (fun i => φ (z (k₀.succAbove i))) (b ∘ k₀.succAbove)} *
            chainIdeal (fun i : Fin (l₀ + 1) => φ (z (k₀.succAbove (σ' (Fin.castLE (by omega) i)))))
              (fun i : Fin (l₀ + 1) => monomialOf (fun i => φ (z (k₀.succAbove i)))
                (a (Fin.castLE (by omega) i) ∘ k₀.succAbove)) := by
        rw [hK', hI, hres]
      exact Or.inl (stratumIn_comap_of_stratumIn_castLE hφs hkerφ hk₀C hC hσ' hl h0
        ((h _ c' _ _ _ hfree'' hb').2 hK''))

end Hironaka.Resolution
