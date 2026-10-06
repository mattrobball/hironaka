/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Predicates
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.RestrictDivisors
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# CP3 at the stalk of a member, and the snc clause

Three stalk-level facts that the proof of the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) consumes in given chain coordinates,
in Steps 2.1 and 2.2 of the proof of [Kol07, Theorem 103]:

* `stalkIdeal_map_of_isClosedImmersion` — the stalk of a pushed-forward ideal sheaf along a closed
  immersion `g` at `g y` is the preimage of the stalk at `y` under the stalk map (the kernel of the
  composite closed immersion, `ker_stalkMap_of_isClosedImmersion`; at a point off the support both
  sides are the unit ideal). It reads a centre's push-forward from a member back to the ambient
  scheme (the form of the centres in [Kol07, Lemma 62] and the proof of [Kol07, Lemma 102]).
* `exists_chainCoordsFree_comap_member` — the restriction of chain coordinates to a member: at a
  point of the member `Eʲ`, the images of the chain coordinates other than `e_j = z_{c j}` under
  the stalk map of the member are chain coordinates on `Eʲ` for the restricted family
  `(E − Eʲ)|_{Eʲ}` (the restriction of a simple normal crossing divisor of
  [Kol07, Definition 24]), the index maps re-indexed through `succAbove`. The restricted
  coordinates are a regular system of parameters of the stalk of the member
  (`isRegularSystemOfParameters_comp_succAbove`); the equations of the members restrict
  (`stalkIdeal_comap_subschemeι_eq_span`); the chain parameters and the supports of the exponents
  avoid the deleted coordinate.
* `notMem_span_sup_sq_of_isSncAt_append` — the snc clause of the re-basing of the flag
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Rebase`): if `E + H` has simple normal crossings
  at `q` in coordinates `w` (as at the end of Step 2.1, [Kol07, 104, Step 2.1]) and `z` are chain
  coordinates for `E` at `q`, a local equation `x` of `H` lies outside `(z_{c j} : j) + 𝔪²`. Indeed
  `x` is a unit multiple of the `w`-coordinate of `H`, each `z_{c j}` a unit multiple of another
  `w`-coordinate, and a coordinate of a regular system lies outside the span of the others plus
  `𝔪²` (`notMem_span_compl_sup_sq`).

These identities are not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Pass` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Chain`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-- The stalk of a pushed-forward ideal sheaf along a closed immersion is the preimage of the
stalk. -/
theorem stalkIdeal_map_of_isClosedImmersion {Y : Scheme.{u}} (g : Y ⟶ X) [IsClosedImmersion g]
    (Z : Y.IdealSheafData) (y : Y) :
    (Z.map g).stalkIdeal (g y) = (Z.stalkIdeal y).comap (g.stalkMap y).hom := by
  by_cases hy : y ∈ Z.support
  · obtain ⟨y', rfl⟩ := IdealSheafData.exists_subschemeι_eq Z hy
    have h1 := ker_stalkMap_of_isClosedImmersion (Z.subschemeι ≫ g) y'
    rw [Scheme.Hom.stalkMap_comp] at h1
    change (Z.subschemeι ≫ g).ker.stalkIdeal ((Z.subschemeι ≫ g) y') =
      (Z.stalkIdeal (Z.subschemeι y')).comap (g.stalkMap (Z.subschemeι y')).hom
    rw [← h1, ← IdealSheafData.ker_stalkMap_subschemeι Z y', RingHom.comap_ker]
    rfl
  · rw [IdealSheafData.stalkIdeal_eq_top_of_notMem_support Z hy, Ideal.comap_top]
    apply IdealSheafData.stalkIdeal_eq_top_of_notMem_support
    rw [IdealSheafData.support_map]
    intro hmem
    have hcl : IsClosed (g '' (Z.support : Set Y)) :=
      g.isClosedEmbedding.isClosedMap _ Z.support.isClosed
    rw [← SetLike.mem_coe, Closeds.coe_closure, hcl.closure_eq] at hmem
    obtain ⟨y₁, hy₁, hyy⟩ := hmem
    exact hy (g.isClosedEmbedding.injective hyy ▸ hy₁)

/-- The restriction of chain coordinates to a member ([Kol07, Definition 24]: the restriction of
a simple normal crossing divisor to a member not containing the subvariety): at `p ∈ Eʲ`, the
images of the coordinates other than `e_j` under the stalk map of the member are chain
coordinates on `Eʲ` for the family `(E − Eʲ)|_{Eʲ}`, with the index maps determined by
`succAbove`. -/
theorem exists_chainCoordsFree_comap_member (E : DivisorFamily X) (j : E.ι)
    {y : (E.component j).subscheme}
    [IsRegularLocalRing (X.presheaf.stalk ((E.component j).subschemeι y))] {n : ℕ}
    {z : Fin (n + 1) → X.presheaf.stalk ((E.component j).subschemeι y)}
    {c : {j' : E.ι // (E.component j).subschemeι y ∈ (E.component j').support} → Fin (n + 1)}
    {r : ℕ} {σ : Fin (r + 1) → Fin (n + 1)} {a : Fin (r + 1) → Fin (n + 1) → ℕ}
    (h : ChainCoordsFree E ((E.component j).subschemeι y) z c σ a)
    (hj : (E.component j).subschemeι y ∈ (E.component j).support) :
    ∃ (c' : {j' : ((E.erase j).comap (E.component j).subschemeι).ι //
          y ∈ ((((E.erase j).comap (E.component j).subschemeι)).component j').support} → Fin n)
      (σ' : Fin (r + 1) → Fin n),
      (∀ j', ∃ hmem, (c ⟨j, hj⟩).succAbove (c' j') = c ⟨j'.1.1, hmem⟩) ∧
      (∀ i, (c ⟨j, hj⟩).succAbove (σ' i) = σ i) ∧
      ChainCoordsFree ((E.erase j).comap (E.component j).subschemeι) y
        (fun i => (E.component j).subschemeι.stalkMap y (z ((c ⟨j, hj⟩).succAbove i))) c' σ'
        (fun i => a i ∘ (c ⟨j, hj⟩).succAbove) := by
  classical
  obtain ⟨hz, hcinj, hcmem, hσinj, hσc, ha⟩ := h
  have hmem' : ∀ j' : {j' : ((E.erase j).comap (E.component j).subschemeι).ι //
      y ∈ ((((E.erase j).comap (E.component j).subschemeι)).component j').support},
      (E.component j).subschemeι y ∈ (E.component j'.1.1).support := fun j' => by
    have := j'.2
    change y ∈ ((E.component j'.1.1).comap (E.component j).subschemeι).support at this
    exact (mem_support_comap_iff_apply _ _ y).mp this
  have hne : ∀ j', c ⟨j'.1.1, hmem' j'⟩ ≠ c ⟨j, hj⟩ := fun j' heq =>
    j'.1.2 (Subtype.mk.inj (hcinj heq))
  choose c' hc' using fun j' => Fin.exists_succAbove_eq (hne j')
  have hσne : ∀ i, σ i ≠ c ⟨j, hj⟩ := fun i => hσc i ⟨j, hj⟩
  choose σ' hσ' using fun i => Fin.exists_succAbove_eq (hσne i)
  have hφs : Function.Surjective ((E.component j).subschemeι.stalkMap y).hom :=
    (E.component j).subschemeι.stalkMap_surjective y
  have hker : RingHom.ker ((E.component j).subschemeι.stalkMap y).hom =
      Ideal.span {z (c ⟨j, hj⟩)} := by
    rw [IdealSheafData.ker_stalkMap_subschemeι]
    exact hcmem ⟨j, hj⟩
  refine ⟨c', σ', fun j' => ⟨hmem' j', hc' j'⟩, hσ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isRegularSystemOfParameters_comp_succAbove hz (c ⟨j, hj⟩) _ hφs hker
  · intro j₁ j₂ h12
    have h3 := congrArg (c ⟨j, hj⟩).succAbove h12
    rw [hc' j₁, hc' j₂] at h3
    have h5 : j₁.1.1 = j₂.1.1 := Subtype.mk.inj (hcinj h3)
    exact Subtype.ext (Subtype.ext h5)
  · intro j'
    change ((E.component j'.1.1).comap (E.component j).subschemeι).stalkIdeal y = _
    dsimp only
    rw [hc' j']
    exact stalkIdeal_comap_subschemeι_eq_span (E.component j) y (E.component j'.1.1)
      (hcmem ⟨j'.1.1, hmem' j'⟩)
  · intro i₁ i₂ h12
    apply hσinj
    rw [← hσ' i₁, ← hσ' i₂, h12]
  · intro i j' heq
    apply hσc i ⟨j'.1.1, hmem' j'⟩
    rw [← hσ' i, ← hc' j', heq]
  · intro i k hk
    obtain ⟨j₁, hj₁⟩ := ha i ((c ⟨j, hj⟩).succAbove k) hk
    have hj₁ne : j₁.1 ≠ j := fun heq => by
      have h4 : j₁ = ⟨j, hj⟩ := Subtype.ext heq
      rw [h4] at hj₁
      exact Fin.succAbove_ne (c ⟨j, hj⟩) k hj₁.symm
    refine ⟨⟨⟨j₁.1, hj₁ne⟩, ?_⟩, ?_⟩
    · change y ∈ ((E.component j₁.1).comap (E.component j).subschemeι).support
      exact (mem_support_comap_iff_apply _ _ y).mpr j₁.2
    · apply Fin.succAbove_right_injective (p := c ⟨j, hj⟩)
      rw [hc']
      exact hj₁

/-- The snc clause of the re-basing of the flag ([Kol07, 104, Step 2.1]: `H + E` has simple
normal crossings after Step 2.1): if `E.append H` has snc at `q` and `z` are chain coordinates for
`E` at `q`, then a local equation of `H` at `q` lies outside `(z_{c j} : j) + 𝔪²`. -/
theorem notMem_span_sup_sq_of_isSncAt_append {E : DivisorFamily X} {H : X.IdealSheafData} {q : X}
    [IsRegularLocalRing (X.presheaf.stalk q)] (hq : q ∈ H.support) {m : ℕ}
    {w : Fin m → X.presheaf.stalk q} (hsnc : (E.append H).IsSncAt q w)
    {n : ℕ} {z : Fin n → X.presheaf.stalk q} {c : {j : E.ι // q ∈ (E.component j).support} → Fin n}
    {r : ℕ} {σ : Fin (r + 1) → Fin n} {a : Fin (r + 1) → Fin n → ℕ}
    (hc : ChainCoordsFree E q z c σ a) {x : X.presheaf.stalk q}
    (hx : H.stalkIdeal q = Ideal.span {x}) :
    x ∉ Ideal.span (z '' Set.range c) ⊔ IsLocalRing.maximalIdeal (X.presheaf.stalk q) ^ 2 := by
  obtain ⟨hw, c₂, hc₂inj, hc₂mem⟩ := hsnc
  obtain ⟨-, -, hcmem, -, -, -⟩ := hc
  intro hmem
  let iH : {i : (E.append H).ι // q ∈ ((E.append H).component i).support} :=
    ⟨toLex (Sum.inr PUnit.unit), hq⟩
  have hH : H.stalkIdeal q = Ideal.span {w (c₂ iH)} := hc₂mem iH
  have hwx : w (c₂ iH) ∈ Ideal.span {x} := by
    rw [← hx, hH]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hwx
  have hle : Ideal.span (z '' Set.range c) ≤ Ideal.span (w '' {k | k ≠ c₂ iH}) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨jE, rfl⟩, rfl⟩
    let iE : {i : (E.append H).ι // q ∈ ((E.append H).component i).support} :=
      ⟨toLex (Sum.inl jE.1), jE.2⟩
    have hE : (E.component jE.1).stalkIdeal q = Ideal.span {w (c₂ iE)} := hc₂mem iE
    have hzw : z (c jE) ∈ Ideal.span {w (c₂ iE)} := by
      rw [← hE, hcmem jE]
      exact Ideal.mem_span_singleton_self _
    have hne : c₂ iE ≠ c₂ iH := fun heq =>
      Sum.inl_ne_inr (toLex.injective (congrArg Subtype.val (hc₂inj heq)))
    have hsub : ({w (c₂ iE)} : Set (X.presheaf.stalk q)) ⊆ w '' {k | k ≠ c₂ iH} :=
      Set.singleton_subset_iff.mpr ⟨c₂ iE, hne, rfl⟩
    exact Ideal.span_mono hsub hzw
  have hx' : x ∈ Ideal.span (w '' {k | k ≠ c₂ iH}) ⊔ IsLocalRing.maximalIdeal _ ^ 2 :=
    (sup_le_sup_right hle _) hmem
  apply notMem_span_compl_sup_sq hw (c₂ iH)
  rw [← ht]
  exact Ideal.mul_mem_left _ _ hx'

end Hironaka.Resolution
