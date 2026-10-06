/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolation
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.Thm36.FirstCenter
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAbsorbed
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedDisjoint
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNotContained
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUpSequence.StalkProdDisjointSupport
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The isolated marked ideal at the absorbing stage

In the isolation passage of the proof of [Wlo05, Theorem 4.7.1], at the first stage `n` whose
centre contains the strict transform of a component, the modified run replaces the marked ideal
`I_n` by the colon `I' := I_n : I_Γ`, `I_Γ` the reduced ideal of the union `Γ` of the absorbed
strict transforms, and restarts. This module reads that isolation stalkwise, in the index form of
the stages of the run, under the invariant `InvCE` of the loop and the hypothesis `ClaimKC`
(Włodarczyk's Claim in Kollár's setting, `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedHypotheses`):

* the absorbed strict transforms are pairwise disjoint
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedDisjoint`), so `I_Γ` is their product;
* `I_n = I' · I_Γ`: at a point of an absorbed `c̃`, `I_n = M(I_n) · c̃` (Włodarczyk's Claim,
  through `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedAbsorbed`), `I_Γ = c̃`, and `(M c̃ : c̃) · c̃
  = M c̃`; off `Γ` the colon is by the unit ideal;
* the monomial part is unchanged, `M(I') = M(I_n)`: its exponents are the orders at the generic
  points of the components of the members of the boundary, which lie off `Γ`
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNotContained`);
* `N(I') = 1` along `Γ`: `M(I_n) ≤ I'` at the points of `Γ`, so the colon `I' : M(I')` is the unit
  ideal there;
* `N(I_n) ≤ N(I')`: the nonmonomial support can only shrink at the isolation.

The splitting `I = M(I) · N(I)` is that of [Kol07, Definition–Lemma 110]. Since `ClaimKC` is
false for the transcribed order, the theorems of this module are CONDITIONAL lemmas; the
definitions (`absorbIndex`, `absorbed`, `absorbedIdeal`, `isolatedMarkedIdeal`) and the
unconditional bookkeeping are used by `Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRemaining`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedIsolatedState`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedStep` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP1Remaining`. The unconditional treatment of the
isolated ideal is CP2 (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry`) and CP6
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation`).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-- A point lies in the supremum of finitely many closed sets iff it lies in one of them. -/
theorem mem_biSup_closeds_iff {X : Scheme.{u}} {ι : Type v} (A : Finset ι) (Z : ι → Closeds X)
    (x : X) : x ∈ (⨆ a ∈ A, Z a : Closeds X) ↔ ∃ a ∈ A, x ∈ Z a := by
  change x ∈ ((⨆ a ∈ A, Z a : Closeds X) : Set X) ↔ _
  rw [← Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂]
  exact ⟨fun ⟨a, ha, hx⟩ => ⟨a, ha, hx⟩, fun ⟨a, ha, hx⟩ => ⟨a, ha, hx⟩⟩

section Isolated

variable (T : MarkedTriple k) (hm : T.m = 1) (C : Finset T.X.left.IdealSheafData)
  (h : ∃ n, HasAbsorptionAt T hm C n)

open Classical in
/-- The absorbing stage `Nat.find h` of the loop as a centre index of the run
(`find_lt_length`). -/
noncomputable def absorbIndex : Fin (bmoOneRun T hm).length :=
  ⟨Nat.find h, find_lt_length T hm C h⟩

open Classical in
/-- The members absorbed at the absorbing stage — the filter in the definition of
`isolatedTriple`. -/
noncomputable def absorbed : Finset T.X.left.IdealSheafData :=
  C.filter fun c => CenterContains (bmoOneRun T hm) c (Nat.find h)

/-- Włodarczyk's `I_Γ` at the absorbing stage, in index form: the reduced ideal of the union of the
absorbed strict transforms ([Wlo05, Theorem 4.7.1, proof]). -/
noncomputable def absorbedIdeal :
    ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (⨆ c ∈ absorbed T hm C h,
    ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).support)

/-- Włodarczyk's isolated marked ideal `I_n : I_Γ` at the absorbing stage, in index form
([Wlo05, Theorem 4.7.1, proof]). -/
noncomputable def isolatedMarkedIdeal :
    ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc).IdealSheafData :=
  ((bmoOneRun T hm).markedTransformSeq T.I 1 (absorbIndex T hm C h).castSucc).colon
    (absorbedIdeal T hm C h)

variable {T hm C h}

open Classical in
/-- The absorbed members are members. -/
theorem absorbed_subset : absorbed T hm C h ⊆ C := Finset.filter_subset _ _

/-- The data of an absorbed member: the invariant of the loop gives its generic point `η`, off the
boundary, at which `T.I` agrees with it; the stop rule gives absorption at the stage of the loop
and at none before. -/
theorem absorbed_spec (hinv : InvCE T.I T.E C) {c : T.X.left.IdealSheafData}
    (hc : c ∈ absorbed T hm C h) :
    ∃ η : T.X.left, η ∈ T.I.support.genericPoints ∧ c = Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure {η}) ∧
      (∀ i, η ∉ (T.E.component i).support) ∧
      T.I.stalkIdeal η = (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).stalkIdeal η ∧
      CenterContains (bmoOneRun T hm) (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η}))
        (absorbIndex T hm C h) ∧
      ∀ m < (absorbIndex T hm C h).val,
        ¬ CenterContains (bmoOneRun T hm) (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            {η})) m := by
  classical
  rw [absorbed, Finset.mem_filter] at hc
  obtain ⟨η, hη, rfl, hηE, hIc⟩ := hinv.mem c hc.1
  exact ⟨η, hη, rfl, hηE, hIc, hc.2, fun m hm' => not_centerContains_of_lt_find T hm C h hc.1 hm'⟩

/-- The absorbed strict transforms are pairwise disjoint (the disjointness of
[Wlo05, Theorem 4.7.1] for the loop; conditional on `ClaimKC`). -/
theorem pairwise_disjoint_strictTransformSeq_absorbed (hinv : InvCE T.I T.E C) (hKC : ClaimKC k) :
    ((absorbed T hm C h : Finset T.X.left.IdealSheafData) : Set
      T.X.left.IdealSheafData).Pairwise fun a b =>
      Disjoint ((bmoOneRun T hm).strictTransformSeq a (absorbIndex T hm C h).castSucc).support
        ((bmoOneRun T hm).strictTransformSeq b (absorbIndex T hm C h).castSucc).support := by
  intro a ha b hb hab
  obtain ⟨η, hη, rfl, hηE, hIc, habs, hfirst⟩ := absorbed_spec hinv (Finset.mem_coe.mp ha)
  obtain ⟨η', hη', rfl, hηE', hIc', habs', hfirst'⟩ := absorbed_spec hinv (Finset.mem_coe.mp hb)
  refine disjoint_closeds_iff.mpr fun p hp hp' => hab ?_
  rw [eq_of_mem_strictTransformSeq_support_of_absorbed T hm hη hηE hIc hη' hηE' hIc'
    (absorbIndex T hm C h) habs hfirst hfirst' hKC hp hp']

/-- Włodarczyk's `I_Γ` is the product of the absorbed strict transforms (each is integral, hence
the vanishing ideal of its support; pairwise disjoint). Conditional on `ClaimKC`. -/
theorem absorbedIdeal_eq_prod (hinv : InvCE T.I T.E C) (hKC : ClaimKC k) :
    absorbedIdeal T hm C h = ∏ c ∈ absorbed T hm C h,
      (bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc := by
  have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
  refine Scheme.IdealSheafData.vanishingIdeal_iSup_support_eq_prod _ _ (fun c hc => ?_)
    (pairwise_disjoint_strictTransformSeq_absorbed hinv hKC)
  obtain ⟨η, -, rfl, -, -, -, hfirst⟩ := absorbed_spec hinv hc
  have := isIntegral_subscheme_vanishingIdeal_closure η
  have := isIntegral_strictTransformSeq_of_le_firstCenterIndex (bmoOneRun T hm)
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) (absorbIndex T hm C h).castSucc
    (val_le_firstCenterIndex_of_absorbed T hm (absorbIndex T hm C h) hfirst)
  rw [Scheme.IdealSheafData.vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]

/-- The stalk of `I_Γ` at a point of an absorbed strict transform is the stalk of that strict
transform. Conditional on `ClaimKC`. -/
theorem stalkIdeal_absorbedIdeal_of_mem (hinv : InvCE T.I T.E C) (hKC : ClaimKC k)
    {c : T.X.left.IdealSheafData} (hc : c ∈ absorbed T hm C h)
    {p : (bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc}
    (hp : p ∈ ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).support) :
    (absorbedIdeal T hm C h).stalkIdeal p =
      ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).stalkIdeal p := by
  rw [absorbedIdeal_eq_prod hinv hKC]
  exact Scheme.IdealSheafData.stalkIdeal_finset_prod_eq_of_mem_of_pairwise_disjoint _ _
    (pairwise_disjoint_strictTransformSeq_absorbed hinv hKC) hc hp

/-- `I_n = (I_n : I_Γ) · I_Γ` (the isolation of [Wlo05, Theorem 4.7.1, proof]; conditional on
`ClaimKC`): stalkwise, at a point of an absorbed `c̃`, `I_n = M(I_n) · c̃` and
`(M c̃ : c̃) · c̃ = M c̃`; off `Γ` the colon is by the unit ideal. -/
theorem markedTransformSeq_eq_isolatedMarkedIdeal_mul_absorbedIdeal (hinv : InvCE T.I T.E C)
    (hKC : ClaimKC k) :
    (bmoOneRun T hm).markedTransformSeq T.I 1 (absorbIndex T hm C h).castSucc =
      isolatedMarkedIdeal T hm C h * absorbedIdeal T hm C h := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun (absorbIndex T hm C h).castSucc).X.left ↘
      Spec (.of k)).isLocallyNoetherian_of_field
  refine Scheme.IdealSheafData.ext_stalkIdeal fun p => ?_
  rw [Scheme.IdealSheafData.stalkIdeal_mul, isolatedMarkedIdeal,
      Scheme.IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian]
  by_cases hp : p ∈ (absorbedIdeal T hm C h).support
  · rw [absorbedIdeal, support_vanishingIdeal_eq, mem_biSup_closeds_iff] at hp
    obtain ⟨c, hc, hpc⟩ := hp
    have hΓp := stalkIdeal_absorbedIdeal_of_mem hinv hKC hc hpc
    obtain ⟨η, hη, rfl, hηE, hIc, habs, hfirst⟩ := absorbed_spec hinv hc
    have hK3 := stalkIdeal_markedTransformSeq_eq_mul_of_absorbed T hm hη hηE hIc
      (absorbIndex T hm C h) habs hfirst hKC hpc
    rw [hΓp, hK3]
    refine le_antisymm ?_ ?_
    · exact Ideal.mul_mono_left fun x hx =>
        Submodule.mem_colon.mpr fun y hy => Ideal.mul_mem_mul hx hy
    · exact Ideal.mul_le.mpr fun r hr s hs => Submodule.mem_colon.mp hr s hs
  · rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hp, Submodule.top_coe,
      Submodule.colon_univ,
      Ideal.mul_top]

/-- The monomial part is unchanged by the isolation (conditional on `ClaimKC`): its exponents are
the orders at the generic points of the components of the members of the boundary, which lie off
`Γ` (`notMem_strictTransformSeq_support_of_mem_genericPoints_component`), where the colon by `I_Γ`
changes nothing. -/
theorem monomialPart_isolatedMarkedIdeal (hinv : InvCE T.I T.E C) (hKC : ClaimKC k) :
    monomialPart (isolatedMarkedIdeal T hm C h)
        ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc) =
      monomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 (absorbIndex T hm C h).castSucc)
        ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc) := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun (absorbIndex T hm C h).castSucc).X.left ↘
      Spec (.of k)).isLocallyNoetherian_of_field
  rw [monomialPart_eq_monomial, monomialPart_eq_monomial]
  refine monomial_congr _ fun i ζ hζ => ?_
  have hζΓ : ζ ∉ (absorbedIdeal T hm C h).support := by
    rw [absorbedIdeal, support_vanishingIdeal_eq, mem_biSup_closeds_iff]
    rintro ⟨c, hc, hζc⟩
    obtain ⟨η, hη, rfl, hηE, hIc, habs, hfirst⟩ := absorbed_spec hinv hc
    exact notMem_strictTransformSeq_support_of_mem_genericPoints_component T hm hη hηE hIc
      (absorbIndex T hm C h) habs hfirst hKC i hζ hζc
  have hst : (isolatedMarkedIdeal T hm C h).stalkIdeal ζ =
      ((bmoOneRun T hm).markedTransformSeq T.I 1 (absorbIndex T hm C h).castSucc).stalkIdeal ζ := by
    rw [isolatedMarkedIdeal, Scheme.IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian,
      Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hζΓ, Submodule.top_coe,
          Submodule.colon_univ]
  rw [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, hst]

/-- The nonmonomial part of the isolated marked ideal is the unit ideal along the absorbed strict
transforms (conditional on `ClaimKC`): at such a point `M(I') = M(I_n) ≤ I' = (M(I_n) c̃ : c̃)`. -/
theorem stalkIdeal_nonmonomialPart_isolatedMarkedIdeal_eq_top (hinv : InvCE T.I T.E C)
    (hKC : ClaimKC k) {c : T.X.left.IdealSheafData} (hc : c ∈ absorbed T hm C h)
    {p : (bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc}
    (hp : p ∈ ((bmoOneRun T hm).strictTransformSeq c (absorbIndex T hm C h).castSucc).support) :
    (nonmonomialPart (isolatedMarkedIdeal T hm C h)
      ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc)).stalkIdeal p =
      ⊤ := by
  have hrun := isOrderGeSeq_bmoOneRun T hm
  have hlN : IsLocallyNoetherian ((bmoOneRun T hm).stage (absorbIndex T hm C h).castSucc) :=
    ((T.induced (bmoOneRun T hm) hrun (absorbIndex T hm C h).castSucc).X.left ↘
      Spec (.of k)).isLocallyNoetherian_of_field
  have hΓp := stalkIdeal_absorbedIdeal_of_mem hinv hKC hc hp
  obtain ⟨η, hη, rfl, hηE, hIc, habs, hfirst⟩ := absorbed_spec hinv hc
  have hK3 := stalkIdeal_markedTransformSeq_eq_mul_of_absorbed T hm hη hηE hIc
    (absorbIndex T hm C h) habs hfirst hKC hp
  rw [nonmonomialPart_eq_colon, Scheme.IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian,
    monomialPart_isolatedMarkedIdeal hinv hKC, isolatedMarkedIdeal,
    Scheme.IdealSheafData.stalkIdeal_colon_of_isLocallyNoetherian, hΓp, hK3]
  refine (Ideal.eq_top_iff_one _).mpr (Submodule.mem_colon.mpr fun s hs => ?_)
  rw [one_smul]
  exact Submodule.mem_colon.mpr fun y hy => Ideal.mul_mem_mul hs hy

/-- The nonmonomial part can only shrink at the isolation: `N(I_n) ≤ N(I_n : I_Γ)` (the monomial
parts agree and `I_n ≤ I_n : I_Γ`). Conditional on `ClaimKC`. -/
theorem nonmonomialPart_le_nonmonomialPart_isolatedMarkedIdeal (hinv : InvCE T.I T.E C)
    (hKC : ClaimKC k) :
    nonmonomialPart ((bmoOneRun T hm).markedTransformSeq T.I 1 (absorbIndex T hm C h).castSucc)
        ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc) ≤
      nonmonomialPart (isolatedMarkedIdeal T hm C h)
        ((bmoOneRun T hm).totalTransformSeq T.E (absorbIndex T hm C h).castSucc) := by
  rw [nonmonomialPart_eq_colon, nonmonomialPart_eq_colon, monomialPart_isolatedMarkedIdeal hinv hKC]
  exact Scheme.IdealSheafData.colon_mono_left _ _ _ (Scheme.IdealSheafData.le_colon_self _ _)

end Isolated

end Hironaka.Resolution
