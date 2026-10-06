/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative
import Hironaka.Algebra.Local.Regular
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Kol07.StrictTransformSupport
import Hironaka.Resolution.Algebraic.Wlo05.ChainIdealInf
import Hironaka.Resolution.Algebraic.Wlo05.ComponentsColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainColon
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedProtected
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedPullbackTools
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Resolution.Algebraic.Wlo05.OffCentreTransport
import Hironaka.Resolution.Algebraic.Wlo05.StrictTransformReduced
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUp.FlatColon
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tools for the un-isolated ideal

The statement CP6 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) follows the un-isolated ideal `I₀ =
I_Γ ⊓ K` along the loop `bedAux` (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`): at every stage
its mark-`1` transform is `Ĩ_Γ ⊓ K̃`, the strict transform of the protected components intersected
with the transform of the isolated ideal, and the identity is checked STALKWISE, on the blow-up of a
stage, from the chain forms. This module provides the stalk tools for that check and the two
structural lemmas that carry it along a sequence:

* the stalk of a finite intersection of ideal sheaves is the intersection of the stalks
  (localisation commutes with finite intersections); for the ideal of a disjoint union of closed
  subschemes, at a point of one member the stalk of the intersection is that member's stalk, and
  off the union it is the unit ideal;
* at a point `p ∈ Γ`, an ideal chain-relative monomial along `Γ` is the intersection of the stalk
  of `Γ` with the stalk of its colon by `Γ` (`chainIdeal_eq_span_inf_chainKIdeal` of
  `Hironaka.Resolution.Algebraic.Wlo05.ChainIdealInf` with CP2's `chainRelativeKAt_colon`);
* locality of the marked transform through the stalk at `π q`, and the unit stalk of a strict
  transform off `π⁻¹(Γ)`;
* clause (4′) of [Kol07, Definition 66] at the mark `1`: along a sequence of order `≥ 1` the marked
  transform lies in the ideal of the centre (the centre is smooth, hence reduced), the hypothesis
  `K ≤ Z` of the one-blow-up identity of CP4
  (`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf`);
* the single-ideal transport `markedTransformSeq_eq_inf_of_forall_step`: `I₀ = P ⊓ K` and the
  one-blow-up identity at every stage give `I_j = P̃_j ⊓ K_j` at every stage — the induction
  engine of CP6, by structural recursion on the sequence;
* the bridge for a disjoint union of reduced closed subschemes: its ideal is the vanishing ideal of
  the union of the supports, it is reduced, its support is the union, and its strict transform
  along a sequence is the intersection of the members' strict transforms
  (`strictTransformSeq_biInf_of_pairwise_disjoint`) — the protected components as a single ideal
  `P = ⨅ γ ∈ Γs, γ`, the shape the transport lemma consumes.

These lemmas are not in the literature. Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP4Sheaf`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Isolation`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Stage`,
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP6Loop` and
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP5`.
-/

public section

universe u

open Ideal CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

/-! ### Stalks: finite intersections, disjoint unions, locality -/

section Stalks

variable {X : Scheme.{u}}

/-- The stalk of a finite intersection of ideal sheaves is the intersection of the stalks
(localisation of finitely generated ideals commutes with finite intersections). -/
theorem stalkIdeal_inf (I J : X.IdealSheafData) (x : X) :
    (I ⊓ J).stalkIdeal x = I.stalkIdeal x ⊓ J.stalkIdeal x := by
  obtain ⟨U, hx⟩ := exists_affineOpens_mem x
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := U.2.isLocalization_stalk ⟨x, hx⟩
  rw [stalkIdeal_eq_map_germ _ U hx, stalkIdeal_eq_map_germ I U hx, stalkIdeal_eq_map_germ J U hx,
    ideal_inf]
  exact IsLocalization.map_inf (S := X.presheaf.stalk x)
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _

/-- `stalkIdeal_inf` for a finite family. -/
theorem stalkIdeal_finset_biInf {ι : Type*} (A : Finset ι)
    (I : ι → X.IdealSheafData) (x : X) :
    (⨅ a ∈ A, I a).stalkIdeal x = ⨅ a ∈ A, (I a).stalkIdeal x := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [stalkIdeal_top]
  | insert b A hb ih => rw [Finset.iInf_insert, Finset.iInf_insert, stalkIdeal_inf, ih]

/-- The ideal of a disjoint union: at a point of one member of a finite family of ideal sheaves
with pairwise disjoint supports, the stalk of the intersection is that member's stalk. -/
theorem stalkIdeal_biInf_eq_of_mem_of_pairwise_disjoint {ι : Type*}
    (A : Finset ι) (I : ι → X.IdealSheafData)
    (hdisj : (A : Set ι).Pairwise fun a b => Disjoint (I a).support (I b).support)
    {a : ι} (ha : a ∈ A) {x : X} (hx : x ∈ (I a).support) :
    (⨅ b ∈ A, I b).stalkIdeal x = (I a).stalkIdeal x := by
  rw [stalkIdeal_finset_biInf]
  refine le_antisymm (iInf₂_le a ha) (le_iInf₂ fun b hb => ?_)
  by_cases hba : b = a
  · subst hba
    exact le_rfl
  · rw [stalkIdeal_eq_top_of_notMem_support _ fun hxb =>
      Hironaka.Resolution.notMem_of_disjoint_closeds (hdisj hb ha hba) hxb hx]
    exact le_top

/-- Off the union of the supports the intersection has the unit stalk. -/
theorem stalkIdeal_biInf_eq_top_of_forall_notMem {ι : Type*}
    (A : Finset ι) (I : ι → X.IdealSheafData) {x : X} (hx : ∀ a ∈ A, x ∉ (I a).support) :
    (⨅ b ∈ A, I b).stalkIdeal x = ⊤ := by
  rw [stalkIdeal_finset_biInf]
  exact le_antisymm le_top
    (le_iInf₂ fun b hb => (stalkIdeal_eq_top_of_notMem_support _ (hx b hb)).ge)

omit [CharZero k] in
/-- The intersection form at `p ∈ Γ` on the scheme (CP2's `chainRelativeKAt_colon` gives the
K-shape of the colon in the same coordinates): an ideal chain-relative monomial along `Γ` at `p`
is, at `p`, the intersection of the stalk of `Γ` with the stalk of its colon by `Γ`,
`I_p = I_{Γ,p} ⊓ (I : I_Γ)_p`. -/
theorem stalkIdeal_eq_inf_colon_of_chainRelativeAt
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] {E : DivisorFamily X} {I Γ : X.IdealSheafData}
    {p : X} (h : ChainRelativeAt E I Γ p) :
    I.stalkIdeal p = Γ.stalkIdeal p ⊓ (I.colon Γ).stalkIdeal p := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨n, z, c, r, σ, a, b, hcc, hb, hI⟩ := h
  have := isRegularLocalRing_stalk f p
  have hb' : ∀ k, k ∈ Set.range σ → b k = 0 := by
    rintro k ⟨i, rfl⟩
    by_contra hne
    obtain ⟨j, hj⟩ := hb _ hne
    exact hcc.2.2.2.2.1 i j hj.symm
  rw [stalkIdeal_colon_of_isLocallyNoetherian, hI, hcc.2.2.2.2.2.2,
    chainIdeal_colon_span_eq' hcc.1 hcc.2.2.2.1 hcc.apply_eq_zero_of_mem_range b hb']
  exact span_mul_chainIdeal_eq_span_inf hcc.1 hcc.apply_eq_zero_of_mem_range b hb'

/-- Locality of the marked transform: the mark-`m` transform along the blow-up of `D` has, at a
point `q`, a stalk determined by the stalk of the ideal at `π q` — two ideals with the same stalk
at `π q` have transforms with the same stalk at `q` (`stalkIdeal_comap`, the stalk of a colon on a
Noetherian scheme). -/
theorem stalkIdeal_markedTransform_eq_of_stalkIdeal_eq [IsLocallyNoetherian X]
    (D I K : X.IdealSheafData) (m : ℕ) {q : D.blowUp}
    (h : I.stalkIdeal (D.blowUpπ q) = K.stalkIdeal (D.blowUpπ q)) :
    (I.markedTransform D m).stalkIdeal q = (K.markedTransform D m).stalkIdeal q := by
  have : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
  change ((I.comap D.blowUpπ).colon (D.exceptionalDivisor ^ m)).stalkIdeal q =
    ((K.comap D.blowUpπ).colon (D.exceptionalDivisor ^ m)).stalkIdeal q
  rw [stalkIdeal_colon_of_isLocallyNoetherian, stalkIdeal_colon_of_isLocallyNoetherian,
    stalkIdeal_comap, stalkIdeal_comap, h]

/-- The strict transform of `Γ` has the unit stalk at a point whose image is off `Γ` (its support
lies in `π⁻¹(Γ)`). -/
theorem stalkIdeal_strictTransform_eq_top_of_notMem [IsLocallyNoetherian X]
    (D Γ : X.IdealSheafData) {q : D.blowUp} (h : D.blowUpπ q ∉ Γ.support) :
    (Γ.strictTransform D).stalkIdeal q = ⊤  :=
  stalkIdeal_eq_top_of_notMem_support _ fun hq =>
    h (Hironaka.Sequence.blowUpπ_mem_support_of_mem_support_strictTransform D Γ hq)



omit [CharZero k] in
/-- For a sequence of order `≥ 1` for `(I, 1)`, the marked transform at a stage lies in the ideal
of the centre ([Kol07, Definition 66 (4′)]: the order along the centre is `≥ 1`; the centre is
smooth, hence reduced). This is the hypothesis `K_n ≤ Z_n` of the sheaf form of CP4. -/
theorem markedTransformSeq_le_center_of_isOrderGeSeq (f : X ⟶ Spec (CommRingCat.of k))
    (S : BlowUpSequence X) (I : X.IdealSheafData) (E : DivisorFamily X)
    (hS : S.IsOrderGeSeq f I 1 E) (i : Fin S.length) :
    S.markedTransformSeq I 1 i.castSucc ≤ S.center i := by
  have hc : Smooth ((S.center i).subschemeι ≫ S.stageMap i.castSucc ≫ f) := hS.1 i
  have hord := IsOrderGeSeq.leOrdAlong hS i
  -- order `≥ 1` at the generic points of the centre puts the whole centre in the support
  have hsupp : (S.center i).support ≤ (S.markedTransformSeq I 1 i.castSucc).support := by
    intro z hz
    obtain ⟨η, hη, hspec⟩ := Closeds.exists_mem_genericPoints_specializes (S.center i).support hz
    have h1 : (1 : ℕ∞) ≤ (S.markedTransformSeq I 1 i.castSucc).ord η := by simpa using hord η hη
    exact hspec.mem_closed (S.markedTransformSeq I 1 i.castSucc).support.isClosed
      ((one_le_ord_iff _ η).mp h1)
  have hrad : S.markedTransformSeq I 1 i.castSucc ≤ (S.center i).radical := by
    rw [← vanishingIdeal_support]
    exact le_support_iff_le_vanishingIdeal.mp hsupp
  -- the centre is smooth, so its stalks are prime and its ideal is radical
  refine le_of_stalkIdeal_le fun x => ?_
  by_cases hx : x ∈ (S.center i).support
  · have := isRegularLocalRing_quotient_stalkIdeal (S.center i)
      (S.stageMap i.castSucc ≫ f) hx
    have hprime : ((S.center i).stalkIdeal x).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    obtain ⟨U, hxU⟩ := exists_affineOpens_mem x
    rw [stalkIdeal_eq_map_germ (S.markedTransformSeq I 1 i.castSucc) U hxU]
    rw [stalkIdeal_eq_map_germ (S.center i) U hxU] at hprime ⊢
    have h1 : ((S.markedTransformSeq I 1 i.castSucc).ideal U).map
          ((S.stage i.castSucc).presheaf.germ U.1 x hxU).hom ≤
        (((S.center i).ideal U).radical).map ((S.stage i.castSucc).presheaf.germ U.1 x hxU).hom :=
      Ideal.map_mono (hrad U)
    exact h1.trans ((Ideal.map_radical_le _).trans_eq hprime.radical)
  · rw [stalkIdeal_eq_top_of_notMem_support (S.center i) hx]
    exact le_top

end Stalks

/-! ### The transport of the intersection form along a succession -/

section Transport

/-- The single-ideal form of the transport of the invariant: `I₀ = P ⊓ K` and the one-step
identity at every stage give `I_j = P̃_j ⊓ K_j` at every stage. -/
theorem markedTransformSeq_eq_inf_of_forall_step :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (P I₀ K : X.IdealSheafData),
      I₀ = P ⊓ K →
      (∀ i : Fin S.length,
        S.markedTransformSeq I₀ 1 i.castSucc =
            S.strictTransformSeq P i.castSucc ⊓ S.markedTransformSeq K 1 i.castSucc →
          (S.markedTransformSeq I₀ 1 i.castSucc).markedTransform (S.center i) 1 =
            (S.strictTransformSeq P i.castSucc).strictTransform (S.center i) ⊓
              (S.markedTransformSeq K 1 i.castSucc).markedTransform (S.center i) 1) →
      ∀ i : Fin (S.length + 1),
        S.markedTransformSeq I₀ 1 i = S.strictTransformSeq P i ⊓ S.markedTransformSeq K 1 i
  | _, nil _, _, _, _, h₀, _, _ => h₀
  | _, cons _ _ _, _, _, _, h₀, _, ⟨0, _⟩ => h₀
  | _, cons X D rest, P, I₀, K, h₀, hstep, ⟨j + 1, hj⟩ =>
    markedTransformSeq_eq_inf_of_forall_step rest (P.strictTransform D) (I₀.markedTransform D 1)
      (K.markedTransform D 1) (hstep ⟨0, Nat.succ_pos _⟩ h₀)
      (fun ⟨v, hv⟩ hv' => hstep ⟨v + 1, Nat.succ_lt_succ hv⟩ hv') ⟨j, Nat.lt_of_succ_lt_succ hj⟩


end Transport

/-! ### The ideal of a disjoint union of reduced closed subschemes and its strict transforms -/

section Bridge

variable {X : Scheme.{u}}

/-- A finite intersection of reduced ideal sheaves is the vanishing ideal of the union of their
supports (each is the vanishing ideal of its support; `vanishingIdeal_iSup`). -/
theorem biInf_eq_vanishingIdeal_biSup_support (Γs : Finset X.IdealSheafData)
    (hred : ∀ γ ∈ Γs, IsReduced γ.subscheme) :
    (⨅ γ ∈ Γs, γ) = vanishingIdeal (⨆ γ ∈ Γs, γ.support) := by
  calc (⨅ γ ∈ Γs, γ) = ⨅ γ ∈ Γs, vanishingIdeal γ.support := by
        refine iInf_congr fun γ => iInf_congr fun hγ => ?_
        have := hred γ hγ
        rw [vanishingIdeal_support_of_isReduced]
    _ = vanishingIdeal (⨆ γ ∈ Γs, γ.support) := by simp only [vanishingIdeal_iSup]

/-- The intersection of finitely many reduced ideal sheaves is reduced. -/
theorem isReduced_biInf_subscheme (Γs : Finset X.IdealSheafData)
    (hred : ∀ γ ∈ Γs, IsReduced γ.subscheme) : IsReduced (⨅ γ ∈ Γs, γ).subscheme := by
  rw [biInf_eq_vanishingIdeal_biSup_support Γs hred]
  exact isReduced_subscheme_vanishingIdeal _

/-- The support of a finite intersection of reduced ideal sheaves is the union of the supports. -/
theorem coe_support_biInf (Γs : Finset X.IdealSheafData)
    (hred : ∀ γ ∈ Γs, IsReduced γ.subscheme) :
    (((⨅ γ ∈ Γs, γ).support : Closeds X) : Set X) = ⋃ γ ∈ Γs, (γ.support : Set X) := by
  rw [biInf_eq_vanishingIdeal_biSup_support Γs hred,
    Hironaka.Sequence.support_vanishingIdeal_eq]
  rw [← Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
  rfl

/-- **The strict transform of a disjoint union is the intersection of the strict transforms**: for
reduced ideal sheaves with pairwise disjoint supports, the strict transform of their intersection
along a sequence is the intersection of their strict transforms (both reduced with the same
support; `strictTransformSeq_eq_prod_of_pairwise_disjoint` and `⨅ = ∏` for disjoint supports). -/
theorem strictTransformSeq_biInf_of_pairwise_disjoint [IsLocallyNoetherian X]
    (S : BlowUpSequence X) (Γs : Finset X.IdealSheafData)
    (hred : ∀ γ ∈ Γs, IsReduced γ.subscheme)
    (hdisj : (↑Γs : Set X.IdealSheafData).Pairwise fun a b => Disjoint a.support b.support)
    (i : Fin (S.length + 1)) :
    S.strictTransformSeq (⨅ γ ∈ Γs, γ) i = ⨅ γ ∈ Γs, S.strictTransformSeq γ i := by
  have hJ := isReduced_biInf_subscheme Γs hred
  rw [Hironaka.Sequence.strictTransformSeq_eq_prod_of_pairwise_disjoint S (⨅ γ ∈ Γs, γ) Γs
    (fun γ => γ) hred (coe_support_biInf Γs hred) i
    (fun a ha b hb hab => disjoint_strictTransformSeq_support_of_disjoint S a b
      (hdisj ha hb hab) i),
    prod_eq_inf_of_pairwise_disjoint _ _
      (fun a ha b hb hab => disjoint_strictTransformSeq_support_of_disjoint S a b
        (hdisj ha hb hab) i),
    Finset.inf_eq_iInf]

end Bridge

end Hironaka.Resolution
