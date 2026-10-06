/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitMain
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Transform
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Exceptional
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The nonmonomial round: the weak transform of `N(I)` is the nonmonomial part

Step 1 of the proof of [Kol07, Theorem 107] (item 111, Step 1) applies order reduction to the
nonmonomial part `N(I)`; Kollár notes that the two birational transforms `(Π₁)⁻¹_* N(I)` and
`(Π₁)⁻¹_*(I, m)` differ only in their monomial part, by an ideal sheaf of exceptional divisors of
`Π₁`, whence `N((Π₁)⁻¹_*(I, m)) = (Π₁)⁻¹_* N(I)`.
`Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step1NonmonomialPart` has the one-step identity
`nonmonomialPart_markedTransform_eq_weakTransform` and the end identity with `N` on both sides.
The proof of the statement CP3 of the embedded desingularization
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedChainRelative`) along Step 1 needs the identity at
every stage, with the weak transform itself on the left. This requires in addition that the weak
transform of `N(I)` has the unit ideal as monomial part, i.e. order `0` along every member of the
induced families: along the strict transforms of the old members because a member of order `0` is
off the centre and the blow-up is an isomorphism there, and along the exceptional divisors because
the pulled-back order at a generic point of the exceptional divisor is the order at the generic
point of the component of the centre ([Kol07, Definition 47], the multiplicity of the pullback along
the exceptional divisor; the weak transform of [Kol07, 58]), which is exactly `d` for a sequence
of order `d` (`IsOrderSeq`); both facts are in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Exceptional`. This module holds the recursion
(`ord_weakTransformSeq_eq_zero_of_mem_genericPoints`), the vanishing of the monomial part
(`nonmonomialPart_eq_self_of_forall_ord_eq_zero`, from [Kol07, Definition–Lemma 110]) and the
identity in its triple form (`weakTransformSeq_eq_nonmonomialPart_markedTransformSeq`). Used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP3Step1`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  Hironaka BlowUpSequence Scheme.IdealSheafData Hironaka.BMO

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}

/-- An ideal of order `0` along every member of `E` has the unit ideal as monomial part and is
its own nonmonomial part ([Kol07, Definition–Lemma 110]). -/
theorem nonmonomialPart_eq_self_of_forall_ord_eq_zero
    (E : DivisorFamily X) (J : X.IdealSheafData)
    (hJE : ∀ (j : E.ι), ∀ ξ ∈ (E.component j).support.genericPoints, J.ord ξ = 0) :
    nonmonomialPart J E = J := by
  rw [nonmonomialPart_eq_colon, monomialPart_eq_monomial]
  have htop : E.monomial (fun η => (J.ord η).toNat) = ⊤ := by
    unfold DivisorFamily.monomial
    rw [← Scheme.IdealSheafData.one_eq_top]
    refine Finset.prod_eq_one fun i _ => ?_
    refine finprod_mem_of_eqOn_one fun η hη => ?_
    change _ ^ (J.ord η).toNat = 1
    rw [hJE i η hη, ENat.toNat_zero, pow_zero]
  rw [htop, colon_top]

/-- The recursion: along a sequence of order `d` for `J` with `J` of order `0` along every member,
the weak transforms have order `0` along every member of the induced families. By structural
recursion on the sequence, the Noetherian instance carried explicitly (through
`isNoetherian_of_field` on the blow-up); at a stage `i + 1` a member is a strict transform of a
member of the previous stage
(`ord_weakTransform_eq_zero_of_mem_genericPoints_strictTransform`) or the exceptional divisor of
the previous blow-up (`ord_weakTransform_eq_zero_of_mem_genericPoints_exceptionalDivisor`, the
order along the centre being exactly `d` by `IsOrderSeq`). -/
theorem ord_weakTransformSeq_eq_zero_of_mem_genericPoints_aux :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) [IsNoetherian X] (f : X ⟶ Spec (CommRingCat.of k))
      (n : ℕ) [SmoothOfRelativeDimension n f] {J : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ},
      S.IsOrderSeq f J E d →
      (∀ (j : E.ι), ∀ ξ ∈ (E.component j).support.genericPoints, J.ord ξ = 0) →
      ∀ (i : Fin (S.length + 1)) (j : (S.totalTransformSeq E i).ι) {ε : S.stage i},
        ε ∈ ((S.totalTransformSeq E i).component j).support.genericPoints →
        (S.weakTransformSeq J i).ord ε = 0
  | _, nil _, _, _, _, _, _, _, _, _, hJE, _, j, ε, hε => hJE j ε hε
  | _, cons _ _ _, _, _, _, _, _, _, _, _, hJE, ⟨0, _⟩, j, ε, hε => hJE j ε hε
  | _, cons X D rest, hN, f, n, hsm, J, E, d, hS, hJE, ⟨i + 1, hi⟩, j, ε, hε => by
    obtain ⟨⟨hD, hsnc, hord⟩, ht⟩ := (isOrderSeq_cons_iff f J E d D rest).1 hS
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have hsm' : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hprop : IsProper D.blowUpπ := blowUp.isProper_π D
    have hN' : IsNoetherian D.blowUp := (D.blowUpπ ≫
        f).isNoetherian_of_field
    refine ord_weakTransformSeq_eq_zero_of_mem_genericPoints_aux rest
        (D.blowUpπ ≫ f) n ht ?_
      ⟨i, Nat.lt_of_succ_lt_succ hi⟩ j hε
    intro j' ξ hξ
    rcases j' with j₀ | j₀
    · exact ord_weakTransform_eq_zero_of_mem_genericPoints_strictTransform D (E.component j₀)
        (hJE j₀) hξ
    · exact ord_weakTransform_eq_zero_of_mem_genericPoints_exceptionalDivisor f n D hD hord hξ

/-- The `Fin` form of the recursion `ord_weakTransformSeq_eq_zero_of_mem_genericPoints_aux`. -/
theorem ord_weakTransformSeq_eq_zero_of_mem_genericPoints [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {S : BlowUpSequence X} {J : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ}
    (hS : S.IsOrderSeq f J E d)
    (hJE : ∀ (j : E.ι), ∀ ξ ∈ (E.component j).support.genericPoints, J.ord ξ = 0)
    (i : Fin (S.length + 1)) (j : (S.totalTransformSeq E i).ι) {ε : S.stage i}
    (hε : ε ∈ ((S.totalTransformSeq E i).component j).support.genericPoints) :
    (S.weakTransformSeq J i).ord ε = 0 :=
  ord_weakTransformSeq_eq_zero_of_mem_genericPoints_aux S f n hS hJE i j hε

/-- The recursion behind `weakTransformSeq_eq_nonmonomialPart_markedTransformSeq`, by induction
on the length, the marked triple advancing through `blowUpTriple`: one step is
`nonmonomialPart_markedTransform_eq_weakTransform` together with the vanishing of the monomial
part at the generic points of the induced family (through `ord_nonmonomialPart_eq_zero`), the
structure map of the blown-up triple being `blowUpπ ≫ (T.X.left ↘ Spec k)`. -/
theorem weakTransformSeq_eq_nonmonomialPart_markedTransformSeq_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (S : BlowUpSequence T.X.left), S.length = l →
      ∀ {d : ℕ}, S.IsOrderSeq (T.X.left ↘ Spec (.of k)) (nonmonomialPart T.I T.E) T.E d →
        S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E →
        ∀ i : Fin (S.length + 1), S.weakTransformSeq (nonmonomialPart T.I T.E) i =
          nonmonomialPart (S.markedTransformSeq T.I T.m i) (S.totalTransformSeq T.E i) := by
  induction l with
  | zero =>
    intro T S hl d hS hge i
    cases S with
    | nil => rfl
    | cons _ D rest => exact absurd hl (Nat.succ_ne_zero _)
  | succ l ih =>
    intro T S hl d hS hge i
    cases S with
    | nil => exact absurd hl (Nat.zero_ne_add_one _)
    | cons _ Z rest =>
      obtain ⟨⟨hD, hsnc, hord⟩, ht⟩ :=
        (isOrderSeq_cons_iff _ (nonmonomialPart T.I T.E) T.E d Z rest).1 hS
      obtain ⟨⟨hD', hsnc', hle⟩, hge'⟩ := (isOrderGeSeq_cons_iff _ T.I T.E T.m Z rest).1 hge
      have hZ : T.IsOrderGeBlowUp Z := ⟨hD', hsnc', hle⟩
      have hNT : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
      have hNS : NoetherianSpace T.X.left := Hironaka.BD.noetherianSpace_triple T.toTriple
      have hsmT : Smooth (T.X.left ↘ Spec (.of k)) := T.smooth
      have hNS₁ : NoetherianSpace Z.blowUp :=
        Hironaka.BD.noetherianSpace_triple (blowUpTriple T Z hZ).toTriple
      obtain ⟨n₀, hn₀⟩ := T.smoothOfRelativeDimension
      have hstep : (nonmonomialPart T.I T.E).weakTransform Z =
          nonmonomialPart (T.I.markedTransform Z T.m) (T.E.totalTransform Z) := by
        rw [nonmonomialPart_markedTransform_eq_weakTransform T Z hZ]
        symm
        apply nonmonomialPart_eq_self_of_forall_ord_eq_zero
        intro j ξ hξ
        rcases j with j₀ | j₀
        · exact ord_weakTransform_eq_zero_of_mem_genericPoints_strictTransform Z
            (T.E.component j₀) (fun ζ hζ => Hironaka.BMO.Snc.ord_nonmonomialPart_eq_zero
              (T.X.left ↘ Spec (.of k)) T.E T.isSnc T.isNonzeroEverywhere hζ) hξ
        · exact ord_weakTransform_eq_zero_of_mem_genericPoints_exceptionalDivisor
            (T.X.left ↘ Spec (.of k)) n₀ Z hD hord hξ
      obtain ⟨i, hi⟩ := i
      cases i with
      | zero => rfl
      | succ i =>
        change rest.weakTransformSeq ((nonmonomialPart T.I T.E).weakTransform Z) ⟨i, _⟩ =
          nonmonomialPart (rest.markedTransformSeq (T.I.markedTransform Z T.m) T.m ⟨i, _⟩)
            (rest.totalTransformSeq (T.E.totalTransform Z) ⟨i, _⟩)
        rw [hstep]
        have e : ((blowUpTriple T Z hZ).X.left ↘ Spec (.of k)) =
            Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)) := by
          change (𝟙 _ ≫ Z.blowUpπ) ≫ _ = _
          rw [Category.id_comp]
        have hS' : rest.IsOrderSeq ((blowUpTriple T Z hZ).X.left ↘ Spec (.of k))
            (nonmonomialPart (blowUpTriple T Z hZ).I (blowUpTriple T Z hZ).E)
            (blowUpTriple T Z hZ).E d := by
          change rest.IsOrderSeq _ (nonmonomialPart (T.I.markedTransform Z T.m)
            (T.E.totalTransform Z)) (T.E.totalTransform Z) d
          rw [e, ← hstep]
          exact ht
        have hge'' : rest.IsOrderGeSeq ((blowUpTriple T Z hZ).X.left ↘ Spec (.of k))
            (blowUpTriple T Z hZ).I (blowUpTriple T Z hZ).m (blowUpTriple T Z hZ).E := by
          rw [e]
          exact hge'
        exact ih (blowUpTriple T Z hZ) rest (Nat.succ_injective hl) hS' hge''
          ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- **Along a round of order `d` for `N(I)` the birational transform of `N(I)` is the nonmonomial
part of the marked transform of `I`** at every stage ([Kol07, 111, Step 1]:
`N((Π₁)⁻¹_*(I, m)) = (Π₁)⁻¹_* N(I)`), in the triple form. -/
theorem weakTransformSeq_eq_nonmonomialPart_markedTransformSeq (T : MarkedTriple k) (hm : T.m = 1)
    {S : BlowUpSequence T.X.left} {d : ℕ}
    (hS : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) (nonmonomialPart T.I T.E) T.E d)
    (hI : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I 1 T.E) (i : Fin (S.length + 1)) :
    S.weakTransformSeq (nonmonomialPart T.I T.E) i =
      nonmonomialPart (S.markedTransformSeq T.I 1 i) (S.totalTransformSeq T.E i) := by
  have h := weakTransformSeq_eq_nonmonomialPart_markedTransformSeq_aux S.length T S rfl hS
    (by rw [hm]; exact hI) i
  rwa [hm] at h

end Hironaka.Resolution
