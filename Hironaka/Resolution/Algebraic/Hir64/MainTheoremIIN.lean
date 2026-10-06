/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Snc.Dictionary
import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyZero
import Hironaka.Resolution.Algebraic.Hir64.OrderReductionRound
import Hironaka.Resolution.Algebraic.OrderReduction.Tuned
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUpSequence.ConcatClauses
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Hironaka's Main Theorem II and Main Theorem II(N) on a triple

Hironaka's Main Theorem II [Hir64, Main Theorem II] and Main Theorem II(N)
[Hir64, Main Theorem II(N)] on a triple `(X, I, E)` in the sense of [Kol07, Notation 64], with
Hironaka's boundary `E₀` the reduced union `T.E.unionIdeal` of the family: the two theorems here
are the triple-level forms. The module
`Hironaka.Resolution.Algebraic.Hir64.ComponentwiseMainTheorems` proves the two main theorems
`exists_blowUpSequence_ord_weakTransformSeq_lt` and `exists_blowUpSequence_weakTransformSeq_eq_top`,
stated in Hironaka's own vocabulary for every smooth scheme, not from these but from the round
`exists_orderReductionRound` and `isHironakaIIN_concat`, run component by component.

* `exists_orderReduction_irreducible` (Main Theorem II): one round of order reduction
  (`exists_orderReductionRound`, Kollár's `BO_d` of [Kol07, Theorem 68] with the centers refined to
  irreducible ones) and its clauses (`IsOrderSeq.hironakaClauses`; the second part of clause (iv),
  `ν(J_r) < d` at every point, is the conclusion `max-ord I_r < d` of Theorem 68 read pointwise).
* `exists_principalization_irreducible` (Main Theorem II(N)): Theorem 68 iterated. By induction on
  a bound for `max-ord T.I` (a natural number, since `T.I` is nonzero everywhere on the Noetherian
  `T.X.left`): `max-ord = 0` means `T.I = 𝒪`, where the empty sequence does (clause (4)); otherwise
  one round is followed by the induction hypothesis at the induced triple of the round's last stage
  (`Triple.induced`, the transform of [Kol07, Definition 66 (1)]), whose ideal has smaller
  `max-ord` and whose family's reduced union is the round's last boundary, so the tail continues
  Hironaka's `E_i`; the rounds are concatenated (`isHironakaIIN_concat`). Clause (2) inside a
  round, the order of the weak transform along the center being the maximal order, is
  `IsOrderSeq.clause2`; this is why Main Theorem II(N) is Theorem 68 iterated and not Kollár's
  principalization theorem, whose `BMO_1` centers have only marked order `≥ 1`. Hironaka's own
  derivation, through his fundamental theorems on resolution data in the paragraph following the
  statement of Main Theorem II(N), is not followed.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Hironaka IdealSheafData BlowUpSequence

namespace Hironaka.Sequence

/-- Clauses (1)–(3) of [Hir64, Main Theorem II(N)] at one stage: the center `D` is regular and
irreducible, the maximal order of the ideal `J` is a positive integer attained on all of `D`, and
the boundary `E` has only normal crossings with `D`. -/
def IINStage {Y : Scheme.{u}} (D J E : Y.IdealSheafData) : Prop :=
  (IsRegular D.subscheme ∧ IrreducibleSpace D.subscheme) ∧
    (∃ d : ℕ, 0 < d ∧ IsGreatest (Set.range J.ord) (d : ℕ∞) ∧
      ∀ z ∈ D.support, J.ord z = d) ∧
    IsSncBoundaryWith E D

/-- The conclusion of [Hir64, Main Theorem II(N)] for a sequence `S` started at `(J, E₀)`: clauses
(1)–(3) at every stage, clause (4) (the final boundary has only normal crossings and the final
weak transform is the unit ideal) at the end. -/
def _root_.AlgebraicGeometry.Scheme.BlowUpSequence.IsHironakaIIN {X : Scheme.{u}}
    (S : BlowUpSequence X)
    (J E₀ : X.IdealSheafData) : Prop :=
  (∀ i : Fin S.length,
      IINStage (S.center i) (S.weakTransformSeq J i.castSucc) (S.boundarySeq E₀ i.castSucc)) ∧
    IsSncBoundary (S.boundarySeq E₀ (Fin.last S.length)) ∧
    S.weakTransformSeq J (Fin.last S.length) = ⊤

/-- The rounds concatenate: clauses (1)–(3) at every stage of `S` and the conclusion of Main
Theorem II(N) for `T` started at the last transforms of `S` give the conclusion for
`S.concat T`. -/
theorem isHironakaIIN_concat {X : Scheme.{u}}
    (S : BlowUpSequence X) (T : BlowUpSequence S.last) (J E₀ : X.IdealSheafData)
    (hS : ∀ i : Fin S.length,
      IINStage (S.center i) (S.weakTransformSeq J i.castSucc) (S.boundarySeq E₀ i.castSucc))
    (hT : T.IsHironakaIIN (S.weakTransformSeq J (Fin.last _)) (S.boundarySeq E₀ (Fin.last _))) :
    (S.concat T).IsHironakaIIN J E₀ :=
  ⟨forall_stage_concat @IINStage S T J E₀ hS hT.1,
    isSncBoundary_boundarySeq_concat_last S T E₀ hT.2.1,
    weakTransformSeq_concat_last_eq_top S T J hT.2.2⟩

variable {k : Type u} [Field k]

/-- Main Theorem II(N) with `J = 𝒪`: the empty sequence does, clause (4) holding at the start. -/
theorem isHironakaIIN_nil_of_eq_top (T : Triple k) (hJ : T.I = ⊤) :
    (nil T.X.left).IsHironakaIIN T.I T.E.unionIdeal :=
  ⟨fun i => i.elim0, IsSnc.isSncBoundary_unionIdeal (T.X.left ↘ Spec (.of k)) T.isSnc, hJ⟩

variable [CharZero k]

/-- [Kol07, Theorem 68] iterated: Main Theorem II(N) on every triple whose ideal has
`max-ord ≤ d`, by induction on `d`. If `max-ord T.I = 0` then `T.I = 𝒪` and the empty sequence
does; otherwise one round of order `d₀ = max-ord T.I` (`exists_orderReductionRound`) is followed
by the induction hypothesis at the induced triple of its last stage (`Triple.induced`), whose
ideal has `max-ord < d₀ ≤ d + 1`, and the two are concatenated. -/
theorem exists_isHironakaIIN_of_maxOrd_le (d : ℕ) :
    ∀ T : Triple k, T.I.maxOrd ≤ (d : ℕ∞) →
      ∃ S : BlowUpSequence T.X.left, S.IsHironakaIIN T.I T.E.unionIdeal := by
  induction d with
  | zero =>
    intro T hd
    exact ⟨nil T.X.left, isHironakaIIN_nil_of_eq_top T (Hironaka.BD.eq_top_of_maxOrd_le_zero T.I
      hd)⟩
  | succ d ih =>
    intro T hd
    have : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    obtain ⟨d₀, hd₀⟩ := ENat.ne_top_iff_exists.mp
      (T.I.maxOrd_ne_top (T.X.left ↘ Spec (.of k)) n T.isNonzeroEverywhere)
    rcases Nat.eq_zero_or_pos d₀ with h0 | hpos
    · subst h0
      exact ⟨nil T.X.left, isHironakaIIN_nil_of_eq_top T
        (Hironaka.BD.eq_top_of_maxOrd_le_zero T.I hd₀.symm.le)⟩
    · obtain ⟨S', h', hirr, hlt⟩ := exists_orderReductionRound T d₀ hd₀.symm hpos
      have hd₀d : (d₀ : ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) := hd₀ ▸ hd
      let T' : Triple k := T.induced S' h' (Fin.last _)
      have hT' : T'.I.maxOrd ≤ (d : ℕ∞) := by
        change (S'.weakTransformSeq T.I (Fin.last _)).maxOrd ≤ (d : ℕ∞)
        have h1 : (S'.weakTransformSeq T.I (Fin.last _)).maxOrd < ((d + 1 : ℕ) : ℕ∞) :=
          lt_of_lt_of_le hlt hd₀d
        rw [Nat.cast_succ] at h1
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).mp h1
      obtain ⟨S₂, h₂⟩ := ih T' hT'
      have hE : T'.E.unionIdeal = S'.boundarySeq T.E.unionIdeal (Fin.last _) :=
        (boundarySeq_eq_unionIdeal_totalTransformSeq S' T.E (Fin.last _)).symm
      rw [hE] at h₂
      refine ⟨S'.concat S₂, isHironakaIIN_concat S' S₂ T.I T.E.unionIdeal (fun i => ?_) h₂⟩
      exact ⟨hirr i, IsOrderSeq.clause2 T h' hd₀.symm hpos (fun j => (hirr j).2) i,
        (IsOrderSeq.hironakaClauses T h').2.1 i⟩

/-- The conclusion of Main Theorem II(N) on every triple: `max-ord T.I` is a natural number,
since `T.I` is nonzero everywhere on the Noetherian `T.X.left`. -/
theorem exists_isHironakaIIN (T : Triple k) :
    ∃ S : BlowUpSequence T.X.left, S.IsHironakaIIN T.I T.E.unionIdeal := by
  have : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (T.I.maxOrd_ne_top (T.X.left ↘ Spec (.of k)) n T.isNonzeroEverywhere)
  exact exists_isHironakaIIN_of_maxOrd_le d T hd.symm.le

/-- **Hironaka's Main Theorem II** [Hir64, Main Theorem II] on a triple: a finite succession of
monoidal transformations with non-singular irreducible centers such that (i)–(iii) hold at every
stage (the center is regular and irreducible, the weak transform has order `≥ d` along it, the
boundary has only normal crossings with it) and (iv) at the end (the boundary has only normal
crossings and the weak transform has order `< d` everywhere). One round of order reduction, with
the second part of (iv) the conclusion `max-ord I_r < d` of [Kol07, Theorem 68] read pointwise. -/
theorem exists_orderReduction_irreducible (T : Triple k) (d : ℕ) (hd : T.I.maxOrd = (d : ℕ∞))
    (hd0 : 0 < d) :
    ∃ S : BlowUpSequence T.X.left,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
        (d : ℕ∞) ≤ (S.weakTransformSeq T.I i.castSucc).ord x) ∧
      (∀ i : Fin S.length,
        IsSncBoundaryWith (S.boundarySeq T.E.unionIdeal i.castSucc) (S.center i)) ∧
      IsSncBoundary (S.boundarySeq T.E.unionIdeal (Fin.last S.length)) ∧
      ∀ y : S.last, (S.weakTransformSeq T.I (Fin.last S.length)).ord y <
          (d : ℕ∞) := by
  obtain ⟨S, h, hirr, hlt⟩ := exists_orderReductionRound T d hd hd0
  obtain ⟨h2, h3, h4⟩ := IsOrderSeq.hironakaClauses T h
  exact ⟨S, hirr, h2, h3, h4, fun y => (Hironaka.BO.maxOrd_lt_iff_forall_ord_lt _ hd0).mp hlt y⟩

/-- **Hironaka's Main Theorem II(N)** [Hir64, Main Theorem II(N)] on a triple: a finite succession
of monoidal transformations with non-singular irreducible centers along which the weak transform
has constant order equal to its maximal order, a positive integer, with the boundary having only
normal crossings with each center, whose final boundary has only normal crossings and whose final
weak transform is the unit ideal; `IsHironakaIIN` unfolded. -/
theorem exists_principalization_irreducible (T : Triple k) :
    ∃ S : BlowUpSequence T.X.left,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ i : Fin S.length, ∃ d : ℕ, 0 < d ∧
        IsGreatest (Set.range ((S.weakTransformSeq T.I i.castSucc).ord)) (d : ℕ∞)
            ∧
        ∀ z ∈ (S.center i).support, (S.weakTransformSeq T.I i.castSucc).ord z =
            d) ∧
      (∀ i : Fin S.length,
        IsSncBoundaryWith (S.boundarySeq T.E.unionIdeal i.castSucc) (S.center i)) ∧
      IsSncBoundary (S.boundarySeq T.E.unionIdeal (Fin.last S.length)) ∧
      S.weakTransformSeq T.I (Fin.last S.length) = ⊤ := by
  obtain ⟨S, h1, h2, h3⟩ := exists_isHironakaIIN T
  exact ⟨S, fun i => (h1 i).1, fun i => (h1 i).2.1, fun i => (h1 i).2.2, h2, h3⟩

end Hironaka.Sequence
