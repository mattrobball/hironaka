/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Snc.Dictionary
import Hironaka.Resolution.Algebraic.Kol07.RefineIrreducible
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
import Hironaka.Resolution.Algebraic.Stage.Theorem68
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# One round of Main Theorem II on a triple

Hironaka's Main Theorem II [Hir64, Main Theorem II, pp. 142–143] on Kollár's triple `(X, I, E)`
[Kol07, Notation 64] is Theorem 68 [Kol07, Theorem 68] with `m := d = max-ord I`, refined to
irreducible centers (`Hironaka/Resolution/Algebraic/Kol07/RefineIrreducible.lean`) and read through
the dictionary between the two vocabularies (`Hironaka/Sequence/Dictionary*.lean`). The round
`exists_orderReductionRound` is the refined value of the order reduction functor `BO_d`: a smooth
blow-up sequence of order `d` for the triple, with regular irreducible centers, whose last weak
transform has `max-ord < d` (Theorem 68 (1)). `IsOrderSeq.hironakaClauses` reads Hironaka's clauses
(ii), (iii) and the first part of (iv) off any such sequence, with Hironaka's `E₀` the reduced
union `T.E.unionIdeal` of Kollár's family (whose members may be reducible or empty), and
`IsOrderSeq.clause2` reads clause (2) of [Hir64, Main Theorem II(N)] off a round with irreducible
centers. The only transport along the refinement's isomorphism is `max-ord`
(`maxOrd_comap_of_isIso`). Main Theorem II(N) is proved by concatenating such rounds.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme IdealSheafData BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

-- `maxOrd_comap_of_isIso` is in `Hironaka/Scheme/IdealSheaf/Order/Invariance.lean`.

variable {X Y : Scheme.{u}}

variable {k : Type u} [Field k] [CharZero k]

/-- One round of Main Theorem II on a triple `T` with `max-ord T.I = d ≥ 1`: a smooth blow-up
sequence of order `d` for `(T.X.left, T.I, T.E)` [Kol07, Definition 66] with regular irreducible
centers, whose last weak transform has `max-ord < d`. It is the value of the order reduction
functor `BO_d` [Kol07, Theorem 68, with `m := d`] refined to irreducible centers; the
refinement's isomorphism `e : S'.last ≅ S.last` carries the last weak transform by inverse image,
so its `max-ord` is that of the value of `BO_d` (`maxOrd_comap_of_isIso`). -/
theorem exists_orderReductionRound (T : Triple k) (d : ℕ) (hd : T.I.maxOrd = (d : ℕ∞))
    (hd0 : 0 < d) :
    ∃ S : BlowUpSequence T.X.left, S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E d ∧
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (S.weakTransformSeq T.I (Fin.last S.length)).maxOrd < (d : ℕ∞) := by
  have : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hT : T.BOClassFree d := ⟨hd0, hd.le⟩
  have h₀ := (Hironaka.Stage.BO_m d k).isOrderSeq T hT
  have hlt : (((Hironaka.Stage.BO_m d k).seq T hT).weakTransformSeq T.I
      (Fin.last _)).maxOrd < (d : ℕ∞) :=
    Hironaka.Stage.dimFreeBO_maxOrd_lt Hironaka.Stage.stage0 d T hT
  obtain ⟨S', h', hirr, -, e, -, hwt, -⟩ :=
    IsOrderSeq.exists_refineIrreducible (T.X.left ↘ Spec (.of k)) n h₀
  refine ⟨S', h', hirr, ?_⟩
  have h2 : (S'.weakTransformSeq T.I (Fin.last _)).maxOrd =
      (((Hironaka.Stage.BO_m d k).seq T hT).weakTransformSeq T.I (Fin.last _)).maxOrd := by
    rw [hwt]
    exact maxOrd_comap_of_isIso _ e.hom
  rw [h2]
  exact hlt

/-- Hironaka's clauses (ii), (iii) and the first part of (iv) of [Hir64, Main Theorem II], read off
a smooth blow-up sequence of order `d` for `(T.X.left, T.I, T.E)` [Kol07, Definition 66] at every
index, with Hironaka's `E₀ := T.E.unionIdeal` (the reduced union of Kollár's family): (ii)
`ν(J_i) ≥ d` on every center; (iii) the boundary `E_i`, the reduced union of Kollár's total
transform `E_i`, has only normal crossings with the center (condition (3) of Definition 66 at the
stage's structure morphism); (iv) the last boundary has only normal crossings (the total transforms
are simple normal crossing families). -/
theorem IsOrderSeq.hironakaClauses (T : Triple k) {d : ℕ} {S : BlowUpSequence T.X.left}
    (h : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E d) :
    (∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
        (d : ℕ∞) ≤ (S.weakTransformSeq T.I i.castSucc).ord x) ∧
      (∀ i : Fin S.length,
        IsSncBoundaryWith (S.boundarySeq T.E.unionIdeal i.castSucc) (S.center i)) ∧
      IsSncBoundary (S.boundarySeq T.E.unionIdeal (Fin.last S.length)) := by
  have : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  refine ⟨fun i x hx => IsOrderSeq.le_ord_of_mem_center (T.X.left ↘ Spec (.of k)) n h i hx,
    fun i => ?_, ?_⟩
  · rw [boundarySeq_eq_unionIdeal_totalTransformSeq]
    have : Smooth (S.stageMap i.castSucc ≫ (T.X.left ↘ Spec (.of k))) :=
      IsSmooth.smooth_stageMap (n := n) h.1 i.castSucc
    exact HasSncWith.isSncBoundaryWith_unionIdeal
      (S.stageMap i.castSucc ≫ (T.X.left ↘ Spec (.of k))) (h.2 i).1
  · rw [boundarySeq_eq_unionIdeal_totalTransformSeq]
    have : Smooth (S.stageMap (Fin.last _) ≫ (T.X.left ↘ Spec (.of k))) :=
      IsSmooth.smooth_stageMap (n := n) h.1 (Fin.last _)
    exact IsSnc.isSncBoundary_unionIdeal
      (S.stageMap (Fin.last _) ≫ (T.X.left ↘ Spec (.of k)))
      (IsOrderSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) n h T.isSnc (Fin.last _))

/-- Clause (2) of [Hir64, Main Theorem II(N)] inside one round (Hironaka's remark after Main
Theorem II: `d` is the maximum of `ν(J_i)` at every stage): along a smooth blow-up sequence of
order `d = max-ord J` with irreducible, hence nonempty, centers, at every stage `i` the maximal
order of `J_i` is the positive integer `d`, attained at every point of the center. -/
theorem IsOrderSeq.clause2 (T : Triple k) {d : ℕ} {S : BlowUpSequence T.X.left}
    (h : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E d)
    (hd : T.I.maxOrd = (d : ℕ∞)) (hd0 : 0 < d)
    (hirr : ∀ i : Fin S.length, IrreducibleSpace (S.center i).subscheme) (i : Fin S.length) :
    ∃ d' : ℕ, 0 < d' ∧
      IsGreatest (Set.range ((S.weakTransformSeq T.I i.castSucc).ord)) (d' : ℕ∞) ∧
      ∀ z ∈ (S.center i).support, (S.weakTransformSeq T.I i.castSucc).ord z =
          d' := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have := hirr i
  obtain ⟨p⟩ := (inferInstance : Nonempty (S.center i).subscheme)
  have hp : (S.center i).subschemeι p ∈ (S.center i).support := by
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self p
  refine ⟨d, hd0, (isGreatest_range_ord_iff _ d).mpr
    ⟨IsOrderSeq.maxOrd_weakTransformSeq_eq (T.X.left ↘ Spec (.of k)) n h hd i ⟨_, hp⟩, _,
      IsOrderSeq.ord_eq_of_mem_center (T.X.left ↘ Spec (.of k)) n h hd i hp⟩,
    fun z hz => IsOrderSeq.ord_eq_of_mem_center (T.X.left ↘ Spec (.of k)) n h hd i hz⟩

end Hironaka.Sequence
