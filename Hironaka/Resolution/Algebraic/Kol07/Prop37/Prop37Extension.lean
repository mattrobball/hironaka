/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Setting
public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
public import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.Functor
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Proposition 37: the extension of a blow-up sequence functor from affine schemes

Kollár's Proposition 37 [Kol07, Proposition 37]: a blow-up sequence functor `B` defined on affine
schemes over `k` and commuting with smooth surjections has a unique extension `B̄` to all schemes
of finite type over `k` (here, to all triples), commuting with smooth surjections. This module
defines the extension `OrderSeqAssignment.extendFromAffine`, proves its specification, and proves
Proposition 37 as stated (existence, `OrderSeqAssignment.exists_extension`; uniqueness,
`OrderSeqAssignment.extension_unique`), with the versions for marked triples. The proof of
[Kol07, Theorem 36] uses it to pass from the resolution of affine schemes to that of all schemes.

* **The extension** (`extendSeq`, `extendFromAffine`): on a triple `T`, `B̄(T)` is the sequence on
  `X` descended from `B(X', g^* I, g^{-1} E)` along the affine cover `g : X' = ∐ Uᵢ → X` of
  `Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Setting.lean`:
  `Triple.exists_isOrderSeq_pullback_coverDesc_eq`
  (`Hironaka/Resolution/Algebraic/Kol07/Prop37/Prop37Local.lean`) applied to the descent datum `τ₁^*
  B(X') = τ₂^* B(X')` (`OrderSeqFunctor.pullback_coverFst_eq_pullback_coverSnd`), the witness
  chosen; it is a smooth blow-up sequence of order `m` for `(X, I, E)` by the descent, and has no
  empty centers because its pullback `B(X')` has none (`NoEmptyCenters.of_pullback`). Its defining
  property is `g^* B̄(X) = B(X')` (`extendFromAffine_pullback_coverDesc`).
* **Restriction to the affine triples** (`extendFromAffine_restrict`): for `X` affine, `g` itself
  is a smooth surjection between affine triples, so `B(X') = g^* B(X)` by the hypothesis on `B`,
  and `g^*` is injective (`pullback_coverDesc_injective`): `B̄(X) = B(X)`.
* **Commutation with smooth surjections** (`extendFromAffine_commutesWithSmoothSurjections`): for
  a smooth surjection `h : Y → X` between triples with `Y` carrying the pullback data, compare on
  the **fibre product of the two affine covers**, `P := X' ×_X Y'` (`comparisonScheme`), affine
  since `g : X' → X` is an affine morphism and `Y'` is affine, whose projections `q : P → X'`,
  `p : P → Y'` are smooth surjections between affine triples carrying the pullback data of both
  cover triples (`comparisonTriple`, `comparisonTriple_isPullbackOf_fst/_snd`): the hypothesis on
  `B` gives `p^* B(Y') = B(P) = q^* B(X')`, and
  `q^* B(X') = q^* g^* B̄(X) = p^* (g_Y ≫ h)^* B̄(X)`, so `B(Y') = (g_Y ≫ h)^* B̄(X)` by injectivity
  along the surjective `p`, and then `B̄(Y) = h^* B̄(X)` by injectivity along `g_Y`. This replaces
  Kollár's refinement of the cover of `Y` by the fibre product, which needs no refinement.
* **Uniqueness** (`extension_unique`): two extensions commuting with smooth surjections agree
  after pullback along `g` (both equal `B(X')`), hence agree.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.BlowUpSequence

namespace Hironaka

variable {k : Type u} [Field k]

/-! ### The fibre product of the two affine covers over a smooth surjection -/

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

open Scheme

section Comparison

variable {T T' : Triple k} (h : T'.X.left ⟶ T.X.left)

/-- `g : X' → X` is an affine morphism: `X'` and `Spec k` are affine and `X → Spec k` is separated
(the argument for the affineness of the kernel pair). -/
theorem isAffineHom_coverDesc (T : Triple k) : IsAffineHom T.coverDesc :=
  have : IsAffineHom (T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := inferInstance
  IsAffineHom.of_comp (f := T.coverDesc) (g := T.X.left ↘ Spec (CommRingCat.of k))

/-- The composite `Y' → Y → X` of the affine cover of `Y` with a surjection is surjective. -/
theorem surjective_coverDesc_comp (hs : Function.Surjective h) :
    Function.Surjective (T'.coverDesc ≫ h) := fun x => by
  obtain ⟨y, hy⟩ := hs x
  obtain ⟨z, hz⟩ := surjective_coverDesc T' y
  exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩

/-- The fibre product `P := X' ×_X Y'` of the affine covers of `X` and `Y` over `h : Y → X`. -/
noncomputable abbrev comparisonScheme : Scheme.{u} :=
  Limits.pullback T.coverDesc (T'.coverDesc ≫ h)

/-- The projection `q : P → X'`. -/
noncomputable def comparisonFst : comparisonScheme h ⟶ T.coverScheme :=
  pullback.fst T.coverDesc (T'.coverDesc ≫ h)

/-- The projection `p : P → Y'`. -/
noncomputable def comparisonSnd : comparisonScheme h ⟶ T'.coverScheme :=
  pullback.snd T.coverDesc (T'.coverDesc ≫ h)

theorem comparisonFst_comp_coverDesc :
    comparisonFst h ≫ T.coverDesc = comparisonSnd h ≫ T'.coverDesc ≫ h :=
  pullback.condition

/-- The cartesian square of the comparison scheme. -/
theorem isPullback_comparison :
    IsPullback (comparisonFst h) (comparisonSnd h) T.coverDesc (T'.coverDesc ≫ h) :=
  IsPullback.of_hasPullback _ _

/-- `P` is affine: `g` is an affine morphism and `Y'` is affine. -/
theorem isAffine_comparisonScheme : IsAffine (comparisonScheme h) :=
  have := isAffineHom_coverDesc T
  inferInstance

/-- `p : P → Y'` is smooth (base change of `g`). -/
theorem smooth_comparisonSnd : Smooth (comparisonSnd h) :=
  property_of_isPullback _ (isPullback_comparison h).flip (smooth_coverDesc T)

/-- `q : P → X'` is smooth (base change of the smooth `g_Y ≫ h`). -/
theorem smooth_comparisonFst [Smooth h] : Smooth (comparisonFst h) :=
  have : Smooth (T'.coverDesc ≫ h) := by
    have := smooth_coverDesc T'
    infer_instance
  property_of_isPullback _ (isPullback_comparison h) this

/-- `p : P → Y'` is smooth of relative dimension `0` (base change of `g`). -/
theorem smoothOfRelativeDimension_zero_comparisonSnd :
    SmoothOfRelativeDimension 0 (comparisonSnd h) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange 0
  exact property_of_isPullback _ (isPullback_comparison h).flip
    (smoothOfRelativeDimension_zero_coverDesc T)

/-- `p : P → Y'` is surjective (base change of the surjective `g`). -/
theorem surjective_comparisonSnd : Function.Surjective (comparisonSnd h) := by
  have hr : Set.range (comparisonSnd h) = (T'.coverDesc ≫ h) ⁻¹' Set.range T.coverDesc :=
    range_fst_of_isPullback (isPullback_comparison h).flip
  rw [← Set.range_eq_univ, hr, Set.range_eq_univ.mpr (surjective_coverDesc T), Set.preimage_univ]

/-- `q : P → X'` is surjective (base change of the surjective `g_Y ≫ h`). -/
theorem surjective_comparisonFst (hs : Function.Surjective h) :
    Function.Surjective (comparisonFst h) := by
  have hr : Set.range (comparisonFst h) = T.coverDesc ⁻¹' Set.range (T'.coverDesc ≫ h) :=
    range_fst_of_isPullback (isPullback_comparison h)
  rw [← Set.range_eq_univ, hr, Set.range_eq_univ.mpr (surjective_coverDesc_comp h hs),
    Set.preimage_univ]

/-- `P` is a scheme over `k` through `p : P → Y'`. -/
noncomputable instance instOverComparisonScheme :
    (comparisonScheme h).Over (Spec (CommRingCat.of k)) :=
  ⟨comparisonSnd h ≫ (T'.coverScheme ↘ Spec (CommRingCat.of k))⟩

instance : LocallyOfFiniteType (comparisonScheme h ↘ Spec (CommRingCat.of k)) := by
  have : LocallyOfFiniteType (comparisonSnd h) :=
    property_of_isPullback _ (isPullback_comparison h).flip
      (inferInstanceAs (LocallyOfFiniteType T.coverDesc))
  exact inferInstanceAs
    (LocallyOfFiniteType (comparisonSnd h ≫ (T'.coverScheme ↘ Spec (CommRingCat.of k))))

instance : IsAffine (comparisonScheme h) := isAffine_comparisonScheme h

instance : IsSeparated (comparisonScheme h ↘ Spec (CommRingCat.of k)) :=
  IsSeparated.of_isAffineHom _

/-- `P` is smooth over `k` of the relative dimension of `Y`. -/
theorem exists_smoothOfRelativeDimension_comparisonScheme :
    ∃ n : ℕ, SmoothOfRelativeDimension n (comparisonScheme h ↘ Spec (CommRingCat.of k)) := by
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_coverScheme T'
  refine ⟨n, ?_⟩
  have := smoothOfRelativeDimension_zero_comparisonSnd h
  change SmoothOfRelativeDimension n
    (comparisonSnd h ≫ (T'.coverScheme ↘ Spec (CommRingCat.of k)))
  simpa using
    smoothOfRelativeDimension_comp 0 n (comparisonSnd h) (T'.coverScheme ↘ Spec (CommRingCat.of k))

/-- The triple of `P = X' ×_X Y'`: the pullback of the triple of `Y'` along `p`. -/
noncomputable def comparisonTriple [PerfectField k] : Triple k :=
  haveI : @HomIsOver Scheme.{u} _ (comparisonScheme h) T'.coverTriple.X.left (comparisonSnd h)
      (Spec (CommRingCat.of k)) (instOverComparisonScheme h) (AlgScheme.over T'.coverTriple.X) :=
        ⟨rfl⟩
  haveI : @Smooth (comparisonScheme h) T'.coverTriple.X.left (comparisonSnd h) :=
    smooth_comparisonSnd h
  Triple.pullback T'.coverTriple (exists_smoothOfRelativeDimension_comparisonScheme h)
    (comparisonSnd h)

theorem comparisonTriple_X [PerfectField k] : (comparisonTriple h).X.left = comparisonScheme h :=
  rfl

/-- The triple of `P` is affine. -/
theorem isAffine_comparisonTriple [PerfectField k] : (comparisonTriple h).IsAffineScheme :=
  isAffine_comparisonScheme h

/-- The triple of `P` carries the pullback data of the triple of `Y'` along `p`. -/
theorem comparisonTriple_isPullbackOf_snd [PerfectField k] :
    (comparisonTriple h).IsPullbackOf T'.coverTriple (comparisonSnd h) :=
  haveI : @HomIsOver Scheme.{u} _ (comparisonScheme h) T'.coverTriple.X.left (comparisonSnd h)
      (Spec (CommRingCat.of k)) (instOverComparisonScheme h) (AlgScheme.over T'.coverTriple.X) :=
        ⟨rfl⟩
  haveI : @Smooth (comparisonScheme h) T'.coverTriple.X.left (comparisonSnd h) :=
    smooth_comparisonSnd h
  isPullbackOf_pullback T'.coverTriple _ _

/-- The triple of `P` carries the pullback data of the triple of `X'` along `q` as well, when `Y`
carries the pullback data of `X` along `h`: `(g_Y ≫ h ≫ p)^* I = (g ≫ q)^* I`. -/
theorem comparisonTriple_isPullbackOf_fst [PerfectField k] (hp : T'.IsPullbackOf T h) :
    (comparisonTriple h).IsPullbackOf T.coverTriple (comparisonFst h) := by
  refine ⟨?_, ?_, ?_⟩
  · change comparisonFst h ≫ T.coverDesc ≫ (T.X.left ↘ Spec (CommRingCat.of k)) =
      comparisonSnd h ≫ T'.coverDesc ≫ (T'.X.left ↘ Spec (CommRingCat.of k))
    rw [← Category.assoc, comparisonFst_comp_coverDesc, Category.assoc, Category.assoc, hp.1]
  · change (T'.I.comap T'.coverDesc).comap (comparisonSnd h) =
      (T.I.comap T.coverDesc).comap (comparisonFst h)
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      comparisonFst_comp_coverDesc, hp.2.1, ← Scheme.IdealSheafData.comap_comp, Category.assoc]
  · change (T'.E.comap T'.coverDesc).comap (comparisonSnd h) =
      (T.E.comap T.coverDesc).comap (comparisonFst h)
    rw [← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, comparisonFst_comp_coverDesc,
      hp.2.2, ← DivisorFamily.comap_comp, Category.assoc]

end Comparison

end AlgebraicGeometry.Triple

namespace Hironaka

variable {k : Type u} [Field k]

/-! ### The extension: the sequence descended from `B(X')` along `g` -/

namespace OrderSeqAssignment

open Scheme

variable {m : ℕ} [CharZero k] (B : OrderSeqAssignment k m Triple.IsAffineScheme)

/-- The value of the extension of [Kol07, Proposition 37] on a triple `T`: the blow-up sequence on
`X` descended along `g : X' → X` from `B(X', g^* I, g^{-1} E)`
(`exists_isOrderSeq_pullback_coverDesc_eq` at the descent datum
`pullback_coverFst_eq_pullback_coverSnd`), the witness chosen. -/
noncomputable def extendSeq (hB : B.CommutesWithSmoothSurjections) (T : Triple k) :
    BlowUpSequence T.X.left :=
  Classical.choose (Triple.exists_isOrderSeq_pullback_coverDesc_eq T
    (B.seq T.coverTriple (Triple.isAffine_coverTriple T)) (B.isOrderSeq T.coverTriple _)
    (pullback_coverFst_eq_pullback_coverSnd B hB T))

/-- The descended sequence is a smooth blow-up sequence of order `m` for `(X, I, E)`. -/
theorem extendSeq_isOrderSeq (hB : B.CommutesWithSmoothSurjections) (T : Triple k) :
    (extendSeq B hB T).IsOrderSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.E m :=
  (Classical.choose_spec (Triple.exists_isOrderSeq_pullback_coverDesc_eq T
    (B.seq T.coverTriple (Triple.isAffine_coverTriple T)) (B.isOrderSeq T.coverTriple _)
    (pullback_coverFst_eq_pullback_coverSnd B hB T))).1

/-- The defining property of the extension: `g^* B̄(X) = B(X')`. -/
theorem extendSeq_pullback_coverDesc (hB : B.CommutesWithSmoothSurjections) (T : Triple k) :
    (extendSeq B hB T).pullback T.coverDesc =
      B.seq T.coverTriple (Triple.isAffine_coverTriple T) :=
  (Classical.choose_spec (Triple.exists_isOrderSeq_pullback_coverDesc_eq T
    (B.seq T.coverTriple (Triple.isAffine_coverTriple T)) (B.isOrderSeq T.coverTriple _)
    (pullback_coverFst_eq_pullback_coverSnd B hB T))).2

/-- The empty blow-up convention [Kol07, 32] for the extension: `B̄(X)` has no empty centers,
because `B(X')` has none. -/
theorem extendSeq_noEmptyCenters (hB : B.CommutesWithSmoothSurjections) (T : Triple k) :
    (extendSeq B hB T).NoEmptyCenters :=
  Hironaka.Sequence.NoEmptyCenters.of_pullback T.coverDesc
    (by rw [extendSeq_pullback_coverDesc]; exact B.noEmptyCenters _ _)

/-- The extension `B̄` of [Kol07, Proposition 37] of `B` to all triples: `B̄(X, I, E)` is the
sequence descended from `B(X', g^* I, g^{-1} E)` along the affine cover `g`. -/
noncomputable def extendFromAffine (hB : B.CommutesWithSmoothSurjections) :
    OrderSeqAssignment k m (fun _ : Triple k => True) where
  seq T _ := extendSeq B hB T
  isOrderSeq T _ := extendSeq_isOrderSeq B hB T
  noEmptyCenters T _ := extendSeq_noEmptyCenters B hB T

theorem extendFromAffine_seq (hB : B.CommutesWithSmoothSurjections) (T : Triple k) (hT : True) :
    (extendFromAffine B hB).seq T hT = extendSeq B hB T := rfl

/-- The specification of the extension: `g^* B̄(X) = B(X')` ("`B(X')` descends to a blow-up
sequence of `X`", the proof of [Kol07, Proposition 37]). -/
theorem extendFromAffine_pullback_coverDesc (hB : B.CommutesWithSmoothSurjections) (T : Triple k) :
    ((extendFromAffine B hB).seq T trivial).pullback T.coverDesc =
      B.seq T.coverTriple (Triple.isAffine_coverTriple T) :=
  extendSeq_pullback_coverDesc B hB T

/-- On the affine triples `B̄` is `B` (it is an extension, [Kol07, Proposition 37]): `g : X' → X`
is a smooth surjection between affine triples, so `B(X') = g^* B(X)`, and `g^*` is injective. -/
theorem extendFromAffine_restrict (hB : B.CommutesWithSmoothSurjections) (T : Triple k)
    (hT : T.IsAffineScheme) : (extendFromAffine B hB).seq T trivial = B.seq T hT := by
  have : @Smooth T.coverTriple.X.left T.X.left T.coverDesc := Triple.smooth_coverDesc T
  apply Triple.pullback_coverDesc_injective T
  change ((extendFromAffine B hB).seq T trivial).pullback T.coverDesc =
    (B.seq T hT).pullback T.coverDesc
  rw [extendFromAffine_pullback_coverDesc]
  exact hB T T.coverTriple T.coverDesc (Triple.surjective_coverDesc T)
    (Triple.coverTriple_isPullbackOf T) hT (Triple.isAffine_coverTriple T)

/-- The extension "commutes with smooth surjections" [Kol07, Proposition 37]: for a smooth
surjection `h : Y → X` between triples, `Y` carrying the pullback data of `X`, `B̄(Y) = h^* B̄(X)`;
compared on the fibre product `P = X' ×_X Y'` of the two affine covers, where
`p^* B(Y') = B(P) = q^* B(X') = q^* g^* B̄(X) = p^* (g_Y ≫ h)^* B̄(X)`, then injectivity along the
surjective smooth `p` and along `g_Y`. -/
theorem extendFromAffine_commutesWithSmoothSurjections (hB : B.CommutesWithSmoothSurjections) :
    (extendFromAffine B hB).CommutesWithSmoothSurjections := by
  intro T T' h _ hs hp hT hT'
  have hsg : @Smooth T'.coverTriple.X.left T'.X.left T'.coverDesc := Triple.smooth_coverDesc T'
  have hsp : @Smooth (Triple.comparisonTriple h).X.left T'.coverTriple.X.left
    (Triple.comparisonSnd h) :=
    Triple.smooth_comparisonSnd h
  have hsp' : Smooth (Triple.comparisonSnd h) := Triple.smooth_comparisonSnd h
  have hsq : @Smooth (Triple.comparisonTriple h).X.left T.coverTriple.X.left
    (Triple.comparisonFst h) :=
    Triple.smooth_comparisonFst h
  apply Triple.pullback_coverDesc_injective T'
  change ((extendFromAffine B hB).seq T' hT').pullback T'.coverDesc =
    (((extendFromAffine B hB).seq T hT).pullback h).pullback T'.coverDesc
  rw [extendFromAffine_pullback_coverDesc, ← pullback_comp]
  apply pullback_injective_of_surjective (Triple.comparisonSnd h)
    (Triple.surjective_comparisonSnd h)
  -- both sides are `B(P)`, resp. its expression through `X'` (the hypotheses restated at the
  -- explicit schemes so that the rewrites match)
  have h₁ : B.seq (Triple.comparisonTriple h) (Triple.isAffine_comparisonTriple h) =
      @BlowUpSequence.pullback T'.coverScheme
        (B.seq T'.coverTriple (Triple.isAffine_coverTriple T')) (Triple.comparisonScheme h)
        (Triple.comparisonSnd h) :=
    hB T'.coverTriple (Triple.comparisonTriple h) (Triple.comparisonSnd h)
      (Triple.surjective_comparisonSnd h) (Triple.comparisonTriple_isPullbackOf_snd h)
      (Triple.isAffine_coverTriple T') (Triple.isAffine_comparisonTriple h)
  have h₂ : B.seq (Triple.comparisonTriple h) (Triple.isAffine_comparisonTriple h) =
      @BlowUpSequence.pullback T.coverScheme
        (B.seq T.coverTriple (Triple.isAffine_coverTriple T)) (Triple.comparisonScheme h)
        (Triple.comparisonFst h) :=
    hB T.coverTriple (Triple.comparisonTriple h) (Triple.comparisonFst h)
      (Triple.surjective_comparisonFst h hs) (Triple.comparisonTriple_isPullbackOf_fst h hp)
      (Triple.isAffine_coverTriple T) (Triple.isAffine_comparisonTriple h)
  rw [← h₁, h₂, ← extendFromAffine_pullback_coverDesc B hB T, ← pullback_comp,
    ← pullback_comp, Triple.comparisonFst_comp_coverDesc]

/-- The existence statement of [Kol07, Proposition 37]: a blow-up sequence functor of order `m` on
the affine triples commuting with smooth surjections extends to a blow-up sequence functor of
order `m` on all triples that commutes with smooth surjections (the extension
`extendFromAffine`). -/
theorem exists_extension (hB : B.CommutesWithSmoothSurjections) :
    ∃ B' : OrderSeqAssignment k m (fun _ : Triple k => True),
      (∀ (T : Triple k) (hT : T.IsAffineScheme), B'.seq T trivial = B.seq T hT) ∧
        B'.CommutesWithSmoothSurjections :=
  ⟨extendFromAffine B hB, extendFromAffine_restrict B hB,
    extendFromAffine_commutesWithSmoothSurjections B hB⟩

/-- The uniqueness statement of [Kol07, Proposition 37]: two blow-up sequence functors on all
triples that restrict to `B` on the affine triples and commute with smooth surjections are equal;
`g^* B₁(X) = B(X') = g^* B₂(X)`, and pullback along the surjective `g` is injective. -/
theorem extension_unique {B₁ B₂ : OrderSeqAssignment k m (fun _ : Triple k => True)}
    (h₁ : ∀ (T : Triple k) (hT : T.IsAffineScheme), B₁.seq T trivial = B.seq T hT)
    (h₂ : ∀ (T : Triple k) (hT : T.IsAffineScheme), B₂.seq T trivial = B.seq T hT)
    (c₁ : B₁.CommutesWithSmoothSurjections) (c₂ : B₂.CommutesWithSmoothSurjections) : B₁ = B₂ := by
  refine ext fun T hT => ?_
  have : @Smooth T.coverTriple.X.left T.X.left T.coverDesc := Triple.smooth_coverDesc T
  apply Triple.pullback_coverDesc_injective T
  change (B₁.seq T hT).pullback T.coverDesc = (B₂.seq T hT).pullback T.coverDesc
  have e₁ : (B₁.seq T hT).pullback T.coverDesc = B₁.seq T.coverTriple trivial :=
    (c₁ T T.coverTriple T.coverDesc (Triple.surjective_coverDesc T)
      (Triple.coverTriple_isPullbackOf T) hT trivial).symm
  have e₂ : (B₂.seq T hT).pullback T.coverDesc = B₂.seq T.coverTriple trivial :=
    (c₂ T T.coverTriple T.coverDesc (Triple.surjective_coverDesc T)
      (Triple.coverTriple_isPullbackOf T) hT trivial).symm
  rw [e₁, e₂, h₁ T.coverTriple (Triple.isAffine_coverTriple T),
    h₂ T.coverTriple (Triple.isAffine_coverTriple T)]

end OrderSeqAssignment

/-! ### The marked version -/

namespace MarkedTriple

variable [PerfectField k] {T T' : MarkedTriple k} (h : T'.X.left ⟶ T.X.left)

/-- The marked triple of `P = X' ×_X Y'`: the pullback of the marked triple of `Y'` along `p`. -/
noncomputable def comparisonTriple : MarkedTriple k :=
  haveI : @HomIsOver Scheme.{u} _ (Triple.comparisonScheme h) T'.coverTriple.X.left
      (Triple.comparisonSnd h) (Spec (CommRingCat.of k)) (Triple.instOverComparisonScheme h)
      (AlgScheme.over T'.coverTriple.toTriple.X) := ⟨rfl⟩
  haveI : @Smooth (Triple.comparisonScheme h) T'.coverTriple.X.left (Triple.comparisonSnd h) :=
    Triple.smooth_comparisonSnd h
  MarkedTriple.pullback T'.coverTriple (Triple.exists_smoothOfRelativeDimension_comparisonScheme h)
    (Triple.comparisonSnd h)

/-- The marked triple of `P` is affine. -/
theorem isAffine_comparisonTriple : (comparisonTriple h).IsAffineScheme :=
  Triple.isAffine_comparisonScheme h

/-- The marked triple of `P` carries the pullback data of the marked triple of `Y'` along `p`. -/
theorem comparisonTriple_isPullbackOf_snd :
    (comparisonTriple h).IsPullbackOf T'.coverTriple (Triple.comparisonSnd h) :=
  haveI : @HomIsOver Scheme.{u} _ (Triple.comparisonScheme h) T'.coverTriple.X.left
      (Triple.comparisonSnd h) (Spec (CommRingCat.of k)) (Triple.instOverComparisonScheme h)
      (AlgScheme.over T'.coverTriple.toTriple.X) := ⟨rfl⟩
  haveI : @Smooth (Triple.comparisonScheme h) T'.coverTriple.X.left (Triple.comparisonSnd h) :=
    Triple.smooth_comparisonSnd h
  isPullbackOf_pullback T'.coverTriple _ _

/-- The marked triple of `P` carries the pullback data of the marked triple of `X'` along `q`. -/
theorem comparisonTriple_isPullbackOf_fst (hp : T'.IsPullbackOf T h) :
    (comparisonTriple h).IsPullbackOf T.coverTriple (Triple.comparisonFst h) :=
  ⟨Triple.comparisonTriple_isPullbackOf_fst h hp.1, hp.2⟩

end MarkedTriple

namespace OrderGeSeqAssignment

open Scheme

variable [CharZero k] (B : OrderGeSeqAssignment k MarkedTriple.IsAffineScheme)

/-- The value of the extension on a marked triple. -/
noncomputable def extendSeq (hB : B.CommutesWithSmoothSurjections) (T : MarkedTriple k) :
    BlowUpSequence T.X.left :=
  Classical.choose (MarkedTriple.exists_isOrderGeSeq_pullback_coverDesc_eq T
    (B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T)) (B.isOrderGeSeq T.coverTriple _)
    (pullback_coverFst_eq_pullback_coverSnd B hB T))

theorem extendSeq_isOrderGeSeq (hB : B.CommutesWithSmoothSurjections) (T : MarkedTriple k) :
    (extendSeq B hB T).IsOrderGeSeq (T.X.left ↘ Spec (CommRingCat.of k)) T.I T.m T.E :=
  (Classical.choose_spec (MarkedTriple.exists_isOrderGeSeq_pullback_coverDesc_eq T
    (B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T)) (B.isOrderGeSeq T.coverTriple _)
    (pullback_coverFst_eq_pullback_coverSnd B hB T))).1

theorem extendSeq_pullback_coverDesc (hB : B.CommutesWithSmoothSurjections) (T : MarkedTriple k) :
    (extendSeq B hB T).pullback T.toTriple.coverDesc =
      B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T) :=
  (Classical.choose_spec (MarkedTriple.exists_isOrderGeSeq_pullback_coverDesc_eq T
    (B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T)) (B.isOrderGeSeq T.coverTriple _)
    (pullback_coverFst_eq_pullback_coverSnd B hB T))).2

theorem extendSeq_noEmptyCenters (hB : B.CommutesWithSmoothSurjections) (T : MarkedTriple k) :
    (extendSeq B hB T).NoEmptyCenters :=
  Hironaka.Sequence.NoEmptyCenters.of_pullback T.toTriple.coverDesc
    (by rw [extendSeq_pullback_coverDesc]; exact B.noEmptyCenters _ _)

/-- The extension of [Kol07, Proposition 37] for marked functors. -/
noncomputable def extendFromAffine (hB : B.CommutesWithSmoothSurjections) :
    OrderGeSeqAssignment k (fun _ : MarkedTriple k => True) where
  seq T _ := extendSeq B hB T
  isOrderGeSeq T _ := extendSeq_isOrderGeSeq B hB T
  noEmptyCenters T _ := extendSeq_noEmptyCenters B hB T

/-- The specification of the marked extension: `g^* B̄(X) = B(X')`. -/
theorem extendFromAffine_pullback_coverDesc (hB : B.CommutesWithSmoothSurjections)
    (T : MarkedTriple k) :
    ((extendFromAffine B hB).seq T trivial).pullback T.toTriple.coverDesc =
      B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T) :=
  extendSeq_pullback_coverDesc B hB T

/-- On the affine marked triples `B̄` is `B`. -/
theorem extendFromAffine_restrict (hB : B.CommutesWithSmoothSurjections) (T : MarkedTriple k)
    (hT : T.IsAffineScheme) : (extendFromAffine B hB).seq T trivial = B.seq T hT := by
  have : @Smooth T.coverTriple.X.left T.X.left T.toTriple.coverDesc :=
    Triple.smooth_coverDesc T.toTriple
  apply Triple.pullback_coverDesc_injective T.toTriple
  change ((extendFromAffine B hB).seq T trivial).pullback T.toTriple.coverDesc =
    (B.seq T hT).pullback T.toTriple.coverDesc
  rw [extendFromAffine_pullback_coverDesc]
  exact hB T T.coverTriple T.toTriple.coverDesc (Triple.surjective_coverDesc T.toTriple)
    (MarkedTriple.coverTriple_isPullbackOf T) hT (MarkedTriple.isAffine_coverTriple T)

/-- The marked extension commutes with smooth surjections (the fibre-product comparison). -/
theorem extendFromAffine_commutesWithSmoothSurjections (hB : B.CommutesWithSmoothSurjections) :
    (extendFromAffine B hB).CommutesWithSmoothSurjections := by
  intro T T' h _ hs hp hT hT'
  have hsg : @Smooth T'.coverTriple.X.left T'.X.left T'.toTriple.coverDesc :=
    Triple.smooth_coverDesc T'.toTriple
  have hsp : @Smooth (MarkedTriple.comparisonTriple h).X.left T'.coverTriple.X.left
      (Triple.comparisonSnd h) := Triple.smooth_comparisonSnd h
  have hsp' : Smooth (Triple.comparisonSnd h) := Triple.smooth_comparisonSnd h
  have hsq : @Smooth (MarkedTriple.comparisonTriple h).X.left T.coverTriple.X.left
      (Triple.comparisonFst h) := Triple.smooth_comparisonFst h
  apply Triple.pullback_coverDesc_injective T'.toTriple
  change ((extendFromAffine B hB).seq T' hT').pullback T'.toTriple.coverDesc =
    (((extendFromAffine B hB).seq T hT).pullback h).pullback T'.toTriple.coverDesc
  rw [extendFromAffine_pullback_coverDesc, ← pullback_comp]
  apply pullback_injective_of_surjective (Triple.comparisonSnd h)
    (Triple.surjective_comparisonSnd h)
  have h₁ : B.seq (MarkedTriple.comparisonTriple h) (MarkedTriple.isAffine_comparisonTriple h) =
      @BlowUpSequence.pullback T'.toTriple.coverScheme
        (B.seq T'.coverTriple (MarkedTriple.isAffine_coverTriple T')) (Triple.comparisonScheme h)
        (Triple.comparisonSnd h) :=
    hB T'.coverTriple (MarkedTriple.comparisonTriple h) (Triple.comparisonSnd h)
      (Triple.surjective_comparisonSnd h) (MarkedTriple.comparisonTriple_isPullbackOf_snd h)
      (MarkedTriple.isAffine_coverTriple T') (MarkedTriple.isAffine_comparisonTriple h)
  have h₂ : B.seq (MarkedTriple.comparisonTriple h) (MarkedTriple.isAffine_comparisonTriple h) =
      @BlowUpSequence.pullback T.toTriple.coverScheme
        (B.seq T.coverTriple (MarkedTriple.isAffine_coverTriple T)) (Triple.comparisonScheme h)
        (Triple.comparisonFst h) :=
    hB T.coverTriple (MarkedTriple.comparisonTriple h) (Triple.comparisonFst h)
      (Triple.surjective_comparisonFst h hs) (MarkedTriple.comparisonTriple_isPullbackOf_fst h hp)
      (MarkedTriple.isAffine_coverTriple T) (MarkedTriple.isAffine_comparisonTriple h)
  rw [← h₁, h₂, ← extendFromAffine_pullback_coverDesc B hB T, ← pullback_comp,
    ← pullback_comp, Triple.comparisonFst_comp_coverDesc]

/-- The existence statement of [Kol07, Proposition 37] for marked functors. -/
theorem exists_extension (hB : B.CommutesWithSmoothSurjections) :
    ∃ B' : OrderGeSeqAssignment k (fun _ : MarkedTriple k => True),
      (∀ (T : MarkedTriple k) (hT : T.IsAffineScheme), B'.seq T trivial = B.seq T hT) ∧
        B'.CommutesWithSmoothSurjections :=
  ⟨extendFromAffine B hB, extendFromAffine_restrict B hB,
    extendFromAffine_commutesWithSmoothSurjections B hB⟩

/-- The uniqueness statement of [Kol07, Proposition 37] for marked functors. -/
theorem extension_unique {B₁ B₂ : OrderGeSeqAssignment k (fun _ : MarkedTriple k => True)}
    (h₁ : ∀ (T : MarkedTriple k) (hT : T.IsAffineScheme), B₁.seq T trivial = B.seq T hT)
    (h₂ : ∀ (T : MarkedTriple k) (hT : T.IsAffineScheme), B₂.seq T trivial = B.seq T hT)
    (c₁ : B₁.CommutesWithSmoothSurjections) (c₂ : B₂.CommutesWithSmoothSurjections) : B₁ = B₂ := by
  refine ext fun T hT => ?_
  have : @Smooth T.coverTriple.X.left T.X.left T.toTriple.coverDesc :=
    Triple.smooth_coverDesc T.toTriple
  apply Triple.pullback_coverDesc_injective T.toTriple
  change (B₁.seq T hT).pullback T.toTriple.coverDesc = (B₂.seq T hT).pullback T.toTriple.coverDesc
  have e₁ : (B₁.seq T hT).pullback T.toTriple.coverDesc = B₁.seq T.coverTriple trivial :=
    (c₁ T T.coverTriple T.toTriple.coverDesc (Triple.surjective_coverDesc T.toTriple)
      (MarkedTriple.coverTriple_isPullbackOf T) hT trivial).symm
  have e₂ : (B₂.seq T hT).pullback T.toTriple.coverDesc = B₂.seq T.coverTriple trivial :=
    (c₂ T T.coverTriple T.toTriple.coverDesc (Triple.surjective_coverDesc T.toTriple)
      (MarkedTriple.coverTriple_isPullbackOf T) hT trivial).symm
  rw [e₁, e₂, h₁ T.coverTriple (MarkedTriple.isAffine_coverTriple T),
    h₂ T.coverTriple (MarkedTriple.isAffine_coverTriple T)]

end OrderGeSeqAssignment

end Hironaka
