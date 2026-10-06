/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.RegularSmooth.SingularLocus
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Hir64.SingleCenterTools
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineTheorem36
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Scheme.BlowUp.InvertibleSheaf
import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp
import Hironaka.Scheme.BlowUpSequence.ConcatCenters
import Hironaka.Scheme.BlowUpSequence.NowhereDenseSupport
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.EmptyFamily
import Hironaka.Scheme.Snc.RelativeDimensionConstant
import Hironaka.Scheme.Snc.TrivialSncData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The single-centre form of Main Theorem I: the enlargement of the centre

Hironaka's Main Theorem I [Hir64, Main Theorem I, p. 132] resolves a reduced irreducible algebraic
`k`-scheme `X` by ONE monoidal transformation whose centre `D` has the singular locus of `X` as its
set of points. In the strong form [Hir64, p. 132] the resolving morphism is obtained by a finite
succession of monoidal transformations with non-singular centres containing no simple point, and
Hironaka remarks that any finite succession is a single monoidal transformation with a suitably
chosen centre [Hir64, pp. 132–133]. This file makes that remark precise in the form needed: given a
finite succession `S` of monoidal transformations of `X` with smooth last stage `X_r` (hypothesis
`hsmooth`) whose centres lie over `Sing X` (hypothesis `hcenters`), it produces one closed subscheme
`D ⊆ X` with `|D| = Sing X` and `D.blowUp` non-singular (`exists_center_support_eq_singularLocus`).
This is the conclusion of Main Theorem I. The main theorem, with the succession provided by
Kollár's resolution functor, is in `Hironaka.Resolution.Algebraic.Hir64.MainTheoremI`.

## The argument

Let `𝒥 := X.singIdeal` be the ideal of `Sing X` with its reduced structure. `X_r` is integral
(`Hironaka.Resolution.Algebraic.Hir64.SingleCenterTools`), and `T := (X_r, 𝒥·𝒪_{X_r}, ∅)` is a
triple (`enlargementTriple`). Let `P := BP T` be its principalization [Kol07, Theorem 35] and
`S' := S.concat P`. The composite `S'.last → X` is one blow-up `K.blowUp` with `|K| ⊆ Sing X`
(`AlgebraicGeometry.exists_blowUp_composite_iso`; the centres of `P` lie over `Π⁻¹(Sing X)` by
`stageMap_mem_support_of_mem_center_BP` and `forall_center_concat_mem`). Set `D := K * 𝒥`. Then
`|D| = |K| ∪ Sing X = Sing X`, and `D.blowUp ≅ K.blowUp`, because `𝒥·𝒪_{K.blowUp}` corresponds
to `(𝒥·𝒪_{X_r})·𝒪_{P.last}`, which is invertible by clause (2) of [Kol07, Theorem 35]
(`isInvertible_comap_composite_BP`), so the second blow-up is an isomorphism
(`exists_iso_blowUp_mul_of_isInvertible_comap`). Finally `D.blowUp ≅ S'.last` is smooth over `k`
(`smooth_composite_BP`), hence regular (`isRegular_of_smooth`, `IsRegular.of_isIso`).

## Conventions

The helpers are stated for a structure morphism `f : X ⟶ Spec k`; the two that need neither `k`
nor `f` are stated without them. The theorem itself is stated in the `X.Over` form of the main
theorems.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  IdealSheafData BlowUpSequence
open AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section Helpers

variable {X : Scheme.{u}} [IsReduced X] [IrreducibleSpace X] (S : BlowUpSequence X)

/-- Every centre lies over `Sing X`, which misses the (regular) generic point of the integral scheme
`X`, so the last stage `X_r` has a point over the generic point
(`exists_stage_point_over_of_forall_center_mem`). -/
theorem exists_last_point_over_genericPoint
    (hcenters : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ X.singularLocus) :
    ∃ z : S.last, S.composite z = genericPoint X := by
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hη : genericPoint X ∉ X.singularLocus := fun h => h isRegularAt_genericPoint_of_isIntegral
  exact exists_stage_point_over_of_forall_center_mem S X.singularLocus hcenters (genericPoint X)
    hη (Fin.last S.length)

/-- The last stage `X_r` is integral: no centre is a whole stage
(`support_center_ne_top_of_forall_mem_singularLocus`) and blow-ups of an integral locally
Noetherian scheme in proper centres stay integral (`isIntegral_last_of_forall_support_ne_top`). -/
theorem isIntegral_last [IsLocallyNoetherian X]
    (hcenters : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ X.singularLocus) :
    IsIntegral S.last := by
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  exact isIntegral_last_of_forall_support_ne_top S
    (support_center_ne_top_of_forall_mem_singularLocus X S hcenters)

/-- The pullback `𝒥·𝒪_{X_r}` of the ideal of `Sing X` has nonzero stalks everywhere (condition (2)
of [Kol07, Notation 64] for the triple `T`): its support `Π⁻¹(Sing X)` is a proper closed subset of
the irreducible `X_r` (it misses a point over the generic point), hence nowhere dense
(`isNonzeroEverywhere_of_isNowhereDense_support`). -/
theorem isNonzeroEverywhere_comap_singIdeal (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hcenters : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ X.singularLocus) :
    IsNonzeroEverywhere (X.singIdeal.comap S.composite) := by
  have hN : IsNoetherian X := f.isNoetherian_of_field
  have hNl : IsNoetherian S.last := isNoetherian_stage S (Fin.last S.length)
  have hint : IsIntegral S.last := isIntegral_last S hcenters
  refine isNonzeroEverywhere_of_isNowhereDense_support _ ?_
  have hsupp : ((X.singIdeal.comap S.composite).support : Set S.last) =
      S.composite ⁻¹' X.singularLocus := by
    rw [support_comap]
    change S.composite ⁻¹' (X.singIdeal.support : Set X) = S.composite ⁻¹' X.singularLocus
    rw [Scheme.coe_support_singIdeal_eq_singularLocus f]
  have hcl : IsClosed (S.composite ⁻¹' X.singularLocus) :=
    (Scheme.isClosed_singularLocus f).preimage S.composite.continuous
  rw [hsupp, hcl.isNowhereDense_iff, interior_eq_empty_iff_dense_compl]
  obtain ⟨z, hz⟩ := exists_last_point_over_genericPoint S hcenters
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hη : genericPoint X ∉ X.singularLocus := fun h => h isRegularAt_genericPoint_of_isIntegral
  refine hcl.isOpen_compl.dense ⟨z, fun h => hη ?_⟩
  rw [← hz]
  exact h

/-- The triple `(X_r, 𝒥·𝒪_{X_r}, ∅)` to which the principalization theorem is applied in the
enlargement of the centre (not Hironaka's step: his single centre [Hir64, p. 133] is defined by
`J(m)J_0` with `f_0⁻¹(J(m)) = f_0⁻¹(J_0)^m J_1`): `X_r → Spec k` is smooth (hypothesis
`hsmooth`), proper over `X` so quasi-compact and separated, and equidimensional since `X_r` is
irreducible (`exists_smoothOfRelativeDimension_of_preconnectedSpace`); the ideal is nonzero
everywhere (`isNonzeroEverywhere_comap_singIdeal`); the boundary is empty, a simple normal
crossing divisor on a smooth scheme (`isSnc_empty_of_smooth`). -/
noncomputable def enlargementTriple (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f]
    (hcenters : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ X.singularLocus)
    (hsmooth : Smooth (S.composite ≫ f)) : Triple k where
  X := .ofHom (S.composite ≫ f)
    (by
      have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      have hp : IsProper S.composite := isProper_stageMap S (Fin.last S.length)
      exact inferInstanceAs (FiniteType (S.composite ≫ f)))
    (by
      have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      have hp : IsProper S.composite := isProper_stageMap S (Fin.last S.length)
      exact inferInstanceAs (IsSeparated (S.composite ≫ f)))
  smoothOfRelativeDimension := by
    have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    have hint : IsIntegral S.last := isIntegral_last S hcenters
    have := hsmooth
    exact exists_smoothOfRelativeDimension_of_preconnectedSpace (S.composite ≫ f)
  I := X.singIdeal.comap S.composite
  isNonzeroEverywhere := isNonzeroEverywhere_comap_singIdeal S f hcenters
  E := DivisorFamily.empty S.last
  isSnc := by
    have := hsmooth
    exact isSnc_empty_of_smooth (S.composite ≫ f)

end Helpers

section Assembly

variable (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k))] [IsSeparated (X ↘ Spec (CommRingCat.of k))]
  [IsReduced X] [IrreducibleSpace X]

/-- The enlargement of the centre [Hir64, pp. 132–133]: for `X` a reduced irreducible algebraic
`k`-scheme and a finite succession `S` of monoidal transformations with smooth last stage
(`hsmooth`) whose centres lie over `Sing X` (`hcenters`), there is a closed subscheme `D` with
`|D| = Sing X` and `D.blowUp` non-singular. -/
theorem exists_center_support_eq_singularLocus (S : BlowUpSequence X)
    (hsmooth : Smooth (S.composite ≫ (X ↘ Spec (CommRingCat.of k))))
    (hcenters : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ X.singularLocus) :
    ∃ D : X.IdealSheafData, (D.support : Set X) = X.singularLocus ∧
        IsRegular D.blowUp := by
  classical
  have hN : IsNoetherian X := (X ↘ Spec (CommRingCat.of k)).isNoetherian_of_field
  -- the triple, the principalization and the concatenated succession
  set T : Triple k := enlargementTriple S (X ↘ Spec (CommRingCat.of k)) hcenters hsmooth
  set P : BlowUpSequence S.last := Hironaka.Sequence.BP T
  set S' : BlowUpSequence X := S.concat P
  -- the whole succession is one blow-up of `X`
  obtain ⟨K, hK, e, he, -⟩ := exists_blowUp_composite_iso S'
  -- its centre lies over `Sing X`
  have hE : IsEmpty T.E.ι := inferInstanceAs (IsEmpty PEmpty)
  have hTI : (T.I.support : Set T.X.left) = S.composite ⁻¹' X.singularLocus := by
    change ((X.singIdeal.comap S.composite).support : Set S.last) = _
    rw [support_comap]
    change S.composite ⁻¹' (X.singIdeal.support : Set X) = S.composite ⁻¹' X.singularLocus
    rw [Scheme.coe_support_singIdeal_eq_singularLocus (X ↘ Spec (CommRingCat.of k))]
  have hPcenters : ∀ (i : Fin P.length) (z : P.stage i.castSucc), z ∈ (P.center i).support →
      S.composite (P.stageMap i.castSucc z) ∈ X.singularLocus := by
    intro i z hz
    have h := stageMap_mem_support_of_mem_center_BP T hE i hz
    have h' : P.stageMap i.castSucc z ∈ (T.I.support : Set T.X.left) := h
    rw [hTI] at h'
    exact h'
  have hKsub : (K.support : Set X) ⊆ X.singularLocus := by
    rw [hK]
    refine Set.iUnion_subset fun i => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact forall_center_concat_mem S P X.singularLocus hcenters hPcenters i z hz
  -- the enlarged centre and its support
  refine ⟨K * X.singIdeal, ?_, ?_⟩
  · rw [support_mul, Closeds.coe_sup, Scheme.coe_support_singIdeal_eq_singularLocus
      (X ↘ Spec (.of k))]
    exact Set.union_eq_right.mpr hKsub
  -- `(K * 𝒥).blowUp ≅ K.blowUp ≅ S'.last`, and `S'.last` is smooth over `k`
  · have hinv : (X.singIdeal.comap K.blowUpπ).IsInvertible := by
      -- `𝒥.comap π_K = (𝒥.comap S'.composite).comap e.inv`, and `𝒥.comap S'.composite` is the
      -- pull-back of `T.I` along `P.composite` (up to the identification of the last stages)
      have h1 : X.singIdeal.comap K.blowUpπ =
          (X.singIdeal.comap S'.composite).comap e.inv := by
        rw [← he, ← comap_comp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      have h2 : X.singIdeal.comap S'.composite =
          (T.I.comap P.composite).comap (eqToHom (last_concat S P)) := by
        change X.singIdeal.comap (S.concat P).composite =
          ((X.singIdeal.comap S.composite).comap P.composite).comap (eqToHom (last_concat S P))
        rw [composite_concat, comap_comp, comap_comp]
      rw [h1, h2]
      have hT35 : (T.I.comap P.composite).IsInvertible := isInvertible_comap_composite_BP T
      exact (hT35.comap_of_isOpenImmersion (eqToHom (last_concat S P))).comap_of_isOpenImmersion
        e.inv
    obtain ⟨e₂, -⟩ := exists_iso_blowUp_mul_of_isInvertible_comap K X.singIdeal hinv
    -- regularity of `S'.last = P.last` (smooth over `k` by Theorem 35 (1)), transported
    have hsm : Smooth (P.composite ≫ (T.X.left ↘ Spec (CommRingCat.of k))) := smooth_composite_BP T
    have hregP : IsRegular P.last :=
      isRegular_of_smooth (P.composite ≫ (T.X.left ↘ Spec (CommRingCat.of k)))
    have hregS' : IsRegular S'.last :=
      IsRegular.of_isIso (eqToHom (last_concat S P).symm) hregP
    exact IsRegular.of_isIso (e ≪≫ e₂.symm).hom hregS'

end Assembly

end Hironaka.Resolution
