/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Scheme.BlowUp.Composite
import Hironaka.Scheme.BlowUp.Glue.Product
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Blow-up calculus for the single-centre form of Main Theorem I

Hironaka's Main Theorem I asks for a single monoidal transformation resolving `X` with centre
exactly the singular locus; his strong form obtains the resolving morphism as a finite succession of
monoidal transformations, and he remarks that a finite succession of monoidal transformations can be
replaced by a single monoidal transformation with a suitably chosen centre [Hir64, pp. 132–133].
This file proves two general facts of the blow-up calculus used to make that remark precise
(`Hironaka.Resolution.Algebraic.Hir64.SingleCenter`):

* `isIntegral_last_of_forall_support_ne_top`: a finite succession of monoidal transformations
  with proper centres starting at an integral locally Noetherian scheme ends at an integral scheme
  (the blow-up of an integral scheme in a proper centre is integral [Sta, Tag 0BFL], iterated).
  Every stage `X_i` is read as the closed subscheme `V(⊥)` of itself: the strict transform of `⊥`
  along a blow-up is `⊥` (the saturation of `⊥` by the invertible exceptional ideal is `⊥`), so
  `strictTransformSeq ⊥ i = ⊥` at every stage and `AlgebraicGeometry.isIntegral_strictTransformSeq`
  (the strict transform of an integral closed subscheme contained in no centre stays integral)
  applies with `J = ⊥`; "no centre is a whole stage" is exactly "no centre contains `V(⊥)`", and
  `V(⊥) ≅ X_i` transports integrality.
* `exists_iso_blowUp_mul_of_isInvertible_comap`: blowing up `K * J` is blowing up `K` when the
  pullback of `J` to `blowUp K` is invertible, because `blowUp (K * J) ≅ blowUp_{blowUp K} (J·𝒪)`
  over the base [Sta, Tag 080A] and the blow-up of an invertible ideal is an isomorphism
  [Sta, Tag 0807]. This is Hironaka's centre `J(m)·J₀` for two successive monoidal transformations
  [Hir64, p. 133].

The file also records that a point off a closed set over which all centres lie has a point of
every stage above it, that the generic point of an integral scheme is regular, and that if every
centre lies over the singular locus of a reduced irreducible scheme, no centre is a whole stage.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
open AlgebraicGeometry.Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {Y : Scheme.{u}}

/-- The strict transform of the zero ideal (the whole scheme as a closed subscheme) along a blow-up
is the zero ideal: `(⊥.comap π).saturate E = ⊥.saturate E = ⊥` for the invertible exceptional
ideal `E` (`saturate_bot_of_isInvertible`). -/
theorem strictTransform_bot (D :
    Y.IdealSheafData) : Scheme.IdealSheafData.strictTransform ⊥ D = ⊥ := by
  change ((⊥ : Y.IdealSheafData).comap D.blowUpπ).saturate D.exceptionalDivisor = ⊥
  rw [comap_bot]
  exact saturate_bot_of_isInvertible (blowUp.isInvertible_comap_π D)

/-- Along a finite succession the strict transform of `⊥` stays `⊥` at every stage. -/
theorem strictTransformSeq_bot :
    ∀ {Y : Scheme.{u}} (S : BlowUpSequence Y) (i : Fin (S.length + 1)),
      S.strictTransformSeq ⊥ i = ⊥
  | _, nil _, _ => rfl
  | _, cons _ _ _, ⟨0, _⟩ => rfl
  | _, cons X D rest, ⟨j + 1, h⟩ => by
    change rest.strictTransformSeq (Scheme.IdealSheafData.strictTransform ⊥ D) ⟨j,
        Nat.lt_of_succ_lt_succ h⟩ = ⊥
    rw [strictTransform_bot]
    exact strictTransformSeq_bot rest _

/-- A finite succession of monoidal transformations with proper centres (no centre a whole stage)
starting at an integral locally Noetherian scheme ends at an integral scheme ([Sta, Tag 0BFL]
iterated): the strict transform of the integral closed subscheme `V(⊥) = Y` along the succession
(`AlgebraicGeometry.isIntegral_strictTransformSeq`), read back on the stage through `V(⊥) ≅ X_i`. -/
theorem isIntegral_last_of_forall_support_ne_top [IsIntegral Y] [IsLocallyNoetherian Y]
    (S : BlowUpSequence Y) (h : ∀ i : Fin S.length, (S.center i).support ≠ ⊤) :
    IsIntegral S.last := by
  have hbot : IsIntegral (⊥ : Y.IdealSheafData).subscheme := by
    have : IsIso (⊥ : Y.IdealSheafData).subschemeι :=
      (AlgebraicGeometry.Scheme.isIso_subschemeι_iff_eq_bot _).mpr rfl
    exact IsIntegral.of_isIso (inv (⊥ : Y.IdealSheafData).subschemeι)
  have key : IsIntegral (S.strictTransformSeq ⊥ (Fin.last S.length)).subscheme :=
    isIntegral_strictTransformSeq S ⊥ (Fin.last S.length) fun m _ hle => by
      rw [strictTransformSeq_bot, le_bot_iff] at hle
      exact h m (by rw [hle, support_bot])
  rw [strictTransformSeq_bot] at key
  have hiso : IsIso (⊥ : (S.stage (Fin.last S.length)).IdealSheafData).subschemeι :=
    (AlgebraicGeometry.Scheme.isIso_subschemeι_iff_eq_bot _).mpr rfl
  exact @IsIntegral.of_isIso _ _ key
    (⊥ : (S.stage (Fin.last S.length)).IdealSheafData).subschemeι hiso

/-- If the pullback of `J` to `K.blowUp` is invertible, then `(K * J).blowUp ≅ K.blowUp`
over `Y`: the blow-up of a product is the blow-up of the pullback of the second factor on the
blow-up of the first [Sta, Tag 080A], and the blow-up of an invertible ideal is an isomorphism
[Sta, Tag 0807]. This is Hironaka's remark that two successive monoidal transformations are one
monoidal transformation with centre `J(m)·J₀` [Hir64, p. 133]. -/
theorem exists_iso_blowUp_mul_of_isInvertible_comap (K J : Y.IdealSheafData)
    (h : (J.comap K.blowUpπ).IsInvertible) :
    ∃ e : (K * J).blowUp ≅ K.blowUp, e.hom ≫ K.blowUpπ =
        (K * J).blowUpπ := by
  obtain ⟨e₁, he₁, -⟩ := blowUp.exists_mulIso K J
  have : IsIso (IdealSheafData.blowUpπ (J.comap K.blowUpπ)) :=
    blowUp.isIso_π_of_isInvertible _ h
  refine ⟨e₁.symm ≪≫ asIso (IdealSheafData.blowUpπ (J.comap K.blowUpπ)), ?_⟩
  rw [Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc, ← he₁, Iso.inv_hom_id_assoc]

end Hironaka.Resolution

namespace Hironaka.Resolution

/-- A point `x` of `X` not in a set `Z` over which all the centres of `S` lie has a point of every
stage above it: at each blow-up a point off the centre has exactly one preimage
(`blowUp.existsUnique_preimage_of_notMem_support`). -/
theorem exists_stage_point_over_of_forall_center_mem :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (Z : Set X),
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ Z) →
      ∀ (x : X), x ∉ Z → ∀ i : Fin (S.length + 1), ∃ z : S.stage i, S.stageMap i z = x
  | _, nil X, _, _, x, _, _ => ⟨x, rfl⟩
  | _, cons X D rest, Z, hZ, x, hx, ⟨0, _⟩ => ⟨x, rfl⟩
  | _, cons X D rest, Z, hZ, x, hx, ⟨j + 1, hj⟩ => by
    -- `x` is off the first centre `D`, whose points map into `Z` under the identity
    have hxD : x ∉ D.support := fun h => hx (hZ ⟨0, Nat.succ_pos _⟩ x h)
    obtain ⟨x', hx', -⟩ := blowUp.existsUnique_preimage_of_notMem_support D hxD
    -- the rest of the succession, with the centres over `π⁻¹ Z` and the point `x'` off it
    have hrest : ∀ (i : Fin rest.length) (z : rest.stage i.castSucc),
        z ∈ (rest.center i).support → rest.stageMap i.castSucc z ∈ D.blowUpπ ⁻¹' Z := by
      intro i z hz
      exact hZ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ z hz
    have hx'Z : x' ∉ D.blowUpπ ⁻¹' Z := fun h => hx (hx' ▸ h)
    obtain ⟨z, hz⟩ := exists_stage_point_over_of_forall_center_mem rest
        (D.blowUpπ ⁻¹' Z) hrest
      x' hx'Z ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    refine ⟨z, ?_⟩
    change (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ) z = x
    rw [Scheme.Hom.comp_apply, hz, hx']

/-- The generic point of an integral scheme is a regular point: its stalk is the function field, a
field, and a field is a regular local ring (a local principal ideal domain). -/
theorem isRegularAt_genericPoint_of_isIntegral {X : Scheme.{u}} [IsIntegral X] :
    X.IsRegularAt (genericPoint X) := by
  change IsRegularLocalRing (X.presheaf.stalk (genericPoint X))
  let _ : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  infer_instance

/-- If every centre lies over the singular locus of the reduced irreducible `X`, no centre is a
whole stage: the generic point of `X` is regular and has a point of every stage above it. -/
theorem support_center_ne_top_of_forall_mem_singularLocus (X : Scheme.{u}) [IsReduced X]
    [IrreducibleSpace X] (S : BlowUpSequence X)
    (hcenters : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ X.singularLocus) (i : Fin S.length) :
    (S.center i).support ≠ ⊤ := by
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have hη : genericPoint X ∉ X.singularLocus := fun h => h isRegularAt_genericPoint_of_isIntegral
  obtain ⟨z, hz⟩ := exists_stage_point_over_of_forall_center_mem S X.singularLocus hcenters
    (genericPoint X) hη i.castSucc
  intro htop
  have hzc : z ∈ (S.center i).support := by rw [htop]; trivial
  exact hη (hz ▸ hcenters i z hzc)

end Hironaka.Resolution
