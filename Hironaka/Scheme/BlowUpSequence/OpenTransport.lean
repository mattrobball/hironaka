/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Pullback
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.PullbackSmooth
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.WeakTransformFlat
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.Smooth.ExceptionalBaseChange
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport along an open immersion whose range contains the centers

The proof of Corollary 1 of Main Theorem II [Hir64, pp. 143–144] runs Main Theorem II on the open
subscheme `X̄ = X ∖ S` and extends the succession across `S` by open immersions
`u_i : X̄(i) → X(i)` with `u_i(D̄(i)) = D(i)`. The extension `S` on `X` has `S.pullback u = S̄`
(`Hironaka/Resolution/Algebraic/Hir64/ExtendOpen.lean`), and every center of `S` lies in the range
of the stage lift `u_i` (`CentersInRange`). This module transports along such an open immersion what
the corollary needs:

* **the closed subschemes of the centers**: for a closed `Z ⊆ X` whose support lies in the range
  of the open immersion `φ`, the induced map `V(φ⁻¹ Z) → V(Z)` is an isomorphism (an open
  immersion, as the base change of `φ`, and surjective), so regularity, irreducibility and
  smoothness over the base transfer from `φ⁻¹ Z` to `Z`;
* **smoothness of the sequence** (`isSmooth_of_isSmooth_pullback`);
* **the weak transforms** (`weakTransformSeq_pullback_mk_of_isOpenImmersion`): the induced ideals
  of `S.pullback u` are the inverse images of the induced ideals of `S` under the stage lifts, as
  for the flat transport of `Hironaka/Scheme/BlowUpSequence/WeakTransformFlat.lean`, the order along
  each center of `S` being read off the pulled-back center through the range condition (the weak
  transform is the marked transform with the constant order as mark on both sides, and marked
  transforms commute with flat pull-back). The pull-back of a sequence is that of [Kol07, 30.1].
-/

public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.IdealSheafData
  Scheme BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### The closed subscheme of a center in the range of an open immersion -/

section Subscheme

variable (φ : Y ⟶ X) (Z : X.IdealSheafData)

variable [IsOpenImmersion φ]

/-- `V(φ⁻¹ Z) → V(Z)` is an open immersion, the base change of `φ`. -/
theorem isOpenImmersion_subschemeMap_comap :
    IsOpenImmersion (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ)) :=
  property_of_isPullback @IsOpenImmersion
    (isPullback_subschemeMap_comap φ Z) inferInstance

omit [IsOpenImmersion φ] in
/-- `V(φ⁻¹ Z) → V(Z)` is surjective when `|Z|` lies in the range of `φ`. -/
theorem surjective_subschemeMap_comap (hZ : (Z.support : Set X) ⊆ Set.range φ) :
    Function.Surjective (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ)) := by
  rw [← Set.range_eq_univ,
    range_fst_of_isPullback (isPullback_subschemeMap_comap φ Z)]
  refine Set.eq_univ_of_forall fun z => ?_
  refine hZ ?_
  rw [← range_subschemeι]
  exact Set.mem_range_self z

/-- `V(φ⁻¹ Z) → V(Z)` is an isomorphism when `|Z|` lies in the range of the open immersion `φ`
(a surjective open immersion); this is Hironaka's `u_i(D̄(i)) = D(i)`. -/
theorem isIso_subschemeMap_comap_of_subset (hZ : (Z.support : Set X) ⊆ Set.range φ) :
    IsIso (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ)) := by
  have := isOpenImmersion_subschemeMap_comap φ Z
  have : Epi (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ)).base :=
    (TopCat.epi_iff_surjective _).mpr (surjective_subschemeMap_comap φ Z hZ)
  exact IsOpenImmersion.isIso _

/-- Regularity of `V(Z)` from regularity of `V(φ⁻¹ Z)` (the stalks correspond under the
isomorphism). -/
theorem isRegular_subscheme_of_comap (hZ : (Z.support : Set X) ⊆ Set.range φ)
    (h : IsRegular (Z.comap φ).subscheme) : IsRegular Z.subscheme := by
  have := isIso_subschemeMap_comap_of_subset φ Z hZ
  refine ⟨fun z => ?_⟩
  obtain ⟨w, rfl⟩ := surjective_subschemeMap_comap φ Z hZ z
  have h1 : IsRegularLocalRing ((Z.comap φ).subscheme.presheaf.stalk w) := h.isRegularAt w
  exact IsRegularLocalRing.of_ringEquiv (CategoryTheory.Iso.commRingCatIsoToRingEquiv
    (asIso ((subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ)).stalkMap w)).symm)

/-- Irreducibility of `V(Z)` from irreducibility of `V(φ⁻¹ Z)`. -/
theorem irreducibleSpace_subscheme_of_comap (hZ : (Z.support : Set X) ⊆ Set.range φ)
    (h : IrreducibleSpace (Z.comap φ).subscheme) : IrreducibleSpace Z.subscheme := by
  have := isIso_subschemeMap_comap_of_subset φ Z hZ
  exact (Homeomorph.irreducibleSpace_iff (Scheme.homeoOfIso
    (asIso (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ))))).mp h

/-- Smoothness of `V(Z) → W` from smoothness of `V(φ⁻¹ Z) → Y → X → W`. -/
theorem smooth_subschemeι_comp_of_comap {W : Scheme.{u}} (g : X ⟶ W)
    (hZ : (Z.support : Set X) ⊆ Set.range φ)
    (h : Smooth ((Z.comap φ).subschemeι ≫ φ ≫ g)) : Smooth (Z.subschemeι ≫ g) := by
  have := isIso_subschemeMap_comap_of_subset φ Z hZ
  have e : Z.subschemeι ≫ g = inv (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ)) ≫
      (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ) ≫ Z.subschemeι) ≫ g := by
    simp
  rw [e, subschemeMap_subschemeι, Category.assoc]
  have : Smooth (inv (subschemeMap (Z.comap φ) Z φ (le_map_comap Z φ))) :=
    SmoothOfRelativeDimension.smooth 0 _
  infer_instance

end Subscheme

/-! ### Centers in the range of the stage lifts -/

section Centres

variable (u : Y ⟶ X) [IsOpenImmersion u] (S : BlowUpSequence X)

/-- A predicate on closed subschemes that transfers from `φ⁻¹ Z` to `Z` along open immersions
whose range contains `|Z|` holds on the centers of `S` once it holds on the centers of
`S.pullback u`, provided the centers of `S` lie in the ranges of the stage lifts. -/
theorem forall_center_of_pullback (P : ∀ {W : Scheme.{u}}, W.IdealSheafData → Prop)
    (hP : ∀ {W W' : Scheme.{u}} (φ : W' ⟶ W) [IsOpenImmersion φ] (Z : W.IdealSheafData),
      (Z.support : Set W) ⊆ Set.range φ → P (Z.comap φ) → P Z)
    (hC : S.CentersInRange u) (h : ∀ i, P ((S.pullback u).center i)) : ∀ i, P (S.center i) := by
  rintro ⟨j, hj⟩
  have h1 := h (S.pullbackCenterIdx u ⟨j, hj⟩)
  rw [center_pullback_mk S u j hj] at h1
  have := isOpenImmersion_pullbackStageHom S u (Fin.castSucc ⟨j, hj⟩)
  exact hP _ _ (hC ⟨j, hj⟩) h1

/-- Regular centers transfer from `S.pullback u` to `S`. -/
theorem forall_isRegular_center_of_pullback (hC : S.CentersInRange u)
    (h : ∀ i, IsRegular ((S.pullback u).center i).subscheme) :
    ∀ i, IsRegular (S.center i).subscheme :=
  forall_center_of_pullback u S (fun Z => IsRegular Z.subscheme)
    (fun φ _ Z hZ hreg => isRegular_subscheme_of_comap φ Z hZ hreg) hC h

/-- Irreducible centers transfer from `S.pullback u` to `S`. -/
theorem forall_irreducibleSpace_center_of_pullback (hC : S.CentersInRange u)
    (h : ∀ i, IrreducibleSpace ((S.pullback u).center i).subscheme) :
    ∀ i, IrreducibleSpace (S.center i).subscheme :=
  forall_center_of_pullback u S (fun Z => IrreducibleSpace Z.subscheme)
    (fun φ _ Z hZ hirr => irreducibleSpace_subscheme_of_comap φ Z hZ hirr) hC h

variable {k : Type u} [Field k]

/-- A sequence whose pull-back along `u` is smooth over `k` is smooth over `k` when its centers
lie in the ranges of the stage lifts: each center's closed subscheme is isomorphic to that of the
pulled-back center. -/
theorem isSmooth_of_isSmooth_pullback (f : X ⟶ Spec (.of k)) (hC : S.CentersInRange u)
    (h : (S.pullback u).IsSmooth (u ≫ f)) : S.IsSmooth f := by
  rintro ⟨j, hj⟩
  have h1 := h (S.pullbackCenterIdx u ⟨j, hj⟩)
  rw [center_pullback_mk S u j hj] at h1
  change Smooth (((S.center ⟨j, hj⟩).comap
    (S.pullbackStageHom u (Fin.castSucc ⟨j, hj⟩))).subschemeι ≫
      (S.pullback u).stageMap (S.pullbackStageIdx u (Fin.castSucc ⟨j, hj⟩)) ≫ u ≫ f) at h1
  rw [← Category.assoc ((S.pullback u).stageMap _) u f, ← pullbackStageHom_stageMap S u,
    Category.assoc] at h1
  have := isOpenImmersion_pullbackStageHom S u (Fin.castSucc ⟨j, hj⟩)
  exact smooth_subschemeι_comp_of_comap (S.pullbackStageHom u (Fin.castSucc ⟨j, hj⟩))
    (S.center ⟨j, hj⟩) (S.stageMap (Fin.castSucc ⟨j, hj⟩) ≫ f) (hC ⟨j, hj⟩) h1

end Centres

/-! ### The weak transforms along the stage lifts -/

section WeakTransform

variable {k : Type u} [Field k] [CharZero k]

/-- Along an open immersion `u` whose stage lifts contain the centers of the smooth sequence `S`,
if every induced ideal of `S.pullback u` has constant order on the corresponding center, the
induced ideals of `S.pullback u` are the inverse images of the induced ideals of `S` under the
stage lifts (the flat transport of `Hironaka/Scheme/BlowUpSequence/WeakTransformFlat.lean`, with the
order along each center read off the pulled-back center). -/
theorem weakTransformSeq_pullback_mk_of_isOpenImmersion (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (u : Y ⟶ X) [IsOpenImmersion u] (S : BlowUpSequence X)
    (hC : S.CentersInRange u) (hsm : S.IsSmooth f) (I : X.IdealSheafData)
    (hpt : ∀ (j : ℕ) (hj : j < S.length), ∃ c : ℕ,
      ∀ y ∈ ((S.pullback u).center (S.pullbackCenterIdx u ⟨j, hj⟩)).support,
        ((S.pullback u).weakTransformSeq (I.comap u)
          (S.pullbackStageIdx u ⟨j, Nat.lt_succ_of_lt hj⟩)).ord y = c)
    (j : ℕ) (hj : j < S.length + 1) :
    (S.pullback u).weakTransformSeq (I.comap u) (S.pullbackStageIdx u ⟨j, hj⟩) =
      (S.weakTransformSeq I ⟨j, hj⟩).comap (S.pullbackStageHom u ⟨j, hj⟩) := by
  induction S generalizing Y j with
  | nil X => rfl
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j =>
      obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 hsm
      obtain ⟨hD', -⟩ :=
        (isSmooth_cons_iff (u ≫ f) (D.comap u) (rest.pullback (Scheme.Hom.blowUpMap u D))).1
          (IsSmooth.pullback f u hsm)
      -- the constant order of `I` along the first center, on both sides
      obtain ⟨c, hc⟩ := hpt 0 (Nat.succ_pos _)
      have hm' : (I.comap u).OrdAlongEq (D.comap u).support (c : ℕ∞) := fun η hη => hc η hη.1
      have hm : I.OrdAlongEq D.support (c : ℕ∞) := by
        intro η hη
        obtain ⟨y, rfl⟩ := hC ⟨0, Nat.succ_pos _⟩ hη.1
        have hy : y ∈ (D.comap u).support := (mem_support_comap_iff_apply D u y).mpr hη.1
        have := hc y hy
        change (I.comap u).ord y = (c : ℕ∞) at this
        rw [ord_comap_of_isOpenImmersion I u y] at this
        exact this
      have h0 : SmoothOfRelativeDimension (0 + n) (u ≫ f) := inferInstance
      rw [Nat.zero_add] at h0
      have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
        smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
      have hw : (I.comap u).weakTransform (D.comap u) =
          (I.weakTransform D).comap (Scheme.Hom.blowUpMap u D) :=
        weakTransform_comap_of_orderAlong_of_flat f n (u ≫ f) n u D I hm hm'
      have hC' : rest.CentersInRange (Scheme.Hom.blowUpMap u D) :=
        fun i => hC ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
      have hpt' : ∀ (j' : ℕ) (hj' : j' < rest.length), ∃ c : ℕ,
          ∀ y ∈ ((rest.pullback (Scheme.Hom.blowUpMap u D)).center
            (rest.pullbackCenterIdx (Scheme.Hom.blowUpMap u D) ⟨j', hj'⟩)).support,
            ((rest.pullback (Scheme.Hom.blowUpMap u D)).weakTransformSeq
              ((I.weakTransform D).comap (Scheme.Hom.blowUpMap u D))
              (rest.pullbackStageIdx (Scheme.Hom.blowUpMap u D)
                  ⟨j', Nat.lt_succ_of_lt hj'⟩)).ord y = c := by
        intro j' hj'
        obtain ⟨c', hc'⟩ := hpt (j' + 1) (Nat.succ_lt_succ hj')
        refine ⟨c', fun y hy => ?_⟩
        rw [← hw]
        exact hc' y hy
      have := ih (D.blowUpπ ≫ f) (Scheme.Hom.blowUpMap u D) hC' ht
          (I.weakTransform D) hpt' j
        (Nat.lt_of_succ_lt_succ hj)
      rw [← hw] at this
      exact this

/-- The `Fin`-indexed form of `weakTransformSeq_pullback_mk_of_isOpenImmersion`. -/
theorem weakTransformSeq_pullback_of_isOpenImmersion (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (u : Y ⟶ X) [IsOpenImmersion u] (S : BlowUpSequence X)
    (hC : S.CentersInRange u) (hsm : S.IsSmooth f) (I : X.IdealSheafData)
    (hpt : ∀ (j : ℕ) (hj : j < S.length), ∃ c : ℕ,
      ∀ y ∈ ((S.pullback u).center (S.pullbackCenterIdx u ⟨j, hj⟩)).support,
        ((S.pullback u).weakTransformSeq (I.comap u)
          (S.pullbackStageIdx u ⟨j, Nat.lt_succ_of_lt hj⟩)).ord y = c)
    (i : Fin (S.length + 1)) :
    (S.pullback u).weakTransformSeq (I.comap u) (S.pullbackStageIdx u i) =
      (S.weakTransformSeq I i).comap (S.pullbackStageHom u i) := by
  obtain ⟨j, hj⟩ := i
  exact weakTransformSeq_pullback_mk_of_isOpenImmersion f n u S hC hsm I hpt j hj

end WeakTransform

end AlgebraicGeometry
