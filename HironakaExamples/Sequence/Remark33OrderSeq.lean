/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.Smooth.Graph
public import HironakaExamples.Sequence.Remark33Exceptional
import Hironaka.Resolution.Algebraic.Kol07.Remark33Warning63
import Hironaka.Scheme.BlowUp.Composite.ChartIdeal
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.AffineSpace
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.ExceptionalModel
import Hironaka.Scheme.Smooth.Origin
import Hironaka.Scheme.Snc.ChartOrigin
import Hironaka.Scheme.Snc.EtaleParameters
import Hironaka.Scheme.Snc.HasSncWith
import HironakaExamples.Sequence.Remark33Warning63
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Warning 63 on the model of Remark 33: `Π` is a smooth blow-up sequence of order `≥ 1`

In [Kol07, Warning 63] the sequence `Π` (blow up the origin `p` of `𝔸³`, then the birational
transform `C'` of the `z`-axis `C`) is a smooth blow-up sequence of order `≥ 1` starting with
`(𝔸³, I_C, 1, ∅)` in the sense of [Kol07, Definition 66]. By the recursion of Definition 66
(`isOrderGeSeq_cons_iff`) this is six clauses, treated here in turn:

* **Smooth centers.** `p` and `C` are coordinate subspaces of `𝔸³`;
  `V(x_0, …, x_{r-1}) ≅ Spec k[x_r, …, x_{n-1}]` is smooth over `k` (the standard smoothness of
  polynomial algebras, transported along `quotientCenterAlgEquiv`). The second center `C'` lies
  over the `z`-chart of `X_1 = B_p 𝔸³`, where it is `V(x', y')` again (`Cprime_comap_u_two`,
  `HironakaExamples/Sequence/Remark33Exceptional.lean`) and is the unit ideal over the other two
  charts (`Cprime_comap_u_of_lt`): the single open piece `V(C'|_{U_z}) → V(C')` covers, and `Smooth`
  is Zariski-local at the source.
* **Normal crossings.** The empty family has snc with every smooth center
  (`hasSncWith_empty_of_smooth`). Its total transform `(E_0)` has snc with `C'`: the only point of
  `C' ∩ E_0` is the origin of the `z`-chart, where the chart coordinates `x', y', z` are a regular
  system of parameters (the étale-coordinate lemma at the origin of `𝔸³`, transported along the
  stalk isomorphism of the chart) with `E_0 = (z)` and `C' = (x', y')`; at every other point of
  `C'` the divisor `E_0` is absent and adapted parameters of the smooth `C'` suffice.
* **Orders.** `ord_p I_C ≥ 1` since `I_C ≤ p`, and `ord_{C'} C' ≥ 1` (`leOrdAlong_one_of_le`), the
  marked ideal at the second stage being `C'` itself (`markedTransform_point_curve`).

Together with `not_isOrderGeSeq_seqCurvePoint` (`HironakaExamples/Sequence/Remark33Warning63.lean`)
this is the dichotomy of Warning 63: `Π` is a sequence of order `≥ 1` for `(𝔸³, I_C, 1, ∅)` and `Σ`
is not, although `Π = Σ` as morphisms.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData BlowUpSequence
  CoordinateSubspace affineBlowUpAlgebra Hironaka.Sequence.Remark33
  AlgebraicGeometry.Scheme.IdealSheafData MvPolynomial IsLocalRing

namespace Hironaka.Sequence

open AlgebraicGeometry

variable (k : Type u) [Field k]

/-! ### Coordinate subspaces of `𝔸ⁿ_k` are smooth over `k` -/

section CoordinateSubspaceSmooth

/-- `k → k[x]/(x_0, …, x_{r-1})` is smooth of relative dimension `n − r`: the quotient is the
polynomial algebra in the remaining variables (`quotientCenterAlgEquiv` and the standard
smoothness of polynomial algebras). -/
theorem smoothOfRelativeDimension_Spec_map_mk_comp_algebraMap (n r : ℕ) :
    SmoothOfRelativeDimension (Nat.card {i : Fin n // ¬ i.val < r})
      (Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (centerIdeal k n r)).comp
        (algebraMap k (MvPolynomial (Fin n) k))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{u} _), CommRingCat.hom_ofHom]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact isStandardSmoothOfRelativeDimension_algebraMap_of_algEquiv
    (quotientCenterAlgEquiv k n r).symm
    (ringHom_isStandardSmoothOfRelativeDimension_algebraMap_mvPolynomial k _)

/-- `Spec (k[x]/(x_0, …, x_{r-1})) → Spec k` is smooth. -/
theorem smooth_Spec_map_mk_comp (n r : ℕ) :
    Smooth (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal k n r))) ≫
      affineSpaceToSpec k n) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have := smoothOfRelativeDimension_Spec_map_mk_comp_algebraMap k n r
  exact SmoothOfRelativeDimension.smooth (Nat.card {i : Fin n // ¬ i.val < r}) _

/-- The coordinate subspace `V(x_0, …, x_{r-1}) ⊆ 𝔸ⁿ_k` is smooth over `k` (the smoothness of
the centers `p` and `C`). -/
theorem smooth_coordinateSubspace_subschemeι (n r : ℕ) :
    Smooth ((coordinateSubspace k n r).subschemeι ≫ affineSpaceToSpec k n) := by
  have hloc : IsZariskiLocalAtSource @Smooth.{u} :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : MorphismProperty.RespectsIso @Smooth.{u} := hloc.toRespects
  rw [prop_subschemeι_comp_iff_of_eq_specIdealSheaf (centerIdeal k n r) @Smooth.{u}
    (coordinateSubspace k n r) rfl]
  exact smooth_Spec_map_mk_comp k n r

/-- `V(J) → Spec k` is smooth for every `J` equal to a coordinate subspace (the shape in which the
restrictions of `C'` to the charts arise). -/
theorem smooth_subschemeι_comp_of_eq_coordinateSubspace {n r : ℕ}
    {J : (Spec (.of (MvPolynomial (Fin n) k))).IdealSheafData} (hJ : J = coordinateSubspace k n r) :
    Smooth (J.subschemeι ≫ affineSpaceToSpec k n) := by
  subst hJ
  exact smooth_coordinateSubspace_subschemeι k n r

end CoordinateSubspaceSmooth

/-! ### The birational transform `C'` is smooth over `k` -/

section StrictTransformSmooth

variable (e₀ : blowUp (Zs k) ≅ M k)

/-- The piece of `V(C')` over the `z`-chart is an open immersion
(`isOpenImmersion_subschemeMap_of_comap`). -/
instance isOpenImmersion_subschemeMap_Cprime :
    IsOpenImmersion (subschemeMap ((Cprime k).comap (u k e₀ 2)) (Cprime k) (u k e₀ 2)
      (le_map_comap _ _)) :=
  isOpenImmersion_subschemeMap_of_comap (u k e₀ 2) (Cprime k) _ rfl _

/-- Every point of `V(C')` lies over the `z`-chart: `C'` is the unit ideal over the other two. -/
theorem exists_u_two_eq_of_mem_support (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k))
    {y : blowUp (Zs k)} (hy : y ∈ (Cprime k).support) : ∃ w, u k e₀ 2 w = y := by
  have hy' : y ∈ (⊤ : (blowUp (Zs k)).Opens) := trivial
  rw [← iSup_opensRange_u k e₀] at hy'
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
  obtain ⟨w, hw⟩ := Scheme.Hom.mem_opensRange.mp hj
  by_cases hj2 : j.val < 2
  · exfalso
    have hw' : w ∈ ((Cprime k).comap (u k e₀ j)).support := by
      rw [support_comap]
      change u k e₀ j w ∈ (Cprime k).support
      rw [hw]
      exact hy
    rw [Cprime_comap_u_of_lt k e₀ he₀ j hj2, support_top] at hw'
    have h : w ∈ ((⊥ : Closeds (Spec (.of (MvPolynomial (Fin 3) k)))) : Set _) := hw'
    rw [Closeds.coe_bot] at h
    exact h
  · have h2 : j = 2 := by
      apply Fin.ext
      have := j.isLt
      change j.val = 2
      omega
    subst h2
    exact ⟨w, hw⟩

/-- The piece over the `z`-chart covers `V(C')` (the pullback square of the closed immersions). -/
theorem exists_subschemeMap_Cprime_eq (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k))
    (x : (Cprime k).subscheme) :
    ∃ y, subschemeMap ((Cprime k).comap (u k e₀ 2)) (Cprime k) (u k e₀ 2) (le_map_comap _ _) y =
      x := by
  obtain ⟨w, hw⟩ :=
    exists_u_two_eq_of_mem_support k e₀ he₀ (subschemeι_mem_support (Cprime k) x)
  have sq : IsPullback ((Cprime k).comap (u k e₀ 2)).subschemeι
      (subschemeMap ((Cprime k).comap (u k e₀ 2)) (Cprime k) (u k e₀ 2) (le_map_comap _ _))
      (u k e₀ 2) (Cprime k).subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (subschemeMap_subschemeι _ _ _ _).symm
      (by rw [ker_subschemeι, ker_subschemeι])
  obtain ⟨z, -, hz⟩ := Scheme.exists_preimage_of_isPullback sq w x hw
  exact ⟨z, hz⟩

/-- The chart `U_z → X_1 → 𝔸³ → Spec k` is the structure map of `Spec k[x', y', z]`. -/
theorem u_two_π_comp_structure (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) :
    u k e₀ 2 ≫ blowUpπ (Zs k) ≫ affineSpaceToSpec k 3 = affineSpaceToSpec k 3 := by
  rw [← Category.assoc, u_π k e₀ he₀ 2, Category.assoc]
  exact modelChart_π_comp_structure k 3 3 2 (by decide)

/-- The smoothness of the second center: the birational transform `C'` of the `z`-axis is smooth
over `k`. -/
theorem smooth_Cprime_subschemeι (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) :
    Smooth ((Cprime k).subschemeι ≫ blowUpπ (Zs k) ≫ affineSpaceToSpec k 3) := by
  have hloc : IsZariskiLocalAtSource @Smooth.{u} :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  let 𝒰 : Scheme.OpenCover.{u} (Cprime k).subscheme :=
    Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ => ((Cprime k).comap (u k e₀ 2)).subscheme)
      (fun _ => subschemeMap ((Cprime k).comap (u k e₀ 2)) (Cprime k) (u k e₀ 2)
        (le_map_comap _ _))
      (fun x => ⟨⟨⟩, exists_subschemeMap_Cprime_eq k e₀ he₀ x⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) 𝒰 fun _ => ?_
  change Smooth (subschemeMap ((Cprime k).comap (u k e₀ 2)) (Cprime k) (u k e₀ 2)
    (le_map_comap _ _) ≫ (Cprime k).subschemeι ≫ blowUpπ (Zs k) ≫ affineSpaceToSpec k 3)
  rw [← Category.assoc, subschemeMap_subschemeι, Category.assoc, u_two_π_comp_structure k e₀ he₀]
  exact smooth_subschemeι_comp_of_eq_coordinateSubspace k (Cprime_comap_u_two k e₀ he₀)

end StrictTransformSmooth

/-! ### Stalks and supports of the ideal sheaves of ideals on `Spec R` -/

section SpecStalk

variable {R : Type u} [CommRing R]

/-- `AlgebraicGeometry.stalkIdeal_specIdealSheaf` (the stalk of the ideal sheaf of `J` at `y` is
`J 𝒪_{Spec R, y}`, spelled with Mathlib's `toStalk`) in the spelling of the germs of global
sections: `toStalk R y = toOpen R ⊤ ≫ germ` and `(ΓSpecIso R).inv = toOpen R ⊤`
definitionally. -/
theorem stalkIdeal_specIdealSheaf_germ (J : Ideal R) (y : Spec (.of R)) :
    (specIdealSheaf J).stalkIdeal y =
      J.map (((Spec (.of R)).presheaf.germ ⊤ y trivial).hom.comp
        (Scheme.ΓSpecIso (.of R)).inv.hom) :=
  stalkIdeal_specIdealSheaf J y

end SpecStalk

/-! ### The normal crossings of `E_0` with `C'` -/

section Snc

variable (e₀ : blowUp (Zs k) ≅ M k)

/-- The étale-coordinate lemma (`exists_span_eq_maximalIdeal_of_etale_coordinates`) at the origin
of `𝔸³`, on the stalk: a regular system of parameters of `𝒪_{𝔸³,0}` containing the germs of
`x, y, z`. -/
theorem exists_regularSystem_origin :
    ∃ (m : ℕ) (z : Fin m → (affine3 k).presheaf.stalk (origin k 3)),
      (Ideal.span (Set.range z) = maximalIdeal ((affine3 k).presheaf.stalk (origin k 3)) ∧
        (m : WithBot ℕ∞) = ringKrullDim ((affine3 k).presheaf.stalk (origin k 3))) ∧
      ∃ σ : Fin 3 → Fin m, Function.Injective σ ∧
        ∀ c, z (σ c) = ((affine3 k).presheaf.germ ⊤ (origin k 3) trivial).hom
          ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 3) k))).inv.hom (X c)) := by
  have hprime : (origin k 3).asIdeal.IsPrime := (origin k 3).isPrime
  have hy : (MvPolynomial.aeval (R := k) (X : Fin 3 → MvPolynomial (Fin 3) k)).toRingHom.Etale := by
    rw [aeval_X_left]
    exact RingHom.Etale.of_bijective (f := (AlgHom.id k (MvPolynomial (Fin 3) k)).toRingHom)
      Function.bijective_id
  obtain ⟨-, m, z, ⟨hspan, hdim⟩, σ, hσinj, hσ⟩ :=
    exists_span_eq_maximalIdeal_of_etale_coordinates X hy (origin k 3).asIdeal
  let E₁ : (affine3 k).presheaf.stalk (origin k 3) ≃+*
      Localization.AtPrime (origin k 3).asIdeal :=
    (Spec.stalkIso (.of (MvPolynomial (Fin 3) k)) (origin k 3)).commRingCatIsoToRingEquiv
  refine ⟨m, fun l => E₁.symm (z l), ⟨span_range_symm_eq_maximalIdeal E₁ z hspan,
    hdim.trans (ringKrullDim_eq_of_ringEquiv E₁).symm⟩,
    fun c => σ ⟨c, X_mem_origin_asIdeal k 3 c⟩, fun c c' h => congrArg Subtype.val (hσinj h),
    fun c => ?_⟩
  have h := congrArg (fun φ : CommRingCat.of (MvPolynomial (Fin 3) k) ⟶ _ => φ (X c))
    (Spec.algebraMap_stalkIso_inv (R := .of (MvPolynomial (Fin 3) k)) (x := origin k 3))
  change E₁.symm (z (σ ⟨c, _⟩)) = _
  rw [hσ]
  exact h

/-- The only point of `C' ∩ E_0` is the origin of the `z`-chart. -/
theorem eq_origin_of_mem_support (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) {w : affine3 k}
    (hC : u k e₀ 2 w ∈ (Cprime k).support) (hE : u k e₀ 2 w ∈ (Ezero k).support) :
    w = origin k 3 := by
  have h1 : w ∈ ((Cprime k).comap (u k e₀ 2)).support := by
    rw [support_comap]
    exact hC
  have h2 : w ∈ ((Ezero k).comap (u k e₀ 2)).support := by
    rw [support_comap]
    exact hE
  rw [Cprime_comap_u_two k e₀ he₀] at h1
  rw [Ezero_comap_u k e₀ he₀ 2] at h2
  have h1' := (mem_support_specIdealSheaf_iff (centerIdeal k 3 2) w).mp h1
  have h2' := (mem_support_specIdealSheaf_iff (excChart k 2) w).mp h2
  rw [excChart, map_centerIdeal_three_subst] at h2'
  rw [eq_origin_iff_forall_X_mem]
  intro i
  by_cases hi : i.val < 2
  · exact h1' (X_mem_centerIdeal k 3 2 hi)
  · have h2i : i = 2 := by
      apply Fin.ext
      have := i.isLt
      change i.val = 2
      omega
    subst h2i
    exact h2' (Ideal.mem_span_singleton_self _)

/-- At the origin `a₀` of the `z`-chart the chart coordinates `x', y', z` (the regular system of
parameters of `𝒪_{𝔸³,0}` transported along the chart) exhibit `E_0 = (z)` and `C' = (x', y')`. -/
theorem exists_isSncAt_origin (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) :
    ∃ (n : ℕ) (z : Fin n → (blowUp (Zs k)).presheaf.stalk (u k e₀ 2 (origin k 3))),
      ((DivisorFamily.empty (affine3 k)).totalTransform (Zs k)).IsSncAt
        (u k e₀ 2 (origin k 3)) z ∧
      ∃ s : Finset (Fin n), (Cprime k).stalkIdeal (u k e₀ 2 (origin k 3)) =
        Ideal.span (z '' ↑s) := by
  obtain ⟨m, z, ⟨hspan, hdim⟩, σ, hσinj, hgerm⟩ := exists_regularSystem_origin k
  let E₂ : (blowUp (Zs k)).presheaf.stalk (u k e₀ 2 (origin k 3)) ≃+*
      (affine3 k).presheaf.stalk (origin k 3) :=
    (asIso ((u k e₀ 2).stalkMap (origin k 3))).commRingCatIsoToRingEquiv
  have hbij : Function.Bijective ((u k e₀ 2).stalkMap (origin k 3)).hom := E₂.bijective
  -- inverse image along the stalk map is the image under the inverse equivalence
  have key : ∀ I : Ideal ((affine3 k).presheaf.stalk (origin k 3)),
      Ideal.comap ((u k e₀ 2).stalkMap (origin k 3)).hom I = I.map E₂.symm := fun I => by
    rw [Ideal.map_symm]
    rfl
  -- `E_0` at `a₀`
  have hE0 : (Ezero k).stalkIdeal (u k e₀ 2 (origin k 3)) = Ideal.span {E₂.symm (z (σ 2))} := by
    have h := stalkIdeal_comap (Ezero k) (u k e₀ 2) (origin k 3)
    rw [Ezero_comap_u k e₀ he₀ 2, excChart, map_centerIdeal_three_subst,
      stalkIdeal_specIdealSheaf_germ, Ideal.map_span, Set.image_singleton, RingHom.comp_apply,
      ← hgerm 2] at h
    rw [← Ideal.comap_map_of_bijective (I := (Ezero k).stalkIdeal (u k e₀ 2 (origin k 3))) _ hbij,
      ← h, key, Ideal.map_span, Set.image_singleton]
  -- `C'` at `a₀`
  have hC : (Cprime k).stalkIdeal (u k e₀ 2 (origin k 3)) =
      Ideal.span ((fun l => E₂.symm (z l)) '' ↑({σ 0, σ 1} : Finset (Fin m))) := by
    have h := stalkIdeal_comap (Cprime k) (u k e₀ 2) (origin k 3)
    have hset : (CoordinateSubspace.center 3 2 : Set (Fin 3)) = {0, 1} := by
      ext i
      fin_cases i <;> simp [CoordinateSubspace.center]
    rw [Cprime_comap_u_two k e₀ he₀, Ys, coordinateSubspace,
      stalkIdeal_specIdealSheaf_germ, centerIdeal, coordinateIdeal, Ideal.map_span,
      Set.image_image, hset, Set.image_pair] at h
    simp only [RingHom.comp_apply] at h
    rw [← hgerm 0, ← hgerm 1] at h
    rw [← Ideal.comap_map_of_bijective (I := (Cprime k).stalkIdeal (u k e₀ 2 (origin k 3))) _ hbij,
      ← h, key, Finset.coe_pair, Set.image_pair, Ideal.map_span, Set.image_pair]
  refine ⟨m, fun l => E₂.symm (z l), ⟨⟨span_range_symm_eq_maximalIdeal E₂ z hspan,
    hdim.trans (ringKrullDim_eq_of_ringEquiv E₂).symm⟩, fun _ => σ 2, ?_, ?_⟩, {σ 0, σ 1}, hC⟩
  · rintro ⟨i, -⟩ ⟨j, -⟩ -
    rcases i with i | i
    · exact i.elim
    rcases j with j | j
    · exact j.elim
    rfl
  · rintro ⟨i, hi⟩
    rcases i with i | i
    · exact i.elim
    exact hE0

/-- The normal crossings at the second stage: the total transform `(E_0)` of the empty family has
simple normal crossings with the center `C'`. -/
theorem hasSncWith_totalTransform_empty_Cprime (he₀ : e₀.hom ≫ πm k = blowUpπ (Zs k)) :
    ((DivisorFamily.empty (affine3 k)).totalTransform (Zs k)).HasSncWith (Cprime k) := by
  have hπf : Smooth (blowUpπ (Zs k) ≫ affineSpaceToSpec k 3) := by
    have := smoothOfRelativeDimension_blowUpπ_coordinateSubspace k 3 3
    exact SmoothOfRelativeDimension.smooth 3 _
  have hC' : Smooth ((Cprime k).subschemeι ≫ blowUpπ (Zs k) ≫ affineSpaceToSpec k 3) :=
    smooth_Cprime_subschemeι k e₀ he₀
  intro a' ha'
  by_cases hE : a' ∈ (Ezero k).support
  · obtain ⟨w, rfl⟩ := exists_u_two_eq_of_mem_support k e₀ he₀ ha'
    obtain rfl := eq_origin_of_mem_support k e₀ he₀ ha' hE
    exact exists_isSncAt_origin k e₀ he₀
  · obtain ⟨m, c, y, -, hdim, hmax, hZ⟩ :=
      exists_adaptedParameters_of_smooth (blowUpπ (Zs k) ≫ affineSpaceToSpec k 3) (Cprime k) ha'
    have hidx : ∀ i : {i : ((DivisorFamily.empty (affine3 k)).totalTransform (Zs k)).ι //
        a' ∈ (((DivisorFamily.empty (affine3 k)).totalTransform (Zs k)).component i).support},
        False := by
      rintro ⟨i, hi⟩
      rcases i with i | i
      · exact i.elim
      · exact hE hi
    refine ⟨m, y, ⟨⟨hmax.symm, hdim⟩, fun i => (hidx i).elim, fun i => (hidx i).elim,
      fun i => (hidx i).elim⟩, Finset.univ.filter (fun j : Fin m => j.val < c), ?_⟩
    change (Cprime k).stalkIdeal a' = _
    rw [hZ]
    congr 2
    ext j
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]

end Snc

/-! ### `Π` is a smooth blow-up sequence of order `≥ 1` -/

section Assembly

/-- The marked transform of `C` under the point blow-up is `C'` (`markedTransform_point_curve` for
the coordinate subspaces). -/
theorem markedTransform_Zs_Ys : (Ys k).markedTransform (Zs k) 1 = Cprime k := by
  refine (eq_markedTransform_of_pow_mul_eq (Zs k) (Ys k) 1 (Cprime k) ?_).symm
  rw [pow_one]
  exact (coordinateSubspace_comap_eq k).symm

/-- `Π` is a smooth blow-up sequence of order `≥ 1` starting with `(𝔸³, I_C, 1, ∅)`, stated for
the coordinate subspaces `Zs` and `Ys`. -/
theorem isOrderGeSeq_Cprime :
    (cons (affine3 k) (Zs k) (cons _ (Cprime k) (nil _))).IsOrderGeSeq (affineSpaceToSpec k 3)
      (Ys k) 1 (DivisorFamily.empty (affine3 k)) := by
  obtain ⟨e₀, he₀⟩ := exists_iso_blowUp_coordinateSubspace k 3 3
  have hf : Smooth (affineSpaceToSpec k 3) := by
    have := smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k 3
    exact SmoothOfRelativeDimension.smooth 3 _
  have hZ : Smooth ((Zs k).subschemeι ≫ affineSpaceToSpec k 3) :=
    smooth_coordinateSubspace_subschemeι k 3 3
  rw [isOrderGeSeq_cons_iff, isOrderGeSeq_cons_iff]
  refine ⟨⟨hZ, hasSncWith_empty_of_smooth (affineSpaceToSpec k 3) (Zs k),
    leOrdAlong_one_of_le ((specIdealSheaf_le_iff _ _).mpr (centerIdeal_two_le k))⟩,
    ⟨smooth_Cprime_subschemeι k e₀ he₀, hasSncWith_totalTransform_empty_Cprime k e₀ he₀, ?_⟩,
    isOrderGeSeq_nil _ _ _ _⟩
  rw [markedTransform_Zs_Ys]
  exact leOrdAlong_one_of_le le_rfl

/-- The same for centers given by equations (the shape of `seqPointCurve`). -/
theorem isOrderGeSeq_aux {p C : (affine3 k).IdealSheafData} (hp : p = Zs k) (hC : C = Ys k) :
    (cons (affine3 k) p (cons _ (C.strictTransform p) (nil _))).IsOrderGeSeq
      (affineSpaceToSpec k 3) C 1 (DivisorFamily.empty (affine3 k)) := by
  subst hp hC
  exact isOrderGeSeq_Cprime k

/-- [Kol07, Warning 63]: `Π` is a smooth blow-up sequence of order `≥ 1` starting with
`(𝔸³, I_C, 1, ∅)` (whereas `Σ` is not, `not_isOrderGeSeq_seqCurvePoint`). -/
theorem isOrderGeSeq_seqPointCurve :
    (seqPointCurve k).IsOrderGeSeq (affineSpaceToSpec k 3) (curve k) 1
      (DivisorFamily.empty (affine3 k)) :=
  isOrderGeSeq_aux k (point_eq_coordinateSubspace k) (curve_eq_coordinateSubspace k)

end Assembly

end Hironaka.Sequence
