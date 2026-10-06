/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Manifold.Defs
public import Hironaka.AnalyticSpace.Restrict.Defs
public import Hironaka.Manifold.Snc.Defs
public import Hironaka.AnalyticSpace.OpenSubspaceLemmas
import Hironaka.AnalyticSpace.Glue
import Hironaka.AnalyticSpace.RestrictToIso
import Hironaka.Manifold.Snc.Dense
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Simple normal crossings divisor sets: locality and density of the complement

`AnalyticSpace.IsSncDivisorSet X Z`, defined here: every point has an open neighbourhood `U` and a
`K`-isomorphism `e : Sp(M) ≅ X | U` with the space of an analytic manifold carrying an snc
hypersurface family `F` whose support `e` maps onto `Z ∩ U`. Clause (3) of the resolution theorem,
[Kol07, Theorem 45 (3)], is checked in this form on the pieces of a gluing.

* `isSncDivisorSet_of_openCover`: the predicate is local on the space — a chart of the open
  subspace `X | Vᵢ` at a point is a chart of `X` there, through `restrictOpen_restrictOpen_iso`
  (`(X | Vᵢ) | U' ≅ X | imageOpens`, `Hironaka/AnalyticSpace/OpenSubspaceLemmas.lean`), the support
  equation read through `Subtype.val`;
* `IsSncDivisorSet.dense_compl`: the complement of an snc divisor set is dense — in each chart the
  complement of the support of an snc family is dense in the manifold
  (`HypersurfaceFamily.IsSnc.dense_compl_support`, `Hironaka/Manifold/Snc/Dense.lean`),
  transported along the homeomorphism underlying `e`. This gives the range clause of the
  resolution theorem its content (`Hironaka/Resolution/Analytic/Kol07Thm45/ResolutionSnc.lean`);
  compare [Hir64, Introduction] (the simple locus of a reduced complex space is dense) and
  [BM97, Remarks 1.7 (2)] (`X.regularLocus` Zariski-dense in a geometric space);
* `val_toFun_restrictOpen_restrictOpen_iso_hom`: the point of `X` under the
  restriction-of-restriction isomorphism.

Used by `Hironaka/AnalyticSpace/SncBoundaryChart.lean` and
`Hironaka/AnalyticSpace/SncDivisorSetCover.lean`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- `Z` is the set of points of a simple normal crossings divisor of the non-singular space `X`
([Kol07, Theorem 45 (3)]; Hironaka's Definition 2 with `D = X`, [Hir64, Ch. 0, §5]): every point
`x` has an open neighbourhood `U` and a `K`-isomorphism `e : Sp(M) ≅ X | U` with the space
`Sp(M)` of an analytic manifold `M` modelled on `K^d` (`AnalyticSpace.toSpace`; on a
non-singular space such charts exist) carrying a simple normal crossings hypersurface family `F`
on `M` (`HypersurfaceFamily.IsSnc`) whose support `e` maps onto `Z ∩ U`. The coordinates on `K^d`
are the identity. -/
def IsSncDivisorSet (X : AnalyticSpace.{u} K) (Z : Set X) : Prop :=
  ∀ x : X, ∃ (d : ℕ) (M : AnalyticManifold.{u} K (Fin d → K))
    (U : TopologicalSpace.Opens X) (_ : x ∈ U)
    (e : AnalyticSpace.KLocallyRingedSpace.KIso
      (AnalyticSpace.toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) M).toKLocallyRingedSpace
      ((AnalyticSpace.toKLocallyRingedSpace X).restrictOpen U))
    (F : Manifold.HypersurfaceFamily M),
    F.IsSnc (ContinuousLinearEquiv.refl K (Fin d → K)) ∧
      Subtype.val '' (AnalyticSpace.KLocallyRingedSpace.Hom.toFun e.hom '' F.support) =
        Z ∩ (U : Set X)

/-- The point of `A` under the restriction-of-restriction isomorphism `(A|U)|V ≅ A|imageOpens U V`
is the point of `A` under the two inclusions. -/
theorem val_toFun_restrictOpen_restrictOpen_iso_hom {A : KLocallyRingedSpace.{u} K} (U : Opens A)
    (V : Opens (A.restrictOpen U)) (w : (A.restrictOpen U).restrictOpen V) :
    (KLocallyRingedSpace.Hom.toFun (restrictOpen_restrictOpen_iso U V).hom w).1 = w.1.1 := by
  have h : (restrictOpen_restrictOpen_iso U V).hom ≫ ofRestrict A (imageOpens U V) =
      ofRestrict (A.restrictOpen U) V ≫ ofRestrict A U := by
    rw [← restrictOpen_restrictOpen_iso_inv_comp A U V, Iso.hom_inv_id_assoc]
  exact congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ w) h

/-- The snc-divisor-set property is local on the space: it holds when it holds on the open
subspaces of an open cover ([Kol07, Theorem 45 (3)], checked on the pieces of a gluing). At
`x ∈ Vᵢ`, the chart `e : Sp(M) ≅ (X | Vᵢ) | U'` of the hypothesis composed with
`(X | Vᵢ) | U' ≅ X | imageOpens` is a chart of `X` at `x`, and the support equation is read through
`Subtype.val`. -/
theorem isSncDivisorSet_of_openCover (X : AnalyticSpace.{u} K) (Z : Set X)
    {ι : Type*}
    (V : ι → Set X) (hV : ∀ i, IsOpen (V i)) (hcov : ⋃ i, V i = univ)
    (h :
        ∀ i, IsSncDivisorSet (X.restrictSet (V i))
            (Subtype.val ⁻¹' Z)) :
    IsSncDivisorSet X Z := by
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ V i := mem_iUnion.mp (hcov ▸ mem_univ x)
  have hx' : x ∈ openOf X (V i) := by rw [openOf_of_isOpen X (hV i)]; exact hi
  obtain ⟨d, M, U', hxU', e, F, hF, hsupp⟩ := h i ⟨x, hx'⟩
  refine ⟨d, M, imageOpens (openOf X (V i)) U', mem_imageOpens.mpr ⟨hx', hxU'⟩,
    e ≪≫ restrictOpen_restrictOpen_iso (openOf X (V i)) U', F, hF, ?_⟩
  ext y
  constructor
  · rintro ⟨w, ⟨m, hm, rfl⟩, rfl⟩
    have h1 := val_toFun_restrictOpen_restrictOpen_iso_hom (openOf X (V i)) U'
      (KLocallyRingedSpace.Hom.toFun e.hom m)
    have h2 := (Set.ext_iff.mp hsupp (KLocallyRingedSpace.Hom.toFun e.hom m).1).mp
      ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨?_, (KLocallyRingedSpace.Hom.toFun
      (restrictOpen_restrictOpen_iso (openOf X (V i)) U').hom
        (KLocallyRingedSpace.Hom.toFun e.hom m)).2⟩
    exact (congrArg (fun q => q ∈ Z) h1).mpr h2.1
  · rintro ⟨hyZ, hyI⟩
    obtain ⟨hyO, hyU'⟩ := mem_imageOpens.mp hyI
    have h2 := (Set.ext_iff.mp hsupp ⟨y, hyO⟩).mpr ⟨hyZ, hyU'⟩
    obtain ⟨w', ⟨m, hm, hmw'⟩, hw'⟩ := h2
    have hw : w' = ⟨⟨y, hyO⟩, hyU'⟩ := Subtype.ext hw'
    refine ⟨KLocallyRingedSpace.Hom.toFun (restrictOpen_restrictOpen_iso (openOf X (V i)) U').hom
      w', ⟨m, hm, ?_⟩, ?_⟩
    · exact congrArg
        (KLocallyRingedSpace.Hom.toFun (restrictOpen_restrictOpen_iso (openOf X (V i)) U').hom) hmw'
    · exact (val_toFun_restrictOpen_restrictOpen_iso_hom (openOf X (V i)) U' w').trans
        (congrArg (fun p => p.1.1) hw)

/-- The complement of an snc divisor set is dense (compare [Hir64, Introduction] and
[BM97, Remarks 1.7 (2)]): at every point, the chart `e : Sp(M) ≅ X | U` carries the dense
complement of the snc support (`IsSnc.dense_compl_support`) onto the complement of `Z` in
`X | U`. -/
theorem IsSncDivisorSet.dense_compl {X : AnalyticSpace.{u} K} {Z : Set X}
    (hZ : IsSncDivisorSet X Z) : Dense Zᶜ := by
  rw [dense_iff_inter_open]
  rintro S hS ⟨x, hxS⟩
  obtain ⟨d, M, U, hxU, e, F, hF, hsupp⟩ := hZ x
  have hdense := hF.dense_compl_support
  set ho := KIso.homeomorph e with hho
  have hT : IsOpen (ho ⁻¹' (Subtype.val ⁻¹' S)) :=
    (hS.preimage continuous_subtype_val).preimage ho.continuous
  have hne : (ho ⁻¹' (Subtype.val ⁻¹' S)).Nonempty := by
    refine ⟨ho.symm ⟨x, hxU⟩, ?_⟩
    exact (congrArg (fun q => q.1 ∈ S) (ho.apply_symm_apply ⟨x, hxU⟩)).mpr hxS
  obtain ⟨m, hmT, hms⟩ := dense_iff_inter_open.mp hdense _ hT hne
  refine ⟨(ho m).1, hmT, fun hZm => ?_⟩
  have h1 : (ho m).1 ∈ Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' F.support) :=
    (Set.ext_iff.mp hsupp (ho m).1).mpr ⟨hZm, (ho m).2⟩
  obtain ⟨p, ⟨m', hm', hpm'⟩, hp⟩ := h1
  have hmm : m' = m := ho.injective ((hpm'.trans (Subtype.ext hp)) : ho m' = ho m)
  exact hms (hmm ▸ hm')

end AnalyticSpace

end
