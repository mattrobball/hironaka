/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncDivisorSetLocal
import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.Manifold.FiniteSuccession.Functor.LocalCover
import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The snc-divisor predicate: restriction to open subspaces and locality on open-immersion covers

`AnalyticSpace.IsSncDivisorSet X Z` (at every point a chart `Sp(M) ≅ X | U` carrying an snc
hypersurface family onto `Z ∩ U`) is a local predicate. Two consequences, needed to read clause (3)
of the resolution theorem — the inverse image of the singular locus is an snc divisor set,
[Kol07, Theorem 45 (3)] — off the pieces of a gluing:

* `IsSncDivisorSet.restrictOpen`: an snc divisor set restricts to every open subspace `X | V` —
  the chart at a point of `V` shrinks to the open submanifold `M | W`, `W` the trace of `V`, the
  family pulls back along the inclusion (`isSnc_comap`, a local diffeomorphism), and the shrunk
  chart is `isoOfRangeEq` of the composite open immersion `Sp(M | W) → Sp(M) → X`, with image in
  `V`;
* `isSncDivisorSet_of_openImmersion_cover`: `Z` is an snc divisor set when its inverse image in
  every piece of a cover by open immersions is — the open-immersion form of
  `isSncDivisorSet_of_openCover` (`Hironaka/AnalyticSpace/SncDivisorSetLocal.lean`).

Not in the sources: the predicate is the chart form of Hironaka's normal crossings
[Hir64, Ch. 0, §5, Definition 2] and of [Kol07, Definition 24]. Used by
`Hironaka/AnalyticSpace/Glue/OverSnc.lean`.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology AlgebraicGeometry
open AnalyticSpace.KLocallyRingedSpace Manifold

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

/-- **An snc divisor set restricts to every open subspace**: at `x ∈ V` the chart `Sp(M) ≅ X | U`
of `Z` shrinks to the open submanifold `M | W`, `W` the points of `M` carried into `V`; the
composite `Sp(M | W) → Sp(M) → X | U → X` is an open immersion with image in `V`, so `isoOfRangeEq`
identifies `Sp(M | W)` with `(X | V) | U'`, `U'` its image; the family `F.comap (M.inclusion W)` is
snc (`isSnc_comap` along the local diffeomorphism `isLocalDiffeomorph_inclusion`) with support the
trace of `|F|` (`support_comap`). -/
theorem IsSncDivisorSet.restrictOpen {X : AnalyticSpace.{u} K} {Z : Set X}
    (hZ : IsSncDivisorSet X Z) (V : Opens X) :
    IsSncDivisorSet (X.restrictOpen V) (Subtype.val ⁻¹' Z) := by
  intro x
  obtain ⟨d, M, U, hxU, e, F, hF, hsupp⟩ := hZ x.1
  -- the opens of `X`, read on the `K`-space
  let U₀ : Opens X.toKLocallyRingedSpace := ⟨(U : Set X), U.isOpen⟩
  let V₀ : Opens X.toKLocallyRingedSpace := ⟨(V : Set X), V.isOpen⟩
  -- the chart's open immersion into `X`
  have hehom : LocallyRingedSpace.IsOpenImmersion e.hom.1 := by
    have := KIso.isIso_hom_val e
    infer_instance
  have hoU : LocallyRingedSpace.IsOpenImmersion (ofRestrict X.toKLocallyRingedSpace U₀).1 :=
    inferInstance
  obtain ⟨c, hc⟩ : ∃ c : (toSpace (ContinuousLinearEquiv.refl K (Fin d → K))
      M).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace,
      c = e.hom ≫ ofRestrict X.toKLocallyRingedSpace U₀ := ⟨_, rfl⟩
  have hcoi : LocallyRingedSpace.IsOpenImmersion c.1 := by
    rw [hc]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.hom.1 hehom
      (ofRestrict X.toKLocallyRingedSpace U₀).1 hoU
  have hce : ∀ p : (toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) M).toKLocallyRingedSpace,
      KLocallyRingedSpace.Hom.toFun c p = (KLocallyRingedSpace.Hom.toFun e.hom p).1 := by
    intro p
    rw [hc]
    rfl
  -- the trace of `V` on `M`, and the shrunk chart's open immersion into `X`
  let W : Opens M := ⟨KLocallyRingedSpace.Hom.toFun c ⁻¹' (V : Set X),
    V.isOpen.preimage (KLocallyRingedSpace.Hom.continuous_toFun c)⟩
  obtain ⟨c', hc'⟩ : ∃ c' : (toSpace (ContinuousLinearEquiv.refl K (Fin d → K))
      (M.restrict W)).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace,
      c' = (toSpaceHom (ContinuousLinearEquiv.refl K (Fin d → K)) (M.inclusion W) :
        (toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) (M.restrict W)).toKLocallyRingedSpace ⟶
          (toSpace (ContinuousLinearEquiv.refl K (Fin d → K)) M).toKLocallyRingedSpace) ≫ c :=
    ⟨_, rfl⟩
  have hc'oi : LocallyRingedSpace.IsOpenImmersion c'.1 := by
    rw [hc']
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (toSpaceHom (ContinuousLinearEquiv.refl K (Fin d → K)) (M.inclusion W)).1
      (isOpenImmersion_ofManifoldHom_val W) c.1 hcoi
  have hc'm : ∀ m : M.restrict W,
      KLocallyRingedSpace.Hom.toFun c' m = KLocallyRingedSpace.Hom.toFun c m.1 := by
    intro m
    rw [hc']
    rfl
  have hrangeV : range (KLocallyRingedSpace.Hom.toFun c') ⊆ (V : Set X) := by
    rintro _ ⟨m, rfl⟩
    exact (congrArg (fun q => q ∈ (V : Set X)) (hc'm m)).mpr m.2
  -- the image open of `X|V` and the chart
  let U' : Opens (X.restrictOpen V) :=
    ⟨Subtype.val ⁻¹' range (KLocallyRingedSpace.Hom.toFun c'),
      (isOpen_range_toFun c').preimage continuous_subtype_val⟩
  have hoU' : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (X.restrictOpen V).toKLocallyRingedSpace U').1 := inferInstance
  have hoV : LocallyRingedSpace.IsOpenImmersion (ofRestrict X.toKLocallyRingedSpace V₀).1 :=
    inferInstance
  obtain ⟨ι', hι'⟩ : ∃ ι' : (X.restrictOpen V).toKLocallyRingedSpace.restrictOpen U' ⟶
      X.toKLocallyRingedSpace,
      ι' = ofRestrict (X.restrictOpen V).toKLocallyRingedSpace U' ≫
        ofRestrict X.toKLocallyRingedSpace V₀ := ⟨_, rfl⟩
  have hι'oi : LocallyRingedSpace.IsOpenImmersion ι'.1 := by
    rw [hι']
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (ofRestrict (X.restrictOpen V).toKLocallyRingedSpace U').1 hoU'
      (ofRestrict X.toKLocallyRingedSpace V₀).1 hoV
  have hι'u : ∀ u : (X.restrictOpen V).toKLocallyRingedSpace.restrictOpen U',
      KLocallyRingedSpace.Hom.toFun ι' u = u.1.1 := by
    intro u
    rw [hι']
    rfl
  have hrange : range (KLocallyRingedSpace.Hom.toFun c') =
      range (KLocallyRingedSpace.Hom.toFun ι') := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨⟨⟨KLocallyRingedSpace.Hom.toFun c' m, hrangeV ⟨m, rfl⟩⟩, ⟨m, rfl⟩⟩, hι'u _⟩
    · rintro ⟨u, rfl⟩
      rw [hι'u]
      exact u.2
  let φ := isoOfRangeEq c' ι' hrange
  have hφ : ∀ m, (KLocallyRingedSpace.Hom.toFun φ.hom m).1.1 =
      KLocallyRingedSpace.Hom.toFun c' m := fun m =>
    (hι'u _).symm.trans (congrArg (fun k => KLocallyRingedSpace.Hom.toFun k m)
      (isoOfRangeEq_hom_comp c' ι' hrange))
  -- `x` lies in the image: `x.1 = c (e⁻¹ ⟨x.1, hxU⟩)`
  have hinv : ∀ q : X.toKLocallyRingedSpace.restrictOpen U,
      KLocallyRingedSpace.Hom.toFun e.hom (KLocallyRingedSpace.Hom.toFun e.inv q) = q := fun q =>
    congrArg (fun k => KLocallyRingedSpace.Hom.toFun k q) e.inv_hom_id
  have hcx : KLocallyRingedSpace.Hom.toFun c
      (KLocallyRingedSpace.Hom.toFun e.inv ⟨x.1, hxU⟩) = x.1 :=
    (hce _).trans (congrArg Subtype.val (hinv ⟨x.1, hxU⟩))
  have hx' : x ∈ U' := by
    refine ⟨⟨KLocallyRingedSpace.Hom.toFun e.inv ⟨x.1, hxU⟩, ?_⟩, (hc'm _).trans hcx⟩
    exact (congrArg (fun q => q ∈ (V : Set X)) hcx).mpr x.2
  -- the support equation of the original chart, pointwise
  have hZe : ∀ p : M, p ∈ F.support ↔ (KLocallyRingedSpace.Hom.toFun e.hom p).1 ∈ Z := by
    intro p
    constructor
    · intro hp
      exact ((Set.ext_iff.mp hsupp _).mp ⟨_, ⟨p, hp, rfl⟩, rfl⟩).1
    · intro hp
      obtain ⟨q, ⟨p', hp', hqp'⟩, hq⟩ :=
        (Set.ext_iff.mp hsupp _).mpr ⟨hp, (KLocallyRingedSpace.Hom.toFun e.hom p).2⟩
      have hpp : p' = p := (KIso.homeomorph e).injective ((hqp'.trans (Subtype.ext hq)) :
        KIso.homeomorph e p' = KIso.homeomorph e p)
      exact hpp ▸ hp'
  refine ⟨d, M.restrict W, U', hx', φ, F.comap (M.inclusion W),
    HypersurfaceFamily.isSnc_comap hF (M.inclusion W) (isLocalDiffeomorph_inclusion M W), ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have hm' : m.1 ∈ F.support :=
      (Set.ext_iff.mp (HypersurfaceFamily.support_comap (M.inclusion W) F) m).mp hm
    refine ⟨?_, (KLocallyRingedSpace.Hom.toFun φ.hom m).2⟩
    exact (congrArg (fun q => q ∈ Z) ((hφ m).trans ((hc'm m).trans (hce m.1)))).mpr
      ((hZe m.1).mp hm')
  · rintro ⟨hyZ, hyU'⟩
    obtain ⟨m, hm⟩ := hyU'
    have hmZ : (KLocallyRingedSpace.Hom.toFun e.hom m.1).1 ∈ Z :=
      (congrArg (fun q => q ∈ Z) ((hce m.1).symm.trans ((hc'm m).symm.trans hm))).mpr hyZ
    refine ⟨KLocallyRingedSpace.Hom.toFun φ.hom m, ⟨m, ?_, rfl⟩, ?_⟩
    · exact (Set.ext_iff.mp (HypersurfaceFamily.support_comap (M.inclusion W) F) m).mpr
        ((hZe m.1).mpr hmZ)
    · exact Subtype.ext ((hφ m).trans hm)

/-- **The snc-divisor predicate is local on the target of a cover by open immersions**: `Z` is an
snc divisor set of `X` when its inverse image in every piece `A i` is — at `x = g i a` the chart
`Sp(M) ≅ (A i) | U'` at `a`, composed with the identification of `(A i) | U'` with its image open
in `X` (`isoOfRangeEq` of `ofRestrict ≫ g i`), is a chart of `X` at `x`, and the support equation
is read through `g i`. The open-immersion form of `isSncDivisorSet_of_openCover`
(`Hironaka/AnalyticSpace/SncDivisorSetLocal.lean`). -/
theorem isSncDivisorSet_of_openImmersion_cover (X : AnalyticSpace.{u} K)
    (Z : Set X)
    {ι : Type*} (A : ι → AnalyticSpace.{u} K)
    (g : ∀ i, (A i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace)
    [hg : ∀ i, LocallyRingedSpace.IsOpenImmersion (g i).1]
    (hcov : ∀ x : X, ∃ (i : ι) (a : A i), KLocallyRingedSpace.Hom.toFun (g i) a = x)
    (h : ∀ i, IsSncDivisorSet (A i)
      (KLocallyRingedSpace.Hom.toFun (g i) ⁻¹' Z)) :
    IsSncDivisorSet X Z := by
  intro x
  obtain ⟨i, a, rfl⟩ := hcov x
  obtain ⟨d, M, U', haU', e, F, hF, hsupp⟩ := h i a
  -- the chart's open, read on the `K`-space; the open immersion of the chart's open into `X`
  let U'₀ : Opens (A i).toKLocallyRingedSpace := ⟨(U' : Set (A i)), U'.isOpen⟩
  have hoU' : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict (A i).toKLocallyRingedSpace U'₀).1 := inferInstance
  obtain ⟨c, hc⟩ : ∃ c : (A i).toKLocallyRingedSpace.restrictOpen U'₀ ⟶ X.toKLocallyRingedSpace,
      c = ofRestrict (A i).toKLocallyRingedSpace U'₀ ≫ g i := ⟨_, rfl⟩
  have hcoi : LocallyRingedSpace.IsOpenImmersion c.1 := by
    rw [hc]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (ofRestrict (A i).toKLocallyRingedSpace U'₀).1 hoU' (g i).1 (hg i)
  have hcw : ∀ w : (A i).toKLocallyRingedSpace.restrictOpen U'₀,
      KLocallyRingedSpace.Hom.toFun c w = KLocallyRingedSpace.Hom.toFun (g i) w.1 := by
    intro w
    rw [hc]
    rfl
  let Ui : Opens X.toKLocallyRingedSpace :=
    ⟨range (KLocallyRingedSpace.Hom.toFun c), isOpen_range_toFun c⟩
  have hrange : range (KLocallyRingedSpace.Hom.toFun c) =
      range (KLocallyRingedSpace.Hom.toFun (ofRestrict X.toKLocallyRingedSpace Ui)) :=
    (range_toFun_ofRestrict X.toKLocallyRingedSpace Ui).symm
  let φ := isoOfRangeEq c (ofRestrict X.toKLocallyRingedSpace Ui) hrange
  have hφ : ∀ w, (KLocallyRingedSpace.Hom.toFun φ.hom w).1 =
      KLocallyRingedSpace.Hom.toFun c w := fun w =>
    congrArg (fun k => KLocallyRingedSpace.Hom.toFun k w) (isoOfRangeEq_hom_comp c _ hrange)
  refine ⟨d, M, Ui, ⟨⟨a, haU'⟩, (hcw _)⟩, e ≪≫ φ, F, hF, ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    have h1 := (Set.ext_iff.mp hsupp (KLocallyRingedSpace.Hom.toFun e.hom m).1).mp
      ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨?_, (KLocallyRingedSpace.Hom.toFun φ.hom (KLocallyRingedSpace.Hom.toFun e.hom m)).2⟩
    exact (congrArg (fun q => q ∈ Z) ((hφ _).trans (hcw _))).mpr h1.1
  · rintro ⟨hyZ, hyU⟩
    obtain ⟨w, hw⟩ := hyU
    have hwZ : w.1 ∈ KLocallyRingedSpace.Hom.toFun (g i) ⁻¹' Z ∩ (U' : Set (A i)) :=
      ⟨(congrArg (fun q => q ∈ Z) ((hcw w).symm.trans hw)).mpr hyZ, w.2⟩
    obtain ⟨q, ⟨m, hm, hqm⟩, hq⟩ := (Set.ext_iff.mp hsupp _).mpr hwZ
    have hqw : q = w := Subtype.ext hq
    refine ⟨KLocallyRingedSpace.Hom.toFun φ.hom w, ⟨m, hm, ?_⟩, ?_⟩
    · exact congrArg (KLocallyRingedSpace.Hom.toFun φ.hom) (hqm.trans hqw)
    · exact (hφ w).trans hw

end AnalyticSpace

end
