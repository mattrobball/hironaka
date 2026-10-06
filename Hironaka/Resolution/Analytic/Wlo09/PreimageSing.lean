/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.Snc.Trace
public import Hironaka.AnalyticSpace.SncDivisorSetLocal
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceResolution
import Hironaka.AnalyticSpace.Manifold.ClosedSub
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.AnalyticSpace.Manifold.Restrict
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.IdealSheaf.Vanishing
import Hironaka.Manifold.Snc.NonSingular
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.Principalization.MonomialStalk
import Hironaka.Resolution.Analytic.Wlo09.BoundaryBridge
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.IsoOverReg
import Hironaka.Resolution.Analytic.Wlo09.ProperSncOfEmbeddedDesing
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The preimage of the singular locus is the trace of the exceptional divisor

For an embedded desingularization functor `bed` (`bed.IsEmbeddedDesing`) and a piece `Y|_W` of an
analytic space, the local resolution map `Π = σ^r|_{Ỹ} : Ỹ → Y|_W` satisfies
`Π⁻¹((Y|_W).singularLocus) = Ỹ ∩ |E_r|` as subsets of `Ỹ`, and this set is a simple normal crossing
divisor of the non-singular space `Ỹ` (`IsSncDivisorSet`). This is clause (2) of Włodarczyk's
resolution of analytic spaces [Wlo09, Theorem 2.0.1], "the inverse image of the singular locus is a
simple normal crossing divisor", deduced from clauses (2)–(3) of [Wlo09, Theorem 2.0.2] and the fact
that the support of the exceptional divisor is the exceptional locus.

**The set equality.** A point of `E_r` lies over the image of a centre, which is not a simple point
(clause (2), `support_totalTransformSeq_subset_preimage_of_centersOver`); off `E_r` the composite is
a local isomorphism and `Ỹ` is the pullback of `Y` stalkwise
(`Hironaka/Resolution/Analytic/Wlo09/IsoOverReg.lean`), so regularity of the quotient stalks
transports (`isRegularLocalRing_quotient_strictTransformSubspaceSeq_iff_of_notMem_support`) and the
non-singularity of `Ỹ` (clause (3)) makes the image simple.

**The simple normal crossing divisor.** At a point `x` of `Ỹ`, the proper form of clause (3)
(`IsEmbeddedDesing.isProperSnc`,
`Hironaka/Resolution/Analytic/Wlo09/ProperSncOfEmbeddedDesing.lean`) gives an adapted chart `φ` of
`Ỹ` which is a simple-normal-crossing chart of `E_r` with the components' coordinates off the block
of `Ỹ`. Shrunk to a neighbourhood meeting only the components through `x`
(`IsSnc.exists_isOpen_forall_mem_of_mem`), the one chart serves every point of `Ỹ ∩ φ.source`
(`IsSncChartAt.of_forall_mem`, `IsSncChartAt.comap_transportChart`): on the open submanifold
`U := φ.source`, `Ỹ ∩ U` is a closed submanifold of codimension `c` whose ideal sheaf is `Ỹ|_U`
(`comap_inclusion_eq_idealSheaf_of_isRegularLocalRing_quotient`, through the vanishing ideals), and
the pulled-back family `E_r|_U` has proper simple normal crossings with it
(`hasSncWithProper_comap_inclusion_of_isSncChartAt`), so its trace is a simple normal crossing
divisor of the bundled submanifold (`isSnc_traceFamily`). The predicate follows
(`isSncDivisorSet_toAnalyticSpace_of_forall`): `Sp(Ỹ ∩ U) ≅ Sp(U)/𝓘 = Sp(U)/(Ỹ|_U) ≅ Ỹ|_U'`
(`closedSubmanifoldIso`, `restrictOpen_quotient_iso`), the image of the trace's support being the
trace of `|E_r|`. This is the chart-wise simple normal
crossings of [Kol07, Definition 24] read on the subspace.

Together with `Hironaka/Resolution/Analytic/Wlo09/IsoOverReg.lean` these are the clauses from which
the resolution of analytic spaces is assembled in `Hironaka/Manifold/Sequence/Restrict/`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology TopologicalSpace Manifold AnalyticSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Off the exceptional family, regularity of the quotient stalk of the strict transform is
regularity of the quotient stalk of `J` at the image: the germ map of the composite is bijective
there and carries the one stalk ideal onto the other. -/
theorem isRegularLocalRing_quotient_strictTransformSubspaceSeq_iff_of_notMem_support
    (J : IdealSheaf M) (i : Fin (S.length + 1)) {z : S.stage i}
    (hz : z ∉ (S.totalTransformSeq i).support) :
    IsRegularLocalRing ((structureSheaf 𝕜 E (S.stage i)).presheaf.stalk z ⧸
        (S.strictTransformSubspaceSeq J i).stalkIdeal z) ↔
      IsRegularLocalRing ((structureSheaf 𝕜 E M).presheaf.stalk (S.stageMap i z) ⧸
        J.stalkIdeal (S.stageMap i z)) := by
  have hst := S.stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support J i hz
  have hbij := S.germMap_stageMap_bijective_of_notMem_support i hz
  let e : (structureSheaf 𝕜 E M).presheaf.stalk (S.stageMap i z) ≃+*
      (structureSheaf 𝕜 E (S.stage i)).presheaf.stalk z := RingEquiv.ofBijective _ hbij
  have hmap : (S.strictTransformSubspaceSeq J i).stalkIdeal z =
      Ideal.map (e : (structureSheaf 𝕜 E M).presheaf.stalk (S.stageMap i z) →+*
        (structureSheaf 𝕜 E (S.stage i)).presheaf.stalk z) (J.stalkIdeal (S.stageMap i z)) := hst
  let q := Ideal.quotientEquiv (J.stalkIdeal (S.stageMap i z))
    ((S.strictTransformSubspaceSeq J i).stalkIdeal z) e hmap
  exact ⟨fun hr => IsRegularLocalRing.of_ringEquiv q.symm,
    fun hr => IsRegularLocalRing.of_ringEquiv q⟩

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

section Charts

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- Near a point of a simple normal crossing divisor only the components through the point are
met. -/
theorem _root_.Manifold.HypersurfaceFamily.IsSnc.exists_isOpen_forall_mem_of_mem
    {F : HypersurfaceFamily M}
    (hF : F.IsSnc ψ) (a : M) :
    ∃ V : Set M, IsOpen V ∧ a ∈ V ∧ ∀ j, ∀ x ∈ V, x ∈ F.hyp j → a ∈ F.hyp j := by
  classical
  obtain ⟨U, hU, hfin⟩ := hF.2.1 a
  refine ⟨interior U ∩ ⋂ j ∈ hfin.toFinset.filter (fun j => a ∉ F.hyp j), (F.hyp j)ᶜ,
    isOpen_interior.inter (isOpen_biInter_finset fun j _ => (hF.1 j).isClosed.isOpen_compl),
    ⟨mem_interior_iff_mem_nhds.mpr hU,
      Set.mem_iInter₂.mpr fun j hj => (Finset.mem_filter.mp hj).2⟩, fun j x hx hxj => ?_⟩
  by_contra haj
  have hjT : j ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨x, hxj, interior_subset hx.1⟩
  exact Set.mem_iInter₂.mp hx.2 j (Finset.mem_filter.mpr ⟨hjT, haj⟩) hxj

/-- A simple-normal-crossing chart at `a` is a simple-normal-crossing chart at every point `b` of
its source all of whose components pass through `a`, with the indices restricted. -/
theorem _root_.Manifold.HypersurfaceFamily.IsSncChartAt.of_forall_mem {F : HypersurfaceFamily M}
    {φ : OpenPartialHomeomorph M E} {a : M} {c : {j // a ∈ F.hyp j} → Fin n}
    (hc : F.IsSncChartAt ψ φ a c) {b : M} (hb : b ∈ φ.source)
    (hsub : ∀ j, b ∈ F.hyp j → a ∈ F.hyp j) :
    F.IsSncChartAt ψ φ b fun j => c ⟨j.1, hsub j.1 j.2⟩ :=
  ⟨hc.1, hb, fun j x hx => hc.2.2.1 ⟨j.1, hsub j.1 j.2⟩ x hx, fun j j' h => by
    have e := congrArg (Subtype.val : {j // a ∈ F.hyp j} → F.ι) (hc.2.2.2 h)
    exact Subtype.ext e⟩

end Charts

section Transport

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M N : AnalyticManifold.{u} 𝕜 E}

/-- A simple-normal-crossing chart of `F` at `h a` transports along a local inverse of `h` to a
simple-normal-crossing chart of the inverse image `F.comap h` at `a` (the step inside
`isSnc_comap`, made a lemma). -/
theorem _root_.Manifold.HypersurfaceFamily.IsSncChartAt.comap_transportChart
    {F : HypersurfaceFamily M}
    (h : AnalyticMap N M) {Φ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) N M ω} {a : N}
    (haΦ : a ∈ Φ.source) (hΦ : Set.EqOn h Φ Φ.source) {φ : OpenPartialHomeomorph M E}
    {c : {j // h a ∈ F.hyp j} → Fin n} (hc : F.IsSncChartAt ψ φ (h a) c) :
    (F.comap h).IsSncChartAt ψ (transportChart Φ.symm φ) a fun j => c ⟨j.1, j.2⟩ := by
  refine ⟨transportChart_mem_maximalAtlas _ hc.1, ?_, ?_, ?_⟩
  · rw [transportChart_source]
    refine ⟨haΦ, ?_⟩
    change Φ a ∈ φ.source
    rw [← hΦ haΦ]
    exact hc.2.1
  · intro j x hx
    rw [transportChart_source] at hx
    obtain ⟨hxΦ, hxφ⟩ := hx
    have hx' : h x ∈ φ.source := by
      rw [hΦ hxΦ]
      exact hxφ
    rw [transportChart_apply]
    change h x ∈ F.hyp j.1 ↔ ψ (φ (Φ x)) (c ⟨j.1, j.2⟩) = 0
    rw [← hΦ hxΦ]
    exact hc.2.2.1 ⟨j.1, j.2⟩ (h x) hx'
  · intro j j' hjj'
    exact Subtype.ext (congrArg Subtype.val (hc.2.2.2 hjj'))

end Transport

section Ideal

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  (ψ : E ≃L[𝕜] (Fin n → 𝕜)) {A : AnalyticManifold.{u} 𝕜 E}

include ψ in
/-- An ideal sheaf with regular quotient stalks along its support is the reduced ideal of its
support: its stalks are the vanishing ideals. At a support point the stalk is a coordinate ideal on
an adapted chart (`exists_adaptedChart_of_isRegularLocalRing_quotient`), so the local Hadamard lemma
applies; off the closed support both sides are the unit ideal. -/
theorem stalkIdeal_eq_vanishingStalk_cosupport_of_isRegularLocalRing_quotient
    (J : AnalyticManifold.IdealSheaf A)
    (hns : ∀ a ∈ J.support, IsRegularLocalRing ((structureSheaf 𝕜 E A).presheaf.stalk a ⧸
      J.stalkIdeal a)) (a : A) :
    J.stalkIdeal a = vanishingStalk (𝕜 := 𝕜) (E := E) J.support a := by
  by_cases ha : a ∈ J.support
  · obtain ⟨c, φ, σ, hφ, haφ, hJ⟩ :=
      exists_adaptedChart_of_isRegularLocalRing_quotient (ψ := ψ) J (hns a ha)
    exact (vanishingStalk_cosupport_eq_stalkIdeal_of_eq_span_coord (ψ := ψ) J hφ.1 σ hJ haφ).symm
  · have h1 : J.stalkIdeal a = ⊤ := not_not.mp ha
    rw [h1, vanishingStalk_eq_top_of_notMem_closure]
    rwa [(IdealSheaf.isClosed_support (J := J)).closure_eq]

/-- On an open `U` on which the support of such a `J` is a closed submanifold, the inverse image
of `J` is the ideal sheaf of that submanifold. -/
theorem comap_inclusion_eq_idealSheaf_of_isRegularLocalRing_quotient
    (J : AnalyticManifold.IdealSheaf A)
    (hns : ∀ a ∈ J.support, IsRegularLocalRing ((structureSheaf 𝕜 E A).presheaf.stalk a ⧸
      J.stalkIdeal a)) (U : Opens A) {c : ℕ}
    (hS : IsClosedSubmanifold ψ (⇑(A.inclusion U) ⁻¹' J.support) c) :
    J.pullback _ (A.inclusion U).contMDiff = hS.idealSheaf := by
  apply IdealSheaf.ext
  intro a
  rw [hS.stalkIdeal_idealSheaf_eq_vanishingStalk, IdealSheaf.stalkIdeal_pullback,
    stalkIdeal_eq_vanishingStalk_cosupport_of_isRegularLocalRing_quotient ψ J hns,
    vanishingStalk_preimage_of_isLocalDiffeomorphAt (A.inclusion U)
      (isLocalDiffeomorph_inclusion A U a) J.support]

end Ideal

section Proper

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- A proper adapted simple-normal-crossing chart at a point `a` of `Y`, whose source meets only the
components through `a`, makes the inverse image of `F` on the open submanifold `φ.source` have
proper simple normal crossings with the trace of `Y` there, with the one transported chart at every
point. -/
theorem hasSncWithProper_comap_inclusion_of_isSncChartAt {F : HypersurfaceFamily A} {Y : Set A}
    {c : ℕ} {φ : OpenPartialHomeomorph A (Fin n → 𝕜)} {σ : Fin c ↪ Fin n} {a : A}
    {cidx : {j // a ∈ F.hyp j} → Fin n}
    (hφ : IsAdaptedChart (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) Y φ σ)
    (hc : F.IsSncChartAt (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) φ a cidx)
    (hproper : ∀ j, cidx j ∉ Set.range σ)
    (hsub : ∀ j, ∀ x ∈ φ.source, x ∈ F.hyp j → a ∈ F.hyp j) :
    (F.comap (A.inclusion ⟨φ.source, φ.open_source⟩)).HasSncWithProper
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (⇑(A.inclusion ⟨φ.source, φ.open_source⟩) ⁻¹' Y) c := by
  intro b hb
  have hbφ : A.inclusion ⟨φ.source, φ.open_source⟩ b ∈ φ.source := b.2
  have hsub' : ∀ j, A.inclusion ⟨φ.source, φ.open_source⟩ b ∈ F.hyp j → a ∈ F.hyp j :=
    fun j hj => hsub j _ hbφ hj
  refine ⟨transportChart (inclusionPartialDiffeomorph A ⟨φ.source, φ.open_source⟩ b).symm φ, σ,
    fun j => cidx ⟨j.1, hsub' j.1 j.2⟩, ?_, ?_, fun j => hproper _⟩
  · exact isAdaptedChart_transportChart _ (image_inclusionInv_eq ⟨φ.source, φ.open_source⟩ b Y) hφ
  · exact (hc.of_forall_mem hbφ hsub').comap_transportChart (A.inclusion _) (Set.mem_univ b)
      fun _ _ => rfl

/-- The predicate `IsSncDivisorSet` for a closed subspace `V(J)` and the trace of an ambient set
`Z`, from local data at every point of the support: an open `U`, the support a closed submanifold
of `U` with `J|_U` its ideal sheaf, and a family on `U` whose trace is a simple normal crossing
family with support the trace of `Z`. The comparison isomorphisms are `Sp(Y) ≅ Sp(M)/𝓘_Y`
(`closedSubmanifoldIso`) and `(X|_U)/(𝒥|_U) ≅ (X/𝒥)|_U` (`restrictOpen_quotient_iso`). -/
theorem isSncDivisorSet_toAnalyticSpace_of_forall (J : AnalyticManifold.IdealSheaf A)
    (Z : Set A)
    (h : ∀ x ∈ J.support, ∃ (U : Opens A) (_ : x ∈ U) (c : ℕ)
      (hS : IsClosedSubmanifold (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (⇑(A.inclusion U) ⁻¹' J.support) c),
      J.pullback _ (A.inclusion U).contMDiff = hS.idealSheaf ∧
      ∃ F : HypersurfaceFamily (A.restrict U),
        (hS.traceFamily F).IsSnc (ContinuousLinearEquiv.refl 𝕜 (Fin (n - c) → 𝕜)) ∧
        F.support = ⇑(A.inclusion U) ⁻¹' Z) :
    IsSncDivisorSet J.toAnalyticSpace
      ((fun y => (J.toAnalyticSpaceι y : A)) ⁻¹' Z) := by
  intro x
  obtain ⟨U, hxU, c, hS, hJU, F, hF, hFZ⟩ := h x.1 x.2
  -- the ambient space, the space of the open submanifold, and the inclusion between them
  set XA : KLocallyRingedSpace.{u} 𝕜 := KLocallyRingedSpace.ofManifold 𝕜 (Fin n → 𝕜) A with hXA
  set XU : KLocallyRingedSpace.{u} 𝕜 :=
    KLocallyRingedSpace.ofManifold 𝕜 (Fin n → 𝕜) (A.restrict U) with hXU
  set ι : XU ⟶ XA := KLocallyRingedSpace.ofManifoldHom (K := 𝕜) (E := Fin n → 𝕜)
    (E' := Fin n → 𝕜) ⇑(A.inclusion U) (A.inclusion U).contMDiff with hι
  -- `J|_U` as the inverse image along the inclusion; it is the ideal sheaf of `Ỹ ∩ U`
  set JU : IdealSheaf XU.toLocallyRingedSpace.𝒪 := QuotientSpace.comap ι.1 J with hJUdef
  have hJU' : JU = hS.idealSheaf := by
    rw [hJUdef, hι, KLocallyRingedSpace.comap_ofManifoldHom_eq_pullback]
    exact hJU
  let _i := hS.chartedSpace
  -- the comparison isomorphism `Sp(Ỹ ∩ U) ≅ Sp(U)/𝓘 ≅ Sp(U)/(J|U) ≅ Ỹ | U'`; every object is
  -- named once so that the point computations below are rewrites, never unfoldings
  set Xc : KLocallyRingedSpace.{u} 𝕜 :=
    KLocallyRingedSpace.ofManifold 𝕜 (Fin (n - c) → 𝕜) (⇑(A.inclusion U) ⁻¹' J.support) with hXc
  set e₁ : KLocallyRingedSpace.KIso Xc (XU.quotient hS.idealSheaf) :=
    KLocallyRingedSpace.closedSubmanifoldIso hS with he₁
  set e₂ := eqToIso (congrArg XU.quotient hJU'.symm) with he₂
  have hιst : ∀ z' : XU.toLocallyRingedSpace, IsIso (ι.1.stalkMap z') := by
    intro z'
    obtain ⟨z'', rfl⟩ : ∃ z'' : (A.restrict U : Type u), z'' = z' := ⟨z', rfl⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    have hfun : ⇑(ι.1.stalkMap z'').hom =
        germMap ⇑(A.inclusion U) (A.inclusion U).contMDiff z'' :=
      funext fun s => KLocallyRingedSpace.stalkMap_ofManifoldHom_eq_germMap _ _ _ s
    rw [hfun]
    exact germMap_bijective_of_isLocalDiffeomorphAt ⇑(A.inclusion U) (A.inclusion U).contMDiff
      (isLocalDiffeomorph_inclusion A U z'')
  have hιemb : IsOpenEmbedding ι.1.base := by
    change IsOpenEmbedding (Subtype.val : U → A)
    exact U.isOpen.isOpenEmbedding_subtypeVal
  have hoi : LocallyRingedSpace.IsOpenImmersion
      (KLocallyRingedSpace.quotientMap ι JU J (QuotientSpace.compat_comap _ _)).1 :=
    QuotientSpace.isOpenImmersion_map_comap ι.1 J hιemb
  have hrange : Set.range (KLocallyRingedSpace.Hom.toFun
      (KLocallyRingedSpace.quotientMap ι JU J (QuotientSpace.compat_comap _ _))) =
      Set.range (KLocallyRingedSpace.Hom.toFun (KLocallyRingedSpace.ofRestrict (XA.quotient J)
        (KLocallyRingedSpace.quotientOpens XA J U))) := by
    rw [KLocallyRingedSpace.range_toFun_ofRestrict]
    ext q
    constructor
    · rintro ⟨w, rfl⟩
      change (KLocallyRingedSpace.Hom.toFun
        (KLocallyRingedSpace.quotientMap ι JU J (QuotientSpace.compat_comap _ _)) w).1 ∈ U
      exact (w.1 : U).2
    · intro hq
      have hcs := QuotientSpace.cosupport_comap ι.1 (J : IdealSheaf XA.toLocallyRingedSpace.𝒪)
      have hq' : (⟨q.1, hq⟩ : U) ∈ JU.support := (Set.ext_iff.mp hcs ⟨q.1, hq⟩).mpr q.2
      exact ⟨⟨⟨q.1, hq⟩, hq'⟩, Subtype.ext rfl⟩
  set e₃ := KLocallyRingedSpace.isoOfRangeEq
    (KLocallyRingedSpace.quotientMap ι JU J (QuotientSpace.compat_comap _ _))
    (KLocallyRingedSpace.ofRestrict (XA.quotient J) (KLocallyRingedSpace.quotientOpens XA J U))
    hrange with he₃
  set e := e₁ ≪≫ e₂ ≪≫ e₃ with he
  refine ⟨n - c, hS.toAnalyticManifold, KLocallyRingedSpace.quotientOpens XA J U, hxU, e,
    hS.traceFamily F, hF, ?_⟩
  -- each step is the identity on the underlying points of the ambient manifold
  have key : ∀ (X : KLocallyRingedSpace.{u} 𝕜) (J₁ J₂ : IdealSheaf X.toLocallyRingedSpace.𝒪)
      (h : J₁ = J₂) (z : X.quotient J₁),
      (KLocallyRingedSpace.Hom.toFun (eqToHom (congrArg X.quotient h)) z).1 = z.1 := by
    rintro X J₁ J₂ rfl z
    rfl
  have h1 : ∀ b : hS.toAnalyticManifold,
      (KLocallyRingedSpace.Hom.toFun e₁.hom b).1 =
        (b : ↥(⇑(A.inclusion U) ⁻¹' J.support)).1 :=
    fun b => KLocallyRingedSpace.toFun_closedSubmanifoldIso_hom_comp hS b
  have h2 : ∀ w, (KLocallyRingedSpace.Hom.toFun e₂.hom w).1 = w.1 :=
    fun w => key _ _ _ hJU'.symm w
  have h3 : ∀ w, (KLocallyRingedSpace.Hom.toFun e₃.hom w).1.1 = w.1.1 := by
    intro w
    have hc : e₃.hom ≫ KLocallyRingedSpace.ofRestrict (XA.quotient J)
        (KLocallyRingedSpace.quotientOpens XA J U) =
        KLocallyRingedSpace.quotientMap ι JU J (QuotientSpace.compat_comap _ _) := by
      rw [he₃]
      exact KLocallyRingedSpace.isoOfRangeEq_hom_comp _ _ _
    have hw := congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ w) hc
    have hL : KLocallyRingedSpace.Hom.toFun (e₃.hom ≫ KLocallyRingedSpace.ofRestrict
        (XA.quotient J) (KLocallyRingedSpace.quotientOpens XA J U)) w =
        (KLocallyRingedSpace.Hom.toFun e₃.hom w).1 :=
      rfl
    have hR : (KLocallyRingedSpace.Hom.toFun
        (KLocallyRingedSpace.quotientMap ι JU J (QuotientSpace.compat_comap _ _)) w).1 = w.1.1 :=
      QuotientSpace.map_base_apply _ _ _ _ w
    exact (congrArg Subtype.val (hL.symm.trans hw)).trans hR
  have hpt : ∀ b : Xc,
      (KLocallyRingedSpace.Hom.toFun e.hom b).1.1 =
        ((b : ↥(⇑(A.inclusion U) ⁻¹' J.support)).1).1 := by
    intro b
    rw [he, Iso.trans_hom, Iso.trans_hom, KLocallyRingedSpace.Hom.toFun_comp,
      KLocallyRingedSpace.Hom.toFun_comp, Function.comp_apply, Function.comp_apply, h3, h2]
    exact congrArg Subtype.val (h1 b)
  -- the image equation
  ext q
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    have hbZ : ((b : ↥(⇑(A.inclusion U) ⁻¹' J.support)).1).1 ∈ Z := by
      have hb' := hb
      rw [hS.traceFamily_support] at hb'
      change (b : ↥(⇑(A.inclusion U) ⁻¹' J.support)).1 ∈ F.support at hb'
      rw [hFZ] at hb'
      exact hb'
    refine ⟨?_, ?_⟩
    · change (KLocallyRingedSpace.Hom.toFun e.hom b).1.1 ∈ Z
      rw [hpt b]
      exact hbZ
    · change (KLocallyRingedSpace.Hom.toFun e.hom b).1.1 ∈ U
      rw [hpt b]
      exact ((b : ↥(⇑(A.inclusion U) ⁻¹' J.support)).1).2
  · rintro ⟨hqZ, hqU⟩
    have hu : (⟨q.1, hqU⟩ : U) ∈ ⇑(A.inclusion U) ⁻¹' J.support := q.2
    refine ⟨KLocallyRingedSpace.Hom.toFun e.hom (⟨⟨q.1, hqU⟩, hu⟩ : hS.toAnalyticManifold),
      ⟨_, ?_, rfl⟩, Subtype.ext (hpt _)⟩
    rw [hS.traceFamily_support]
    change (⟨q.1, hqU⟩ : U) ∈ F.support
    rw [hFZ]
    exact hqZ

end Proper

section

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- The preimage of the singular locus under the local resolution map is the trace of the
exceptional divisor: `Π⁻¹((Y|_W).singularLocus) = Ỹ ∩ |E_r|` as subsets of `Ỹ` (from clauses (2) and
(3) of [Wlo09, Theorem 2.0.2]). -/
theorem PieceEmbedding.localResolutionMap_preimage_sing_eq (bed : BEDanFamStar.{u} 𝕜)
    (W : Opens (pieceAmbient 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
    (hbed : bed.IsEmbeddedDesing) :
    (E.localResolutionMap bed W hW) ⁻¹'
        singularLocus ((E.restrictedIdeal W).toAnalyticSpace) =
      (fun y => (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
          (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι y :
          (E.localResolutionSeq bed W hW).toSuccession.stage (Fin.last _))) ⁻¹'
        ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq (Fin.last _)).support := by
  set S := (E.localResolutionSeq bed W hW).toSuccession with hS
  set J := E.restrictedIdeal W with hJ
  have hZ : S.CentersOver (AnalyticManifold.IdealSheaf.regSet J)ᶜ :=
    hbed.centersOver_compl_regSet n E.ambientTriple E.domBEDan_ambientTriple W hW
  obtain ⟨-, -, -, hns, -, -⟩ := hbed.1 n E.ambientTriple E.domBEDan_ambientTriple W hW
  ext y
  constructor
  · intro hy
    by_contra hE
    apply hy
    rw [mem_reg_toAnalyticSpace_iff]
    have hreg := (mem_reg_toAnalyticSpace_iff _ y).mp (Set.eq_univ_iff_forall.mp hns y)
    exact (S.isRegularLocalRing_quotient_strictTransformSubspaceSeq_iff_of_notMem_support J
      (Fin.last _) hE).mp hreg
  · intro hE hy
    exact S.support_totalTransformSeq_subset_preimage_of_centersOver hZ (Fin.last _) hE
      ⟨KLocallyRingedSpace.Hom.toFun (E.localResolutionMap bed W hW) y, hy, rfl⟩

/-- Clause (2) of [Wlo09, Theorem 2.0.1] for the local resolution map of a piece: the preimage of
the singular locus is the trace of the exceptional divisor, and it is a simple normal crossing
divisor of the non-singular space `Ỹ`. -/
theorem PieceEmbedding.localResolutionMap_preimage_sing_eq_inter_exceptional
    (bed : BEDanFamStar.{u} 𝕜) (W : Opens (pieceAmbient 𝕜 E.G))
    (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G)))) (hbed : bed.IsEmbeddedDesing) :
    (E.localResolutionMap bed W hW) ⁻¹'
        singularLocus ((E.restrictedIdeal W).toAnalyticSpace) =
      (fun y => (((E.localResolutionSeq bed W hW).toSuccession.strictTransformSubspaceSeq
          (E.restrictedIdeal W) (Fin.last _)).toAnalyticSpaceι y :
          (E.localResolutionSeq bed W hW).toSuccession.stage (Fin.last _))) ⁻¹'
        ((E.localResolutionSeq bed W hW).toSuccession.totalTransformSeq (Fin.last _)).support ∧
    IsSncDivisorSet (E.localResolution bed W hW)
      ((E.localResolutionMap bed W hW) ⁻¹'
        singularLocus ((E.restrictedIdeal W).toAnalyticSpace)) := by
  refine ⟨E.localResolutionMap_preimage_sing_eq bed W hW hbed, ?_⟩
  rw [E.localResolutionMap_preimage_sing_eq bed W hW hbed]
  set S := (E.localResolutionSeq bed W hW).toSuccession with hS
  set J := E.restrictedIdeal W with hJ
  obtain ⟨hsnc1, -, -, hns, -, -⟩ := hbed.1 n E.ambientTriple E.domBEDan_ambientTriple W hW
  have hproper := hbed.isProperSnc n E.ambientTriple E.domBEDan_ambientTriple W hW
  have hnsq : ∀ a ∈ (S.strictTransformSubspaceSeq J (Fin.last _)).support,
      IsRegularLocalRing ((structureSheaf 𝕜 (Fin n → 𝕜) (S.stage (Fin.last _))).presheaf.stalk a ⧸
        (S.strictTransformSubspaceSeq J (Fin.last _)).stalkIdeal a) :=
    fun a ha => (mem_reg_toAnalyticSpace_iff _ ⟨a, ha⟩).mp (Set.eq_univ_iff_forall.mp hns ⟨a, ha⟩)
  refine isSncDivisorSet_toAnalyticSpace_of_forall (S.strictTransformSubspaceSeq J (Fin.last _))
    (S.totalTransformSeq (Fin.last _)).support fun x hx => ?_
  obtain ⟨c, φ, σ, cidx, hφ, hsnc, hprop⟩ := hproper.2 x hx
  obtain ⟨V, hVo, hxV, hV⟩ := (hsnc1 (Fin.last _)).exists_isOpen_forall_mem_of_mem x
  have hφ'a := hφ.restrOpen' V hVo
  have hsnc' := HypersurfaceFamily.IsSncChartAt.restrOpen hsnc hVo hxV
  have hxφ' : x ∈ (φ.restrOpen V hVo).source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hsnc.2.1, hxV⟩
  have hsub : ∀ j, ∀ y ∈ (φ.restrOpen V hVo).source,
      y ∈ (S.totalTransformSeq (Fin.last _)).hyp j →
        x ∈ (S.totalTransformSeq (Fin.last _)).hyp j := by
    intro j y hy hyj
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hV j y hy.2 hyj
  have hS' := IsClosedSubmanifoldOn.restrict
    ⟨(φ.restrOpen V hVo).source, (φ.restrOpen V hVo).open_source⟩ hφ'a.isClosedSubmanifoldOn'
  refine ⟨⟨(φ.restrOpen V hVo).source, (φ.restrOpen V hVo).open_source⟩, hxφ', c, hS',
    comap_inclusion_eq_idealSheaf_of_isRegularLocalRing_quotient _ _ hnsq _ hS',
    (S.totalTransformSeq (Fin.last _)).comap (AnalyticManifold.inclusion _ _), ?_,
    HypersurfaceFamily.support_comap _ _⟩
  exact hS'.isSnc_traceFamily
    (HypersurfaceFamily.isSnc_comap (hsnc1 (Fin.last _)) _ (isLocalDiffeomorph_inclusion _ _))
    (hasSncWithProper_comap_inclusion_of_isSncChartAt hφ'a hsnc' hprop hsub)

end

end Hironaka.Manifold

end
