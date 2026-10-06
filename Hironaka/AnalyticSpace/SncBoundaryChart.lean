/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.SncFamily
public import Hironaka.AnalyticSpace.SncDivisorSetLocal
import Hironaka.Algebra.RegularSmooth.ParameterCount
import Hironaka.AnalyticSpace.Manifold.StratumIso
import Hironaka.AnalyticSpace.SncFamilyDivisor
import Hironaka.AnalyticSpace.SncFamilyTransport
import Hironaka.Manifold.AdaptedChart
import Hironaka.Manifold.Germ.StalkNoetherian
import Hironaka.Manifold.Snc.NonSingular
import Hironaka.Manifold.Snc.Spreading
import Hironaka.Manifold.Submanifold.Charts
import Hironaka.Manifold.Submanifold.Ideal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The support of a simple normal crossings boundary is an snc divisor set

`isSncDivisorSet_of_isSncBoundary`: the support of a simple normal crossings boundary `E` of an
analytic `K`-space `X` (`ClosedSubspace.IsSncBoundary`: Kollár's Definition 24 read on the stalks of
a locally finite family of closed subspaces [Kol07, Definition 24]) is an snc divisor set in the
sense of `AnalyticSpace.IsSncDivisorSet` — at every point a chart of `X` by the analytic space of an
analytic manifold `M` (`exists_manifold_of_isNonsingular`,
`Hironaka/AnalyticSpace/Manifold/StratumIso.lean`) on which the support is the support of an snc
hypersurface family of `M` (`HypersurfaceFamily.IsSnc`). The two formulations of clause (3) of the
resolution theorem, the divisor form of [Kol07, Theorem 45 (3)] and the chart form, thus agree.

The lemmas:

* `IsSncBoundary.space_isNonsingular`: the pointwise clause gives a regular system of parameters
  at every stalk, so `X` is non-singular;
* `IsSncFamily.exists_countable_reindex`: the members with nonempty support of a locally finite
  family on the σ-compact `X` are countable — the countable, linearly ordered index type that a
  `HypersurfaceFamily` (`Hironaka/Manifold/Snc/Defs.lean`) carries;
* `IsSncFamily.comap_ofRestrict`: an snc family restricted to an open subspace;
* `exists_isSncChartAt_of_isSncFamily`, `isClosedSubmanifold_support_of_isSncFamily`,
  `exists_hypersurfaceFamily_isSnc_of_isSncFamily` — the manifold side: an snc family of closed
  subspaces of `Sp(M)` (`ClosedSubspace.IsSncFamily`, `Hironaka/AnalyticSpace/SncFamily.lean`) has,
  at every point `a : M`, an snc chart (`HypersurfaceFamily.IsSncChartAt`) in the sense of
  [Kol07, Definition 24]: a chart of the maximal atlas on whose source every member through `a` is
  a coordinate hyperplane, distinct members having distinct coordinates; hence every member's
  support is a closed submanifold of codimension one, and the supports of a countable, linearly
  ordered family form an snc hypersurface family of `M` with the same support;
* `isSncDivisorSet_of_isSncBoundary`: the family behind `E`
  (`isSncBoundary_iff_exists_isSncFamily_divisorOf`), restricted to the stratum and carried to
  `Sp(M)` along the chart (`isSncFamily_comap_of_isIso`), re-indexed, read as an snc hypersurface
  family, with the support identity by set algebra through the chart.

The chart is built as in `exists_adaptedChart_of_isRegularLocalRing_quotient`
(`Hironaka/Manifold/Snc/NonSingular.lean`), read on the regular system of parameters `z` of the
pointwise clause: sections representing the `z_i` near `a` (`exists_sections_of_germs`,
`Hironaka/Manifold/Snc/Spreading.lean`) vanish at `a` and have independent differentials
(`IsRegularLocalRing.linearIndependent_toCotangent_of_span_eq`,
`linearIndependent_cotangentClass_of_residueField`,
`hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass'`), so they are the
coordinates `σ i` of a chart `e` at `a` (`exists_chart_extending`,
`Hironaka/Manifold/AdaptedChart.lean`); the stalk identity `(H j)_a = (z_{c j})` of each of the
finitely many members through `a` spreads to an open neighbourhood
(`exists_opens_stalkIdeal_eq_span`); on the restriction of `e` to their intersection a point lies
on the member iff the coordinate germ `z_{c j}` is not a unit there iff the coordinate `σ (c j)`
vanishes at it (`mem_maximalIdeal_iff_eval`). The independence of the differentials is the
Jacobian criterion Hironaka invokes at [Hir64, Ch. 0, §1, p. 121].

Used by `Hironaka/Resolution/Analytic/Kol07Thm45/CoproductGluedFamily.lean` and
`Hironaka/Resolution/Analytic/Kol07Thm45/Glue/OverFamilyPartner.lean`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Manifold
open scoped Manifold ContDiff
open IsLocalRing Filter Topology

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

namespace ClosedSubspace

variable {X : AnalyticSpace.{u} K}

/-- A space carrying an snc boundary is non-singular: the pointwise clause of `IsSncBoundary` gives
a regular system of parameters at every stalk. -/
theorem IsSncBoundary.space_isNonsingular {E : ClosedSubspace X} (h : E.IsSncBoundary) :
    X.IsNonsingular := by
  obtain ⟨ι, H, -, hx⟩ := h
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  obtain ⟨n, z, ⟨hspan, hdim⟩, -, -⟩ := hx x
  have : IsNoetherianRing (X.presheaf.stalk x) := AnalyticSpace.isNoetherianRing_stalk X x
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [← hdim, ← hspan]
  have hle : (Ideal.span (Set.range z)).spanFinrank ≤ n := by
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    calc (Set.range z).ncard = (z '' Set.univ).ncard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set (Fin n)).ncard := Set.ncard_image_le Set.finite_univ
      _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact_mod_cast hle

/-- An snc family on the σ-compact space `X` re-indexed by a countable linearly ordered type, the
empty members dropped, with the same support. -/
theorem IsSncFamily.exists_countable_reindex {ι : Type u} {H : ι → ClosedSubspace X}
    (h : IsSncFamily H) :
    ∃ (ι' : Type u) (_ : Countable ι') (_ : LinearOrder ι') (H' : ι' → ClosedSubspace X),
      IsSncFamily H' ∧ (⋃ j, (H' j).support) = ⋃ j, (H j).support := by
  classical
  have : SigmaCompactSpace X.toLocallyRingedSpace.toTopCat := X.sigmaCompact
  let ι' : Type u := {j : ι // (H j).support.Nonempty}
  have hlf : LocallyFinite fun j : ι' => (H j.1).support := h.1.comp_injective Subtype.val_injective
  have hcount : Countable ι' :=
    Set.countable_univ_iff.mp (hlf.countable_univ fun j => j.2)
  let _ : Encodable ι' := Encodable.ofCountable ι'
  let _ : LinearOrder ι' := LinearOrder.lift' Encodable.encode Encodable.encode_injective
  refine ⟨ι', hcount, inferInstance, fun j => H j.1, ⟨hlf, fun x => ?_⟩, ?_⟩
  · obtain ⟨n, z, hz, c, hc, hcz⟩ := h.2 x
    refine ⟨n, z, hz, fun j => c ⟨j.1.1, j.2⟩, fun j₁ j₂ hj => ?_, fun j => hcz ⟨j.1.1, j.2⟩⟩
    have := hc hj
    exact Subtype.ext (Subtype.ext (congrArg (fun k : {j // x ∈ (H j).support} => k.1) this))
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j.1, hj⟩
    · rintro ⟨j, hj⟩
      exact ⟨⟨j, ⟨x, hj⟩⟩, hj⟩

/-- An snc family restricted to an open subspace: the pointwise clause is read back along the
stalk isomorphisms `KLocallyRingedSpace.isIso_ofRestrict_stalkMap`. -/
theorem IsSncFamily.comap_ofRestrict {ι : Type u} {H : ι → ClosedSubspace X} (h : IsSncFamily H)
    (U : Opens X) :
    IsSncFamily (X := AnalyticSpace.restrictOpen X U) fun j =>
      QuotientSpace.comap (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U).1 (H j) := by
  rw [isSncFamily_iff_isSncAtIdeals] at h ⊢
  refine ⟨?_, fun y => ?_⟩
  · have hsupp : (fun j => (QuotientSpace.comap
          (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U).1 (H j) :
          ClosedSubspace (X.restrictOpen U)).support) = fun j => Subtype.val ⁻¹' (H j).support :=
      funext fun j => QuotientSpace.cosupport_comap _ (H j)
    rw [hsupp]
    exact h.1.preimage_continuous continuous_subtype_val
  · have instS : IsLocalRing ((X.restrictOpen U).presheaf.stalk y) :=
      (X.restrictOpen U).toLocallyRingedSpace.isLocalRing y
    have hiso := KLocallyRingedSpace.isIso_ofRestrict_stalkMap X.toKLocallyRingedSpace U y
    have hb := ConcreteCategory.bijective_of_isIso
      ((KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U).1.stalkMap y)
    have hpt := @IsSncAtIdeals.map_ringHom_of_bijective _ _ _ _ _ _ instS _ _ hb
      (h.2 ((KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U).1.base y))
    exact Eq.mp (congrArg (@IsSncAtIdeals _ _ instS _) (funext fun j =>
      (QuotientSpace.stalkIdeal_comap
        (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U).1 (H j) y).symm)) hpt

end ClosedSubspace

section ManifoldChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] {n : ℕ} {ψ : E ≃L[K] (Fin n → K)}
  {M : AnalyticManifold.{u} K E}

/-- **An snc chart at every point** ([Kol07, Definition 24]): for an snc family of closed subspaces
of `Sp(M)` and a point `a : M`, a chart of `M` at `a` on whose source every member through `a` is a
coordinate hyperplane, distinct members having distinct coordinates — `exists_chart_extending` on
the regular system of parameters at `a`, the stalk identities of the members through `a` spread by
`exists_opens_stalkIdeal_eq_span`. -/
theorem exists_isSncChartAt_of_isSncFamily {ι : Type u} {H : ι → ClosedSubspace (toSpace ψ M)}
    (h : ClosedSubspace.IsSncFamily H) (a : M) :
    ∃ (φ : OpenPartialHomeomorph M E) (cidx : {j // a ∈ (H j).support} → Fin n),
      φ ∈ IsManifold.maximalAtlas 𝓘(K, E) ω M ∧ a ∈ φ.source ∧ Function.Injective cidx ∧
        ∀ j : {j // a ∈ (H j).support}, ∀ y ∈ φ.source,
          y ∈ (H j.1).support ↔ ψ (φ y) (cidx j) = 0 := by
  classical
  have _hfd : FiniteDimensional K E := ψ.symm.toLinearEquiv.finiteDimensional
  have hreg₀ : IsRegularLocalRing ((structureSheaf K E M).presheaf.stalk a) :=
    isRegularLocalRing_stalk_of_chart E ψ (chartAt E a) (mem_chart_source E a)
      (IsManifold.chart_mem_maximalAtlas a)
  have _hfin : Finite {j // a ∈ (H j).support} := (h.1.point_finite a).to_subtype
  obtain ⟨m, z, ⟨hspan, hdim⟩, c, hc, hH⟩ := h.2 a
  -- the regular system of parameters, read in the structure sheaf's stalk at `a`
  have hspan' : Ideal.span (Set.range z) =
      maximalIdeal ((structureSheaf K E M).presheaf.stalk a) := hspan
  have hdim' : (m : WithBot ℕ∞) = ringKrullDim ((structureSheaf K E M).presheaf.stalk a) := hdim
  have hz : ∀ i, z i ∈ maximalIdeal ((structureSheaf K E M).presheaf.stalk a) := fun i =>
    hspan' ▸ Ideal.subset_span ⟨i, rfl⟩
  -- representatives of the parameters as sections
  obtain ⟨U, hxU, g, hg⟩ := exists_sections_of_germs (structureSheaf K E M) z
  have hz0 : ∀ j, extendSection K E (g j) a = 0 := by
    intro j
    rw [extendSection_of_mem K E _ hxU]
    have h1 : Manifold.eval K E M a ((structureSheaf K E M).presheaf.germ U a hxU (g j)) = (g j)
        ⟨a, hxU⟩ :=
      contMDiffSheafCommRing.eval_germ 𝓘(K, E) 𝓘(K) ω M K U a hxU (g j)
    rw [← h1, hg j]
    exact (mem_maximalIdeal_iff_eval E _).mp (hz _)
  have hzc : ∀ j, ContMDiffAt 𝓘(K, E) 𝓘(K) ω (extendSection K E (g j)) a := fun j =>
    (contMDiffOn_extendBy0 𝓘(K, E) ω M (g j)).contMDiffAt (U.isOpen.mem_nhds hxU)
  -- independent differentials
  have hliκ := IsRegularLocalRing.linearIndependent_toCotangent_of_span_eq
    (R := (structureSheaf K E M).presheaf.stalk a) z hz hspan' hdim'
  have hliK := linearIndependent_cotangentClass_of_residueField z hz hliκ
  have hind : HasIndependentDifferentialsAt E (fun j => extendSection K E (g j)) a := by
    rw [hasIndependentDifferentialsAt_iff_linearIndependent_cotangentClass' E hxU g]
    simpa only [hg] using hliK
  obtain ⟨e, σ, he, hae, -, hcoord⟩ :=
    exists_chart_extending ψ (fun j => extendSection K E (g j)) a hzc hz0 hind
  -- on `e.source ∩ U` the germs of the sections are the coordinates `σ j` of `e`
  have hgerm : ∀ y (hyU : y ∈ U) (hye : y ∈ e.source) j,
      (structureSheaf K E M).presheaf.germ U y hyU (g j) = coord E ψ e he hye (σ j) := by
    intro y hyU hye j
    apply stalkToGerm_injective 𝓘(K, E) ω M y
    rw [stalkToGerm_structureSheaf_germ, stalkToGerm_coord, Germ.coe_eq]
    filter_upwards [(e.open_source.inter U.isOpen).mem_nhds ⟨hye, hyU⟩] with y' hy'
    have h1 : extendSection K E (g j) y' = ψ (e y') (σ j) := hcoord y' hy'.1 j
    rw [h1, extendSection_of_mem K E _ hy'.1]
    rfl
  -- each member's stalk identity at `a`, read in the structure sheaf's vocabulary, spreads to an
  -- open neighbourhood `W j` of `a`
  have hJ : ∀ j : {j // a ∈ (H j).support},
      IdealSheaf.stalkIdeal (𝒪 := structureSheaf K E M) (H j.1) a = Ideal.span (Set.range
        fun _ : Unit => (structureSheaf K E M).presheaf.germ U a hxU (g (c j))) := by
    intro j
    rw [Set.range_const, hg]
    exact hH j
  choose W haW hWU hW using fun j : {j // a ∈ (H j).support} =>
    IdealSheaf.exists_opens_stalkIdeal_eq_span (𝒪 := structureSheaf K E M) (J := H j.1) hxU
      (fun _ : Unit => g (c j)) (hJ j)
  have hWs : ∀ j y (hy : y ∈ W j), IdealSheaf.stalkIdeal (𝒪 := structureSheaf K E M) (H j.1) y =
      Ideal.span {(structureSheaf K E M).presheaf.germ U y (hWU j hy) (g (c j))} :=
    fun j y hy => (hW j y hy).trans (congrArg Ideal.span Set.range_const)
  -- the chart `e` restricted to the intersection of the `W j`
  let V : Set M := ⋂ j, (W j : Set M)
  have hV : IsOpen V := isOpen_iInter_of_finite fun j => (W j).isOpen
  have haV : a ∈ V := Set.mem_iInter.mpr haW
  have he' : e.restrOpen V hV ∈ IsManifold.maximalAtlas 𝓘(K, E) ω M := by
    rw [OpenPartialHomeomorph.restrOpen_eq_restr]
    exact restr_mem_maximalAtlas _ he hV
  refine ⟨e.restrOpen V hV, fun j => σ (c j), he', ⟨hae, haV⟩, σ.injective.comp hc, ?_⟩
  intro j y hy
  have hyW : y ∈ W j := Set.mem_iInter.mp hy.2 j
  -- a point of the source lies on the member iff the coordinate germ is not a unit there iff the
  -- coordinate vanishes at it
  have hu : IsUnit (coord E ψ e he hy.1 (σ (c j))) ↔ ψ (e y) (σ (c j)) ≠ 0 := by
    constructor
    · intro hu h0
      have h1 := IsLocalRing.notMem_maximalIdeal.mpr hu
      rw [mem_maximalIdeal_iff_eval, eval_coord] at h1
      exact h1 h0
    · exact isUnit_coord_of_ne_zero _ he hy.1
  change IdealSheaf.stalkIdeal (𝒪 := structureSheaf K E M) (H j.1) y ≠ ⊤ ↔ ψ (e y) (σ (c j)) = 0
  rw [hWs j y hyW, hgerm y (hWU j hyW) hy.1 (c j), ne_eq, Ideal.span_singleton_eq_top]
  exact not_iff_comm.mp hu.symm

/-- Each member's support is a closed submanifold of codimension one ([Kol07, Definition 24]: each
member is smooth): the snc chart at a point of the member, and `isClosed_cosupport`. -/
theorem isClosedSubmanifold_support_of_isSncFamily {ι : Type u}
    {H : ι → ClosedSubspace (toSpace ψ M)} (h : ClosedSubspace.IsSncFamily H) (j : ι) :
    IsClosedSubmanifold (M := (M : Type u)) ψ (H j).support 1 where
  isClosed := IdealSheaf.isClosed_support (H j)
  exists_adaptedChart a ha := by
    obtain ⟨φ, cidx, hφ, haφ, -, hiff⟩ := exists_isSncChartAt_of_isSncFamily h a
    exact ⟨φ, singleEmb (cidx ⟨j, ha⟩), haφ, hφ, fun y hy =>
      (hiff ⟨j, ha⟩ y hy).trans ⟨fun h0 _ => h0, fun h0 => h0 0⟩⟩

/-- The supports of a countable, linearly ordered snc family of closed subspaces of `Sp(M)` form an
snc hypersurface family of `M` with the same support ([Kol07, Definition 24]). -/
theorem exists_hypersurfaceFamily_isSnc_of_isSncFamily {ι : Type u} [Countable ι] [LinearOrder ι]
    {H : ι → ClosedSubspace (toSpace ψ M)} (h : ClosedSubspace.IsSncFamily H) :
    ∃ F : HypersurfaceFamily M, F.IsSnc ψ ∧ (F.support : Set M) = ⋃ j, (H j).support :=
  ⟨⟨ι, fun j => (H j).support⟩,
    ⟨isClosedSubmanifold_support_of_isSncFamily h, h.1, fun a =>
      let ⟨φ, cidx, hφ, haφ, hinj, hiff⟩ := exists_isSncChartAt_of_isSncFamily h a
      ⟨φ, cidx, hφ, haφ, hiff, hinj⟩⟩, rfl⟩

end ManifoldChart

namespace ClosedSubspace

variable {X : AnalyticSpace.{u} K}

/-- **The support of an snc boundary is an snc divisor set**: the chart of the stratum
`exists_manifold_of_isNonsingular`, the family transported along it (`isSncFamily_comap_of_isIso`,
`support_comap_eq_preimage`), `exists_hypersurfaceFamily_isSnc_of_isSncFamily` on the manifold,
and the support identity from `isSncBoundary_iff_exists_isSncFamily_divisorOf` and
`support_divisorOf`. -/
theorem isSncDivisorSet_of_isSncBoundary (E : ClosedSubspace X) (h : E.IsSncBoundary) :
    IsSncDivisorSet X E.support := by
  classical
  have hX : X.IsNonsingular := h.space_isNonsingular
  intro x
  obtain ⟨ι, H, hH, hfam, rfl⟩ := (isSncBoundary_iff_exists_isSncFamily_divisorOf E).mp h
  obtain ⟨n, z, ⟨hspan, hdim⟩, -⟩ := hfam.2 x
  obtain ⟨U, hU, M, ⟨e⟩⟩ := AnalyticSpace.exists_manifold_of_isNonsingular X hX n
  have hxU : x ∈ U := by
    have hmem : x ∈ (U : Set X) := by
      rw [hU]
      exact hdim.symm
    exact hmem
  -- the family restricted to `U` and carried to `Sp(M)` along the chart
  have hres := hfam.comap_ofRestrict U
  let f : toSpace (ContinuousLinearEquiv.refl K (Fin n → K)) M ⟶ X.restrictOpen U := e.hom
  have hf : IsIso f := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  have hfam₂ := isSncFamily_comap_of_isIso f hf hres
  obtain ⟨ι', hcount, hord, H₂, hfam₃, hsupp₃⟩ := hfam₂.exists_countable_reindex
  let _ := hcount
  let _ := hord
  obtain ⟨F, hF, hFsupp⟩ := exists_hypersurfaceFamily_isSnc_of_isSncFamily hfam₃
  refine ⟨n, M, U, hxU, e, F, hF, ?_⟩
  -- the support: `F.support = (val ∘ e) ⁻¹' E.support`
  have hsupp : (F.support : Set M) =
      (fun m => (f m).1) ⁻¹' (divisorOf H hH).support := by
    rw [hFsupp, hsupp₃, support_divisorOf, Set.preimage_iUnion]
    refine Set.iUnion_congr fun j => ?_
    rw [support_comap_eq_preimage]
    exact congrArg (Set.preimage ⇑f)
      (QuotientSpace.cosupport_comap
        (KLocallyRingedSpace.ofRestrict X.toKLocallyRingedSpace U).1 (H j))
  have hg : Function.Surjective ⇑f := by
    intro y
    obtain ⟨a, ha⟩ := (KLocallyRingedSpace.KIso.homeomorph e).surjective y
    exact ⟨a, ha⟩
  have hrange : Set.range (fun m => (f m).1) = (U : Set X) := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact (f m).2
    · intro hy
      obtain ⟨m, hm⟩ := hg ⟨y, hy⟩
      exact ⟨m, congrArg Subtype.val hm⟩
  calc Subtype.val '' (KLocallyRingedSpace.Hom.toFun e.hom '' F.support)
      = (fun m => (f m).1) '' F.support := Set.image_image _ _ _
    _ = (divisorOf H hH).support ∩ (U : Set X) := by
        rw [hsupp, Set.image_preimage_eq_inter_range, hrange]

end ClosedSubspace

end AnalyticSpace

end
