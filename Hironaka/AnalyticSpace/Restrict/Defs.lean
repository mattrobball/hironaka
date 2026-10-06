/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Defs
import Hironaka.AnalyticSpace.KSpace
import Hironaka.Manifold.IdealSheaf.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Open subspaces of analytic `K`-spaces

The restriction `(U, 𝒪_X|U)` of an analytic `K`-space to an open subset `U` is an analytic
`K`-space [Hir64, Ch. 0, §1, p. 120]. This file proves it and defines the restriction of spaces
and of morphisms to open subsets in the form used by the statement of the resolution theorem.

* Topology of an analytic `K`-space (not in the sources; routine): every point has an open
  neighbourhood homeomorphic to an open subset of a local model, itself a closed subset of an open
  subset of `Kⁿ`; hence `X` is locally compact and, being countable at infinity, second countable
  (`locallyCompactSpace`, `secondCountableTopology`), and every open subset is σ-compact.
* `AnalyticSpace.restrictOpen X V`: the open subspace `X | V`, an analytic `K`-space. The
  local-model clause for `X | V` follows from that of `X` by three applications of
  `KLocallyRingedSpace.isoOfRangeEq`; this is what the up-to-an-open form of the clause buys
  (`AnalyticSpace.locallyModel`).
* `openOf U` (`U` if open, the whole space otherwise), `restrictSet X U` (`X | U` for open `U`,
  `X` itself for non-open `U`) and `Hom.restrictSet f V : X | f⁻¹V ⟶ Y | V`, the lift of `f`
  through the open immersions, in which the resolution theorem is stated: `restrictSet X U`
  accepts any set `U`, and the convention for a non-open `U` keeps `Hom.restrictSet` total in `V`
  (the alternative convention `interior U` would leave it uninhabitable for a non-open `V` with
  empty interior).
* `f.IsIsoOver U`: `f` restricts to an isomorphism `f⁻¹(U) → U` over the set `U`, clause (2) of
  [Kol07, Theorem 45]; total in `U` by the convention of `restrictSet`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AnalyticSpace

variable {K : Type} [RCLike K]

open KLocallyRingedSpace

section Topology

variable (K) (n : ℕ)

/-- A local model is locally compact: its support is closed in `G`. -/
theorem locallyCompactSpace_localModel (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) : LocallyCompactSpace (localModel K n G f) :=
  have : LocallyCompactSpace (analyticSpaceOfOpen K n G).toLocallyRingedSpace.toTopCat :=
    G.isOpen.locallyCompactSpace
  (Manifold.IdealSheaf.isClosed_support (modelIdeal K n G f)).locallyCompactSpace

/-- A local model is second countable: its support is a subset of `G ⊆ Kⁿ`. -/
theorem secondCountableTopology_localModel (G : Opens (Kn.{u} K n)) {k : ℕ}
    (f : Fin k → AnalyticFun K n G) : SecondCountableTopology (localModel K n G f) :=
  have : SecondCountableTopology (analyticSpaceOfOpen K n G).toLocallyRingedSpace.toTopCat :=
    inferInstanceAs (SecondCountableTopology G)
  inferInstanceAs (SecondCountableTopology (modelIdeal K n G f).support)

end Topology


variable (X : AnalyticSpace.{u} K)

/-- Every point of an analytic `K`-space has an open neighbourhood that is locally compact and
second countable: it is homeomorphic to an open subset of a local model. -/
theorem exists_nhd_locallyCompact_secondCountable (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U), LocallyCompactSpace U ∧ SecondCountableTopology U := by
  obtain ⟨U, hxU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel x
  have := locallyCompactSpace_localModel K n G f
  have := secondCountableTopology_localModel K n G f
  have : LocallyCompactSpace ((localModel K n G f).restrictOpen W) :=
    W.isOpen.locallyCompactSpace
  have : SecondCountableTopology ((localModel K n G f).restrictOpen W) :=
    inferInstanceAs (SecondCountableTopology W)
  have h := KIso.homeomorph e
  exact ⟨U, hxU, h.locallyCompactSpace_iff.mpr inferInstance, h.secondCountableTopology⟩

/-- An analytic `K`-space is locally compact. -/
instance locallyCompactSpace : LocallyCompactSpace X := by
  refine ⟨fun x N hN => ?_⟩
  obtain ⟨U, hxU, hU, -⟩ := exists_nhd_locallyCompact_secondCountable X x
  obtain ⟨t, ht, hts, htc⟩ := hU.local_compact_nhds ⟨x, hxU⟩ (Subtype.val ⁻¹' N)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hN)
  refine ⟨Subtype.val '' t, U.isOpen.isOpenMap_subtype_val.image_mem_nhds ht, ?_,
    htc.image continuous_subtype_val⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hts hy

/-- An analytic `K`-space is second countable: it is countable at infinity and every point has a
second countable open neighbourhood. -/
instance secondCountableTopology : SecondCountableTopology X := by
  obtain ⟨C, hC, hCu⟩ := SigmaCompactSpace.exists_compact_covering (X := X)
  choose U hxU hU using fun x : X => exists_nhd_locallyCompact_secondCountable X x
  have hcov : ∀ m, ∃ t : Finset X, C m ⊆ ⋃ x ∈ t, (U x : Set X) := fun m =>
    (hC m).elim_finite_subcover (fun x : X => (U x : Set X)) (fun x => (U x).isOpen)
      fun y _ => Set.mem_iUnion.mpr ⟨y, hxU y⟩
  choose t ht using hcov
  have : ∀ p : (m : ℕ) × (t m), SecondCountableTopology (U p.2.1 : Set X) :=
    fun p => (hU p.2.1).2
  refine secondCountableTopology_of_countable_cover (ι := (m : ℕ) × (t m))
    (U := fun p => (U p.2.1 : Set X)) (fun p => (U p.2.1).isOpen) ?_
  apply Set.eq_univ_of_forall
  intro y
  have hy : y ∈ ⋃ m, C m := hCu ▸ Set.mem_univ y
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht m hm)
  exact Set.mem_iUnion.mpr ⟨⟨m, ⟨x, hxt⟩⟩, hyx⟩

/-- Every open subset of an analytic `K`-space is countable at infinity. -/
instance (V : Opens X) : SigmaCompactSpace V :=
  have : LocallyCompactSpace V := V.isOpen.locallyCompactSpace
  inferInstance

/-- The trace on the open subspace `X | V` of an open `U` of `X`, as an open of `X | V`. -/
abbrev traceOpens (V U : Opens X) : Opens (X.toKLocallyRingedSpace.restrictOpen V) :=
  (Opens.map (X.toKLocallyRingedSpace.ofRestrict V).1.base).obj U

/-- The range of the open immersion `(X | V) | U' ⟶ X`, `U'` the trace of `U` on `V`, is
`V ∩ U`. -/
theorem range_toFun_ofRestrict_ofRestrict (V U : Opens X) :
    Set.range (KLocallyRingedSpace.Hom.toFun
      (ofRestrict (X.toKLocallyRingedSpace.restrictOpen V) (traceOpens X V U) ≫
        ofRestrict X.toKLocallyRingedSpace V)) = (V : Set X) ∩ U := by
  rw [Hom.range_toFun_comp, range_toFun_ofRestrict]
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, hv⟩
  · rintro ⟨hxV, hxU⟩
    exact ⟨⟨x, hxV⟩, hxU, rfl⟩

/-- The open subspace `X | V` of an analytic `K`-space is an analytic `K`-space
[Hir64, Ch. 0, §1, p. 120]. -/
def restrictOpen (V : Opens X) : AnalyticSpace.{u} K where
  toKLocallyRingedSpace := X.toKLocallyRingedSpace.restrictOpen V
  locallyModel := by
    intro y
    obtain ⟨U, hyU, n, k, G, f, W, ⟨e⟩⟩ := X.locallyModel y.1
    -- (X | V) | U' ≅ (X | U) | U'', `U'`, `U''` the traces: both are `X` restricted to `U ∩ V`
    let a₁ := ofRestrict (X.toKLocallyRingedSpace.restrictOpen V) (traceOpens X V U) ≫
      ofRestrict X.toKLocallyRingedSpace V
    let a₂ := ofRestrict (X.toKLocallyRingedSpace.restrictOpen U) (traceOpens X U V) ≫
      ofRestrict X.toKLocallyRingedSpace U
    have ha₁ : LocallyRingedSpace.IsOpenImmersion a₁.1 :=
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((ofRestrict (X.toKLocallyRingedSpace.restrictOpen V) (traceOpens X V U)).1 ≫
          (ofRestrict X.toKLocallyRingedSpace V).1))
    have ha₂ : LocallyRingedSpace.IsOpenImmersion a₂.1 :=
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((ofRestrict (X.toKLocallyRingedSpace.restrictOpen U) (traceOpens X U V)).1 ≫
          (ofRestrict X.toKLocallyRingedSpace U).1))
    have h₁₂ : Set.range (KLocallyRingedSpace.Hom.toFun a₁) =
        Set.range (KLocallyRingedSpace.Hom.toFun a₂) := by
      simp only [a₁, a₂, range_toFun_ofRestrict_ofRestrict]
      exact Set.inter_comm _ _
    let i₁ := isoOfRangeEq a₁ a₂ h₁₂
    -- (X | U) | U'' ≅ (M | W) | W'', `W''` the image of `U''` under `e`
    let b := ofRestrict (X.toKLocallyRingedSpace.restrictOpen U) (traceOpens X U V) ≫ e.hom
    have hb : LocallyRingedSpace.IsOpenImmersion b.1 :=
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((ofRestrict (X.toKLocallyRingedSpace.restrictOpen U) (traceOpens X U V)).1 ≫ e.hom.1))
    let W'' : Opens ((localModel K n G f).restrictOpen W) :=
      ⟨Set.range (KLocallyRingedSpace.Hom.toFun b), isOpen_range_toFun b⟩
    let i₂ := isoOfRangeEq b (ofRestrict ((localModel K n G f).restrictOpen W) W'')
      (by rw [range_toFun_ofRestrict]; rfl)
    -- (M | W) | W'' ≅ M | W', `W'` the image of `W''` in `M`
    let c := ofRestrict ((localModel K n G f).restrictOpen W) W'' ≫
      ofRestrict (localModel K n G f) W
    have hc : LocallyRingedSpace.IsOpenImmersion c.1 :=
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((ofRestrict ((localModel K n G f).restrictOpen W) W'').1 ≫
          (ofRestrict (localModel K n G f) W).1))
    let W' : Opens (localModel K n G f) :=
      ⟨Set.range (KLocallyRingedSpace.Hom.toFun c), isOpen_range_toFun c⟩
    let i₃ := isoOfRangeEq c (ofRestrict (localModel K n G f) W')
      (by rw [range_toFun_ofRestrict]; rfl)
    exact ⟨traceOpens X V U, hyU, n, k, G, f, W', ⟨i₁ ≪≫ i₂ ≪≫ i₃⟩⟩
  t2 := inferInstanceAs (T2Space V)
  sigmaCompact := inferInstanceAs (SigmaCompactSpace V)

/-- The open set to which `restrictSet` restricts: `U` itself when it is open, the whole space
otherwise (`restrictSet X U` accepts any set `U`). -/
def openOf (U : Set X) : Opens X := by classical exact if h : IsOpen U then ⟨U, h⟩ else ⊤

/-- For an open `U`, `openOf X U` is `U` itself. -/
theorem openOf_of_isOpen {U : Set X} (h : IsOpen U) : openOf X U = ⟨U, h⟩ := by
  simp [openOf, h]

/-- For a non-open `U`, `openOf X U` is the whole space. -/
theorem openOf_of_not_isOpen {U : Set X} (h : ¬ IsOpen U) : openOf X U = ⊤ := by
  simp [openOf, h]

/-- `X | U` for an open `U` [Hir64, Ch. 0, §1, p. 120], `X` itself (restricted along `⊤`) for a
non-open `U`. -/
def restrictSet (U : Set X) : AnalyticSpace.{u} K := X.restrictOpen (openOf X U)

variable {X}

/-- The lift condition for `Hom.restrictSet`: `f` maps `f⁻¹V` into `V`, and the whole space into
the whole space. -/
theorem range_toFun_ofRestrict_comp_subset {Y : AnalyticSpace.{u} K} (f : X ⟶ Y) (V : Set Y) :
    Set.range (KLocallyRingedSpace.Hom.toFun
      (ofRestrict X.toKLocallyRingedSpace (openOf X (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) ≫
        (f : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace))) ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun
        (ofRestrict Y.toKLocallyRingedSpace (openOf Y V))) := by
  rw [Hom.range_toFun_comp, range_toFun_ofRestrict, range_toFun_ofRestrict]
  by_cases hV : IsOpen V
  · rw [openOf_of_isOpen X (hV.preimage (Hom.continuous_toFun f)), openOf_of_isOpen Y hV]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · rw [openOf_of_not_isOpen Y hV]
    exact fun _ _ => trivial

/-- The restriction `f | f⁻¹V : X | f⁻¹V ⟶ Y | V` of a morphism to an open subset `V` of the
target, the lift of `f` through the open immersion `Y | V ⟶ Y` (total in `V` by the convention
`openOf`). Its source is written with the coercion `⇑f`, as in the morphism types of the resolution
theorem. -/
def Hom.restrictSet {Y : AnalyticSpace.{u} K} (f : X ⟶ Y) (V : Set Y) :
    X.restrictSet (f ⁻¹' V) ⟶ Y.restrictSet V :=
  have h₁ : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict Y.toKLocallyRingedSpace (openOf Y V)).1 := inferInstance
  Hom.ofFac
    (ofRestrict X.toKLocallyRingedSpace (openOf X (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) ≫
      (f : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace))
    (ofRestrict Y.toKLocallyRingedSpace (openOf Y V))
    (LocallyRingedSpace.IsOpenImmersion.lift (H := h₁)
      (ofRestrict Y.toKLocallyRingedSpace (openOf Y V)).1
      (ofRestrict X.toKLocallyRingedSpace (openOf X (KLocallyRingedSpace.Hom.toFun f ⁻¹' V)) ≫
        (f : X.toKLocallyRingedSpace ⟶ Y.toKLocallyRingedSpace)).1
      (range_toFun_ofRestrict_comp_subset f V))
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (H := h₁) _ _ _)

end AnalyticSpace

/-! ### Isomorphisms over a subset of the target -/

namespace AnalyticSpace.Hom

variable {K : Type} [RCLike K]

/-- `f` restricts to an isomorphism `f⁻¹(U) → U` over the open set `U` (clause (2) of the
resolution problem of [Hir64, Introduction] and of [Kol07, Theorem 45]). -/
def IsIsoOver {X Y : AnalyticSpace.{u} K} (f : Y ⟶ X) (U : Set X) : Prop :=
  IsIso (f.restrictSet U)

end AnalyticSpace.Hom
