/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Manifold.FiniteSuccession.Functor.Triple
public import Hironaka.Manifold.FiniteSuccession.CenterList
public import Hironaka.Manifold.FiniteSuccession.Order
public import Hironaka.Manifold.IdealSheaf.Basic
public import Hironaka.Manifold.StructureSheaf
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.DerivTransform
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.FiniteSuccession.Lemmas
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Resolution.Analytic.OrderReduction.ColonOrder
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The base cases of order reduction: dimensions zero and one

Kollár settles the two lowest dimensions of the induction directly [Kol07, 70]. In dimension `0`,
"`I = 𝒪_X`", `I` being nonzero on every irreducible component of `X`, and "everything is
resolved without blow-ups": on a manifold modelled on `𝕜⁰` the stalks of the structure sheaf are
fields (regular local domains of Krull dimension `0`), so a nonzero stalk ideal is the unit ideal
and the order of the ideal sheaf is `0 < m` everywhere (`AnalyticTriple.eq_top_of_dim_zero`,
`AnalyticTriple.ord_lt_of_dim_zero`). In dimension `1` the cosupport is a Cartier divisor, "our
algorithm tells us to blow up `Z := cosupp(I, m)`", and in the marked case the maximal order of
`I ⊗ 𝒪_X(Z)` drops: the ideal sheaf of a closed hypersurface is invertible in every
dimension, generated near each of its points by the adapted coordinate
(`IsClosedSubmanifold.isInvertible_idealSheaf_codimOne`); and when `cosupp(𝓘, m)` is a closed
hypersurface (on a curve it is a discrete closed set, the zeros of a nonzero analytic function of
one variable being isolated), blowing it up is a smooth blow-up sequence of order `≥ m` after
which the controlled transform has order `< m` everywhere
(`AnalyticTriple.orderReduction_dim_one`). For the last point the centre has simple normal
crossings with `E` because on a curve every closed hypersurface has
(`HypersurfaceFamily.IsSnc.hasSncWith_of_dim_one`), the order of `𝓘` along the centre is at least
`m`, over the centre the colon stalk is the unit ideal (`ColonOrder.lean`; the blowing-up of a
hypersurface is an isomorphism, [Kol07, Warning 20]), and off the centre the controlled transform is
the total transform, of the order of `𝓘` at the image, which is `< m` there.

The dimension-zero results give the base stage of the order-reduction tower
(`Stage/Family.lean`). The dimension-one results stand apart from the tower, whose recursion handles
dimension `1` through Theorem 103; they record Kollár's remark on that case.
-/

public section

noncomputable section

open Set Topology Filter AnalyticManifold
open scoped Manifold ContDiff
open IsManifold (maximalAtlas)

universe u

namespace Manifold

open Hironaka.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E]

-- The finite-dimensionality `[FiniteDimensional 𝕜 E]` of the model space belongs to every statement
-- here, as to Kollár's varieties; a proof that does not need it names it (`have _hfd := hfd`) so
-- that it remains part of the statement.

/-! ### Dimension zero -/

section DimZero

variable {ψ₀ : E ≃L[𝕜] (Fin 0 → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- The case `dim X = 0` of [Kol07, 70], "here `I = 𝒪_X` since `I` is assumed nonzero on every
irreducible component of `X`": on a manifold modelled on `𝕜⁰`, the ideal sheaf of a triple is the
unit ideal sheaf. The stalks are fields (regular local domains of Krull dimension `0`), so a
nonzero stalk ideal is the unit ideal. -/
theorem AnalyticTriple.eq_top_of_dim_zero (T : AnalyticTriple ψ₀ M) : T.I = ⊤ := by
  have _hfd := hfd
  have hfin : Module.finrank 𝕜 E = 0 := by
    rw [LinearEquiv.finrank_eq ψ₀.toLinearEquiv, Module.finrank_fin_fun]
  refine IdealSheaf.ext fun a => ?_
  rw [IdealSheaf.stalkIdeal_top]
  have := isDomain_stalk ψ₀ (IsManifold.chart_mem_maximalAtlas a) (mem_chart_source E a)
  have : Ring.KrullDimLE 0 ((structureSheaf 𝕜 E M).presheaf.stalk a) := by
    rw [Ring.krullDimLE_iff, ringKrullDim_stalk E a, hfin]
  have hF : IsField ((structureSheaf 𝕜 E M).presheaf.stalk a) :=
    Ring.KrullDimLE.isField_of_isDomain
  by_contra hne
  exact T.isNonzeroEverywhere a (le_bot_iff.mp
    ((IsLocalRing.isField_iff_maximalIdeal_eq.mp hF) ▸ IsLocalRing.le_maximalIdeal hne))

/-- The case `dim X = 0` of [Kol07, 70], "everything is resolved without blow-ups": on a manifold
modelled on `𝕜⁰`, the order of the ideal sheaf of a triple is `0 < m` at every point, so the empty
sequence is order reduction. -/
theorem AnalyticTriple.ord_lt_of_dim_zero (T : AnalyticTriple ψ₀ M) {m : ℕ} (hm : 1 ≤ m) (x : M) :
    T.I.ord x < (m : ℕ∞) := by
  have _hfd := hfd
  have h0 : T.I.ord x = 0 := by
    change IsLocalRing.ord (T.I.stalkIdeal x) = 0
    rw [T.eq_top_of_dim_zero, IdealSheaf.stalkIdeal_top, IsLocalRing.ord_top]
  rw [h0]
  exact_mod_cast (hm : 0 < m)

end DimZero

/-! ### Codimension one: the ideal sheaf of a hypersurface is invertible -/

section CodimOne

variable {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

/-- "The cosupport of an ideal sheaf is a Cartier divisor" in the case `dim X = 1` of [Kol07, 70],
in the form true in every dimension: the ideal sheaf of a closed submanifold of codimension one is
invertible, generated near each of its points by the adapted coordinate, a nonzero element of the
domain stalk, and off the submanifold by `1`. -/
theorem IsClosedSubmanifold.isInvertible_idealSheaf_codimOne {Z : Set M}
    (hZ : IsClosedSubmanifold ψ₀ Z 1) :
        IdealSheaf.IsInvertible hZ.idealSheaf := by
  have _hfd := hfd
  intro x
  by_cases hx : x ∈ Z
  · obtain ⟨φ, σ, hxφ, hφ⟩ := hZ.exists_adaptedChart x hx
    have := isDomain_stalk ψ₀ hφ.1 hxφ
    refine ⟨coord E ψ₀ φ hφ.1 hxφ (σ default),
      mem_nonZeroDivisors_of_ne_zero (coord_ne_zero hφ.1 hxφ _), ?_⟩
    rw [hZ.stalkIdeal_idealSheaf_eq_span hx hφ hxφ, Set.range_unique]
  · refine ⟨1, (nonZeroDivisors _).one_mem, ?_⟩
    rw [hZ.stalkIdeal_idealSheaf_of_notMem hx, Ideal.span_singleton_one]

end CodimOne

/-! ### Dimension one -/

section DimOne

variable {ψ₀ : E ≃L[𝕜] (Fin 1 → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

omit hfd in
/-- On a curve, two points of a chart's source at which one and the same coordinate vanishes
coincide: the chart is injective on its source and `𝕜¹` has a single coordinate. -/
theorem _root_.Hironaka.Manifold.eq_of_coord_eq_zero_of_dim_one {φ : OpenPartialHomeomorph M E}
    {x y : M}
    (hx : x ∈ φ.source) (hy : y ∈ φ.source) {k : Fin 1} (hx0 : ψ₀ (φ x) k = 0)
    (hy0 : ψ₀ (φ y) k = 0) : x = y := by
  apply φ.injOn hx hy
  apply ψ₀.injective
  funext i
  rw [Subsingleton.elim i k, hx0, hy0]

/-- On a curve every closed hypersurface `Z` has simple normal crossings with every boundary `E`
with simple normal crossings (the centre `Z := cosupp(I, m)` of the case `dim X = 1` of [Kol07, 70]
must be admissible): at a point of `Z` on a member of `E`, the snc chart of `E` restricted to the
source of an adapted chart of `Z` is adapted to `Z`, both meeting that source in the single point;
at a point of `Z` on no member, an adapted chart of `Z` is vacuously an snc chart. -/
theorem HypersurfaceFamily.IsSnc.hasSncWith_of_dim_one {F : HypersurfaceFamily M} (hF : F.IsSnc ψ₀)
    {Z : Set M} (hZ : IsClosedSubmanifold ψ₀ Z 1) : F.HasSncWith ψ₀ Z 1 := by
  have _hfd := hfd
  intro a ha
  obtain ⟨φ', σ', haφ', hφ'⟩ := hZ.exists_adaptedChart a ha
  have hZa : ∀ x ∈ φ'.source, x ∈ Z → x = a := fun x hx hxZ =>
    eq_of_coord_eq_zero_of_dim_one hx haφ' ((hφ'.2 x hx).mp hxZ 0) ((hφ'.2 a haφ').mp ha 0)
  by_cases hmem : ∃ j, a ∈ F.hyp j
  · obtain ⟨j₀, hj₀⟩ := hmem
    obtain ⟨φ, cidx, hc⟩ := hF.2.2 a
    refine ⟨φ.restrOpen φ'.source φ'.open_source, singleEmb (cidx ⟨j₀, hj₀⟩), cidx, ?_,
      hc.restrOpen φ'.open_source haφ'⟩
    refine isAdaptedChart_singleIdx (hc.restrOpen φ'.open_source haφ').mem_maximalAtlas
      fun x hx => ?_
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    change x ∈ Z ↔ ψ₀ (φ x) (cidx ⟨j₀, hj₀⟩) = 0
    have ha0 : ψ₀ (φ a) (cidx ⟨j₀, hj₀⟩) = 0 := (hc.mem_iff ⟨j₀, hj₀⟩ hc.mem_source).mp hj₀
    constructor
    · intro hxZ
      rw [hZa x hx.2 hxZ]
      exact ha0
    · intro hx0
      rw [eq_of_coord_eq_zero_of_dim_one hx.1 hc.mem_source hx0 ha0]
      exact ha
  · have hnone : ∀ j : {j // a ∈ F.hyp j}, False := fun j => hmem ⟨j.1, j.2⟩
    exact ⟨φ', σ', fun j => (hnone j).elim, hφ',
      ⟨hφ'.1, haφ', fun j => (hnone j).elim, fun j₁ _ _ => (hnone j₁).elim⟩⟩

/-- The case `dim X = 1` of [Kol07, 70], "our algorithm tells us to blow up `Z := cosupp(I, m)`",
after which the maximal order of `I ⊗ 𝒪_X(Z)` has dropped: on a manifold modelled on `𝕜¹`, for a
triple
with `1 ≤ m` and `ord 𝓘 ≤ m` everywhere, blowing up `cosupp(𝓘, m)` is a smooth blow-up sequence of
order `≥ m` starting with `(M, 𝓘, m, E)`, after which the controlled transform has order `< m` at
every point. The centre has normal crossings with `E` (`hasSncWith_of_dim_one`) and the order of `𝓘`
along it is at least `m`; over the centre the colon stalk is the unit ideal
(`ord_colon_totalTransform_eq_zero`; the blowing-up of a hypersurface is an isomorphism,
[Kol07, Warning 20]), off the centre the controlled transform is the total transform, of the order
of `𝓘` at the image, `< m` there. Under the bound `ord 𝓘 ≤ m` one step suffices. -/
theorem AnalyticTriple.orderReduction_dim_one (T : AnalyticTriple ψ₀ M) {m : ℕ} (hm : 1 ≤ m)
    (hmax : ∀ x, T.I.ord x ≤ (m : ℕ∞))
    (hZ : IsClosedSubmanifold ψ₀ {x | (m : ℕ∞) ≤ T.I.ord x} 1) :
    (BlowUpSequence.cons hZ (BlowUpSequence.nil _)).toSuccession.IsOfOrderGe T.I m T.F.idealSheaf ∧
      ∀ y : (BlowUpSequence.cons hZ (BlowUpSequence.nil _)).toSuccession.stage (Fin.last _),
        ((BlowUpSequence.cons hZ (BlowUpSequence.nil _)).toSuccession.markedTransformSeq T.I m
          (Fin.last _)).ord y < (m : ℕ∞) := by
  have _hfd := hfd
  -- the order of `𝓘` along the centre is `≥ m`
  have hord : ∀ a ∈ {x | (m : ℕ∞) ≤ T.I.ord x},
      (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal hZ.idealSheaf T.I a := fun a ha => by
    rw [IdealSheaf.le_ordAlongIdeal_iff]
    exact stalkIdeal_le_pow_of_eventually_le_ord hZ T.I ha (Eventually.of_forall fun y => y.2)
  refine ⟨?_, ?_⟩
  · rw [BlowUpSequence.toSuccession_cons, FiniteSuccession.isOfOrderGe_cons_iff,
      BlowUpSequence.toSuccession_nil]
    exact ⟨⟨HasSncWith.hasOnlyNormalCrossingsWith_idealSheaf T.isSnc hZ
      (T.isSnc.hasSncWith_of_dim_one hZ), hord⟩,
          FiniteSuccession.isOfOrderGe_nil _ _ _⟩
  · set S := (BlowUpSequence.cons hZ (BlowUpSequence.nil _)).toSuccession with hSdef
    intro y
    have : NeZero S.length := ⟨Nat.one_ne_zero⟩
    -- the controlled transform after the one step
    have hmk : S.markedTransformSeq T.I m (Fin.last _) =
        (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center 0) (S.isBlowUp_map 0)
          ⟨T.I, m⟩).I := rfl
    rw [hmk]
    change IdealSheaf.ord (MarkedIdealSheaf.birationalTransform
      (S.isClosedSubmanifold_center 0) (S.isBlowUp_map 0) ⟨T.I, m⟩).I y < (m : ℕ∞)
    have hcenter : (S.center 0).support = {x | (m : ℕ∞) ≤ T.I.ord x} := hZ.cosupport_idealSheaf
    have hord' : ∀ a ∈ (S.center 0).support,
        (m : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (S.isClosedSubmanifold_center 0).idealSheaf T.I a := by
      rw [S.idealSheaf_center, hcenter]
      exact hord
    -- the blowing-up of a hypersurface is an analytic isomorphism
    obtain ⟨g, hg⟩ := IsBlowUp.exists_diffeomorph_of_codim_one hZ (isBlowUp_blowUpπ ψ₀ hZ)
    have hπ : ⇑(blowUpπ ψ₀ hZ) = ⇑g := funext fun p => (hg p).symm
    have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω (S.map 0) y := by
      change IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω ⇑(blowUpπ ψ₀ hZ) y
      rw [hπ]
      exact g.isLocalDiffeomorph y
    by_cases hy : S.map 0 y ∈ (S.center 0).support
    · -- over the centre: the colon stalk with exponent `m` is the unit ideal
      have hcol := isDivExceptional_birationalTransform (S.isClosedSubmanifold_center 0)
        (S.isBlowUp_map 0) ⟨T.I, m⟩ hord' y
      dsimp only at hcol
      unfold IdealSheaf.ord
      rw [hcol, ord_colon_totalTransform_eq_zero (S.isClosedSubmanifold_center 0)
        (S.isBlowUp_map 0) T.I hloc (hmax _) hy (hord' _ hy)]
      exact_mod_cast (hm : 0 < m)
    · -- off the centre: the controlled transform is the total transform, of order `ord 𝓘 (π y) < m`
      have hst := birationalTransform_stalkIdeal_of_notMem (S.isClosedSubmanifold_center 0)
        (S.isBlowUp_map 0) hord' hy
      have h1 : (MarkedIdealSheaf.birationalTransform (S.isClosedSubmanifold_center 0)
          (S.isBlowUp_map 0) ⟨T.I, m⟩).I.ord y =
          (T.I.pullback (S.map 0) (S.isBlowUp_map 0).contMDiff).ord y := by
        unfold IdealSheaf.ord
        rw [hst]
      have h2 : (T.I.pullback (S.map 0) (S.isBlowUp_map 0).contMDiff).ord y = T.I.ord (S.map 0 y) :=
        IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I hloc
      rw [hcenter] at hy
      exact (h1.trans h2).trans_lt (not_le.mp hy)

end DimOne

end Manifold

end
