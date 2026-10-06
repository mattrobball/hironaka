/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Basic
public import Hironaka.Manifold.IdealSheaf.Tuning
public import Hironaka.Manifold.FiniteSuccession.Order
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.Object
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Manifold.FiniteSuccession.OrderLemmas
import Hironaka.Manifold.IdealSheaf.CosupportDeriv
import Hironaka.Manifold.IdealSheaf.Identity
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Snc.Dictionary
import Hironaka.Manifold.Submanifold.Components
import Hironaka.Resolution.Analytic.OrderReduction.ColonOrder
import Hironaka.Scheme.Snc.TotalTransformOffCentre
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The first step of Lemma 102: the centre `Z_{-1}`

The proof of [Kol07, Lemma 102] begins by blowing up `Z_{-1}`, "the union of those irreducible
components `E^{jk} ⊂ E^j`" contained in `cosupp(I, m)`: the blow-up `π_{-1} : X_0 → X` is an
isomorphism, but the order of `I` along each such component drops by `m`, giving a new ideal sheaf
`I_0` with `max-ord_{E^{jk}} I_0 ≤ 0`, so that `cosupp(I_0, m)` contains no irreducible component
of `E^j`. On a manifold the irreducible components of the smooth
hypersurface `E^j` are its connected components, and `Z_{-1}` is the set `BD.Zminus1`:
the points of `E^j` whose component lies in `{ord 𝓘 ≥ m}`.

The first group of results describes `Z_{-1}` as a set and as a submanifold: its characterisation
(`mem_Zminus1_iff`), the inclusions `Z_{-1} ⊆ cosupp(𝓘, m)` and `Z_{-1} ⊆ E^j`, the fact that it
is a
union of connected components of `E^j`, and that it is a closed hypersurface
(`isClosedSubmanifold_Zminus1`): every point of `E^j` has an adapted chart of `E^j` whose source
meets `E^j` only inside the component of the point, so on that source `Z_{-1}` is all of `E^j` or
empty.

The second group is the first step itself. Blowing up `Z_{-1}` is a smooth blow-up sequence of
order `m` (`isOfOrder_firstStep`): `Z_{-1}` has simple normal crossings with `E`, an snc chart of
`E` at a point of `Z_{-1}` restricted to a neighbourhood meeting `E^j` only in the component of the
point being adapted to `Z_{-1}` (`hasSncWith_Zminus1`), and the order of `𝓘` along `Z_{-1}` is `m`
at each of its points, at least `m` because `ord 𝓘 ≥ m` on all of `Z_{-1}` and at most `m` by the
bound (`ordAlong_Zminus1_eq`). The weak transform `I_0` has order `0` over `Z_{-1}`
(`ord_weakTransformOf_eq_zero_of_mem_Zminus1`): the blowing-up of a hypersurface is a local
analytic isomorphism ([Kol07, Warning 20]), so the total transform has the order of `𝓘`, at most
`m`, and lies in the `m`-th power of the exceptional ideal, whose colon by that power is then the
unit ideal (`ColonOrder.lean`). Off `Z_{-1}` the weak transform has the order of `𝓘` at the image
(`ord_weakTransformOf_eq_of_not_mem`). Hence no component of the transform of `E^j` lies in
`cosupp(I_0, m)` (`Zminus1_weakTransformOf_eq_empty`).

The last group prepares the next triple `(S, I_0|_S, E_S)` of Kollár's proof, which requires
`I_0|_S` nonzero on every component of `S = E^j`. A D-balanced ideal sheaf ([Kol07, Definition 83])
of order at most `m` has order `0` or `m` at every point (`ord_eq_zero_or_eq_of_isDBalanced`), and
for such `𝓘` the restriction of `I_0` to the transform of `E^j` is nonzero everywhere
(`isNonzeroEverywhere_pullback_weakTransformOf`): its zero stalks form an open and closed set, while
every component of the transform of `E^j` carries a point where `I_0` has order `0`.

The results are assembled into Lemma 102's functor in `BD.lean`; their behaviour under pull-back is
in `Functoriality.lean`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BD

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [hfd : FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}

-- The finite-dimensionality `[FiniteDimensional 𝕜 E]` of the model space belongs to every statement
-- here, as to Kollár's varieties; a proof that does not need it names it (`have _hfd := hfd`) so
-- that it remains part of the statement.

/-- A point lies in `Z_{-1}` iff it lies in `E^j` and its connected component in `E^j` lies in
`cosupp(𝓘, m)` (the definition of `Zminus1` unfolded; the proof of [Kol07, Lemma 102]). -/
theorem mem_Zminus1_iff (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι) (x : M) :
    x ∈ Zminus1 T.I m (T.F.hyp j) ↔
      x ∈ T.F.hyp j ∧ connectedComponentIn (T.F.hyp j) x ⊆ {y | (m : ℕ∞) ≤ T.I.ord y} := by
  have _hfd := hfd
  exact Iff.rfl

omit hfd in
/-- The connected component through a point of `Z_{-1}` lies in `Z_{-1}`: `Z_{-1}` is a union of
connected components of the hypersurface. -/
theorem connectedComponentIn_subset_Zminus1 {I : AnalyticManifold.IdealSheaf M} {m : ℕ}
    {Y : Set M}
    {x : M} (hx : x ∈ Zminus1 I m Y) : connectedComponentIn Y x ⊆ Zminus1 I m Y := by
  intro y hy
  refine ⟨connectedComponentIn_subset Y x hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hx.2

/-- `Z_{-1} ⊆ cosupp(𝓘, m)` (the proof of [Kol07, Lemma 102]). -/
theorem Zminus1_subset_cosupp (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι) :
    Zminus1 T.I m (T.F.hyp j) ⊆ {x | (m : ℕ∞) ≤ T.I.ord x} := by
  have _hfd := hfd
  intro x hx
  exact hx.2 (mem_connectedComponentIn hx.1)

/-- `Z_{-1} ⊆ E^j` ("`E^{jk} ⊂ E^j`" in the proof of [Kol07, Lemma 102]). -/
theorem Zminus1_subset (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι) :
    Zminus1 T.I m (T.F.hyp j) ⊆ T.F.hyp j := by
  have _hfd := hfd
  exact fun _ hx => hx.1

/-- `Z_{-1}`, a union of connected components of the closed hypersurface `E^j`, is a closed
hypersurface: on the source of an adapted chart of `E^j` meeting `E^j` only inside one component,
`Z_{-1}` is all of `E^j` or empty. -/
theorem isClosedSubmanifold_Zminus1 (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι) :
    IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1 := by
  have _hfd := hfd
  have hY : IsClosedSubmanifold ψ₀ (T.F.hyp j) 1 := T.isSnc.1 j
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
    by_cases hxY : x ∈ T.F.hyp j
    · obtain ⟨φ, σ, hxs, -, hsub⟩ := hY.exists_adaptedChart_source_inter_subset hxY
      refine Filter.mem_of_superset (φ.open_source.mem_nhds hxs) fun y hy hyZ => hx ?_
      have hyC : y ∈ connectedComponentIn (T.F.hyp j) x := hsub ⟨hy, hyZ.1⟩
      refine ⟨hxY, ?_⟩
      rw [connectedComponentIn_eq hyC]
      exact hyZ.2
    · exact Filter.mem_of_superset (hY.isClosed.isOpen_compl.mem_nhds hxY) fun y hy hyZ => hy hyZ.1
  · obtain ⟨φ, σ, hbs, h, hsub⟩ := hY.exists_adaptedChart_source_inter_subset hb.1
    refine ⟨φ, σ, hbs, h.1, fun x hx => ?_⟩
    constructor
    · intro hxZ
      exact (h.2 x hx).mp hxZ.1
    · intro hz
      have hxY : x ∈ T.F.hyp j := (h.2 x hx).mpr hz
      exact connectedComponentIn_subset_Zminus1 hb (hsub ⟨hx, hxY⟩)

/-! ### `Z_{-1}` has simple normal crossings with `E`, and the order along it -/

/-- `Z_{-1}` has simple normal crossings with `E` (the centre of the proof of [Kol07, Lemma 102]
must be admissible): an snc chart of `E` at a point of `Z_{-1}`, restricted to a neighbourhood
meeting `E^j` only inside the component of the point, is adapted to `Z_{-1}` with the coordinate
of `E^j`. -/
theorem hasSncWith_Zminus1 (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι) :
    T.F.HasSncWith ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1 := by
  have _hfd := hfd
  intro a ha
  have haj : a ∈ T.F.hyp j := ha.1
  obtain ⟨φ, cidx, hc⟩ := T.isSnc.2.2 a
  obtain ⟨W, hW, hWo, haW⟩ :=
    eventually_nhds_iff.mp ((T.isSnc.1 j).eventually_connectedComponentIn_eq haj)
  refine ⟨φ.restrOpen W hWo, singleEmb (cidx ⟨j, haj⟩), cidx, ?_, hc.restrOpen hWo haW⟩
  refine isAdaptedChart_singleIdx (hc.restrOpen hWo haW).mem_maximalAtlas fun x hx => ?_
  rw [OpenPartialHomeomorph.restrOpen_source] at hx
  change x ∈ Zminus1 T.I m (T.F.hyp j) ↔ ψ₀ (φ x) (cidx ⟨j, haj⟩) = 0
  rw [← hc.mem_iff ⟨j, haj⟩ hx.1]
  refine ⟨fun h => Zminus1_subset T m j h, fun hxj => connectedComponentIn_subset_Zminus1 ha ?_⟩
  rw [← hW x hx.2 hxj]
  exact mem_connectedComponentIn hxj

/-- The order of `𝓘` along `Z_{-1}` at each of its points is `m` (the proof of
[Kol07, Lemma 102], "`max-ord_{E^{jk}} I ≤ m` to start with"): at least `m` because `ord 𝓘 ≥ m` on
all of `Z_{-1}`, at most `m` by the bound at the point. -/
theorem ordAlong_Zminus1_eq (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι)
    (hmax : ∀ x, T.I.ord x ≤ (m : ℕ∞))
    (hZ : IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1) {a : M}
    (ha : a ∈ Zminus1 T.I m (T.F.hyp j)) :
    IdealSheaf.ordAlongIdeal hZ.idealSheaf T.I a = m := by
  have _hfd := hfd
  refine le_antisymm ((ordAlong_le_ord hZ T.I ha).trans (hmax a)) ?_
  rw [IdealSheaf.le_ordAlongIdeal_iff]
  exact stalkIdeal_le_pow_of_eventually_le_ord hZ T.I ha
    (Filter.Eventually.of_forall fun y => Zminus1_subset_cosupp T m j y.2)

/-- The first step of the proof of [Kol07, Lemma 102], "blow up `Z_{-1}`": for `ord 𝓘 ≤ m`
everywhere, blowing up `Z_{-1}` is a smooth blow-up sequence of order `m` starting with
`(M, 𝓘, E)` ([Kol07, Definition 66]): the centre has normal crossings with `E`
(`hasSncWith_Zminus1`) and `ord_{Z_{-1}} 𝓘 = m` at every point of the centre
(`ordAlong_Zminus1_eq`). -/
theorem isOfOrder_firstStep (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι)
    (hmax : ∀ x, T.I.ord x ≤ (m : ℕ∞))
    (hZ : IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1) :
    (AnalyticManifold.BlowUpSequence.cons hZ (AnalyticManifold.BlowUpSequence.nil
        _)).toSuccession.IsOfOrder T.I T.F.idealSheaf m := by
  have _hfd := hfd
  rw [AnalyticManifold.BlowUpSequence.toSuccession_cons,
      AnalyticManifold.FiniteSuccession.isOfOrder_cons_iff,
    AnalyticManifold.BlowUpSequence.toSuccession_nil]
  exact ⟨⟨HasSncWith.hasOnlyNormalCrossingsWith_idealSheaf T.isSnc hZ (hasSncWith_Zminus1 T m j),
    fun a ha => ordAlong_Zminus1_eq T m j hmax hZ ha⟩,
    AnalyticManifold.FiniteSuccession.isOfOrder_nil _ _ _⟩

/-! ### The orders of the weak transform -/

/-- "Since `max-ord_{E^{jk}} I ≤ m` to start with, `max-ord_{E^{jk}} I_0 = max-ord_{E^{jk}} I − m
≤ 0`"
(the proof of [Kol07, Lemma 102]): for `ord 𝓘 ≤ m` everywhere, the weak transform `I_0` of `𝓘` by
the blowing-up of `Z_{-1}` has order `0` at every point over `Z_{-1}`. The stalk of `I_0` is the
colon `(π⁻¹(𝓘)_{x'} : u^m)`, `m` being the order of `𝓘` along `Z_{-1}` and `u` the scaling
coordinate of a blow-up chart; `π⁻¹(𝓘)_{x'} ⊆ (u)^m`, and `ord π⁻¹(𝓘)_{x'} = ord 𝓘_{π x'} ≤ m`
because the blowing-up of a hypersurface is an isomorphism ([Kol07, Warning 20]); the colon is then
the unit ideal (`ord_colon_totalTransform_eq_zero`). -/
theorem ord_weakTransformOf_eq_zero_of_mem_Zminus1 (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι)
    (hmax : ∀ x, T.I.ord x ≤ (m : ℕ∞))
    (hZ : IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1) {x' : Manifold.blowUp ψ₀ hZ}
    (hx : Manifold.blowUpπ ψ₀ hZ x' ∈ Zminus1 T.I m (T.F.hyp j)) :
    (IdealSheaf.weakTransformOf hZ (isBlowUp_blowUpπ ψ₀ hZ) T.I).ord x' = 0 := by
  have _hfd := hfd
  have h := isBlowUp_blowUpπ ψ₀ hZ
  -- the colon stalk, with exponent `m` (the order of `𝓘` along `Z_{-1}`)
  have hexp : (IdealSheaf.genericOrdAlong hZ.idealSheaf T.I (Manifold.blowUpπ ψ₀ hZ x')).toNat = m
      := by
    rw [genericOrdAlong_eq_ordAlong hZ T.I hx, ordAlong_Zminus1_eq T m j hmax hZ hx,
      ENat.toNat_natCast]
  have hcol := isDivExceptional_weakTransformOf hZ h T.I x'
  dsimp only at hcol
  rw [hexp] at hcol
  -- the blowing-up of a hypersurface is an analytic isomorphism
  obtain ⟨g, hg⟩ := IsBlowUp.exists_diffeomorph_of_codim_one hZ h
  have hπ : ⇑(Manifold.blowUpπ ψ₀ hZ) = ⇑g := funext fun p => (hg p).symm
  have hloc : IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E) ω ⇑(Manifold.blowUpπ ψ₀ hZ) x' := by
    rw [hπ]
    exact g.isLocalDiffeomorph x'
  unfold IdealSheaf.ord
  rw [hcol]
  exact ord_colon_totalTransform_eq_zero hZ h T.I hloc (hmax _) hx
    (ordAlong_Zminus1_eq T m j hmax hZ hx).ge

/-- Off the centre the blowing-up is the identity on the ideal sheaf: at a point not over `Z_{-1}`
the weak transform has the order of `𝓘` at its image. The exponent of the colon is `0` there (the
component of the centre through a point off it is empty), so the stalk of `I_0` is the total
transform's, and `π` is a local analytic isomorphism off the centre. -/
theorem ord_weakTransformOf_eq_of_not_mem (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι)
    (hZ : IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1) {x' : Manifold.blowUp ψ₀ hZ}
    (hx : Manifold.blowUpπ ψ₀ hZ x' ∉ Zminus1 T.I m (T.F.hyp j)) :
    (IdealSheaf.weakTransformOf hZ (isBlowUp_blowUpπ ψ₀ hZ) T.I).ord x' =
      T.I.ord (Manifold.blowUpπ ψ₀ hZ x') := by
  have _hfd := hfd
  have h := isBlowUp_blowUpπ ψ₀ hZ
  have hexp : (IdealSheaf.genericOrdAlong hZ.idealSheaf T.I (Manifold.blowUpπ ψ₀ hZ x')).toNat = 0
      := by
    rw [IdealSheaf.genericOrdAlong_def, hZ.cosupport_idealSheaf, connectedComponentIn_eq_empty hx]
    simp
  have hcol := isDivExceptional_weakTransformOf hZ h T.I x'
  dsimp only at hcol
  rw [hexp] at hcol
  rw [pow_zero, Ideal.one_eq_top, Ideal.colon_coe_top] at hcol
  have h1 : (IdealSheaf.weakTransformOf hZ h T.I).ord x' =
      (T.I.pullback _ h.contMDiff).ord x' := by
    unfold IdealSheaf.ord
    rw [hcol]
  rw [h1]
  exact IdealSheaf.ord_pullback_of_isLocalDiffeomorphAt _ _ T.I
    (h.isLocalDiffeomorphOn_compl ⟨x', hx⟩)

/-- "Thus `cosupp(I_0, m)` does not contain any irreducible component of `E^j`" (the proof of
[Kol07, Lemma 102]): for `1 ≤ m` and `ord 𝓘 ≤ m` everywhere, no connected component of the
preimage of `E^j` under the blowing-up of `Z_{-1}` lies in `cosupp(I_0, m)`. The points over
`Z_{-1}` carry order `0`; a component not over `Z_{-1}` is, through the isomorphism `π`
([Kol07, Warning 20]), a component of `E^j` that was not selected, which carries a point of order
`< m` of `𝓘`, where `I_0` has that order. -/
theorem Zminus1_weakTransformOf_eq_empty (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι) (hm : 1 ≤ m)
    (hmax : ∀ x, T.I.ord x ≤ (m : ℕ∞))
    (hZ : IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1) :
    Zminus1 (IdealSheaf.weakTransformOf hZ (isBlowUp_blowUpπ ψ₀ hZ) T.I) m
      (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j) = ∅ := by
  have _hfd := hfd
  have h := isBlowUp_blowUpπ ψ₀ hZ
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have hlt : ∀ y' ∈ connectedComponentIn (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j) y,
      ¬ (IdealSheaf.weakTransformOf hZ h T.I).ord y' < m :=
    fun y' hy' => not_lt.mpr (hy.2 hy')
  by_cases hyZ : Manifold.blowUpπ ψ₀ hZ y ∈ Zminus1 T.I m (T.F.hyp j)
  · refine hlt y (mem_connectedComponentIn hy.1) ?_
    rw [ord_weakTransformOf_eq_zero_of_mem_Zminus1 T m j hmax hZ hyZ]
    exact_mod_cast (hm : 0 < m)
  · -- the component of `π y` in `Eʲ` is not inside `cosupp(𝓘, m)`: a point `z` of order `< m`
    have hnot : ¬ connectedComponentIn (T.F.hyp j) (Manifold.blowUpπ ψ₀ hZ y) ⊆
        {z | (m : ℕ∞) ≤ T.I.ord z} := fun hsub => hyZ ⟨hy.1, hsub⟩
    obtain ⟨z, hz, hzo⟩ := Set.not_subset.mp hnot
    -- `z` is the image of a point `y'` of the component of `y` (the blowing-up is an isomorphism)
    obtain ⟨g, hg⟩ := IsBlowUp.exists_diffeomorph_of_codim_one hZ h
    have hπ : ⇑(Manifold.blowUpπ ψ₀ hZ) = ⇑g.toHomeomorph := funext fun p => (hg p).symm
    have himg : ⇑(Manifold.blowUpπ ψ₀ hZ) '' connectedComponentIn
        (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j) y =
        connectedComponentIn (T.F.hyp j) (Manifold.blowUpπ ψ₀ hZ y) := by
      have hy1 : y ∈ ⇑g.toHomeomorph ⁻¹' T.F.hyp j := by
        rw [← hπ]
        exact hy.1
      have := g.toHomeomorph.image_connectedComponentIn hy1
      rw [Set.image_preimage_eq _ g.toHomeomorph.surjective, ← hπ] at this
      exact this
    have hz0 := hz
    rw [← himg] at hz
    obtain ⟨y', hy'c, hy'z⟩ := hz
    rw [← hy'z] at hz0 hzo
    have hy'Z : Manifold.blowUpπ ψ₀ hZ y' ∉ Zminus1 T.I m (T.F.hyp j) := fun hmem =>
      hyZ (connectedComponentIn_subset_Zminus1 hmem (by
        rw [← connectedComponentIn_eq hz0]
        exact mem_connectedComponentIn (show Manifold.blowUpπ ψ₀ hZ y ∈ T.F.hyp j from hy.1)))
    refine hlt y' hy'c ?_
    rw [ord_weakTransformOf_eq_of_not_mem T m j hZ hy'Z]
    exact not_le.mp hzo

/-! ### The restriction of the weak transform to the transform of `E^j` is nonzero -/

/-- A D-balanced ideal sheaf ([Kol07, Definition 83]) with `ord 𝓘 ≤ m` everywhere has order `0` or
`m` at every point, as Kollár notes after Definition 83. Not stated in the sources for sheaves; the
argument: if `0 < ord_x 𝓘 = k < m` then `x ∉ cosupp(D^k 𝓘)`, so `(D^k 𝓘)^m ⊆ 𝓘^{m-k}` makes the
stalk of `𝓘^{m-k}`, hence of `𝓘`, the unit ideal at `x`. -/
theorem _root_.Manifold.IdealSheaf.ord_eq_zero_or_eq_of_isDBalanced
    {I : AnalyticManifold.IdealSheaf M} {m : ℕ} (hDb : I.IsDBalanced m)
        (hmax : ∀ x, I.ord x ≤ (m : ℕ∞))
    (x : M) : I.ord x = 0 ∨ I.ord x = m := by
  have _hfd := hfd
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, hm⟩ := hcon
  have hne : I.ord x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top m) (hmax x)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hkm : k < m := by
    have h1 := hmax x
    rw [← hk] at h1 hm
    exact lt_of_le_of_ne (by exact_mod_cast h1) fun h => hm (by rw [h])
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact h0 (by rw [← hk]; rfl)
  -- `x ∉ cosupp(D^k 𝓘) = {k + 1 ≤ ord 𝓘}`
  have hnot : x ∉ (I.iteratedDeriv k).support := by
    have hc := IdealSheaf.support_iteratedDeriv I (Nat.succ_pos k)
    rw [Nat.succ_sub_one] at hc
    rw [hc]
    intro hx
    have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ I.ord x := hx
    rw [← hk] at h1
    exact Nat.not_succ_le_self k (by exact_mod_cast h1)
  rw [IdealSheaf.mem_support, not_not] at hnot
  have hle := hDb k hkm
  rw [IdealSheaf.le_def] at hle
  have h1 := hle x
  rw [IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow, hnot, Ideal.top_pow] at h1
  have htop : I.stalkIdeal x = ⊤ :=
    eq_top_iff.mpr (h1.trans (Ideal.pow_le_self (by omega)))
  exact h0 ((IdealSheaf.ord_eq_zero_iff _).mpr fun hx => (IdealSheaf.mem_support _).mp hx htop)

/-- The next triple `(S, I_0|_S, E_S)` of the proof of [Kol07, Lemma 102], with `S := E^j`, has an
ideal sheaf that is nonzero on every component of `S`, as [Kol07, Definition 31 (1)] requires: for
D-balanced `𝓘` ([Kol07, Definition 83]) with `ord 𝓘 ≤ m` everywhere, the restriction of the weak
transform `I_0` to the transform of `E^j` (a closed hypersurface `hZ'` of the blown-up manifold) is
nonzero everywhere. The zero stalks of the restriction form an open and closed set, hence a union
of components of the transform of `E^j`; but every component carries a point where `I_0` has order
`0`: every point over `Z_{-1}`, and on a component not over `Z_{-1}` the point of order `< m`, hence
`0` by D-balancedness, of `𝓘` on the unselected component of `E^j` it covers; there the restricted
stalk is the unit ideal. -/
theorem isNonzeroEverywhere_pullback_weakTransformOf (T : AnalyticTriple ψ₀ M) (m : ℕ) (j : T.F.ι)
    (hDb : T.I.IsDBalanced m) (hmax : ∀ x, T.I.ord x ≤ (m : ℕ∞))
    (hZ : IsClosedSubmanifold ψ₀ (Zminus1 T.I m (T.F.hyp j)) 1)
    (hZ' : IsClosedSubmanifold ψ₀ (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j) 1) :
    ((IdealSheaf.weakTransformOf hZ (isBlowUp_blowUpπ ψ₀ hZ) T.I).pullback ⇑hZ'.inclusionMap
      hZ'.inclusionMap.contMDiff).IsNonzeroEverywhere := by
  have _hfd := hfd
  have h := isBlowUp_blowUpπ ψ₀ hZ
  -- where `I₀` has order `0`, the restricted stalk is the unit ideal
  have hunit : ∀ p : hZ'.toAnalyticManifold,
      (IdealSheaf.weakTransformOf hZ h T.I).ord (hZ'.inclusionMap p) = 0 →
      ((IdealSheaf.weakTransformOf hZ h T.I).pullback ⇑hZ'.inclusionMap
        hZ'.inclusionMap.contMDiff).stalkIdeal p ≠ ⊥ := by
    intro p hp
    rw [IdealSheaf.stalkIdeal_pullback]
    have htop : (IdealSheaf.weakTransformOf hZ h T.I).stalkIdeal (hZ'.inclusionMap p) = ⊤ := by
      by_contra hne
      exact (IdealSheaf.ord_eq_zero_iff _).mp hp ((IdealSheaf.mem_support _).mpr hne)
    rw [htop, Ideal.map_top]
    exact top_ne_bot
  intro p hp
  -- the zero stalks form a clopen set: the component of `p` consists of zero stalks
  have hcomp : connectedComponent p ⊆ {q : hZ'.toAnalyticManifold |
      ((IdealSheaf.weakTransformOf hZ h T.I).pullback ⇑hZ'.inclusionMap
        hZ'.inclusionMap.contMDiff).stalkIdeal q = ⊥} :=
    (IdealSheaf.isClopen_setOf_stalkIdeal_eq_bot _).connectedComponent_subset hp
  have hp1 : (hZ'.inclusionMap p : Manifold.blowUp ψ₀ hZ) ∈ ⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j
      := p.2
  by_cases hpZ : Manifold.blowUpπ ψ₀ hZ (hZ'.inclusionMap p) ∈ Zminus1 T.I m (T.F.hyp j)
  · exact hunit p (ord_weakTransformOf_eq_zero_of_mem_Zminus1 T m j hmax hZ hpZ) hp
  · -- a point `z` of the component of `π p` in `Eʲ` with `ord 𝓘 z < m`
    have hnot : ¬ connectedComponentIn (T.F.hyp j) (Manifold.blowUpπ ψ₀ hZ (hZ'.inclusionMap p)) ⊆
        {z | (m : ℕ∞) ≤ T.I.ord z} := fun hsub => hpZ ⟨hp1, hsub⟩
    obtain ⟨z, hz, hzo⟩ := Set.not_subset.mp hnot
    -- `z = π y'` with `y'` in the component of `p` in the transform of `E^j`
    obtain ⟨g, hg⟩ := IsBlowUp.exists_diffeomorph_of_codim_one hZ h
    have hπ : ⇑(Manifold.blowUpπ ψ₀ hZ) = ⇑g.toHomeomorph := funext fun q => (hg q).symm
    have himg : ⇑(Manifold.blowUpπ ψ₀ hZ) '' connectedComponentIn
        (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j)
        (hZ'.inclusionMap p) =
          connectedComponentIn (T.F.hyp j) (Manifold.blowUpπ ψ₀ hZ (hZ'.inclusionMap p)) := by
      have hp1' : (hZ'.inclusionMap p : Manifold.blowUp ψ₀ hZ) ∈ ⇑g.toHomeomorph ⁻¹' T.F.hyp j := by
        rw [← hπ]
        exact hp1
      have := g.toHomeomorph.image_connectedComponentIn hp1'
      rw [Set.image_preimage_eq _ g.toHomeomorph.surjective, ← hπ] at this
      exact this
    have hz0 := hz
    rw [← himg] at hz
    obtain ⟨y', hy'c, hy'z⟩ := hz
    rw [← hy'z] at hz0 hzo
    have hy'Z : Manifold.blowUpπ ψ₀ hZ y' ∉ Zminus1 T.I m (T.F.hyp j) := fun hmem =>
      hpZ (connectedComponentIn_subset_Zminus1 hmem (by
        rw [← connectedComponentIn_eq hz0]
        exact mem_connectedComponentIn
          (show Manifold.blowUpπ ψ₀ hZ (hZ'.inclusionMap p) ∈ T.F.hyp j from hp1)))
    -- `y'` is a point `q` of the component of `p` in the submanifold
    have hcompIn : connectedComponentIn (⇑(Manifold.blowUpπ ψ₀ hZ) ⁻¹' T.F.hyp j)
        (hZ'.inclusionMap p) =
        Subtype.val '' connectedComponent p := connectedComponentIn_eq_image p.2
    rw [hcompIn] at hy'c
    obtain ⟨q, hq, hqy'⟩ := hy'c
    refine hunit q ?_ (hcomp hq)
    change (IdealSheaf.weakTransformOf hZ h T.I).ord (q : Manifold.blowUp ψ₀ hZ) = 0
    rw [hqy', ord_weakTransformOf_eq_of_not_mem T m j hZ hy'Z]
    rcases IdealSheaf.ord_eq_zero_or_eq_of_isDBalanced hDb hmax
        (Manifold.blowUpπ ψ₀ hZ y') with h0 | hm'
    · exact h0
    · exact (hzo hm'.ge).elim

end Hironaka.Manifold.BD

end
