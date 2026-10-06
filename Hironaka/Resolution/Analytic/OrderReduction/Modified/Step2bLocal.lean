/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bCenter
import Hironaka.Manifold.BlowUp.Transform.Colon
import Hironaka.Manifold.BlowUp.Transform.OrderAlong
import Hironaka.Manifold.BlowUp.Transform.Weak
import Hironaka.Resolution.Analytic.OrderReduction.Functoriality
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The positive locus is local, and it commutes with local isomorphisms

Two facts about the centre of the monomial phase (`Step2bCenter.lean`):

* **Locality.** A point `x` of the member `E^j` lies in the positive locus (Kollár's `Z_{-1}` at the
  mark `1`: its connected component in `E^j` lies in `cosupp(𝓘, 1)`) iff `ord_{E^j} 𝓘 ≥ 1` at `x`,
  i.e. iff `𝓘_x ⊆ 𝓘_{E^j, x}`, a condition on the stalk at `x` alone. Forwards, this is the
  criterion `stalkIdeal_le_pow_of_eventually_le_ord` (near `x` the points of `E^j` lie in the
  component of `x`, `eventually_connectedComponentIn_eq`); backwards, the constancy of the order
  along `E^j` on its connected components (`ordAlong_eq_of_isPreconnected`, an identity theorem)
  together with `ord_{E^j} 𝓘 ≤ ord 𝓘`. This is the form in which the exponents after a step and the
  restriction to opens are read.

* **Functoriality.** Along a local analytic isomorphism `h : N → M` the positive locus of the
  pulled-back triple is the preimage of the positive locus (`Zminus1_comap`, the functoriality
  argument in the proof of [Kol07, Lemma 102]), so the active members of the pull-back are among the
  active members, and the centre of the pulled-back step is the preimage of the centre whenever the
  top members agree: the ingredients of the commutation of the phase with local isomorphisms
  [Kol07, 34.1] and of its compatibility under restriction.
-/

public section

noncomputable section

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BD

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)} {M : AnalyticManifold.{u} 𝕜 E}
  (T : AnalyticTriple ψ₀ M)

/-! ### Locality -/

omit [FiniteDimensional 𝕜 E] in
/-- `x ∈ E^j` lies in the positive locus iff the order of `𝓘` along `E^j` at `x` is at least `1`, a
condition on the stalk at `x`. -/
theorem mem_positiveLocus_iff_one_le_ordAlong {j : T.F.ι} {x : M} :
    x ∈ positiveLocus T j ↔
      x ∈ T.F.hyp j ∧ ((1 : ℕ) : ℕ∞) ≤ IdealSheaf.ordAlongIdeal (T.isSnc.1 j).idealSheaf T.I x := by
  have hY : IsClosedSubmanifold ψ₀ (T.F.hyp j) 1 := T.isSnc.1 j
  constructor
  · rintro ⟨hxY, hsub⟩
    refine ⟨hxY, (IdealSheaf.le_ordAlongIdeal_iff _ T.I x 1).mpr ?_⟩
    refine stalkIdeal_le_pow_of_eventually_le_ord hY T.I hxY ?_
    have h1 := (continuous_subtype_val.tendsto (⟨x, hxY⟩ : T.F.hyp j)).eventually
      (hY.eventually_connectedComponentIn_eq hxY)
    filter_upwards [h1] with y hy
    refine hsub ?_
    rw [← hy y.2]
    exact mem_connectedComponentIn y.2
  · rintro ⟨hxY, hord⟩
    refine ⟨hxY, fun y hy => ?_⟩
    have hyY : y ∈ T.F.hyp j := connectedComponentIn_subset _ _ hy
    have heq := ordAlong_eq_of_isPreconnected hY T.I (connectedComponentIn_subset _ x)
      isPreconnected_connectedComponentIn (mem_connectedComponentIn hxY) hy
    exact hord.trans (heq.le.trans (ordAlong_le_ord hY T.I hyY))

/-! ### Functoriality along local analytic isomorphisms -/

variable {N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- The positive locus of the pulled-back triple is the preimage of the positive locus
(`Zminus1_comap` at the mark `1`). -/
theorem positiveLocus_pullback (j : T.F.ι) :
    positiveLocus (T.pullback h hh) j = ⇑h ⁻¹' positiveLocus T j :=
  Zminus1_comap h hh T.I 1 (T.isSnc.1 j)

/-- A member active for the pull-back is active. -/
theorem activeMembers_pullback_subset : activeMembers (T.pullback h hh) ⊆ activeMembers T := by
  intro j hj
  obtain ⟨y, hy⟩ := hj
  exact ⟨h y, (positiveLocus_pullback T h hh j).subset hy⟩

/-- A member whose positive locus meets the range of `h` is active for the pull-back. -/
theorem mem_activeMembers_pullback_of_range {j : T.F.ι} {x : M} (hx : x ∈ positiveLocus T j)
    (hxr : x ∈ Set.range h) : j ∈ activeMembers (T.pullback h hh) := by
  obtain ⟨y, rfl⟩ := hxr
  exact ⟨y, (positiveLocus_pullback T h hh j).symm.subset hx⟩

/-- For a surjective local isomorphism the active members agree. -/
theorem activeMembers_pullback_of_surjective (hs : Function.Surjective h) :
    activeMembers (T.pullback h hh) = activeMembers T := by
  refine Set.Subset.antisymm (activeMembers_pullback_subset T h hh) fun j hj => ?_
  obtain ⟨x, hx⟩ := hj
  exact mem_activeMembers_pullback_of_range T h hh hx (hs x)

/-- When the top members agree, the Step 2b centre of the pull-back is the preimage of the Step 2b
centre. -/
theorem step2bCenter_pullback (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)
    (hfin' : (activeMembers (T.pullback h hh)).Finite)
    (hne' : (activeMembers (T.pullback h hh)).Nonempty)
    (htop : topMember (T.pullback h hh) hfin' hne' = topMember T hfin hne) :
    step2bCenter (T.pullback h hh) hfin' hne' = ⇑h ⁻¹' step2bCenter T hfin hne := by
  change positiveLocus (T.pullback h hh) (topMember (T.pullback h hh) hfin' hne') = _
  rw [htop]
  exact positiveLocus_pullback T h hh _

/-- The top members agree as soon as the top member of `T` is active for the pull-back (the
pull-back's active members lie among `T`'s, and `T`'s top member bounds them). -/
theorem topMember_pullback_eq (hfin : (activeMembers T).Finite) (hne : (activeMembers T).Nonempty)
    (hfin' : (activeMembers (T.pullback h hh)).Finite)
    (hne' : (activeMembers (T.pullback h hh)).Nonempty)
    (hmem : topMember T hfin hne ∈ activeMembers (T.pullback h hh)) :
    topMember (T.pullback h hh) hfin' hne' = topMember T hfin hne :=
  le_antisymm
    (le_topMember T hfin hne (activeMembers_pullback_subset T h hh (topMember_mem _ hfin' hne')))
    (le_topMember _ hfin' hne' hmem)

end Hironaka.Manifold.BMOmod

end
