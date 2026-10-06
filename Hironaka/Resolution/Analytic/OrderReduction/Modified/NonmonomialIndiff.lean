/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialTriple
public import Hironaka.Resolution.Analytic.Functor.EraseEmptyBoundary
import Hironaka.Manifold.BlowUp.Transform.IdealSheafCongr
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The nonmonomial part is indifferent to empty boundary members

The counterpart, for boundary members, of the empty blow-up convention [Kol07, 32], for the
decomposition `I = M(I) · N(I)` of
[Kol07, Definition–Lemma 110] in its fine form: deleting empty members of the boundary changes
neither the fine monomial part `M(I)` nor the nonmonomial part `N(I) = I : M(I)`. Two boundary
families `G`, `G'` with simple normal crossings which differ by an *empty extension* along an order
embedding `e : G.ι ↪o G'.ι` (`HypersurfaceFamily.IsEmptyExtension`: the members correspond along
`e`, the members outside its range are empty) have the same connected components: an empty member
has none, and the components of corresponding members are the same subsets of `M` (`emptyExtIdx`, a
bijection of the component indices which preserves the component sets and their chosen
representatives). So the stalks of `M(I)`, finite products of the component factors
(`stalkIdeal_monomialPart`), agree (`Finset.prod_bij`), hence `M(I)` and `N(I)` agree
(`IdealSheaf.ofStalks_congr`). The nonmonomial triple of a triple with an empty extension of the
boundary is therefore the nonmonomial triple of the original with the boundary replaced
(`nonmonomialTriple_eq_of_isEmptyExtension`): the input of the indifference property of the rounds
on the nonmonomial part (the value of `bo d` read at the nonmonomial triple), and of the transport
of the invariant of the descent through the deletion of empty blow-ups.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMOmod

open _root_.Manifold

open Hironaka.Manifold.BMO

/-! ### Connected components along an equality of subsets -/

section Cast

variable {M : Type u} [TopologicalSpace M]

/-- Transport of connected components along an equality of subsets (a `cast`). -/
def ccCast {s t : Set M} (h : s = t) (C : ConnectedComponents s) : ConnectedComponents t :=
  cast (congrArg (fun r : Set M => ConnectedComponents r) h) C

theorem ccCast_ccCast {s t : Set M} (h : s = t) (C : ConnectedComponents s) :
    ccCast h.symm (ccCast h C) = C := by
  subst h
  rfl

theorem ccCast_injective {s t : Set M} (h : s = t) : Function.Injective (ccCast h) := by
  subst h
  exact fun _ _ hC => hC

/-- The chosen representative of a transported component is the representative of the component
(the transport is a `cast`, so the two `Quotient.out` are the same term after `subst`). -/
theorem out_val_ccCast {s t : Set M} (h : s = t) (C : ConnectedComponents s) :
    (ccCast h C).out.val = C.out.val := by
  subst h
  rfl

/-- The underlying subset of a transported component is the underlying subset of the component. -/
theorem image_preimage_ccCast {s t : Set M} (h : s = t) (C : ConnectedComponents s) :
    Subtype.val '' (ConnectedComponents.mk ⁻¹' {ccCast h C} : Set t) =
      Subtype.val '' (ConnectedComponents.mk ⁻¹' {C} : Set s) := by
  subst h
  rfl

end Cast

/-! ### The components of an empty extension -/

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ}
  {ψ : E ≃L[𝕜] (Fin n → 𝕜)} {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(𝕜, E) ω M]

variable {G G' : HypersurfaceFamily M} {e : G.ι ↪o G'.ι}
  (he : HypersurfaceFamily.IsEmptyExtension e)

/-- The component of `G'` corresponding to a component `⟨j, C⟩` of `G` under an empty extension
along `e`: the member `e j` (whose set is `G.hyp j`) with the component `C` transported. -/
def emptyExtIdx (i : ComponentIndex G) : ComponentIndex G' :=
  ⟨e i.1, ccCast (he.1 i.1).symm i.2⟩

theorem componentSet_emptyExtIdx (i : ComponentIndex G) :
    componentSet G' (emptyExtIdx he i) = componentSet G i := by
  unfold componentSet emptyExtIdx
  exact image_preimage_ccCast (he.1 i.1).symm i.2

theorem out_val_emptyExtIdx (i : ComponentIndex G) :
    (emptyExtIdx he i).2.out.val = i.2.out.val :=
  out_val_ccCast (he.1 i.1).symm i.2

theorem emptyExtIdx_injective : Function.Injective (emptyExtIdx he) := by
  rintro ⟨j, C⟩ ⟨j', C'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : j = j' := e.injective h1
  exact congrArg (Sigma.mk j) (ccCast_injective (he.1 j).symm (eq_of_heq h2))

/-- Every component of `G'` comes from a component of `G`: a member outside the range of `e` is
empty (`he.2`), so it has no connected component. -/
theorem emptyExtIdx_surjective : Function.Surjective (emptyExtIdx he) := by
  rintro ⟨b, C'⟩
  have hb : b ∈ Set.range e := by
    by_contra hb
    exact Set.eq_empty_iff_forall_notMem.mp (he.2 b hb) _ C'.out.2
  obtain ⟨j, rfl⟩ := hb
  refine ⟨⟨j, ccCast (he.1 j) C'⟩, ?_⟩
  change (⟨e j, ccCast (he.1 j).symm (ccCast (he.1 j) C')⟩ : ComponentIndex G') = ⟨e j, C'⟩
  rw [ccCast_ccCast]

omit [TopologicalSpace M] in
include he in
/-- The nonempty members of `G` are finite when those of `G'` are (they inject along `e`). -/
theorem finite_nonempty_left_of_isEmptyExtension (hfin : Finite {b // G'.hyp b ≠ ∅}) :
    Finite {j // G.hyp j ≠ ∅} :=
  Finite.of_injective
    (fun j : {j // G.hyp j ≠ ∅} => (⟨e j.1, by rw [he.1 j.1]; exact j.2⟩ : {b // G'.hyp b ≠ ∅}))
    fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))

omit [TopologicalSpace M] in
include he in
/-- The nonempty members of `G'` are finite when those of `G` are (every nonempty member of `G'`
is the image of a member of `G`). -/
theorem finite_nonempty_right_of_isEmptyExtension (hfin : Finite {j // G.hyp j ≠ ∅}) :
    Finite {b // G'.hyp b ≠ ∅} := by
  refine Finite.of_surjective
    (fun j : {j // G.hyp j ≠ ∅} => (⟨e j.1, by rw [he.1 j.1]; exact j.2⟩ : {b // G'.hyp b ≠ ∅}))
    ?_
  rintro ⟨b, hb⟩
  have hbr : b ∈ Set.range e := by
    by_contra hbr
    exact hb (he.2 b hbr)
  obtain ⟨j, rfl⟩ := hbr
  exact ⟨⟨j, by rw [← he.1 j]; exact hb⟩, rfl⟩

/-! ### The fine monomial part and the nonmonomial part -/

variable (hG : G.IsSnc ψ) (hG' : G'.IsSnc ψ) (I : IdealSheaf (structureSheaf 𝕜 E M))

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Corresponding components have the same reduced ideal sheaf (the ideal sheaf of a closed
submanifold depends only on the subset, `IsClosedSubmanifold.idealSheaf_congr`). -/
theorem componentIdeal_emptyExtIdx (i : ComponentIndex G) :
    componentIdeal G' hG' (emptyExtIdx he i) = componentIdeal G hG i := by
  unfold componentIdeal
  exact IsClosedSubmanifold.idealSheaf_congr _ _ (componentSet_emptyExtIdx he i)

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Corresponding components have the same exponent `ord_D I` (the same ideal sheaf, read at the
same representative). -/
theorem componentExponent_emptyExtIdx (i : ComponentIndex G) :
    componentExponent G' hG' I (emptyExtIdx he i) = componentExponent G hG I i := by
  unfold componentExponent
  rw [componentIdeal_emptyExtIdx he hG hG', out_val_emptyExtIdx he]

omit [IsManifold 𝓘(𝕜, E) ω M] in
/-- Corresponding components have the same fine monomial factor `𝓘_D ^ (ord_D I)`. -/
theorem componentFactor_emptyExtIdx (i : ComponentIndex G) :
    componentFactor G' hG' I (emptyExtIdx he i) = componentFactor G hG I i := by
  unfold componentFactor
  rw [componentIdeal_emptyExtIdx he hG hG', componentExponent_emptyExtIdx he hG hG' I]

omit [IsManifold 𝓘(𝕜, E) ω M] in
include he in
/-- The stalk products which define `M(I)` agree: the components through `x` correspond along
`emptyExtIdx` (same component sets), with the same factors. -/
theorem prod_componentFactor_stalkIdeal_eq_of_isEmptyExtension (x : M) :
    ∏ i ∈ IdealSheaf.activeFinset (componentSet G') (componentSet_locallyFinite G' hG') x,
        (componentFactor G' hG' I i).stalkIdeal x =
      ∏ i ∈ IdealSheaf.activeFinset (componentSet G) (componentSet_locallyFinite G hG) x,
        (componentFactor G hG I i).stalkIdeal x := by
  symm
  refine Finset.prod_bij (fun i _ => emptyExtIdx he i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [IdealSheaf.mem_activeFinset] at hi ⊢
    rw [componentSet_emptyExtIdx]
    exact hi
  · intro i₁ _ i₂ _ h
    exact emptyExtIdx_injective he h
  · intro i' hi'
    obtain ⟨i, rfl⟩ := emptyExtIdx_surjective he i'
    refine ⟨i, ?_, rfl⟩
    rw [IdealSheaf.mem_activeFinset] at hi' ⊢
    rw [componentSet_emptyExtIdx] at hi'
    exact hi'
  · intro i _
    rw [componentFactor_emptyExtIdx]

/-- Two ideal sheaves prescribed by the same stalk ideals are equal (the generator proofs are
irrelevant). -/
theorem _root_.Manifold.IdealSheaf.ofStalks_congr {X : TopCat}
    {𝒪 : TopCat.Sheaf CommRingCat X} {f g : ∀ x : X, Ideal (𝒪.presheaf.stalk x)} (h : f = g)
    (hf : IdealSheaf.HasLocalGenerators f) (hg : IdealSheaf.HasLocalGenerators g) :
    IdealSheaf.ofStalks 𝒪 f hf = IdealSheaf.ofStalks 𝒪 g hg := by
  subst h
  rfl

omit [IsManifold 𝓘(𝕜, E) ω M] in
include he in
/-- **The fine monomial part is indifferent to empty members**: `M(I)` for `G'` is `M(I)` for `G`
under an empty extension `G ↪ G'` (the counterpart, for boundary members, of [Kol07, 32], for the
decomposition of [Kol07, Definition–Lemma 110]). -/
theorem monomialPart_eq_of_isEmptyExtension : monomialPart G' hG' I = monomialPart G hG I := by
  unfold monomialPart IdealSheaf.locallyFiniteProduct
  exact IdealSheaf.ofStalks_congr
    (funext fun x => prod_componentFactor_stalkIdeal_eq_of_isEmptyExtension he hG hG' I x) _ _

include he in
/-- **The nonmonomial part is indifferent to empty members**: `N(I) = I : M(I)` for `G'` is `N(I)`
for `G` under an empty extension `G ↪ G'` (the counterpart, for boundary members, of [Kol07, 32],
for the decomposition of [Kol07, Definition–Lemma 110]). -/
theorem nonmonomialPart_eq_of_isEmptyExtension :
    nonmonomialPart G' hG' I = nonmonomialPart G hG I := by
  unfold nonmonomialPart
  exact IdealSheaf.ofStalks_congr
    (funext fun x => by rw [monomialPart_eq_of_isEmptyExtension he hG hG' I]) _ _

/-! ### The nonmonomial triple -/

/-- **The nonmonomial triple of a triple with an empty extension of the boundary** is the
nonmonomial triple of the original with the boundary replaced: the ideal `N(𝓘)` is the same
(`nonmonomialPart_eq_of_isEmptyExtension`), the boundary is the replaced one. This is the input of
the indifference property of the rounds on the nonmonomial part, the value of `bo d` being read at
the nonmonomial triple (the counterpart, for boundary members, of [Kol07, 32]). -/
theorem nonmonomialTriple_eq_of_isEmptyExtension {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
    {X : AnalyticManifold.{u} 𝕜 E} (T : AnalyticTriple ψ₀ X) (F' : HypersurfaceFamily X)
    (hsnc' : F'.IsSnc ψ₀) {e : F'.ι ↪o T.F.ι} (he : HypersurfaceFamily.IsEmptyExtension e) :
    nonmonomialTriple (⟨T.I, T.isNonzeroEverywhere, F', hsnc'⟩ : AnalyticTriple ψ₀ X) =
      ⟨(nonmonomialTriple T).I, (nonmonomialTriple T).isNonzeroEverywhere, F', hsnc'⟩ := by
  -- both identifications rewritten by their projection lemmas before the `exact`
  refine AnalyticTriple.ext' ?_ ?_
  · dsimp only
    rw [nonmonomialTriple_I, nonmonomialTriple_I]
    dsimp only
    exact (nonmonomialPart_eq_of_isEmptyExtension he hsnc' T.isSnc T.I).symm
  · dsimp only
    rw [nonmonomialTriple_F]

end Hironaka.Manifold.BMOmod

end
