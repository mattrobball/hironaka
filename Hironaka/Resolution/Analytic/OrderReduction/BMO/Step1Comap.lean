/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.MaximalContact.StalkEquiv
public import Hironaka.Manifold.FiniteSuccession.Functor.Pullback
public import Hironaka.Resolution.Analytic.OrderReduction.BMO.NonmonomialPart
import Hironaka.Manifold.BlowUp.Transform.GermIso
import Hironaka.Manifold.FiniteSuccession.PullbackIdealSheaf
import Hironaka.Manifold.IdealSheaf.DerivLocality
import Hironaka.Manifold.IdealSheaf.Pullback
import Hironaka.Manifold.Submanifold.Components
import Hironaka.Resolution.Analytic.Functor.PullbackTransport
import Hironaka.Resolution.Analytic.OrderReduction.BMO.Step1MeasureOrder
import Hironaka.Resolution.Analytic.OrderReduction.Modified.Step2bTools
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The monomial and nonmonomial parts commute with local analytic isomorphisms

For a local analytic isomorphism `h : N → M` and a boundary family `F` on `M` with simple normal
crossings, the pulled-back family `F.comap h` has the members `h⁻¹(E^j)`, and the monomial part with
respect to it of the pulled-back ideal is the pull-back of the monomial part: `M(h^*𝓘) = h^* M(𝓘)`,
and likewise `N(h^*𝓘) = h^* N(𝓘)` (`monomialPart_comap`, `nonmonomialPart_comap`). This is the
compatibility of the decomposition `𝓘 = M(𝓘) · N(𝓘)` of [Kol07, Definition–Lemma 110] with local
analytic isomorphisms, the analytic form of the smooth morphisms of [Kol07, 34.1], which the
functoriality of the marked order reduction [Kol07, Theorem 107 (2)] requires of every step of its
construction.

Since `M(𝓘)` is a locally finite product of component factors (`BMO/MonomialPart.lean`), the
statement is proved stalk by stalk. Its core is the correspondence of connected components under
`h`: at a point `b` with `a = h b`, the connected component of `h⁻¹(E^j)` through `b` agrees near
`b` with the preimage of the component of `E^j` through `a` (both agree with `h⁻¹(E^j)` near `b`,
the components being open in their members), so the two reduced ideal sheaves have the same stalk
(`componentIdeal_comap_stalkIdeal`), and the order of `h^*𝓘` along the one is the order of `𝓘` along
the other (`componentExponent_comap`). The factors through `b` then correspond bijectively to the
factors through `a`, with equal exponents. -/

public section

open Set Topology TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace Hironaka.Manifold.BMO

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : ℕ} {ψ₀ : E ≃L[𝕜] (Fin n → 𝕜)}
  {M N : AnalyticManifold.{u} 𝕜 E} (h : AnalyticMap N M)
  (hh : IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) ω h)

/-- `Ideal.map` along a ring homomorphism distributes over a finite product of ideals. -/
theorem map_finset_prod_ideal {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S]
    [RingHomClass F R S] (f : F) {ι : Type*} (s : Finset ι) (J : ι → Ideal R) :
    Ideal.map f (∏ i ∈ s, J i) = ∏ i ∈ s, Ideal.map f (J i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, Ideal.one_eq_top, Ideal.map_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Ideal.map_mul, ih]

omit [FiniteDimensional 𝕜 E] in
/-- A connected component of a member of a boundary family with simple normal crossings is the
intersection of the member with an open set of `M`: the member is a closed submanifold, hence
locally connected, so its connected components are open in it. -/
theorem exists_isOpen_componentSet_eq (G : HypersurfaceFamily M) (hG : G.IsSnc ψ₀)
    (i₀ : ComponentIndex G) :
    ∃ W : Set M, IsOpen W ∧ componentSet G i₀ = G.hyp i₀.1 ∩ W := by
  have _hlc : LocallyConnectedSpace (G.hyp i₀.1) :=
    (hG.isClosedSubmanifold i₀.1).locallyConnectedSpace'
  have hpre : (Subtype.val : G.hyp i₀.1 → M) ⁻¹' componentSet G i₀
      = connectedComponent i₀.2.out := by
    rw [componentSet, Set.preimage_image_eq _ Subtype.val_injective]
    conv_lhs => rw [← Quotient.out_eq' i₀.2]
    exact connectedComponents_preimage_singleton
  have hopen : IsOpen ((Subtype.val : G.hyp i₀.1 → M) ⁻¹' componentSet G i₀) := by
    rw [hpre]; exact isOpen_connectedComponent
  obtain ⟨W, hWo, hW⟩ := isOpen_induced_iff.mp hopen
  have hsub : componentSet G i₀ ⊆ G.hyp i₀.1 := Subtype.coe_image_subset _ _
  have hrange : Set.range (Subtype.val : G.hyp i₀.1 → M) = G.hyp i₀.1 := Subtype.range_coe
  refine ⟨W, hWo, ?_⟩
  have e1 : componentSet G i₀
      = (Subtype.val : G.hyp i₀.1 → M) '' ((Subtype.val) ⁻¹' componentSet G i₀) := by
    rw [Set.image_preimage_eq_inter_range, hrange, Set.inter_eq_self_of_subset_left hsub]
  rw [e1, ← hW, Set.image_preimage_eq_inter_range, hrange, Set.inter_comm]

omit [FiniteDimensional 𝕜 E] in
/-- A point of a member lies on the component indexed by its own connected component. -/
theorem mem_componentSet_mk (G : HypersurfaceFamily M) (j : G.ι) {x : M} (hx : x ∈ G.hyp j) :
    x ∈ componentSet G ⟨j, ConnectedComponents.mk ⟨x, hx⟩⟩ :=
  ⟨⟨x, hx⟩, rfl, rfl⟩

omit [FiniteDimensional 𝕜 E] in
/-- The connected component of a point of `componentSet G i₀` in its member is the component of
`i₀`. -/
theorem mk_eq_of_mem_componentSet (G : HypersurfaceFamily M) (i₀ : ComponentIndex G) {x : M}
    (hx : x ∈ componentSet G i₀) (hxmem : x ∈ G.hyp i₀.1) :
    ConnectedComponents.mk (⟨x, hxmem⟩ : G.hyp i₀.1) = i₀.2 := by
  obtain ⟨y, hy, hyx⟩ := hx
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
  rw [show (⟨x, hxmem⟩ : G.hyp i₀.1) = y from Subtype.ext hyx.symm, hy]

omit [FiniteDimensional 𝕜 E] in
/-- Two components of `G` through a common point `x` with the same member index are equal: each is
the connected component of `x` in that member. -/
theorem componentIndex_ext_of_mem {G : HypersurfaceFamily M} {i₁ i₂ : ComponentIndex G} {x : M}
    (h1 : x ∈ componentSet G i₁) (h2 : x ∈ componentSet G i₂) (hj : i₁.1 = i₂.1) : i₁ = i₂ := by
  obtain ⟨j₁, C₁⟩ := i₁
  obtain ⟨j₂, C₂⟩ := i₂
  obtain rfl : j₁ = j₂ := hj
  have hm : x ∈ G.hyp j₁ := (Subtype.coe_image_subset _ _) h1
  rw [Sigma.mk.inj_iff]
  refine ⟨rfl, heq_of_eq ?_⟩
  calc C₁ = ConnectedComponents.mk (⟨x, hm⟩ : G.hyp j₁) :=
        (mk_eq_of_mem_componentSet G ⟨j₁, C₁⟩ h1 hm).symm
    _ = C₂ := mk_eq_of_mem_componentSet G ⟨j₁, C₂⟩ h2 hm

omit [FiniteDimensional 𝕜 E] in
/-- Let `i'` be a component of the pulled-back family `F.comap h` and `i` a component of `F` with
the same member index, and let `b` lie on `i'` with `h b` on `i`. Then the stalk at `b` of the
reduced ideal sheaf of `i'` is the stalk of the pull-back `h^* 𝓘_D` of the reduced ideal sheaf of
`i`: the component `i'` and the preimage `h⁻¹(D)` agree on a neighbourhood of `b`, both being the
member `h⁻¹(E^j)` there (`exists_isOpen_componentSet_eq` on either side), and the ideal sheaf of a
closed submanifold depends only on the submanifold near the point. -/
theorem componentIdeal_comap_stalkIdeal (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (i : ComponentIndex F) (i' : ComponentIndex (F.comap h)) {b : N}
    (hib : b ∈ componentSet (F.comap h) i') (hnb : h b ∈ componentSet F i)
    (hji : i'.1 = i.1) :
    (componentIdeal (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh) i').stalkIdeal b
      = ((componentIdeal F hF i).pullback h h.contMDiff).stalkIdeal b := by
  -- the germ-agreement: both `componentSet` traces are `h⁻¹(E^j)` on `W₁ ∩ h⁻¹O`
  obtain ⟨W1, hW1o, hW1⟩ :=
    exists_isOpen_componentSet_eq (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh) i'
  obtain ⟨O, hOo, hO⟩ := exists_isOpen_componentSet_eq F hF i
  have hcomap_hyp : (F.comap h).hyp i'.1 = ⇑h ⁻¹' F.hyp i.1 := by
    simp only [HypersurfaceFamily.comap_hyp, hji]
  have hbU : b ∈ W1 ∩ ⇑h ⁻¹' O :=
    ⟨(hW1 ▸ hib).2, Set.mem_preimage.mpr (hO ▸ hnb).2⟩
  have hYY' : componentSet (F.comap h) i' ∩ (W1 ∩ ⇑h ⁻¹' O)
      = (⇑h ⁻¹' componentSet F i) ∩ (W1 ∩ ⇑h ⁻¹' O) := by
    rw [hW1, hcomap_hyp, hO, Set.preimage_inter]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [componentIdeal, componentIdeal,
    comap_idealSheaf_of_isLocalDiffeomorph ψ₀ h hh (componentSubmanifold F hF i)]
  exact IsClosedSubmanifold.stalkIdeal_idealSheaf_congr_nhds _ _ hib
    (hW1o.inter (hOo.preimage h.contMDiff.continuous)) hbU hYY'

omit [FiniteDimensional 𝕜 E] in
/-- The exponents of the monomial part transport under a local analytic isomorphism: for a component
`i'` of `F.comap h` and the component `i` of `F` with the same member index that `h` maps it into,
`ord_{D'}(h^*𝓘) = ord_D 𝓘`. The order along a component is read at any of its points; at `b` the
two reduced ideal sheaves agree (`componentIdeal_comap_stalkIdeal`) and the order along a
submanifold is preserved by a local analytic isomorphism. -/
theorem componentExponent_comap (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (I : AnalyticManifold.IdealSheaf M) (i : ComponentIndex F)
        (i' : ComponentIndex (F.comap h)) {b : N}
    (hib : b ∈ componentSet (F.comap h) i') (hnb : h b ∈ componentSet F i) (hji : i'.1 = i.1) :
    componentExponent (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
        (I.pullback h h.contMDiff) i'
      = componentExponent F hF I i := by
  have hcongr : IdealSheaf.ordAlongIdeal (componentIdeal (F.comap h)
        (HypersurfaceFamily.isSnc_comap hF h hh) i') (I.pullback h h.contMDiff) b
      = IdealSheaf.ordAlongIdeal ((componentIdeal F hF i).pullback h h.contMDiff)
        (I.pullback h h.contMDiff) b := by
    unfold IdealSheaf.ordAlongIdeal
    rw [componentIdeal_comap_stalkIdeal h hh F hF i i' hib hnb hji]
  rw [componentExponent_eq_toNat_ordAlongIdeal (F.comap h)
        (HypersurfaceFamily.isSnc_comap hF h hh) (I.pullback h h.contMDiff) i' hib,
      componentExponent_eq_toNat_ordAlongIdeal F hF I i hnb, hcongr,
      IdealSheaf.ordAlongIdeal_comap_of_isLocalDiffeomorphAt h (componentIdeal F hF i) I (hh b)]

omit [FiniteDimensional 𝕜 E] in
/-- The factor of `M(h^*𝓘)` at a component `i'` of `F.comap h`, at a stalk `b`, is the image of the
factor of `M(𝓘)` at the corresponding component `i` of `F` under the isomorphism of stalks induced
by `h`: the two reduced ideal sheaves correspond (`componentIdeal_comap_stalkIdeal`) and the
exponents agree (`componentExponent_comap`). -/
theorem componentFactor_comap_stalkIdeal (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (I : AnalyticManifold.IdealSheaf M) (i : ComponentIndex F)
        (i' : ComponentIndex (F.comap h)) {b : N}
    (hib : b ∈ componentSet (F.comap h) i') (hnb : h b ∈ componentSet F i) (hji : i'.1 = i.1) :
    (componentFactor (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
        (I.pullback h h.contMDiff) i').stalkIdeal b
      = ((componentFactor F hF I i).stalkIdeal (h b)).map (germAlgEquiv h (hh b)) := by
  unfold componentFactor
  rw [IdealSheaf.stalkIdeal_pow, IdealSheaf.stalkIdeal_pow,
    componentExponent_comap h hh F hF I i i' hib hnb hji,
    componentIdeal_comap_stalkIdeal h hh F hF i i' hib hnb hji,
    stalkIdeal_comap_eq_map_germAlgEquiv h hh (componentIdeal F hF i) b, Ideal.map_pow]

omit [FiniteDimensional 𝕜 E] in
/-- The monomial part commutes with pull-back along a local analytic isomorphism:
`M(h^*𝓘) = h^* M(𝓘)`, the monomial part on the left taken with respect to the pulled-back boundary
family `F.comap h` (the compatibility of [Kol07, Definition–Lemma 110] with local analytic
isomorphisms, the analytic form of the smooth morphisms of [Kol07, 34.1]). Stalkwise,
the components of `F.comap h` through `b` correspond bijectively to the components of `F` through
`h b`, with corresponding factors (`componentFactor_comap_stalkIdeal`). -/
theorem monomialPart_comap (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (I : AnalyticManifold.IdealSheaf M) :
    monomialPart (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
        (I.pullback h h.contMDiff)
      = (monomialPart F hF I).pullback h h.contMDiff := by
  refine IdealSheaf.ext fun b => ?_
  rw [stalkIdeal_comap_eq_map_germAlgEquiv h hh (monomialPart F hF I) b, stalkIdeal_monomialPart,
    stalkIdeal_monomialPart, map_finset_prod_ideal]
  -- a point on a comap-component maps into the corresponding member of `F` (defeq)
  have key : ∀ i' : ComponentIndex (F.comap h), b ∈ componentSet (F.comap h) i' →
      h b ∈ F.hyp i'.1 := by
    intro i' hi'
    have hb : b ∈ (F.comap h).hyp i'.1 := (Subtype.coe_image_subset _ _) hi'
    exact hb
  refine Finset.prod_bij
    (fun i' hi' => (⟨i'.1, ConnectedComponents.mk
      ⟨h b, key i' (IdealSheaf.mem_activeFinset.mp hi')⟩⟩ : ComponentIndex F)) ?_ ?_ ?_ ?_
  · intro i' hi'
    rw [IdealSheaf.mem_activeFinset]
    exact mem_componentSet_mk F i'.1 (key i' (IdealSheaf.mem_activeFinset.mp hi'))
  · intro i₁ hi₁ i₂ hi₂ heq
    have hj : i₁.1 = i₂.1 := by have hf := congrArg Sigma.fst heq; exact hf
    exact componentIndex_ext_of_mem (IdealSheaf.mem_activeFinset.mp hi₁)
      (IdealSheaf.mem_activeFinset.mp hi₂) hj
  · intro i hi
    have hi_mem := IdealSheaf.mem_activeFinset.mp hi
    have hhb : h b ∈ F.hyp i.1 := (Subtype.coe_image_subset _ _) hi_mem
    have hbmem : b ∈ (F.comap h).hyp i.1 := hhb
    refine ⟨⟨i.1, ConnectedComponents.mk ⟨b, hbmem⟩⟩, ?_, ?_⟩
    · rw [IdealSheaf.mem_activeFinset]
      exact mem_componentSet_mk (F.comap h) i.1 hbmem
    · exact componentIndex_ext_of_mem
        (mem_componentSet_mk F i.1 (key _ (mem_componentSet_mk (F.comap h) i.1 hbmem)))
        hi_mem rfl
  · intro i' hi'
    exact componentFactor_comap_stalkIdeal h hh F hF I _ i'
      (IdealSheaf.mem_activeFinset.mp hi')
      (mem_componentSet_mk F i'.1 (key i' (IdealSheaf.mem_activeFinset.mp hi'))) rfl

omit [FiniteDimensional 𝕜 E] in
/-- The nonmonomial part commutes with pull-back along a local analytic isomorphism:
`N(h^*𝓘) = h^* N(𝓘)`. The colon `𝓘 : M(𝓘)` transports under the isomorphism of stalks induced by
`h`, and the monomial part transports by `monomialPart_comap`. This is the ideal half of the
statement that the nonmonomial triple of a pulled-back triple is the pull-back of the nonmonomial
triple (`Modified/NonmonomialComapInhabit.lean`). -/
theorem nonmonomialPart_comap (F : HypersurfaceFamily M) (hF : F.IsSnc ψ₀)
    (I : AnalyticManifold.IdealSheaf M) :
    nonmonomialPart (F.comap h) (HypersurfaceFamily.isSnc_comap hF h hh)
        (I.pullback h h.contMDiff)
      = (nonmonomialPart F hF I).pullback h h.contMDiff := by
  have hM := monomialPart_comap h hh F hF I
  refine IdealSheaf.ext fun b => ?_
  have hbij := germMap_bijective_of_isLocalDiffeomorphAt (⇑h) h.contMDiff (hh b)
  have hcs : ∀ J :
      AnalyticManifold.IdealSheaf M, (J.pullback h h.contMDiff).stalkIdeal b
      = Ideal.map (germMap (⇑h) h.contMDiff b) (J.stalkIdeal (h b)) := by
    intro J
    rw [IdealSheaf.stalkIdeal_pullback]
  rw [stalkIdeal_nonmonomialPart, hM, hcs I, hcs (monomialPart F hF I),
    hcs (nonmonomialPart F hF I), stalkIdeal_nonmonomialPart]
  conv_rhs => rw [← pow_one ((monomialPart F hF I).stalkIdeal (h b))]
  rw [Ideal.map_colon_pow_of_bijective _ hbij, pow_one]

end Hironaka.Manifold.BMO
