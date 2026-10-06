/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.FiniteType
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Local
import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineEndResult
import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback
import Hironaka.Resolution.Algebraic.Kol07.Thm36.ClassClosure
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Identification
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow
import Hironaka.Scheme.BlowUp.Glue.RestrictOpen
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.ConcatClauses
import Hironaka.Scheme.BlowUpSequence.OpenTransport
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.SubschemeStalk
import Hironaka.Scheme.Snc.DictionaryOrder
import Hironaka.Scheme.Snc.TrivialSncData
public import Hironaka.Scheme.DisjointIntegralComponents

/-!
# Deleting the irreducible components of a regular scheme by monoidal transformations

The degenerate case of Hironaka's Main Theorem II [Hir64, Main Theorem II, pp. 142–143]. When the
ideal sheaf `J` has order `0` at every point (`d = 0`, that is `J = 𝒪_X`), clause (iv), "`J_r` has
order `< 0` at every point of `X_r`", holds exactly when `X_r` is empty, and a finite succession of
monoidal transformations with non-singular irreducible centres emptying `X` exists: blow up the
irreducible components of `X` one after another. On a regular Noetherian scheme the irreducible
components are pairwise disjoint (a regular local ring is a domain, so a point lies on one
component only), hence open. The blow-up of `X` along the reduced ideal of a component `C` is, over
`C`, the blow-up along the zero ideal, which is empty (`blowUp.isEmpty_bot`), and over the
complement of `C` an isomorphism, so its blow-up map is the open immersion of the union of the
other components. After one blow-up per component the last stage is empty, and every clause of
Main Theorem II holds: (i) each centre is an irreducible component of a regular scheme; (ii)
`0 ≤ ν` is trivial; (iii) the boundary `E_i` at each stage is the restriction of `E₀` to the open
subscheme `X_i ⊆ X` — the reduced transform along an open immersion missing the centre is the
inverse image — and Hironaka's Definition 2 is a condition on stalks, which the stalk isomorphisms
of an open immersion preserve, while the centre, whose stalk ideals vanish on its support, has only
normal crossings with any such boundary; (iv) holds vacuously on the empty last stage.

* `exists_blowUpSequence_isEmpty_last_of_isRegular`: the succession, for a regular Noetherian
  scheme `X` and a reduced closed subscheme `E₀` with only normal crossings;
  `exists_blowUpSequence_isEmpty_last_of_smooth` is the same for a scheme smooth and of finite type
  over a field of characteristic zero, the hypotheses of Main Theorem II.
* The induction (`exists_blowUpSequence_isEmpty_last_aux`) runs over the open immersions
  `u : Y ⟶ X` into the fixed `X`, on the number of irreducible components of `X` meeting the range
  of `u`, with boundary `E₀.comap u` on `Y`: the centre is the inverse image of the reduced ideal
  of a component through a point of the range, its blow-up map is an open immersion missing the
  centre (`isOpenImmersion_blowUpπ_of_comap_eq_bot`), and the next stage is the composite with
  `u`. Every property of a stage — regularity, the integrality of the centre, the reducedness and
  the normal crossings of the boundary — is read off `X` through `u` instead of being established
  anew on the blow-up.
* The transport lemmas: `IsSncBoundaryWith.comap_of_isOpenImmersion` (Definition 2 along
  an open immersion), `IsRegular.of_isOpenImmersion`,
  `isRegular_subscheme_of_forall_stalkIdeal_eq_bot`,
  `reducedTransform_eq_comap_of_forall_notMem_support`, and the disjointness of the irreducible
  components of a regular scheme (`hasDisjointIntegralComponents_of_isRegular`).
-/

public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry Scheme Scheme.IdealSheafData
  Scheme.BlowUpSequence

namespace AlgebraicGeometry

open Hironaka.Sequence

variable {X Y : Scheme.{u}}

/-! ### Transport along an open immersion -/

/-- Regularity descends along an open immersion: the stalks of the source are stalks of the
target. -/
theorem IsRegular.of_isOpenImmersion (u : Y ⟶ X) [IsOpenImmersion u] [IsRegular X] :
    IsRegular Y :=
  ⟨fun y =>
    have : IsRegularLocalRing (X.presheaf.stalk (u y)) := IsRegular.isRegularAt (u y)
    IsRegularLocalRing.of_ringEquiv (stalkEquivOfIsOpenImmersion u y)⟩

/-- The inverse image of the kernel of `f` along `f` is zero: `f` factors through its
scheme-theoretic image `V(ker f)` (`Hom.toImage_imageι`), on which `ker f` restricts to zero
(`comap_subschemeι_eq_bot`). -/
theorem Scheme.Hom.comap_ker_self (f : Y ⟶ X) : f.ker.comap f = ⊥ := by
  calc f.ker.comap f = f.ker.comap (f.toImage ≫ f.imageι) := by rw [Scheme.Hom.toImage_imageι]
    _ = (f.ker.comap f.imageι).comap f.toImage := comap_comp _ _ _
    _ = ⊥ := by
      rw [show f.imageι = f.ker.subschemeι from rfl, comap_subschemeι_eq_bot, comap_bot]

namespace Scheme.IdealSheafData

/-- Hironaka's Definition 2 [Hir64, Ch. 0, §5, Definition 2] transports along an open immersion
`u`: the regular system of parameters at `u y`, the minimal primes of the stalk of `E` and the
generators of the stalk of `D` are carried to `y` by the stalk isomorphism
(`stalkEquivOfIsOpenImmersion`), so `u⁻¹ E` has only normal crossings with `u⁻¹ D` when `E` has
only normal crossings with `D`. -/
theorem IsSncBoundaryWith.comap_of_isOpenImmersion {E D : X.IdealSheafData}
    (h : IsSncBoundaryWith E D) (u : Y ⟶ X) [IsOpenImmersion u] :
    IsSncBoundaryWith (E.comap u) (D.comap u) := by
  intro y hy
  obtain ⟨n, z, hz, hmin, s, hs⟩ := h (u y) ((mem_support_comap_iff_apply D u y).mp hy)
  set e : X.presheaf.stalk (u y) ≃+* Y.presheaf.stalk y := stalkEquivOfIsOpenImmersion u y
    with he_def
  set e' : X.presheaf.stalk (u y) →+* Y.presheaf.stalk y :=
    (e : X.presheaf.stalk (u y) →+* Y.presheaf.stalk y) with he'_def
  have he : ∀ J : X.IdealSheafData, (J.comap u).stalkIdeal y = (J.stalkIdeal (u y)).map e' :=
    fun J => by rw [stalkIdeal_comap, he'_def, he_def, stalkEquivOfIsOpenImmersion_toRingHom]
  refine ⟨n, fun i => e (z i), isRegularSystemOfParameters_comp_ringEquiv e hz, ?_, s, ?_⟩
  · intro P hP
    rw [he] at hP
    have hP' : P.comap e' ∈ (E.stalkIdeal (u y)).minimalPrimes := by
      have h1 := Ideal.comap_minimalPrimes_eq_of_surjective (f := e') e.surjective
        ((E.stalkIdeal (u y)).map e')
      rw [Ideal.comap_map_of_bijective e' e.bijective] at h1
      rw [h1]
      exact ⟨P, hP, rfl⟩
    obtain ⟨i, hi⟩ := hmin _ hP'
    refine ⟨i, ?_⟩
    rw [← Ideal.map_comap_of_surjective e' e.surjective P, hi, Ideal.map_span,
      Set.image_singleton]
    rfl
  · rw [he, hs, Ideal.map_span, Set.image_image]
    rfl

/-- `IsSncBoundaryWith.comap_of_isOpenImmersion` at `D = X`: normal crossings transport
along an open immersion. -/
theorem IsSncBoundary.comap_of_isOpenImmersion {E : X.IdealSheafData}
    (h : IsSncBoundary E) (u : Y ⟶ X) [IsOpenImmersion u] :
    IsSncBoundary (E.comap u) := by
  have := IsSncBoundaryWith.comap_of_isOpenImmersion h u
  rwa [comap_bot] at this

end Scheme.IdealSheafData

end AlgebraicGeometry

namespace Hironaka.Sequence

open AlgebraicGeometry Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-! ### Stalks along an open immersion -/

/-- The stalk of the inverse image of `J` along an open immersion `u` is zero iff the stalk of
`J` at the image point is zero: the stalk map is an isomorphism (`stalkIdeal_comap`). -/
theorem stalkIdeal_comap_eq_bot_iff_of_isOpenImmersion (u : Y ⟶ X) [IsOpenImmersion u]
    (J : X.IdealSheafData) (y : Y) : (J.comap u).stalkIdeal y = ⊥ ↔ J.stalkIdeal (u y) = ⊥ := by
  rw [stalkIdeal_comap]
  exact Ideal.map_eq_bot_iff_of_injective (ConcreteCategory.bijective_of_isIso (u.stalkMap y)).1

/-- A closed subscheme `D` whose stalk ideals vanish on its support has only normal crossings with
a closed subscheme `E` having only normal crossings: Definition 2 at `x ∈ D` with the empty set of
parameters generating `D_x = 0`. -/
theorem isSncBoundaryWith_of_forall_stalkIdeal_eq_bot {E D : X.IdealSheafData}
    (hE : IsSncBoundary E) (hD : ∀ x ∈ D.support, D.stalkIdeal x = ⊥) :
    IsSncBoundaryWith E D := by
  intro x hx
  obtain ⟨n, z, hz, hmin, -⟩ := hE x (by rw [support_bot]; trivial)
  exact ⟨n, z, hz, hmin, ∅, by rw [hD x hx, Finset.coe_empty, Set.image_empty, Ideal.span_empty]⟩

/-- A closed subscheme `V(D)` whose stalk ideals vanish on its support is regular when the ambient
scheme is: its stalks are the stalks of the ambient scheme (`stalkQuotientEquiv` by the zero
ideal). -/
theorem isRegular_subscheme_of_forall_stalkIdeal_eq_bot [IsRegular X] (D : X.IdealSheafData)
    (hD : ∀ x ∈ D.support, D.stalkIdeal x = ⊥) : IsRegular D.subscheme :=
  ⟨fun z =>
    have hz : D.subschemeι z ∈ D.support := by
      have : D.subschemeι z ∈ Set.range D.subschemeι := ⟨z, rfl⟩
      rwa [D.range_subschemeι] at this
    have : IsRegularLocalRing (X.presheaf.stalk (D.subschemeι z)) :=
      IsRegular.isRegularAt (D.subschemeι z)
    IsRegularLocalRing.of_ringEquiv
      (((Ideal.quotEquivOfEq (hD _ hz)).trans (RingEquiv.quotientBot _)).symm.trans
        (D.stalkQuotientEquiv z))⟩

/-! ### The blow-up along a centre that is the whole scheme over an open -/

/-- If the centre `D` restricts to the zero ideal sheaf on an open `U` and every point off `U` is
off the support of `D`, the blow-up map `π : D.blowUp ⟶ X` is an open immersion missing the
support of `D`: over `U` the blow-up is the blow-up of the zero ideal sheaf, which is empty
(`blowUp.restrictIso`, `blowUp.isEmpty_bot`), so `π` lands in the complement `V` of the support,
over which it is an isomorphism [Sta, Tag 02OS] (`blowUp.isIso_π_restrict_compl_support`); hence
`π⁻¹(V)` is all of `D.blowUp` and `π` is the isomorphism `π ∣_ V` followed by the inclusion of
`V`. -/
theorem isOpenImmersion_blowUpπ_of_comap_eq_bot (D : X.IdealSheafData) (U : X.Opens)
    (hU : D.comap U.ι = ⊥) (hUV : ∀ x, x ∈ U ∨ x ∉ D.support) :
    IsOpenImmersion D.blowUpπ ∧ ∀ p : D.blowUp, D.blowUpπ p ∉ D.support := by
  have hempty : IsEmpty (D.blowUpπ ⁻¹ᵁ U : Scheme.{u}) := by
    have h1 : IsEmpty (blowUp (D.comap U.ι)) := by
      rw [hU]
      exact blowUp.isEmpty_bot
    exact ⟨fun p => h1.false ((blowUp.restrictIso D U).inv p)⟩
  have hnot : ∀ p : D.blowUp, D.blowUpπ p ∉ D.support := fun p hp => by
    rcases hUV (D.blowUpπ p) with h | h
    · have h' : p ∈ ((D.blowUpπ ⁻¹ᵁ U : D.blowUp.Opens) : Set D.blowUp) := h
      rw [← Scheme.Opens.range_ι] at h'
      obtain ⟨q, -⟩ := h'
      exact hempty.false q
    · exact h hp
  refine ⟨?_, hnot⟩
  set V : X.Opens := D.support.compl with hVdef
  have hV : D.blowUpπ ⁻¹ᵁ V = ⊤ := by
    ext p
    exact ⟨fun _ => trivial, fun _ => hnot p⟩
  have hι : IsIso (D.blowUpπ ⁻¹ᵁ V).ι := by
    rw [hV]
    exact D.blowUp.topIso.isIso_hom
  have := blowUp.isIso_π_restrict_compl_support D
  have h2 : IsOpenImmersion ((D.blowUpπ ⁻¹ᵁ V).ι ≫ D.blowUpπ) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have h3 : IsOpenImmersion (inv (D.blowUpπ ⁻¹ᵁ V).ι ≫ ((D.blowUpπ ⁻¹ᵁ V).ι ≫ D.blowUpπ)) :=
    inferInstance
  rwa [IsIso.inv_hom_id_assoc] at h3

/-- Hironaka's reduced transform `red(π⁻¹(E) ∪ π⁻¹(D))` [Hir64, Main Theorem II (iii)] under a
blow-up whose map `π` is an open immersion missing the centre `D` is the inverse image `π⁻¹ E` of
the reduced `E`: the preimage of the centre is empty, and the vanishing ideal sheaf of the support
of the reduced `π⁻¹ E` is `π⁻¹ E` itself. -/
theorem reducedTransform_eq_comap_of_forall_notMem_support (E D : X.IdealSheafData)
    [IsReduced E.subscheme] [IsOpenImmersion D.blowUpπ]
    (h : ∀ p : D.blowUp, D.blowUpπ p ∉ D.support) :
    E.reducedTransform D = E.comap D.blowUpπ := by
  have h1 : D.support.preimage D.blowUpπ.continuous = ⊥ :=
    Closeds.ext (Set.eq_empty_of_forall_notMem fun p hp => h p hp)
  have : IsReduced (E.comap D.blowUpπ).subscheme :=
    isReduced_subscheme_comap_of_isOpenImmersion D.blowUpπ E
  rw [Scheme.IdealSheafData.reducedTransform, h1, sup_bot_eq, ← support_comap,
    vanishingIdeal_support, radical_eq_self_of_isReduced_subscheme]

/-! ### The irreducible components of a regular scheme -/

/-- On a regular scheme two irreducible components through a common point coincide: their generic
points are maximal points of `X` specialising to the point, and a regular local ring has a single
minimal prime (`eq_of_specializes_of_isRegular` at the zero ideal sheaf). -/
theorem eq_of_mem_irreducibleComponents_of_mem_of_isRegular [IsRegular X] {C₁ C₂ : Set X}
    (h₁ : C₁ ∈ irreducibleComponents X) (h₂ : C₂ ∈ irreducibleComponents X) {x : X}
    (hx₁ : x ∈ C₁) (hx₂ : x ∈ C₂) : C₁ = C₂ := by
  have hreg : IsRegular (⊥ : X.IdealSheafData).subscheme :=
    IsRegular.of_isIso (inv (⊥ : X.IdealSheafData).subschemeι) inferInstance
  have hirr₁ : IsIrreducible C₁ := h₁.1
  have hirr₂ : IsIrreducible C₂ := h₂.1
  have hg₁ := hirr₁.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C₁ h₁)
  have hg₂ := hirr₂.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C₂ h₂)
  have hm : ∀ (C : Set X), C ∈ irreducibleComponents X → ∀ (η : X), IsGenericPoint η C →
      η ∈ (⊥ : X.IdealSheafData).support.genericPoints := fun _ hC _ hη =>
    mem_genericPoints_of_isGenericPoint_of_mem hC hη _ (by rw [support_bot]; trivial)
  have e := eq_of_specializes_of_isRegular ⊥ hreg (hm _ h₁ _ hg₁) (hm _ h₂ _ hg₂)
    (hg₁.specializes hx₁) (hg₂.specializes hx₂)
  calc C₁ = closure {hirr₁.genericPoint} := hg₁.def.symm
    _ = closure {hirr₂.genericPoint} := by rw [e]
    _ = C₂ := hg₂.def

/-- A regular scheme is reduced with pairwise disjoint irreducible components: a member of the
class `HasDisjointIntegralComponents`. -/
theorem hasDisjointIntegralComponents_of_isRegular [IsRegular X] :
    HasDisjointIntegralComponents X :=
  ⟨isReduced_of_isRegular inferInstance, fun _ h₁ _ h₂ ⟨_, hx₁, hx₂⟩ =>
    eq_of_mem_irreducibleComponents_of_mem_of_isRegular h₁ h₂ hx₁ hx₂⟩

/-! ### The succession -/

section Deletion

variable [IsNoetherian X] [IsRegular X]

/-- The induction behind `exists_blowUpSequence_isEmpty_last_of_isRegular`, over the open
immersions `u : Y ⟶ X` into the fixed regular Noetherian `X`, on the number `n` of irreducible
components of `X` meeting the range of `u`, with the boundary `E₀.comap u` on `Y`. If `Y` is
empty the empty succession does. Otherwise some component `C` of `X` meets the range; the centre
is the inverse image `D` of the reduced ideal of `C`, an integral closed subscheme (open in
`V(C)`) whose stalk ideals vanish on its support, so it is regular and has only normal crossings
with the boundary; its blow-up map `π` is an open immersion missing `D`
(`isOpenImmersion_blowUpπ_of_comap_eq_bot`), along which the boundary is carried to
`E₀.comap (π ≫ u)`, and the succession continues with the one the induction hypothesis gives for
`π ≫ u`, whose range meets one component fewer. -/
theorem exists_blowUpSequence_isEmpty_last_aux (E₀ : X.IdealSheafData) [IsReduced E₀.subscheme]
    (hE₀ : IsSncBoundary E₀) (n : ℕ) :
    ∀ {Y : Scheme.{u}} (u : Y ⟶ X) [IsOpenImmersion u],
      {C ∈ irreducibleComponents X | (C ∩ Set.range u).Nonempty}.ncard ≤ n →
      ∃ S : BlowUpSequence Y,
        (∀ i : Fin S.length,
          IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
        (∀ i : Fin S.length,
          IsSncBoundaryWith (S.boundarySeq (E₀.comap u) i.castSucc) (S.center i)) ∧
        IsEmpty S.last := by
  induction n with
  | zero =>
    intro Y u _ hn
    refine ⟨nil Y, fun i => i.elim0, fun i => i.elim0, ⟨fun y => ?_⟩⟩
    have hfin : {C ∈ irreducibleComponents X | (C ∩ Set.range u).Nonempty}.Finite :=
      NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1
    have hpos : 0 < {C ∈ irreducibleComponents X | (C ∩ Set.range u).Nonempty}.ncard :=
      (Set.ncard_pos hfin).mpr ⟨_, irreducibleComponent_mem_irreducibleComponents (u y), u y,
        mem_irreducibleComponent, y, rfl⟩
    omega
  | succ n ih =>
    intro Y u _ hn
    by_cases hY : IsEmpty Y
    · exact ⟨nil Y, fun i => i.elim0, fun i => i.elim0, hY⟩
    obtain ⟨y⟩ := not_isEmpty_iff.mp hY
    obtain ⟨C, hC, hyC⟩ : ∃ C ∈ irreducibleComponents X, u y ∈ C :=
      ⟨_, irreducibleComponent_mem_irreducibleComponents (u y), mem_irreducibleComponent⟩
    have hX : HasDisjointIntegralComponents X := hasDisjointIntegralComponents_of_isRegular
    have hregY : IsRegular Y := IsRegular.of_isOpenImmersion u
    set U₀ : X.Opens := X.irreducibleComponentOpen C with hU₀def
    have hU₀ : (U₀ : Set X) = C := hX.irreducibleComponentOpen_eq C hC
    set DX : X.IdealSheafData := X.irreducibleComponentIdeal C hC with hDXdef
    have hDXU : DX.comap U₀.ι = ⊥ := by
      rw [hDXdef, Scheme.irreducibleComponentIdeal_def]
      exact Scheme.Hom.comap_ker_self U₀.ι
    set D : Y.IdealSheafData := DX.comap u with hDdef
    have hDsupp : ∀ y' : Y, y' ∈ D.support ↔ u y' ∈ C := fun y' =>
      mem_support_comap_iff_apply DX u y'
    have hDstalk : ∀ y' ∈ D.support, D.stalkIdeal y' = ⊥ := fun y' hy' => by
      have hx : u y' ∈ (U₀ : Set X) := by
        rw [hU₀]
        exact (hDsupp y').mp hy'
      rw [← Scheme.Opens.range_ι] at hx
      obtain ⟨w, hw⟩ := hx
      rw [hDdef, stalkIdeal_comap_eq_bot_iff_of_isOpenImmersion, ← hw,
        ← stalkIdeal_comap_eq_bot_iff_of_isOpenImmersion U₀.ι, hDXU, stalkIdeal_bot]
    have hcomap : D.comap (u ⁻¹ᵁ U₀).ι = ⊥ := by
      rw [hDdef, ← comap_comp, ← morphismRestrict_ι, comap_comp, hDXU, comap_bot]
    have hcover : ∀ y' : Y, y' ∈ u ⁻¹ᵁ U₀ ∨ y' ∉ D.support := fun y' => by
      by_cases h : u y' ∈ C
      · refine Or.inl ?_
        change u y' ∈ (U₀ : Set X)
        rw [hU₀]
        exact h
      · exact Or.inr fun h' => h ((hDsupp y').mp h')
    obtain ⟨hπ, hnot⟩ := isOpenImmersion_blowUpπ_of_comap_eq_bot D (u ⁻¹ᵁ U₀) hcomap hcover
    -- the induction hypothesis at `π ≫ u`: one component fewer meets the range
    have hsub : {C' ∈ irreducibleComponents X | (C' ∩ Set.range (D.blowUpπ ≫ u)).Nonempty} ⊆
        {C' ∈ irreducibleComponents X | (C' ∩ Set.range u).Nonempty} \ {C} := by
      rintro C' ⟨hC', x, hxC', p, hp⟩
      rw [Scheme.Hom.comp_apply] at hp
      refine ⟨⟨hC', x, hxC', D.blowUpπ p, hp⟩, fun hC'C => hnot p ?_⟩
      rw [Set.mem_singleton_iff] at hC'C
      subst hC'C
      rw [hDsupp, hp]
      exact hxC'
    have hfin : {C' ∈ irreducibleComponents X | (C' ∩ Set.range u).Nonempty}.Finite :=
      NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1
    have hmemC : C ∈ {C' ∈ irreducibleComponents X | (C' ∩ Set.range u).Nonempty} :=
      ⟨hC, u y, hyC, y, rfl⟩
    have hn' : {C' ∈ irreducibleComponents X |
        (C' ∩ Set.range (D.blowUpπ ≫ u)).Nonempty}.ncard ≤ n := by
      calc _ ≤ ({C' ∈ irreducibleComponents X | (C' ∩ Set.range u).Nonempty} \ {C}).ncard :=
            Set.ncard_le_ncard hsub hfin.sdiff
        _ = {C' ∈ irreducibleComponents X | (C' ∩ Set.range u).Nonempty}.ncard - 1 :=
            Set.ncard_sdiff_singleton_of_mem hmemC
        _ ≤ n := by omega
    obtain ⟨S', hS'1, hS'2, hS'3⟩ := ih (D.blowUpπ ≫ u) hn'
    refine ⟨cons Y D S', ?_, ?_, hS'3⟩
    · -- clause (i): the centre `D` is regular and irreducible, the later centres by induction
      refine (forall_stage_cons_iff (fun {_} D _ _ => IsRegular D.subscheme ∧
        IrreducibleSpace D.subscheme) D S' ⊥ ⊥).mpr ⟨⟨?_, ?_⟩, hS'1⟩
      · exact isRegular_subscheme_of_forall_stalkIdeal_eq_bot D hDstalk
      · have hint : IsIntegral DX.subscheme := isIntegral_irreducibleComponent hX C hC
        have hoi := isOpenImmersion_subschemeMap_comap u DX
        have hne : Nonempty D.subscheme := by
          obtain ⟨p, -⟩ := D.exists_subschemeι_eq ((hDsupp y).mpr hyC)
          exact ⟨p⟩
        have := isIntegral_of_isOpenImmersion
          (subschemeMap (DX.comap u) DX u (le_map_comap DX u))
        infer_instance
    · -- clause (iii): the boundary along the succession
      have hE : IsSncBoundary (E₀.comap u) := hE₀.comap_of_isOpenImmersion u
      have hEred : IsReduced (E₀.comap u).subscheme :=
        isReduced_subscheme_comap_of_isOpenImmersion u E₀
      have hred : (E₀.comap u).reducedTransform D = E₀.comap (D.blowUpπ ≫ u) := by
        rw [reducedTransform_eq_comap_of_forall_notMem_support _ D hnot, comap_comp]
      refine (forall_stage_cons_iff (fun {_} D _ E => IsSncBoundaryWith E D) D S' ⊥
        (E₀.comap u)).mpr ⟨?_, ?_⟩
      · exact isSncBoundaryWith_of_forall_stalkIdeal_eq_bot hE hDstalk
      · rw [hred]
        exact hS'2

/-- **Deleting the irreducible components** of a regular Noetherian scheme `X`: for a reduced
closed subscheme `E₀` of `X` having only normal crossings there is a finite succession of monoidal
transformations of `X` whose centres are regular and irreducible, whose boundaries
`E_i = S.boundarySeq E₀ i` have only normal crossings with the centres, and whose last stage `X_r`
is empty: blow up the irreducible components of `X` one after another, each blow-up deleting its
component. This is the degenerate case `d = 0` of Hironaka's Main Theorem II
[Hir64, Main Theorem II, pp. 142–143], in which clause (ii) is trivial and clause (iv) is
vacuous. -/
theorem exists_blowUpSequence_isEmpty_last_of_isRegular (E₀ : X.IdealSheafData)
    [IsReduced E₀.subscheme] (hE₀ : IsSncBoundary E₀) :
    ∃ S : BlowUpSequence X,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ i : Fin S.length, IsSncBoundaryWith (S.boundarySeq E₀ i.castSucc) (S.center i)) ∧
      IsEmpty S.last := by
  obtain ⟨S, h1, h2, h3⟩ := exists_blowUpSequence_isEmpty_last_aux E₀ hE₀ _ (𝟙 X) le_rfl
  rw [comap_id] at h2
  exact ⟨S, h1, h2, h3⟩

end Deletion

/-- `exists_blowUpSequence_isEmpty_last_of_isRegular` for an algebraic scheme smooth over a field
`k` of characteristic zero, the setting of Main Theorem II [Hir64, Main Theorem II, pp. 142–143]:
such a scheme is Noetherian (`isNoetherian_of_field`) and regular (`isRegular_of_smooth`). -/
theorem exists_blowUpSequence_isEmpty_last_of_smooth {k : Type u} [Field k] [CharZero k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [FiniteType (X ↘ Spec (.of k))]
    [Smooth (X ↘ Spec (.of k))] (E₀ : X.IdealSheafData) [IsReduced E₀.subscheme]
    (hE₀ : IsSncBoundary E₀) :
    ∃ S : BlowUpSequence X,
      (∀ i : Fin S.length,
        IsRegular (S.center i).subscheme ∧ IrreducibleSpace (S.center i).subscheme) ∧
      (∀ i : Fin S.length, IsSncBoundaryWith (S.boundarySeq E₀ i.castSucc) (S.center i)) ∧
      IsEmpty S.last := by
  have : IsNoetherian X := (X ↘ Spec (.of k)).isNoetherian_of_field
  have : IsRegular X := isRegular_of_smooth (X ↘ Spec (.of k))
  exact exists_blowUpSequence_isEmpty_last_of_isRegular E₀ hE₀

end Hironaka.Sequence
