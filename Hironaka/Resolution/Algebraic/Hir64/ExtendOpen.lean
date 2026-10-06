/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Defs
import Hironaka.Resolution.Algebraic.Kol07.Prop37.Prop37Descent
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.Pullback
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Extension of a blow-up sequence across the complement of an open subscheme

In the proof of Corollary 1 of Main Theorem II [Hir64, p. 144], a finite succession of monoidal
transformations on the open subscheme `X̄ = X ∖ S` whose centers `D̄(i)` are mapped into the closed
subset `T − S` of `X` is extended to a finite succession `f_i : X(i+1) → X(i)` on `X` itself, with
centers `D(i)` and open immersions `u_i : X̄(i) → X(i)` such that "`u_i(D̄(i)) = D(i)` and
`u_i ∘ f̄_i = f_i ∘ u_{i+1}`". This module proves that extension in general:

* **The closedness ground**: a subset of `U` closed in `U` whose image under the open immersion
  `u : U ⟶ X` lies in a closed `C ⊆ u(U)` has closed image in `X`
  (`isClosed_image_of_isOpenImmersion`); its closure stays inside `C ⊆ u(U)`, where `u` is an
  embedding.
* **The extended center**: for a center `D` on `U` with closed image, the ideal sheaf
  `D.map u = ker (D.subschemeι ≫ u)` of `X` (Mathlib's push-forward; the composite is a closed
  immersion, `isClosedImmersion_subschemeι_comp`) has support `u(D)` (`support_map_of_isClosed`)
  and restricts to `D` on `U` (`comap_map_of_isClosed`).
* **The extension** `extendOfOpen u S' C h`, by recursion on `S'`: the first center is extended,
  the next open immersion is the base change `blowUpMap u (D.map u)` of the blow-up (an open
  immersion with image `π⁻¹(u(U))`, [Sta, Tag 0805]; the blow-up maps form a pullback square,
  `isPullback_blowUpMap`) transported along `(D.map u).comap u = D`, and the tail is extended
  over the preimage of `C`. Its pull-back along `u` is `S'` (`pullback_extendOfOpen`: Hironaka's
  `u_i(D̄(i)) = D(i)` and `u_i ∘ f̄_i = f_i ∘ u_{i+1}`, the defining squares of the pull-back) and
  its centers lie over `C` (`stageMap_extendOfOpen_mem`).
* `exists_extend_of_isOpenImmersion` is the existential form.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme BlowUpSequence
  Scheme.IdealSheafData TopologicalSpace

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {U X : Scheme.{u}}

/-! ### The closedness ground -/

/-- A subset `A` closed in `U` whose image under the open immersion `u` lies in a closed
`C ⊆ u(U)` has closed image: the closure of `u(A)` lies in `C`, hence in `u(U)`, where `u` is an
embedding and `A` is closed. -/
theorem isClosed_image_of_isOpenImmersion (u : U ⟶ X) [IsOpenImmersion u] {A : Set U}
    (hA : IsClosed A) {C : Set X} (hC : IsClosed C) (hCU : C ⊆ Set.range u)
    (hAC : u '' A ⊆ C) : IsClosed (u '' A) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨y, rfl⟩ := hCU (hC.closure_subset_iff.mpr hAC hz)
  refine ⟨y, ?_, rfl⟩
  have h1 : closure A = u ⁻¹' closure (u '' A) :=
    u.isOpenEmbedding.toIsEmbedding.toIsInducing.closure_eq_preimage_closure_image A
  have : y ∈ closure A := by
    rw [h1]
    exact hz
  rwa [hA.closure_eq] at this

/-! ### The extended center -/

section Centre

variable (u : U ⟶ X) [IsOpenImmersion u] (D : U.IdealSheafData)

/-- The closed subscheme `D` of `U` with closed image in `X` is a closed subscheme of `X`: the
composite `D ⟶ U ⟶ X` is a preimmersion with closed range. -/
theorem isClosedImmersion_subschemeι_comp (h : IsClosed (u '' (D.support : Set U))) :
    IsClosedImmersion (D.subschemeι ≫ u) := by
  refine IsClosedImmersion.of_isPreimmersion _ ?_
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, IdealSheafData.range_subschemeι]
  exact h

/-- The support of the extended center is the image of the support. -/
theorem support_map_of_isClosed (h : IsClosed (u '' (D.support : Set U))) :
    ((D.map u).support : Set X) = u '' (D.support : Set U) := by
  have := isClosedImmersion_subschemeι_comp u D h
  change ((D.subschemeι ≫ u).ker.support : Set X) = _
  rw [Scheme.Hom.support_ker, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    IdealSheafData.range_subschemeι, h.closure_eq]

/-- The extended center restricts to the center, `(D.map u).comap u = D`: Mathlib's
`ker_ideal_of_isPullback_of_isOpenImmersion` on the square with the identity, which is cartesian
because `u` is a monomorphism. -/
theorem comap_map_of_isClosed (h : IsClosed (u '' (D.support : Set U))) :
    (D.map u).comap u = D := by
  have := isClosedImmersion_subschemeι_comp u D h
  have H : IsPullback D.subschemeι (𝟙 D.subscheme) u (D.subschemeι ≫ u) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  refine Scheme.IdealSheafData.ext (funext fun W => ?_)
  rw [IdealSheafData.ideal_comap_of_isOpenImmersion]
  have := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion (D.subschemeι ≫ u) D.subschemeι (𝟙 _)
    u H W
  rw [IdealSheafData.ker_subschemeι] at this
  exact this.symm

end Centre

/-! ### The extension -/

/-- The data under which a sequence `S'` on `U` extends across the complement of the open
immersion `u : U ⟶ X`: a closed `C ⊆ u(U)` over which every center lies (Hironaka's `T − S`). -/
structure ExtendsOver (u : U ⟶ X) (S' : BlowUpSequence U) (C : Set X) : Prop where
  /-- `C` is closed in `X`. -/
  isClosed : IsClosed C
  /-- `C` lies in the image of `u`. -/
  subset_range : C ⊆ Set.range u
  /-- Every center maps into `C`. -/
  center_mem : ∀ (i : Fin S'.length) (y : S'.stage i.castSucc), y ∈ (S'.center i).support →
    u (S'.stageMap i.castSucc y) ∈ C

section Step

variable (u : U ⟶ X) [IsOpenImmersion u] (D : U.IdealSheafData)
  (rest : BlowUpSequence D.blowUp) (C : Set X) (h : ExtendsOver u (cons U D rest) C)

omit [IsOpenImmersion u] in
include h in
/-- The first center maps into `C`. -/
theorem ExtendsOver.image_subset : u '' (D.support : Set U) ⊆ C := by
  rintro _ ⟨y, hy, rfl⟩
  exact h.center_mem ⟨0, Nat.succ_pos _⟩ y hy

include h in
/-- The first center has closed image. -/
theorem ExtendsOver.isClosed_image : IsClosed (u '' (D.support : Set U)) :=
  isClosed_image_of_isOpenImmersion u D.support.isClosed h.isClosed h.subset_range
    (ExtendsOver.image_subset u D rest C h)

include h in
theorem ExtendsOver.comap_map : (D.map u).comap u = D :=
  comap_map_of_isClosed u D (ExtendsOver.isClosed_image u D rest C h)

/-- Hironaka's next open immersion `u_{i+1}`: the base change of `u` to the blow-ups, transported
along `(D.map u).comap u = D`. -/
noncomputable def extendStep : D.blowUp ⟶ (D.map u).blowUp :=
  eqToHom (congrArg Scheme.IdealSheafData.blowUp (ExtendsOver.comap_map u D rest C h).symm) ≫
    Hom.blowUpMap u (D.map u)

/-- The square of `extendStep` over `u` is cartesian: the `eqToHom` square pasted with the
base-change square of the blow-up (`isPullback_blowUpMap`). -/
theorem isPullback_extendStep :
    IsPullback (extendStep u D rest C h) D.blowUpπ (D.map u).blowUpπ u := by
  have h₁ : IsPullback (eqToHom
      (congrArg Scheme.IdealSheafData.blowUp (ExtendsOver.comap_map u D rest C h).symm))
      D.blowUpπ ((D.map u).comap u).blowUpπ (𝟙 U) :=
    IsPullback.of_horiz_isIso
      ⟨by rw [blowUpπ_eqToHom (ExtendsOver.comap_map u D rest C h).symm, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz (isPullback_blowUpMap u (D.map u))
  rwa [Category.id_comp] at h₂

theorem isOpenImmersion_extendStep : IsOpenImmersion (extendStep u D rest C h) :=
  property_of_isPullback _ (isPullback_extendStep u D rest C h) inferInstance

theorem extendStep_π :
    extendStep u D rest C h ≫ (D.map u).blowUpπ = D.blowUpπ ≫ u :=
  (isPullback_extendStep u D rest C h).w

theorem range_extendStep :
    Set.range (extendStep u D rest C h) = (D.map u).blowUpπ ⁻¹' Set.range u :=
  range_fst_of_isPullback (isPullback_extendStep u D rest C h)

/-- The tail extends over the preimage of `C`. -/
theorem ExtendsOver.tailStep :
    ExtendsOver (extendStep u D rest C h) rest ((D.map u).blowUpπ ⁻¹' C) where
  isClosed := h.isClosed.preimage (D.map u).blowUpπ.continuous
  subset_range := by
    rw [range_extendStep]
    exact Set.preimage_mono h.subset_range
  center_mem := by
    intro i y hy
    have hm := h.center_mem ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ y hy
    change (D.map u).blowUpπ (extendStep u D rest C h (rest.stageMap i.castSucc y)) ∈ C
    have hπ := congrArg (fun f => f (rest.stageMap i.castSucc y)) (extendStep_π u D rest C h)
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hπ
    rw [hπ]
    exact hm

end Step

/-- **The extension** of a sequence on `U` across the complement of the open immersion `u`
[Hir64, Corollary 1 of Main Theorem II, p. 144], by recursion: the first center extended by
`D.map u`, the next open immersion `extendStep`, the tail extended over the preimage of `C`. -/
noncomputable def extendOfOpen : ∀ {U X : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (S' : BlowUpSequence U) (C : Set X), ExtendsOver u S' C → BlowUpSequence X
  | _, X, _, _, nil _, _, _ => nil X
  | _, X, u, _, cons _ D rest, C, h =>
    haveI := isOpenImmersion_extendStep u D rest C h
    cons X (D.map u) (extendOfOpen (extendStep u D rest C h) rest ((D.map u).blowUpπ ⁻¹' C)
      (ExtendsOver.tailStep u D rest C h))

theorem extendOfOpen_nil (u : U ⟶ X) [IsOpenImmersion u] (C : Set X)
    (h : ExtendsOver u (nil U) C) : extendOfOpen u (nil U) C h = nil X := rfl

theorem extendOfOpen_cons (u : U ⟶ X) [IsOpenImmersion u] (D : U.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) (C : Set X) (h : ExtendsOver u (cons U D rest) C) :
    extendOfOpen u (cons U D rest) C h =
      haveI := isOpenImmersion_extendStep u D rest C h
      cons X (D.map u) (extendOfOpen (extendStep u D rest C h) rest
        ((D.map u).blowUpπ ⁻¹' C) (ExtendsOver.tailStep u D rest C h)) := rfl

theorem length_extendOfOpen : ∀ {U X : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (S' : BlowUpSequence U) (C : Set X) (h : ExtendsOver u S' C),
    (extendOfOpen u S' C h).length = S'.length
  | _, _, _, _, nil _, _, _ => rfl
  | _, _, u, _, cons _ D rest, C, h => by
    have := isOpenImmersion_extendStep u D rest C h
    change (extendOfOpen (extendStep u D rest C h) rest _
      (ExtendsOver.tailStep u D rest C h)).length + 1 = rest.length + 1
    rw [length_extendOfOpen]

/-- Pulling back along `eqToHom` and its inverse is the identity. -/
theorem pullback_eqToHom_pullback_eqToHom_symm {X' : Scheme.{u}} (S : BlowUpSequence X)
    (e : X' = X) :
    (S.pullback (eqToHom e)).pullback (eqToHom e.symm) = S := by
  rw [← pullback_comp, eqToHom_trans, eqToHom_refl, pullback_id]

/-- **The pull-back of the extension along `u` is the sequence** (Hironaka's "`u_i(D̄(i)) = D(i)`
and `u_i ∘ f̄_i = f_i ∘ u_{i+1}`", [Hir64, p. 144]): the extended center restricts to the center,
and the pull-back's next stage map is `extendStep` up to the transport. -/
theorem pullback_extendOfOpen : ∀ {U X : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (S' : BlowUpSequence U) (C : Set X) (h : ExtendsOver u S' C),
    (extendOfOpen u S' C h).pullback u = S'
  | _, _, _, _, nil _, _, _ => rfl
  | _, X, u, _, cons _ D rest, C, h => by
    have := isOpenImmersion_extendStep u D rest C h
    have e := (ExtendsOver.comap_map u D rest C h)
    rw [extendOfOpen_cons, pullback_cons, cons_eq_cons_pullback_eqToHom e rest]
    congr 1
    have ih := pullback_extendOfOpen (extendStep u D rest C h) rest
      ((D.map u).blowUpπ ⁻¹' C) (ExtendsOver.tailStep u D rest C h)
    unfold extendStep at ih
    rw [pullback_comp] at ih
    have key := congrArg (fun T : BlowUpSequence D.blowUp =>
      T.pullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp e))) ih
    simp only at key
    rw [pullback_eqToHom_pullback_eqToHom_symm] at key
    exact key

/-- The centers of the extension lie over `C`. -/
theorem stageMap_extendOfOpen_mem : ∀ {U X : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (S' : BlowUpSequence U) (C : Set X) (h : ExtendsOver u S' C)
    (i : Fin (extendOfOpen u S' C h).length) (x : (extendOfOpen u S' C h).stage i.castSucc),
    x ∈ ((extendOfOpen u S' C h).center i).support →
      (extendOfOpen u S' C h).stageMap i.castSucc x ∈ C
  | _, _, _, _, nil _, _, _, i, _, _ => i.elim0
  | _, X, u, _, cons _ D rest, C, h, ⟨0, _⟩, x, hx => by
    have := isOpenImmersion_extendStep u D rest C h
    have hx' : x ∈ ((D.map u).support : Set X) := hx
    rw [support_map_of_isClosed u D (ExtendsOver.isClosed_image u D rest C h)] at hx'
    exact (ExtendsOver.image_subset u D rest C h) hx'
  | _, X, u, _, cons _ D rest, C, h, ⟨j + 1, hj⟩, x, hx => by
    have := isOpenImmersion_extendStep u D rest C h
    exact stageMap_extendOfOpen_mem (extendStep u D rest C h) rest ((D.map u).blowUpπ ⁻¹' C)
      (ExtendsOver.tailStep u D rest C h) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ x hx

/-! ### The existential form -/

/-- **A sequence on an open subscheme whose centers lie over a closed subset of the image extends
across the complement** [Hir64, Corollary 1 of Main Theorem II, p. 144]: the existential form of
`extendOfOpen`, `pullback_extendOfOpen` and `stageMap_extendOfOpen_mem`. -/
theorem exists_extend_of_isOpenImmersion {U X : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u]
    (S' : BlowUpSequence U) (C : Set X) (hC : IsClosed C) (hCU : C ⊆ Set.range u)
    (hcent : ∀ (i : Fin S'.length) (y : S'.stage i.castSucc), y ∈ (S'.center i).support →
      u (S'.stageMap i.castSucc y) ∈ C) :
    ∃ S : BlowUpSequence X, S.pullback u = S' ∧
      ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
        S.stageMap i.castSucc x ∈ C :=
  ⟨extendOfOpen u S' C ⟨hC, hCU, hcent⟩, pullback_extendOfOpen u S' C _,
    stageMap_extendOfOpen_mem u S' C _⟩

end Hironaka.Sequence
