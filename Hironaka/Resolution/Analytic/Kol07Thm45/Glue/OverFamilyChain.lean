/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.OverFamily
import Hironaka.AnalyticSpace.SncFamilyTransport
import Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyPartner
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The glued exceptional family of a chain of gluings

The resolution of a whole analytic space is glued from the resolutions of the members of an
exhaustion by relatively compact open subsets, along their overlaps ([Kol07, Proposition 37];
[Kol07, 44]; [Wlo09, §4.3]); the exceptional divisors of the levels glue with them once their
components are matched level to level by a label, the stage of the common blow-up sequence at which
each is created [Kol07, Proposition 37, (37.2)]. For a gluing datum `G : GlueOver X R π dom` over a
chain (`ι := ULift ℕ`, `dom` monotone), with a simple-normal-crossings family `H n` on every level
and label maps `e n` on the members with non-empty trace on the overlap with the next level,
satisfying the labelled identity on the overlaps (`hpair`, the conclusion of the locality lemma
`ClosedSubspace.comap_eq_of_forall_exists_local`) and covering every member of the next level that
meets the overlap (`hsurj`: a component of a higher level meeting a lower level restricts to a
component of that level), the members glue to a simple-normal-crossings family on the glued space
(`chainGlueFamily`, `isSncFamily_chainGlueFamily`), locally finite
(`locallyFinite_chainGlueFamily`), indexed by the colimit of the levels' members along the label
maps (`chainColimitIndex`), with each level's members as the pull-backs
(`comap_ιGlued_chainGlueFamily_mk`) and support the preimage of the levels' common support
(`iUnion_support_chainGlueFamily`).

Three general tools carry it.

* The colimit index is a tree of chains: the step relation `⟨n, σ⟩ ↦ ⟨n+1, f n σ⟩` is functional and
  raises the level, so its generated equivalence is "a common descendant" and two members of one
  level are identified only when equal (`chainColimitIndex.mk_injective`, `mk_eq_mk_succ_iff`).
* Compatibility of closed subspaces of the levels (`CompatClosedSubspaces` of
  `Hironaka.AnalyticSpace.Glue.OverFamily`, asked for every pair by `glueClosedSubspace`) follows on
  a chain from the adjacent pairs (`compatClosedSubspaces_of_chain`): compatibility of a pair is the
  agreement of the transported stalk ideals `pieceStalkIdeal` at the common glued points, in both
  directions (`pieceStalkIdeal_eq_of_pair`, `compat_pair_of_forall_pieceStalkIdeal_eq`), and on a
  chain the images of the levels are nested, so agreement propagates by induction, with no cocycle
  bookkeeping.
* The locality and partner tools of
  `Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyPartner`, restated in the `restrictOpen`
  spelling of the traces (`ClosedSubspace.comap_eq_of_forall_exists_local`,
  `existsUnique_comap_eq_of_forall_exists_local`,
  `IsSncFamily.eq_of_comap_ofRestrict_eq_of_nonempty`), the spelling in which the transitions `G.t`
  are stated.

The labelled compatibility (`chainLabelledCompat`) has four cases per label and adjacent pair: both
levels represented (the identity `hpair`, the representatives related by `mk_eq_mk_succ_iff`); the
lower level only (the trace on the overlap is empty, both sides are the unit ideal sheaf); the upper
only (by `hsurj` its trace on the overlap is empty, so again both sides are the unit ideal sheaf);
neither.

The glued chain family is the exceptional family of the resolution glued along an exhaustion
(`Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionSncGlobal`); the clause that the exceptional
locus is a divisor with simple normal crossings ([Kol07, Theorem 45, (3)]; [Wlo09, Theorem 2.0.1,
(2)]) follows.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set AlgebraicGeometry
open Manifold AnalyticSpace AnalyticSpace.KLocallyRingedSpace

universe u

namespace Hironaka

/-- The colimit index of a chain of partial maps `f n : {σ // p n σ} → Λ (n+1)`: the quotient of
`Σ n, Λ n` by the generated equivalence `⟨n, σ⟩ ~ ⟨n+1, f n ⟨σ, h⟩⟩`. -/
def chainColimitIndex (Λ : ℕ → Type u) (p : ∀ n, Λ n → Prop)
    (f : ∀ n, {σ // p n σ} → Λ (n + 1)) : Type u :=
  Quot (fun (a b : Σ n, Λ n) => ∃ (h : p a.1 a.2), b = ⟨a.1 + 1, f a.1 ⟨a.2, h⟩⟩)

namespace chainColimitIndex

variable {Λ : ℕ → Type u} {p : ∀ n, Λ n → Prop} {f : ∀ n, {σ // p n σ} → Λ (n + 1)}

/-- The step relation of the colimit: `b` is the image of the non-empty traced `a` under the label
map. -/
def chainStep (Λ : ℕ → Type u) (p : ∀ n, Λ n → Prop) (f : ∀ n, {σ // p n σ} → Λ (n + 1))
    (a b : Σ n, Λ n) : Prop :=
  ∃ (h : p a.1 a.2), b = ⟨a.1 + 1, f a.1 ⟨a.2, h⟩⟩

/-- A step raises the level by one. -/
theorem chainStep_fst_eq {a b : Σ n, Λ n} (h : chainStep Λ p f a b) : b.1 = a.1 + 1 := by
  obtain ⟨_, rfl⟩ := h
  rfl

/-- The step relation is functional. -/
theorem chainStep_unique {a b₁ b₂ : Σ n, Λ n} (h₁ : chainStep Λ p f a b₁)
    (h₂ : chainStep Λ p f a b₂) : b₁ = b₂ := by
  obtain ⟨_, rfl⟩ := h₁
  obtain ⟨_, rfl⟩ := h₂
  rfl

/-- Descendants lie at higher levels. -/
theorem fst_le_of_reflTransGen {a c : Σ n, Λ n} (h : Relation.ReflTransGen (chainStep Λ p f) a c) :
    a.1 ≤ c.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => rw [(chainStep_fst_eq hbc)]; omega

/-- A descendant at the same level is the point itself. -/
theorem eq_of_reflTransGen_of_fst_eq {a c : Σ n, Λ n}
    (h : Relation.ReflTransGen (chainStep Λ p f) a c) (hfst : a.1 = c.1) : a = c := by
  rcases h.cases_head with rfl | ⟨b, hab, hbc⟩
  · rfl
  · have h1 := fst_le_of_reflTransGen hbc
    have h2 := (chainStep_fst_eq hab)
    omega

/-- Descendants of one point are linearly ordered: the step relation is functional. -/
theorem reflTransGen_or_of_reflTransGen {b c₁ c₂ : Σ n, Λ n}
    (h₁ : Relation.ReflTransGen (chainStep Λ p f) b c₁)
    (h₂ : Relation.ReflTransGen (chainStep Λ p f) b c₂) :
    Relation.ReflTransGen (chainStep Λ p f) c₁ c₂ ∨
      Relation.ReflTransGen (chainStep Λ p f) c₂ c₁ := by
  induction h₁ using Relation.ReflTransGen.head_induction_on generalizing c₂ with
  | refl => exact Or.inl h₂
  | head hbb' hb'c₁ ih =>
    rcases h₂.cases_head with rfl | ⟨b'', hbb'', hb''c₂⟩
    · exact Or.inr (Relation.ReflTransGen.head hbb' hb'c₁)
    · rw [chainStep_unique hbb' hbb''] at hb'c₁ ih
      exact ih hb''c₂

/-- Two ancestors of one point at the same level coincide when every `f n` is injective. -/
theorem eq_of_reflTransGen_of_reflTransGen_of_fst_eq (hf : ∀ n, Function.Injective (f n))
    {a a' c : Σ n, Λ n} (h : Relation.ReflTransGen (chainStep Λ p f) a c)
    (h' : Relation.ReflTransGen (chainStep Λ p f) a' c) (hfst : a.1 = a'.1) : a = a' := by
  induction h using Relation.ReflTransGen.head_induction_on generalizing a' with
  | refl => exact (eq_of_reflTransGen_of_fst_eq h' hfst.symm).symm
  | @head a b hab hbc ih =>
    rcases h'.cases_head with rfl | ⟨b', ha'b', hb'c⟩
    · have h1 := fst_le_of_reflTransGen hbc
      have h2 := (chainStep_fst_eq hab)
      omega
    · have hb : b = b' := ih hb'c (by rw [(chainStep_fst_eq hab), (chainStep_fst_eq ha'b'), hfst])
      obtain ⟨m, x⟩ := a
      obtain ⟨m', x'⟩ := a'
      obtain rfl : m = m' := hfst
      obtain ⟨hx, rfl⟩ := hab
      obtain ⟨hx', rfl⟩ := ha'b'
      have h3 : f m ⟨x, hx⟩ = f m ⟨x', hx'⟩ := eq_of_heq (Sigma.mk.inj_iff.mp hb).2
      have h4 := hf m h3
      rw [Subtype.mk.injEq] at h4
      rw [h4]

/-- Descent is contained in the generated equivalence. -/
theorem eqvGen_of_reflTransGen {a c : Σ n, Λ n} (h : Relation.ReflTransGen (chainStep Λ p f) a c) :
    Relation.EqvGen (chainStep Λ p f) a c := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

/-- The generated equivalence of the (functional) step relation is "a common descendant". -/
theorem eqvGen_iff_exists_reflTransGen {a b : Σ n, Λ n} :
    Relation.EqvGen (chainStep Λ p f) a b ↔
      ∃ c, Relation.ReflTransGen (chainStep Λ p f) a c ∧
        Relation.ReflTransGen (chainStep Λ p f) b c := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
    | refl x => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | symm x y _ ih => obtain ⟨c, h₁, h₂⟩ := ih; exact ⟨c, h₂, h₁⟩
    | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨c₁, hx₁, hy₁⟩ := ih₁
      obtain ⟨c₂, hy₂, hz₂⟩ := ih₂
      rcases reflTransGen_or_of_reflTransGen hy₁ hy₂ with h | h
      · exact ⟨c₂, hx₁.trans h, hz₂⟩
      · exact ⟨c₁, hx₁, hz₂.trans h⟩
  · rintro ⟨c, h₁, h₂⟩
    exact Relation.EqvGen.trans _ _ _ (eqvGen_of_reflTransGen h₁)
      (Relation.EqvGen.symm _ _ (eqvGen_of_reflTransGen h₂))

/-- Two members of one level are identified only when equal (each `f n` injective): the colimit
index is a tree of chains, no two members of one level identified. -/
theorem mk_injective (hf : ∀ n, Function.Injective (f n)) (n : ℕ) :
    Function.Injective (fun σ : Λ n => (Quot.mk _ ⟨n, σ⟩ : chainColimitIndex Λ p f)) := by
  intro σ σ' h
  have h1 : Relation.EqvGen (chainStep Λ p f) ⟨n, σ⟩ ⟨n, σ'⟩ := Quot.eq.mp h
  obtain ⟨c, hc, hc'⟩ := eqvGen_iff_exists_reflTransGen.mp h1
  have h2 := eq_of_reflTransGen_of_reflTransGen_of_fst_eq hf hc hc' rfl
  exact eq_of_heq (Sigma.mk.inj_iff.mp h2).2

/-- A level-`n` member and a level-`(n+1)` member share a class iff the second is the first's image.
-/
theorem mk_eq_mk_succ_iff (hf : ∀ n, Function.Injective (f n)) (n : ℕ) (σ : Λ n)
    (τ : Λ (n + 1)) :
    (Quot.mk _ ⟨n, σ⟩ : chainColimitIndex Λ p f) = Quot.mk _ ⟨n + 1, τ⟩ ↔
      ∃ h : p n σ, f n ⟨σ, h⟩ = τ := by
  constructor
  · intro h
    have h1 : Relation.EqvGen (chainStep Λ p f) ⟨n, σ⟩ ⟨n + 1, τ⟩ := Quot.eq.mp h
    obtain ⟨c, hc, hc'⟩ := eqvGen_iff_exists_reflTransGen.mp h1
    rcases hc.cases_head with hac | ⟨b, hab, hbc⟩
    · have h2 : n + 1 ≤ c.1 := fst_le_of_reflTransGen hc'
      have h3 : c.1 = n := by rw [← hac]
      omega
    · have hb : b = ⟨n + 1, τ⟩ :=
        eq_of_reflTransGen_of_reflTransGen_of_fst_eq hf hbc hc' (by rw [(chainStep_fst_eq hab)])
      obtain ⟨hσ, rfl⟩ := hab
      exact ⟨hσ, eq_of_heq (Sigma.mk.inj_iff.mp hb).2⟩
  · rintro ⟨h, rfl⟩
    exact Quot.sound ⟨h, rfl⟩

end chainColimitIndex

end Hironaka

open Hironaka

namespace AnalyticSpace.QuotientSpace

/-- The pull-back of the unit ideal sheaf is the unit ideal sheaf. -/
@[simp]
theorem comap_top {X X' : AlgebraicGeometry.LocallyRingedSpace.{u}} (φ : X' ⟶ X) :
    QuotientSpace.comap φ (⊤ : IdealSheaf X.𝒪) = ⊤ :=
  IdealSheaf.ext fun z => (QuotientSpace.stalkIdeal_comap φ ⊤ z).trans
    ((congrArg (Ideal.map (φ.stalkMap z).hom) (IdealSheaf.stalkIdeal_top _)).trans
      ((Ideal.map_top _).trans (IdealSheaf.stalkIdeal_top (𝒪 := X'.𝒪) z).symm))

end AnalyticSpace.QuotientSpace

namespace Manifold.IdealSheaf

/-- An ideal sheaf with empty cosupport is the unit ideal sheaf. -/
theorem eq_top_of_not_nonempty_support {Y : TopCat.{u}} {𝒪 : TopCat.Sheaf CommRingCat.{u} Y}
    {J : IdealSheaf 𝒪} (h : ¬ J.support.Nonempty) : J = ⊤ := by
  apply IdealSheaf.ext
  intro x
  rw [IdealSheaf.stalkIdeal_top]
  by_contra hx
  exact h ⟨x, hx⟩

end Manifold.IdealSheaf

namespace AnalyticSpace.ClosedSubspace

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K}

/-- A point of the cosupport of a trace on an open subspace lies in the cosupport of the member
(`QuotientSpace.cosupport_comap`; the `restrictInclusion` form is
`mem_support_of_comap_restrictInclusion` of
`Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyPartner`). -/
theorem mem_cosupport_of_comap_ofRestrict {A : ClosedSubspace X} (U : Opens X)
    {p : X.toKLocallyRingedSpace.restrictOpen U}
    (hp : p ∈ (QuotientSpace.comap (ofRestrict X.toKLocallyRingedSpace U).1 A).support) :
    p.1 ∈ A.support :=
  (Set.ext_iff.mp (QuotientSpace.cosupport_comap (ofRestrict X.toKLocallyRingedSpace U).1 A)
    p).mp hp

/-- Two closed subspaces with the same trace on an open subspace have the same stalk ideal at every
point of the open subset (`KLocallyRingedSpace.isIso_ofRestrict_stalkMap`; the `restrictInclusion`
form is
`stalkIdeal_eq_of_comap_restrictInclusion_eq` of
`Hironaka.Resolution.Analytic.Kol07Thm45.Glue.OverFamilyPartner`). -/
theorem stalkIdeal_eq_of_comap_ofRestrict_eq {A B : ClosedSubspace X} (U : Opens X)
    (h : QuotientSpace.comap (ofRestrict X.toKLocallyRingedSpace U).1 A =
      QuotientSpace.comap (ofRestrict X.toKLocallyRingedSpace U).1 B)
    (p : X.toKLocallyRingedSpace.restrictOpen U) : A.stalkIdeal p.1 = B.stalkIdeal p.1 := by
  have hiso : IsIso ((ofRestrict X.toKLocallyRingedSpace U).1.stalkMap p) :=
    KLocallyRingedSpace.isIso_ofRestrict_stalkMap X.toKLocallyRingedSpace U p
  have hbij : Function.Bijective ((ofRestrict X.toKLocallyRingedSpace U).1.stalkMap p).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hA := QuotientSpace.stalkIdeal_comap (ofRestrict X.toKLocallyRingedSpace U).1 A p
  have hB := QuotientSpace.stalkIdeal_comap (ofRestrict X.toKLocallyRingedSpace U).1 B p
  have hmap : (A.stalkIdeal p.1).map ((ofRestrict X.toKLocallyRingedSpace U).1.stalkMap p).hom =
      (B.stalkIdeal p.1).map ((ofRestrict X.toKLocallyRingedSpace U).1.stalkMap p).hom :=
    hA.symm.trans ((congrArg (fun D : IdealSheaf _ => D.stalkIdeal p) h).trans hB)
  have h2 := congrArg (Ideal.comap ((ofRestrict X.toKLocallyRingedSpace U).1.stalkMap p).hom) hmap
  exact (Ideal.comap_map_of_bijective _ hbij).symm.trans
    (h2.trans (Ideal.comap_map_of_bijective _ hbij))

/-- Two members of a simple-normal-crossings family with the same trace on an open subset, the trace
non-empty, are the same member (`IsSncFamily.eq_of_comap_restrictInclusion_eq_of_nonempty` in the
`restrictOpen` spelling). -/
theorem IsSncFamily.eq_of_comap_ofRestrict_eq_of_nonempty {ι : Type u}
    {H : ι → ClosedSubspace X} (h : ClosedSubspace.IsSncFamily H) (U : Opens X) {σ τ : ι}
    (heq : QuotientSpace.comap (ofRestrict X.toKLocallyRingedSpace U).1 (H σ) =
      QuotientSpace.comap (ofRestrict X.toKLocallyRingedSpace U).1 (H τ))
    (hne : (QuotientSpace.comap (ofRestrict X.toKLocallyRingedSpace U).1
      (H σ)).support.Nonempty) : σ = τ := by
  obtain ⟨p, hp⟩ := hne
  have hp' := hp
  rw [heq] at hp'
  exact h.eq_of_stalkIdeal_eq_of_mem_support (mem_cosupport_of_comap_ofRestrict U hp)
    (mem_cosupport_of_comap_ofRestrict U hp') (stalkIdeal_eq_of_comap_ofRestrict_eq U heq p)

/-- A labelled identity between two families along a morphism holds as soon as it holds on an open
neighbourhood of every point: equality of closed subspaces is stalkwise
(`comap_restrict_eq_of_forall_exists_local` in the `restrictOpen` spelling; [Kol07, Proposition 37,
(37.2)]). -/
theorem comap_eq_of_forall_exists_local {Y₁ Y₂ : AnalyticSpace.{u} K} (ψ : Y₁ ⟶ Y₂)
    {Λ₁ Λ₂ : Type u} (A : Λ₁ → ClosedSubspace Y₁) (B : Λ₂ → ClosedSubspace Y₂) (e : Λ₁ → Λ₂)
    (hloc : ∀ x : Y₁, ∃ V : Opens Y₁, x ∈ V ∧ ∀ σ,
      QuotientSpace.comap (ofRestrict Y₁.toKLocallyRingedSpace V).1
          (QuotientSpace.comap ψ.1 (B (e σ))) =
        QuotientSpace.comap (ofRestrict Y₁.toKLocallyRingedSpace V).1 (A σ)) :
    ∀ σ, QuotientSpace.comap ψ.1 (B (e σ)) = A σ := by
  intro σ
  apply IdealSheaf.ext
  intro y
  obtain ⟨V, hyV, hV⟩ := hloc y
  exact stalkIdeal_eq_of_comap_ofRestrict_eq V (hV σ) ⟨y, hyV⟩

/-- Along an isomorphism, a member with non-empty support has a unique partner in a
simple-normal-crossings family whose pull-back is the member, once one is given locally (uniqueness
by the rigidity of the pulled-back family; `existsUnique_partner_of_forall_exists_local_label` in
the `restrictOpen` spelling). -/
theorem existsUnique_comap_eq_of_forall_exists_local {Y₁ Y₂ : AnalyticSpace.{u} K} (ψ : Y₁ ⟶ Y₂)
    (hψ : IsIso ψ) {Λ₁ Λ₂ : Type u} (A : Λ₁ → ClosedSubspace Y₁)
    (B : Λ₂ → ClosedSubspace Y₂) (hB : ClosedSubspace.IsSncFamily B) (e : Λ₁ → Λ₂)
    (hloc : ∀ x : Y₁, ∃ V : Opens Y₁, x ∈ V ∧ ∀ σ,
      QuotientSpace.comap (ofRestrict Y₁.toKLocallyRingedSpace V).1
          (QuotientSpace.comap ψ.1 (B (e σ))) =
        QuotientSpace.comap (ofRestrict Y₁.toKLocallyRingedSpace V).1 (A σ))
    (σ : Λ₁) (hσ : (A σ).support.Nonempty) :
    ∃! τ, QuotientSpace.comap ψ.1 (B τ) = A σ := by
  have hall := comap_eq_of_forall_exists_local ψ A B e hloc
  refine ⟨e σ, hall σ, fun τ hτ => ?_⟩
  have hfam : ClosedSubspace.IsSncFamily fun τ =>
      (QuotientSpace.comap ψ.1 (B τ) : ClosedSubspace Y₁) :=
    ClosedSubspace.isSncFamily_comap_of_isIso ψ hψ hB
  obtain ⟨p, hp⟩ := hσ
  have hpτ := hp
  rw [← hτ] at hpτ
  have hpe := hp
  rw [← hall σ] at hpe
  exact hfam.eq_of_stalkIdeal_eq_of_mem_support hpτ hpe
    (congrArg (fun D : ClosedSubspace Y₁ => D.stalkIdeal p) (hτ.trans (hall σ).symm))

end AnalyticSpace.ClosedSubspace

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K]

/-- The converse of `comap_eq_of_stalk_square`: in the square `α ≫ a = σ' ≫ β ≫ b` with `α`, `β`
surjective and `σ`, `σ'` inverse, ideals identified under `σ` after pulling back have the same
image. -/
theorem map_eq_of_comap_eq_of_stalk_square {A B A' B' S : CommRingCat} (α : A ⟶ A') (β : B ⟶ B')
    (a : A' ⟶ S) (b : B' ⟶ S) (σ : B ⟶ A) (σ' : A ⟶ B) (hσ : σ ≫ σ' = 𝟙 B) (hσ' : σ' ≫ σ = 𝟙 A)
    (hα : Function.Surjective α.hom) (hβ : Function.Surjective β.hom)
    (hsq : α ≫ a = σ' ≫ β ≫ b) (I : Ideal A') (J : Ideal B')
    (hIJ : Ideal.comap σ.hom (Ideal.comap α.hom I) = Ideal.comap β.hom J) :
    Ideal.map a.hom I = Ideal.map b.hom J := by
  have hiso : IsIso σ := ⟨⟨σ', hσ, hσ'⟩⟩
  have hσs : Function.Surjective σ.hom := (ConcreteCategory.bijective_of_isIso σ).2
  have h1 : Ideal.comap α.hom I = Ideal.map σ.hom (Ideal.comap β.hom J) := by
    rw [← hIJ, Ideal.map_comap_of_surjective _ hσs]
  have h2 : Ideal.map σ'.hom (Ideal.comap α.hom I) = Ideal.comap β.hom J := by
    rw [h1, Ideal.map_map, ← CommRingCat.hom_comp, hσ, CommRingCat.hom_id, Ideal.map_id]
  calc Ideal.map a.hom I = Ideal.map a.hom (Ideal.map α.hom (Ideal.comap α.hom I)) := by
        rw [Ideal.map_comap_of_surjective _ hα]
    _ = Ideal.map (α ≫ a).hom (Ideal.comap α.hom I) := by
        rw [CommRingCat.hom_comp, Ideal.map_map]
    _ = Ideal.map (σ' ≫ β ≫ b).hom (Ideal.comap α.hom I) := by rw [hsq]
    _ = Ideal.map b.hom (Ideal.map β.hom (Ideal.map σ'.hom (Ideal.comap α.hom I))) := by
        simp only [CommRingCat.hom_comp, Ideal.map_map, RingHom.comp_assoc]
    _ = Ideal.map b.hom J := by rw [h2, Ideal.map_comap_of_surjective _ hβ]

section Pairwise

variable {X : AnalyticSpace.{u} K} {ι : Type u} [Countable ι] {R : ι → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ι → Opens X}
  (G : GlueOver X R π dom)

/-- Representative independence for one pair from that pair's compatibility (`pieceStalkIdeal_eq`,
pairwise). -/
theorem pieceStalkIdeal_eq_of_pair (C : ∀ i, ClosedSubspace (R i)) {i j : ι}
    (hij : QuotientSpace.comap (G.t i j).1 (restrictGlue π dom j i (C j)) =
      restrictGlue π dom i j (C i))
    {y : R i} {y' : R j} (h : KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y =
        KLocallyRingedSpace.Hom.toFun (G.ιGlued j) y') :
    Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq h)).hom (G.pieceStalkIdeal C i y) =
      G.pieceStalkIdeal C j y' := by
  obtain ⟨v, hv₁, hv₂⟩ := G.exists_t_eq_of_toFun_ιGlued_eq h
  subst hv₁
  subst hv₂
  set f₁ := (ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j)).1 with hf₁
  set f₂ := (G.t i j).1 ≫ (ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)).1
    with hf₂
  have hglue : f₁ ≫ (G.ιGlued i).1 = f₂ ≫ (G.ιGlued j).1 := by
    rw [hf₂, Category.assoc]; exact G.ofRestrict_comp_ιGlued i j
  have hiso : IsIso (G.t i j).1 := G.toKGlueData.toLRSGlueData.toGlueData.t_isIso i j
  have hoi : LocallyRingedSpace.IsOpenImmersion (G.t i j).1 :=
    LocallyRingedSpace.IsOpenImmersion.of_isIso _
  have hoi₂ : LocallyRingedSpace.IsOpenImmersion f₂ :=
    LocallyRingedSpace.IsOpenImmersion.comp (H := hoi) (G.t i j).1
      (ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)).1
  have hb₂ : Function.Bijective (f₂.stalkMap v).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (@LocallyRingedSpace.IsOpenImmersion.stalk_iso _ _ f₂ hoi₂ v)
  have hb₁ : Function.Bijective (f₁.stalkMap v).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hcomp : Ideal.map (f₁.stalkMap v).hom ((C i).stalkIdeal v.1) =
      Ideal.map (f₂.stalkMap v).hom ((C j).stalkIdeal (f₂.base v)) := by
    have h1 := congrArg (fun J : IdealSheaf _ => J.stalkIdeal v) hij
    simp only [restrictGlue, ← QuotientSpace.comap_comp] at h1
    rw [QuotientSpace.stalkIdeal_comap, QuotientSpace.stalkIdeal_comap] at h1
    exact h1.symm
  have hstalk := LocallyRingedSpace.stalkMap_congr_hom _ _ hglue v
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at hstalk
  unfold pieceStalkIdeal
  exact comap_eq_of_stalk_square _ _ _ _ _ _ (stalkSpecializes_comp_eq_id _ h _ _) hb₁ hb₂ hstalk
    _ _ hcomp

/-- Compatibility of one pair from representative independence at every point of its gluing open
subset (the converse of `pieceStalkIdeal_eq_of_pair`). -/
theorem compat_pair_of_forall_pieceStalkIdeal_eq (C : ∀ i, ClosedSubspace (R i)) (i j : ι)
    (hP : ∀ (y : R i) (y' : R j) (h : KLocallyRingedSpace.Hom.toFun
        (G.ιGlued i) y = KLocallyRingedSpace.Hom.toFun (G.ιGlued j) y'),
      Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
          (specializes_of_eq h)).hom (G.pieceStalkIdeal C i y) = G.pieceStalkIdeal C j y') :
    QuotientSpace.comap (G.t i j).1 (restrictGlue π dom j i (C j)) =
      restrictGlue π dom i j (C i) := by
  set f₁ := (ofRestrict (R i).toKLocallyRingedSpace (glueOpens X R π dom i j)).1 with hf₁
  set f₂ := (G.t i j).1 ≫ (ofRestrict (R j).toKLocallyRingedSpace (glueOpens X R π dom j i)).1
    with hf₂
  have hglue : f₁ ≫ (G.ιGlued i).1 = f₂ ≫ (G.ιGlued j).1 := by
    rw [hf₂, Category.assoc]; exact G.ofRestrict_comp_ιGlued i j
  apply IdealSheaf.ext
  intro v
  have hpt : KLocallyRingedSpace.Hom.toFun (G.ιGlued i) v.1 = KLocallyRingedSpace.Hom.toFun
      (G.ιGlued j) (f₂.base v) := by
    have h0 := congrArg (fun φ : _ ⟶ G.gluedOver.toLocallyRingedSpace => φ.base v) hglue
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at h0
    exact h0
  have hα : Function.Surjective ((G.ιGlued i).1.stalkMap v.1).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2
  have hβ : Function.Surjective ((G.ιGlued j).1.stalkMap (f₂.base v)).hom :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).2
  have hstalk := LocallyRingedSpace.stalkMap_congr_hom _ _ hglue v
  rw [LocallyRingedSpace.stalkMap_comp, LocallyRingedSpace.stalkMap_comp] at hstalk
  have hP' := hP v.1 (f₂.base v) hpt
  unfold pieceStalkIdeal at hP'
  have hmap := map_eq_of_comap_eq_of_stalk_square _ _ _ _ _ _
    (stalkSpecializes_comp_eq_id _ hpt _ _) (stalkSpecializes_comp_eq_id _ hpt.symm _ _) hα hβ
    hstalk _ _ hP'
  simp only [restrictGlue, ← QuotientSpace.comap_comp]
  rw [QuotientSpace.stalkIdeal_comap, QuotientSpace.stalkIdeal_comap]
  exact hmap.symm

/-- Representative independence is symmetric in the two representatives
(`stalkSpecializes_comp_eq_id`). -/
theorem pieceStalkIdeal_eq_symm (C : ∀ i, ClosedSubspace (R i)) {i j : ι} {y : R i} {y' : R j}
    (h : KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y = KLocallyRingedSpace.Hom.toFun
        (G.ιGlued j) y')
    (hP : Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq h)).hom (G.pieceStalkIdeal C i y) = G.pieceStalkIdeal C j y') :
    Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq h.symm)).hom (G.pieceStalkIdeal C j y') = G.pieceStalkIdeal C i y := by
  rw [← hP, Ideal.comap_comap, ← CommRingCat.hom_comp, stalkSpecializes_comp_eq_id _ h.symm _ _,
    CommRingCat.hom_id, Ideal.comap_id]

end Pairwise

section Chain

variable {X : AnalyticSpace.{u} K} {R : ULift.{u} ℕ → AnalyticSpace.{u} K}
  {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace} {dom : ULift.{u} ℕ → Opens X}
  (G : GlueOver X R π dom)

/-- The base open subsets of a chain are monotone. -/
theorem dom_mono (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1))) {n m : ℕ}
    (h : n ≤ m) : dom (ULift.up n) ≤ dom (ULift.up m) := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (hmono _)

include G in
/-- On a chain, a lower level lies entirely over the base open subset of every higher level: its
gluing open subset with a higher level is everything. -/
theorem mem_glueOpens_of_le (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1)))
    {n m : ℕ} (h : n ≤ m) (y : R (ULift.up n)) :
    y ∈ glueOpens X R π dom (ULift.up n) (ULift.up m) :=
  ⟨G.range_subset _ ⟨y, rfl⟩, dom_mono hmono h (G.range_subset _ ⟨y, rfl⟩)⟩

/-- A point of level `n` as a point of the gluing open subset with level `m ≥ n`. -/
def liftPt (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1))) {n m : ℕ} (h : n ≤ m)
    (y : R (ULift.up n)) :
    (R (ULift.up n)).toKLocallyRingedSpace.restrictOpen
      (glueOpens X R π dom (ULift.up n) (ULift.up m)) :=
  (⟨y, mem_glueOpens_of_le G hmono h y⟩ : glueOpens X R π dom (ULift.up n) (ULift.up m))

/-- The point-level glue identity along the chain: a point of level `n` and its image in level
`m ≥ n` under the transition have the same image in the glued space (`ofRestrict_comp_ιGlued`). -/
theorem toFun_ιGlued_eq_of_le (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1)))
    {n m : ℕ} (h : n ≤ m) (y : R (ULift.up n)) :
    KLocallyRingedSpace.Hom.toFun (G.ιGlued (ULift.up n)) y = KLocallyRingedSpace.Hom.toFun
        (G.ιGlued (ULift.up m))
      (KLocallyRingedSpace.Hom.toFun (G.t (ULift.up n) (ULift.up m)) (liftPt G hmono h y)).1 := by
  have h0 := congrArg (fun φ : _ ⟶ G.gluedOver.toLocallyRingedSpace =>
    φ.base (liftPt G hmono h y)) (G.ofRestrict_comp_ιGlued (ULift.up n) (ULift.up m))
  simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at h0
  exact h0

/-- Representative independence along the chain, by induction on the higher level from the adjacent
pairs (`pieceStalkIdeal_eq_of_pair`) through the nested images. -/
theorem pieceStalkIdeal_eq_of_le (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1)))
    (C : ∀ i, ClosedSubspace (R i))
    (hadj : ∀ n : ℕ, QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (C (ULift.up (n + 1)))) =
      restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (C (ULift.up n)))
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ (y : R (ULift.up n)) (y' : R (ULift.up m))
      (h : KLocallyRingedSpace.Hom.toFun (G.ιGlued (ULift.up n)) y = KLocallyRingedSpace.Hom.toFun
          (G.ιGlued (ULift.up m)) y'),
      Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
          (specializes_of_eq h)).hom (G.pieceStalkIdeal C (ULift.up n) y) =
        G.pieceStalkIdeal C (ULift.up m) y' := by
  induction hnm with
  | refl =>
    intro y y' h
    have hinj : Function.Injective (KLocallyRingedSpace.Hom.toFun (G.ιGlued (ULift.up n))) :=
      (G.isOpenImmersion_ιGlued (ULift.up n)).base_open.injective
    obtain rfl := hinj h
    rw [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.comap_id]
  | @step m hnm ih =>
    intro y y'' h
    have h₁ := toFun_ιGlued_eq_of_le G hmono hnm y
    have h₂ : KLocallyRingedSpace.Hom.toFun (G.ιGlued (ULift.up m))
        (KLocallyRingedSpace.Hom.toFun (G.t (ULift.up n) (ULift.up m)) (liftPt G hmono hnm y)).1 =
        KLocallyRingedSpace.Hom.toFun (G.ιGlued (ULift.up (m + 1))) y'' := h₁.symm.trans h
    rw [← pieceStalkIdeal_eq_of_pair G C (hadj m) h₂, ← ih y _ h₁, Ideal.comap_comap,
      ← CommRingCat.hom_comp, TopCat.Presheaf.stalkSpecializes_comp]

/-- Representative independence for every pair of levels of a chain (both orders, by symmetry). -/
theorem pieceStalkIdeal_eq_of_chain (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1)))
    (C : ∀ i, ClosedSubspace (R i))
    (hadj : ∀ n : ℕ, QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (C (ULift.up (n + 1)))) =
      restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (C (ULift.up n)))
    (i j : ULift.{u} ℕ) (y : R i) (y' : R j)
    (h : KLocallyRingedSpace.Hom.toFun (G.ιGlued i) y = KLocallyRingedSpace.Hom.toFun
        (G.ιGlued j) y') :
    Ideal.comap (G.gluedOver.toLocallyRingedSpace.presheaf.stalkSpecializes
        (specializes_of_eq h)).hom (G.pieceStalkIdeal C i y) = G.pieceStalkIdeal C j y' := by
  rcases le_total i.down j.down with hij | hji
  · exact pieceStalkIdeal_eq_of_le G hmono C hadj hij y y' h
  · exact pieceStalkIdeal_eq_symm G C h.symm
      (pieceStalkIdeal_eq_of_le G hmono C hadj hji y' y h.symm)

/-- **On a chain, compatibility of closed subspaces of the levels follows from compatibility of the
adjacent pairs**, in one direction: the transported stalk ideals agree at every glued point by
induction along the nested images of the levels; no cocycle bookkeeping. -/
theorem compatClosedSubspaces_of_chain (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1)))
    (C : ∀ i, ClosedSubspace (R i))
    (hadj : ∀ n : ℕ, QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (C (ULift.up (n + 1)))) =
      restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (C (ULift.up n))) :
    G.CompatClosedSubspaces C :=
  fun i j => compat_pair_of_forall_pieceStalkIdeal_eq G C i j
    (fun y y' h => pieceStalkIdeal_eq_of_chain G hmono C hadj i j y y' h)

variable {Λ : ℕ → Type u}

variable (π dom) in
/-- The members of level `n` with non-empty trace on the overlap with level `n+1`. -/
def chainTraceNonempty (H : ∀ n, Λ n → ClosedSubspace (R (ULift.up n))) (n : ℕ) (σ : Λ n) :
    Prop :=
  (restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (H n σ)).support.Nonempty

variable (π dom) in
/-- The index of the glued chain family: the colimit of the levels' members along the label maps on
the non-empty traced members. -/
abbrev ChainIndex (H : ∀ n, Λ n → ClosedSubspace (R (ULift.up n)))
    (e : ∀ n, {σ : Λ n // chainTraceNonempty π dom H n σ} → Λ (n + 1)) : Type u :=
  chainColimitIndex Λ (chainTraceNonempty π dom H) e

section Labelled

variable (hmono : ∀ n : ℕ, dom (ULift.up n) ≤ dom (ULift.up (n + 1)))
  (H : ∀ n, Λ n → ClosedSubspace (R (ULift.up n))) (hH : ∀ n, ClosedSubspace.IsSncFamily (H n))
  (e : ∀ n, {σ : Λ n // chainTraceNonempty π dom H n σ} → Λ (n + 1))
  (hpair : ∀ n (σ : {σ : Λ n // chainTraceNonempty π dom H n σ}),
    QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) (e n σ))) =
      restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (H n σ.1))
  (hsurj : ∀ n (τ : Λ (n + 1)),
    (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) τ)).support.Nonempty →
      ∃ σ, e n σ = τ)

include hH hpair in
/-- The label maps are injective: rigidity of the members of a simple-normal-crossings family on the
non-empty traces (`IsSncFamily.eq_of_comap_ofRestrict_eq_of_nonempty`). -/
theorem injective_chainLabelMap (n : ℕ) : Function.Injective (e n) := by
  intro σ₁ σ₂ h12
  have h1 := hpair n σ₁
  have h2 := hpair n σ₂
  rw [h12] at h1
  have heq := h1.symm.trans h2
  exact Subtype.ext ((hH n).eq_of_comap_ofRestrict_eq_of_nonempty _ heq σ₁.2)

include hH hpair in
/-- The labels are injective on every level (`chainColimitIndex.mk_injective`). -/
theorem injective_chainLabel (i : ULift.{u} ℕ) :
    Function.Injective (fun σ : Λ i.down => (Quot.mk _ ⟨i.down, σ⟩ : ChainIndex π dom H e)) :=
  chainColimitIndex.mk_injective (injective_chainLabelMap G H hH e hpair) i.down

include hmono hH hpair hsurj in
/-- **Labelled compatibility of a chain of simple-normal-crossings families**: the levels' members
labelled by their classes in the colimit index are compatible closed subspaces, given the adjacent
identities on the non-empty traced members (`hpair`) and that every level-`(n+1)` member meeting the
overlap is a partner (`hsurj`): four cases per label and adjacent pair (both levels represented; the
lower only, its trace empty by the definition of the label maps' domain; the upper only, its trace
empty by `hsurj`, so both sides are again the unit ideal sheaf; neither), then the chain lemma
`compatClosedSubspaces_of_chain`. -/
theorem chainLabelledCompat :
    G.LabelledCompat (fun (i : ULift.{u} ℕ) (σ : Λ i.down) => H i.down σ)
      (fun (i : ULift.{u} ℕ) (σ : Λ i.down) => (Quot.mk _ ⟨i.down, σ⟩ : ChainIndex π dom H e)) := by
  have hf := injective_chainLabelMap G H hH e hpair
  have hlab := injective_chainLabel G H hH e hpair
  set H' : ∀ i : ULift.{u} ℕ, Λ i.down → ClosedSubspace (R i) := fun i σ => H i.down σ with hH'
  set lab : ∀ i : ULift.{u} ℕ, Λ i.down → ChainIndex π dom H e :=
    fun i σ => Quot.mk _ ⟨i.down, σ⟩ with hlabdef
  intro l
  apply compatClosedSubspaces_of_chain G hmono
  intro n
  -- the two sides through the two levels' members of the label
  have key : ∀ (A : ClosedSubspace (R (ULift.up n))) (B : ClosedSubspace (R (ULift.up (n + 1))))
      (hm1 : memberOfLabel H' lab (ULift.up n) l = A)
      (hm2 : memberOfLabel H' lab (ULift.up (n + 1)) l = B)
      (hAB : QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
          (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) B) =
        restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) A),
      QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
          (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n)
            (memberOfLabel H' lab (ULift.up (n + 1)) l)) =
        restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (memberOfLabel H' lab (ULift.up n) l) :=
    fun A B hm1 hm2 hAB =>
      (congrArg (fun D => QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
        (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) D)) hm2).trans
        (hAB.trans (congrArg (restrictGlue π dom (ULift.up n) (ULift.up (n + 1))) hm1).symm)
  have rtop : restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (⊤ : ClosedSubspace _) = ⊤ :=
    QuotientSpace.comap_top _
  have rtop' : restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (⊤ : ClosedSubspace _) = ⊤ :=
    QuotientSpace.comap_top _
  have htoptop : QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1
      (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) ⊤) =
      restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) ⊤ :=
    (congrArg (QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1) rtop').trans
      ((QuotientSpace.comap_top _).trans rtop.symm)
  by_cases hn : ∃ σ : Λ n, lab (ULift.up n) σ = l
  · obtain ⟨σ, hσ⟩ := hn
    have hm1 : memberOfLabel H' lab (ULift.up n) l = H n σ := by
      rw [← hσ]; exact memberOfLabel_lab hlab (ULift.up n) σ
    by_cases hn1 : ∃ τ : Λ (n + 1), lab (ULift.up (n + 1)) τ = l
    · obtain ⟨τ, hτ⟩ := hn1
      obtain ⟨hp, hτ'⟩ := (chainColimitIndex.mk_eq_mk_succ_iff hf n σ τ).mp
        (hσ.trans hτ.symm)
      have hm2 : memberOfLabel H' lab (ULift.up (n + 1)) l = H (n + 1) (e n ⟨σ, hp⟩) := by
        rw [← hτ, ← hτ']; exact memberOfLabel_lab hlab (ULift.up (n + 1)) _
      exact key _ _ hm1 hm2 (hpair n ⟨σ, hp⟩)
    · have hm2 : memberOfLabel H' lab (ULift.up (n + 1)) l = ⊤ :=
        memberOfLabel_of_not_exists hn1
      have hne : ¬ chainTraceNonempty π dom H n σ := fun hp =>
        hn1 ⟨e n ⟨σ, hp⟩, ((chainColimitIndex.mk_eq_mk_succ_iff hf n σ _).mpr
          ⟨hp, rfl⟩).symm.trans hσ⟩
      have htop : restrictGlue π dom (ULift.up n) (ULift.up (n + 1)) (H n σ) = ⊤ :=
        IdealSheaf.eq_top_of_not_nonempty_support hne
      exact key _ _ hm1 hm2 (htoptop.trans (rtop.trans htop.symm))
  · have hm1 : memberOfLabel H' lab (ULift.up n) l = ⊤ := memberOfLabel_of_not_exists hn
    by_cases hn1 : ∃ τ : Λ (n + 1), lab (ULift.up (n + 1)) τ = l
    · obtain ⟨τ, hτ⟩ := hn1
      have hm2 : memberOfLabel H' lab (ULift.up (n + 1)) l = H (n + 1) τ := by
        rw [← hτ]; exact memberOfLabel_lab hlab (ULift.up (n + 1)) τ
      have hne : ¬ (restrictGlue π dom (ULift.up (n + 1)) (ULift.up n)
          (H (n + 1) τ)).support.Nonempty := by
        intro hne
        obtain ⟨σ, hστ⟩ := hsurj n τ hne
        exact hn ⟨σ.1, ((chainColimitIndex.mk_eq_mk_succ_iff hf n σ.1 τ).mpr
          ⟨σ.2, hστ⟩).trans hτ⟩
      have htop : restrictGlue π dom (ULift.up (n + 1)) (ULift.up n) (H (n + 1) τ) = ⊤ :=
        IdealSheaf.eq_top_of_not_nonempty_support hne
      exact key _ _ hm1 hm2 ((congrArg (QuotientSpace.comap (G.t (ULift.up n) (ULift.up (n + 1))).1)
        htop).trans ((QuotientSpace.comap_top _).trans rtop.symm))
    · have hm2 : memberOfLabel H' lab (ULift.up (n + 1)) l = ⊤ :=
        memberOfLabel_of_not_exists hn1
      exact key _ _ hm1 hm2 htoptop

/-- **The glued chain family** on the glued space, indexed by the colimit of the levels' members
(`glueFamily` on the labelled data; [Kol07, Theorem 45, (3)]; [Wlo09, §4.3]). -/
noncomputable def chainGlueFamily : ChainIndex π dom H e → ClosedSubspace G.gluedOver :=
  G.glueFamily _ _ (chainLabelledCompat G hmono H hH e hpair hsurj)

/-- The glued member of the class of `⟨n, σ⟩` pulls back to level `n` as `H n σ`. -/
theorem comap_ιGlued_chainGlueFamily_mk (n : ℕ) (σ : Λ n) :
    QuotientSpace.comap (G.ιGlued (ULift.up n)).1
        (chainGlueFamily G hmono H hH e hpair hsurj (Quot.mk _ ⟨n, σ⟩)) = H n σ :=
  G.comap_ιGlued_glueFamily_lab (injective_chainLabel G H hH e hpair)
    (chainLabelledCompat G hmono H hH e hpair hsurj) (ULift.up n) σ

/-- The glued chain family is a simple-normal-crossings family (`isSncFamily_glueFamily`). -/
theorem isSncFamily_chainGlueFamily :
    ClosedSubspace.IsSncFamily (chainGlueFamily G hmono H hH e hpair hsurj) :=
  G.isSncFamily_glueFamily (injective_chainLabel G H hH e hpair)
    (chainLabelledCompat G hmono H hH e hpair hsurj) (fun i => hH i.down)

/-- The glued chain family is locally finite (`locallyFinite_glueFamily`: each level's family is
locally finite). -/
theorem locallyFinite_chainGlueFamily :
    LocallyFinite fun l => (chainGlueFamily G hmono H hH e hpair hsurj l).support :=
  G.locallyFinite_glueFamily (injective_chainLabel G H hH e hpair)
    (chainLabelledCompat G hmono H hH e hpair hsurj) (fun i => (hH i.down).1)

/-- The support of the glued chain family is the preimage of `S` under the descended map when every
level's family has support the preimage of `S` under its map (`toFun_descMap_ιGlued`,
`exists_ιGlued_eq`). -/
theorem iUnion_support_chainGlueFamily (S : Set X)
    (hS : ∀ n, ⋃ σ, (H n σ).support = AnalyticSpace.Hom.toFun (π (ULift.up n)) ⁻¹' S) :
    ⋃ l, (chainGlueFamily G hmono H hH e hpair hsurj l).support =
      AnalyticSpace.Hom.toFun G.descMap ⁻¹' S := by
  have h2 : ⋃ i, KLocallyRingedSpace.Hom.toFun (G.ιGlued i) '' ⋃ k, ((fun (i : ULift.{u} ℕ)
      (σ : Λ i.down) =>
      H i.down σ) i k).support = AnalyticSpace.Hom.toFun G.descMap ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, y, hy, rfl⟩
      have hy' : y ∈ AnalyticSpace.Hom.toFun (π i) ⁻¹' S := by
        rw [← hS i.down]; exact hy
      change KLocallyRingedSpace.Hom.toFun G.descMap (KLocallyRingedSpace.Hom.toFun
          (G.ιGlued i) y) ∈ S
      rw [G.toFun_descMap_ιGlued]
      exact hy'
    · intro hz
      obtain ⟨i, y, rfl⟩ := G.exists_ιGlued_eq z
      refine Set.mem_iUnion.mpr ⟨i, y, ?_, rfl⟩
      rw [hS i.down]
      change KLocallyRingedSpace.Hom.toFun (π i) y ∈ S
      rw [← G.toFun_descMap_ιGlued]
      exact hz
  exact (G.iUnion_support_glueFamily (injective_chainLabel G H hH e hpair)
    (chainLabelledCompat G hmono H hH e hpair hsurj)).trans h2

end Labelled

end Chain

end AnalyticSpace.GlueOver

end
