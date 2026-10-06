/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Resolution.Defs
import Hironaka.AnalyticSpace.IsoOverCover
import Hironaka.AnalyticSpace.Lemmas
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionRestrict
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceRestrict
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Ambient blow-up factorizations: restriction to a smaller open, transport along an isomorphism

Two functorialities of the structure `f.AmbientBlowUpFactorization U` (clause (4) of the resolution
theorem, [Kol07, Theorem 45 (4)] read through [Kol07, Warning 23]; the factorization (∗) of
[Wlo09, Theorem 2.0.2]), used when
the factorization of the glued resolution morphism over an exhaustion open `Uₙ` is transported to
the resolution morphism itself over a relatively compact `U ⊆ Uₙ`
(`Hironaka/Resolution/Analytic/Kol07Thm45/AmbientFactorization.lean`,
`Hironaka/Resolution/Analytic/Kol07Thm45/IsoOverLemmas.lean`):

* `AmbientBlowUpFactorization.ofSubset`: a factorization over `U` is one over any `U' ⊆ U` — the
  same data, the covering clause weakened;
* `AmbientBlowUpFactorization.ofIsoOver`: a factorization of `f' : Y' → X` over `U` transports
  along an isomorphism `e : Y|f⁻¹O ≅ Y'|f'⁻¹O` over `X|O` to a factorization of `f : Y → X` over
  `U`, when the pieces lie inside `O` (the lift over a piece is an isomorphism over the whole
  piece, and `e` identifies `f` with `f'` over `O` only) — every field of the ambient side is
  kept, and the lift over a piece is composed with the restriction of `e` over the piece;
* the restriction of an isomorphism over `O` to an isomorphism over an open `P ⊆ O`
  (`exists_restrictSet_isIso_of_restrictSet_isIso_of_subset`, in the vocabulary's form
  `Hom.exists_restrictSet_isIso_of_isIso_restrictSet_of_subset`): two applications of
  `exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion`
  (`Hironaka/Resolution/Analytic/Kol07Thm45/LocalResolutionRestrict.lean`) at `N := P` — to the
  open immersion `Y|f⁻¹O ⟶ Y'` through `e` and to the open immersion `Y|f⁻¹O ⟶ Y`, both over
  `X` — composed.

Bookkeeping; not in the sources.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Set AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace

open Hironaka

variable {K : Type} [RCLike K]

/-- An ambient blow-up factorization of `f` over `U` is one over any `U' ⊆ U`: the same pieces,
ambient, blow-up sequence, strict transforms and lifts; only the covering clause `U' ⊆ ⋃ Uᵢ`
changes. -/
def AmbientBlowUpFactorization.ofSubset {X Y : AnalyticSpace.{u} K}
    {f : Y ⟶ X} {U U' : Set X} (h : U' ⊆ U)
    (F : f.AmbientBlowUpFactorization U) :
    f.AmbientBlowUpFactorization U' :=
  { F with subset_iUnion_piece := h.trans F.subset_iUnion_piece }

/-- An isomorphism `e : Y|f⁻¹O ≅ Y'|f'⁻¹O` over `X` restricts to an isomorphism over every open
`P ⊆ O`: `exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion`
(`Hironaka/Resolution/Analytic/Kol07Thm45/LocalResolutionRestrict.lean`) applied to the open
immersion `Y|f⁻¹O ⟶ Y'` through `e` and to the open immersion `Y|f⁻¹O ⟶ Y`, both over `X`, at
`N := P`; the two restricted isomorphisms have the same source, and the composite of the inverse
of the second with the first is the restriction of `e`. -/
theorem exists_restrictSet_isIso_of_restrictSet_isIso_of_subset {X Y Y' : AnalyticSpace.{u} K}
    (f : Y ⟶ X) (f' : Y' ⟶ X) {O P : Set X}
    (e : Y.restrictSet (KLocallyRingedSpace.Hom.toFun f ⁻¹' O) ⟶
      Y'.restrictSet (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O)) (he : IsIso e)
    (hcomm : e ≫ Hom.restrictSet f' O = Hom.restrictSet f O) (hP : IsOpen P) (hPO : P ⊆ O) :
    ∃ e' : Y.toKLocallyRingedSpace.restrictOpen
          (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' P)) ⟶
        Y'.toKLocallyRingedSpace.restrictOpen (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' P)),
      IsIso e' ∧ e' ≫ Hom.restrictSet f' P = Hom.restrictSet f P := by
  have hK : @IsIso (KLocallyRingedSpace.{u} K) _
      (Y.toKLocallyRingedSpace.restrictOpen (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)))
      (Y'.toKLocallyRingedSpace.restrictOpen (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O)))
      e := isIso_toKLocallyRingedSpace_of_isIso e
  have hval : @IsIso LocallyRingedSpace.{u} _
      (Y.toKLocallyRingedSpace.restrictOpen
        (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))).toLocallyRingedSpace
      (Y'.toKLocallyRingedSpace.restrictOpen
        (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))).toLocallyRingedSpace e.1 :=
    (isIso_iff_isIso_val
      (X := Y.toKLocallyRingedSpace.restrictOpen (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)))
      (Y := Y'.toKLocallyRingedSpace.restrictOpen
        (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))) e).mp hK
  -- the open immersion `Y|f⁻¹O ⟶ Y'` through `e`, and the projection of `Y|f⁻¹O` to `X` (both
  -- spelled on the `ℜ/K` objects `restrictOpen (openOf …)`, so that the instances are found)
  set χ : Y.toKLocallyRingedSpace.restrictOpen (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ⟶
      Y'.toKLocallyRingedSpace :=
    (e : Y.toKLocallyRingedSpace.restrictOpen (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ⟶
        Y'.toKLocallyRingedSpace.restrictOpen
          (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))) ≫
      ofRestrict Y'.toKLocallyRingedSpace (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))
    with hχdef
  set pA : Y.toKLocallyRingedSpace.restrictOpen (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ⟶
      X.toKLocallyRingedSpace :=
    ofRestrict Y.toKLocallyRingedSpace (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ≫ f
    with hpAdef
  have hχoi : LocallyRingedSpace.IsOpenImmersion χ.1 :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (e : Y.toKLocallyRingedSpace.restrictOpen
            (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) ⟶
          Y'.toKLocallyRingedSpace.restrictOpen
            (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))).1
      (@LocallyRingedSpace.IsOpenImmersion.of_isIso _ _ _ hval)
      (ofRestrict Y'.toKLocallyRingedSpace (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))).1
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (ofRestrict Y'.toKLocallyRingedSpace
        (openOf Y' (KLocallyRingedSpace.Hom.toFun f' ⁻¹' O))).1)
  -- the open immersion through `e` lies over `X`
  have hχ : χ ≫ f' = pA := by
    rw [hχdef, hpAdef]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => e ≫ g) (Hom.restrictSet_comp_ofRestrict f' O).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun g => g ≫ ofRestrict X.toKLocallyRingedSpace (openOf X O)) hcomm).trans
            (Hom.restrictSet_comp_ofRestrict f O))))
  -- `e` is surjective on points
  have hsurj : Function.Surjective (KLocallyRingedSpace.Hom.toFun e) := fun y =>
    ⟨KLocallyRingedSpace.Hom.toFun (@inv (AnalyticSpace.{u} K) _ _ _ e he) y,
      congrArg (fun φ => KLocallyRingedSpace.Hom.toFun φ y)
        (@IsIso.inv_hom_id (AnalyticSpace.{u} K) _ _ _ e he)⟩
  have hrange₁ : KLocallyRingedSpace.Hom.toFun f' ⁻¹' P ⊆
      Set.range (KLocallyRingedSpace.Hom.toFun χ) := by
    intro y hy
    obtain ⟨a, ha⟩ := hsurj ⟨y, mem_openOf_of_subset (Set.preimage_mono hPO) hy⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨ψ₁, hψ₁, hψ₁c⟩ :=
    KLocallyRingedSpace.exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion
    (A := Y.restrictSet (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)) χ (hχ := hχoi) pA f' hχ P hP
    hrange₁
  have hrange₂ : KLocallyRingedSpace.Hom.toFun f ⁻¹' P ⊆ Set.range (KLocallyRingedSpace.Hom.toFun
      (ofRestrict Y.toKLocallyRingedSpace (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)))) :=
    fun y hy => ⟨⟨y, mem_openOf_of_subset (Set.preimage_mono hPO) hy⟩, rfl⟩
  obtain ⟨ψ₂, hψ₂, hψ₂c⟩ :=
    KLocallyRingedSpace.exists_restrictSet_isIso_of_comp_eq_of_isOpenImmersion
    (A := Y.restrictSet (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))
    (ofRestrict Y.toKLocallyRingedSpace (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O)))
    (hχ := (inferInstance : LocallyRingedSpace.IsOpenImmersion
      (ofRestrict Y.toKLocallyRingedSpace (openOf Y (KLocallyRingedSpace.Hom.toFun f ⁻¹' O))).1))
    pA f hpAdef.symm P hP hrange₂
  have := hψ₁
  have := hψ₂
  refine ⟨inv ψ₂ ≫ ψ₁, inferInstance, ?_⟩
  exact (Category.assoc _ _ _).trans ((congrArg (fun g => inv ψ₂ ≫ g) hψ₁c).trans
    ((congrArg (fun g => inv ψ₂ ≫ g) hψ₂c.symm).trans (IsIso.inv_hom_id_assoc ψ₂ _)))

/-- `exists_restrictSet_isIso_of_restrictSet_isIso_of_subset` for morphisms of `An/K`
(`restrictSet`, `Hom.restrictSet`, `≫`): an isomorphism
`e : Y|f⁻¹O ≅ Y'|f'⁻¹O` over `X|O` restricts to an isomorphism over every open `P ⊆ O`. -/
theorem Hom.exists_restrictSet_isIso_of_isIso_restrictSet_of_subset
    {X Y Y' : AnalyticSpace.{u} K}
        {f : Y ⟶ X}
    {f' : Y' ⟶ X} {O P : Set X}
    (e : Y.restrictSet (f ⁻¹' O) ⟶ Y'.restrictSet (f' ⁻¹' O))
    (he : IsIso e) (hcomm : e ≫ f'.restrictSet O = f.restrictSet O) (hP : IsOpen P) (hPO : P ⊆ O) :
    ∃ e' : Y.restrictSet (f ⁻¹' P) ⟶ Y'.restrictSet (f' ⁻¹' P),
      IsIso e' ∧ e' ≫ f'.restrictSet P = f.restrictSet P := by
  obtain ⟨e', h1, h2⟩ :=
    exists_restrictSet_isIso_of_restrictSet_isIso_of_subset (X := X) (Y := Y) (Y' := Y') f f'
      (O := O) (P := P) e he hcomm hP hPO
  exact ⟨e', isIso_of_isIso_toKLocallyRingedSpace _ h1, h2⟩

/-- An ambient blow-up factorization of `f' : Y' → X` over `U` transports along an isomorphism
`e : Y|f⁻¹O ≅ Y'|f'⁻¹O` over `X|O`, `O ⊇ U` open, to one of `f : Y → X` over `U`, when every piece
lies inside `O`: the pieces, the ambient `⊔ Gᵢ`, the ideal, the blow-up sequence, the strict
transforms and `Π_r|_{Y_r}` are those of the given factorization; the lift over the piece `Uᵢ` is
the given lift composed with the restriction of `e` over `Uᵢ`
(`Hom.exists_restrictSet_isIso_of_isIso_restrictSet_of_subset`), an isomorphism, compatible with `f`
by the compatibility of `e` with `f`, `f'` over `Uᵢ`. -/
def AmbientBlowUpFactorization.ofIsoOver {X Y Y' : AnalyticSpace.{u} K}
    {f : Y ⟶ X}
        {f' : Y' ⟶ X}
    {U O : Set X} (_hO : IsOpen O) (_hUO : U ⊆ O)
    (e : Y.restrictSet (f ⁻¹' O) ⟶ Y'.restrictSet (f' ⁻¹' O))
    (he : IsIso e) (hcomm : e ≫ f'.restrictSet O = f.restrictSet O)
    (F : f'.AmbientBlowUpFactorization U)
    (hpieces : ∀ i, F.piece i ⊆ O) :
    f.AmbientBlowUpFactorization U :=
  let h : ∀ i, ∃ e' : Y.restrictSet (f ⁻¹' F.piece i) ⟶ Y'.restrictSet (f' ⁻¹' F.piece i),
      IsIso e' ∧ e' ≫ f'.restrictSet (F.piece i) = f.restrictSet (F.piece i) :=
    fun i => Hom.exists_restrictSet_isIso_of_isIso_restrictSet_of_subset e he hcomm
      (F.isOpen_piece i) (hpieces i)
  { F with
    lift := fun i => Classical.choose (h i) ≫ F.lift i
    lift_isIso := fun i => by
      have := F.finite
      have h1 : IsIso (Classical.choose (h i)) := (Classical.choose_spec (h i)).1
      have h2 : IsIso (F.lift i) := F.lift_isIso i
      exact (IsIso.comp_isIso : IsIso (Classical.choose (h i) ≫ F.lift i))
    map_lift := fun i => by
      have := F.finite
      have hc : Classical.choose (h i) ≫ Hom.restrictSet f' (F.piece i) =
          Hom.restrictSet f (F.piece i) := (Classical.choose_spec (h i)).2
      have hml : F.lift i ≫ Hom.restrictSet F.map (F.ideal.overPiece i) =
          Hom.restrictSet f' (F.piece i) ≫ F.emb i := F.map_lift i
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun g => Classical.choose (h i) ≫ g) hml).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ F.emb i) hc))) }

section

variable {X Y Y' : AnalyticSpace.{u} K}
  {f : Y ⟶ X}
  {f' : Y' ⟶ X} {U U' O : Set X} (h : U' ⊆ U) (hO : IsOpen O)
  (hUO : U ⊆ O)
      (e : Y.restrictSet (f ⁻¹' O) ⟶ Y'.restrictSet (f' ⁻¹' O))
  (he : IsIso e) (hcomm : e ≫ f'.restrictSet O = f.restrictSet O)
  (F : f.AmbientBlowUpFactorization U) (hpieces : ∀ i, F.piece i ⊆ O)
  (F' : f'.AmbientBlowUpFactorization U) (hpieces' : ∀ i, F'.piece i ⊆ O)

/-- The pieces of `ofSubset` are those of the given factorization. -/
theorem AmbientBlowUpFactorization.ofSubset_piece :
    (AmbientBlowUpFactorization.ofSubset h F).piece = F.piece := rfl

/-- The blow-up sequence of `ofSubset` is that of the given factorization. -/
theorem AmbientBlowUpFactorization.ofSubset_seq :
    (AmbientBlowUpFactorization.ofSubset h F).seq = F.seq := rfl

/-- The pieces of `ofIsoOver` are those of the given factorization. -/
theorem AmbientBlowUpFactorization.ofIsoOver_piece :
    (AmbientBlowUpFactorization.ofIsoOver hO hUO e he hcomm F' hpieces').piece =
      F'.piece := rfl

/-- The ambient opens of `ofIsoOver` are those of the given factorization. -/
theorem AmbientBlowUpFactorization.ofIsoOver_G :
    (AmbientBlowUpFactorization.ofIsoOver hO hUO e he hcomm F' hpieces').G = F'.G := rfl

/-- The blow-up sequence of `ofIsoOver` is that of the given factorization. -/
theorem AmbientBlowUpFactorization.ofIsoOver_seq :
    (AmbientBlowUpFactorization.ofIsoOver hO hUO e he hcomm F' hpieces').seq = F'.seq := rfl

/-- The morphism `Π_r|_{Y_r}` of `ofIsoOver` is that of the given factorization. -/
theorem AmbientBlowUpFactorization.ofIsoOver_map :
    (AmbientBlowUpFactorization.ofIsoOver hO hUO e he hcomm F' hpieces').map = F'.map := rfl

end

end AnalyticSpace

end
