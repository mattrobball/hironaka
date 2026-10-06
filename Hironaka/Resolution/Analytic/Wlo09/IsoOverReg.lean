/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceResolution
public import Hironaka.Resolution.Analytic.Principalization.IsoOff
public import Hironaka.Manifold.FiniteSuccession.Restrict.CenterComponents
import Hironaka.AnalyticSpace.IsoOverOpen
import Hironaka.AnalyticSpace.Manifold.Comap
import Hironaka.AnalyticSpace.RegPoints
import Hironaka.AnalyticSpace.SigmaLemmas
import Hironaka.Manifold.BlowUp.Transform.Reduced.ModelComplex
import Hironaka.Manifold.BlowUp.Transform.SaturationFiniteType
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceBasic
import Hironaka.Manifold.BlowUp.Transform.StrictSubspaceClosure
import Hironaka.Manifold.FiniteSuccession.Restrict.RegSetBasic
import Hironaka.Resolution.Analytic.OrderReduction.BDCor85
import Hironaka.Resolution.Analytic.Wlo09.Clauses
import Hironaka.Resolution.Analytic.Wlo09.Components
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The local resolution map is an isomorphism over the simple locus

For an embedded desingularization functor `bed` (`bed.IsEmbeddedDesing`) and a piece of an
analytic space (a closed subspace `Y|_W` of a relatively compact open `W` of an ambient manifold),
the local resolution map `P = σ^r|_{Ỹ} : Ỹ → Y|_W`, the restriction of the composite blow-down to
the final strict transform, is an isomorphism over the simple locus `(Y|_W).regularLocus`
(`Hom.IsIsoOver`). This is clause (1) of Włodarczyk's resolution of analytic spaces [Wlo09, Theorem
2.0.1], "`res_Y : Ỹ → Y` is an isomorphism over the nonsingular part of `Y`", deduced from clauses
(2)–(3) of [Wlo09, Theorem 2.0.2] as in the proof of resolution from principalization in
[Kol07, Theorem 27]; the algebraic counterpart is `isIso_composite_restrict_of_centers_disjoint`.

**Proof.** Clause (2) of the embedded desingularization says that no centre lies over a simple
point: `CentersOver (regSet)ᶜ` (`IsEmbeddedDesing.centersOver_compl_regSet`). Along the sequence
this gives, by induction on the stage: the exceptional divisors lie over `(regSet)ᶜ`
(`support_totalTransformSeq_subset_preimage_of_centersOver`); off the exceptional family the germ
map of the composite `σ^i` is bijective (`germMap_stageMap_bijective_of_notMem_support`, from the
one-step statement `IsBlowUp.germMap_bijective_of_notMem`) and the strict transform is the
pullback stalkwise (`stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support`, from
`stalkIdeal_strictTransformSubspace_of_notMem_cosupport_of_hasLocalGenerators`, the finite-type
input discharged by `saturationStalk_hasLocalGenerators`); hence the whole preimage of `regSet`
lies in `Ỹ` (`preimage_subset_cosupport_strictTransformSubspaceSeq_of_centersOver`). The composite
`σ^r` is an analytic isomorphism over `regSet` (`isAnalyticIsoOver_stageMap`; cf.
[Kol07, Theorem 35 (3)]), so `P` is bijective from `P⁻¹(Reg)` onto `Reg`; its stalk maps there are
isomorphisms (`isIso_map_stalkMap_of_bijective` with `fiberMap_bijective_of_stalkIdeal_eq_map`);
the criterion `isIso_restrictTo_of_bijOn_of_bijective_stalkMap` makes the restriction an
isomorphism of analytic spaces, which is the predicate `IsIsoOver` through
`Hom.restrictSet_eq_restrictTo`.

This is one of the clauses from which the resolution of analytic spaces is assembled in
`Hironaka/Manifold/Sequence/Restrict/`.
-/

public section

noncomputable section

open CategoryTheory Set Topology TopologicalSpace AnalyticManifold Hironaka.Manifold Manifold
  AnalyticSpace
open scoped Manifold ContDiff

universe u

namespace AnalyticManifold.FiniteSuccession

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {M : AnalyticManifold.{u} 𝕜 E} (S : FiniteSuccession M)

/-- Off the exceptional family the germ map of the composite `σ^i : U_i → M` is bijective: the
composite of the germ maps of the blow-ups, each bijective off its exceptional divisor
(`IsBlowUp.germMap_bijective_of_notMem`). -/
theorem germMap_stageMap_bijective_of_notMem_support (i : Fin (S.length + 1)) {z : S.stage i}
    (hz : z ∉ (S.totalTransformSeq i).support) :
    Function.Bijective (germMap (S.stageMap i) (S.stageMap i).contMDiff z) := by
  induction i using Fin.induction with
  | zero =>
    obtain ⟨z', rfl⟩ : ∃ z' : (M : Type u), z' = z := ⟨z, rfl⟩
    change Function.Bijective (germMap (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id z')
    exact Function.bijective_iff_has_inverse.mpr
      ⟨id, fun a => germMap_id z' a, fun b => germMap_id z' b⟩
  | succ i ih =>
    obtain ⟨hzD, hzE⟩ := notMem_exceptionalAt_and_map_notMem_of_notMem_support S i
      (S.isClosed_hyp_totalTransformSeqFrom (F := HypersurfaceFamily.empty M) (fun j => j.elim)
        i.castSucc) hz
    have h1 : Function.Bijective (germMap (S.map i) (S.map i).contMDiff z) :=
      (S.isBlowUp_map i).germMap_bijective_of_notMem hzD
    have h : germMap (S.stageMap i.succ) (S.stageMap i.succ).contMDiff z =
        (germMap (S.map i) (S.map i).contMDiff z).comp
          (germMap (S.stageMap i.castSucc) (S.stageMap i.castSucc).contMDiff (S.map i z)) :=
      RingHom.ext fun s =>
        (germMap_germMap (S.stageMap i.castSucc).contMDiff (S.map i).contMDiff z s).symm
    rw [h]
    exact h1.comp (ih hzE)

/-- Off the exceptional family the strict transform is the pullback, stalkwise: the stalk of `Y_i`
at `z` is the image of the stalk of `J` at `σ^i z` under the germ map
(`stalkIdeal_strictTransformSubspace_of_notMem_cosupport_of_hasLocalGenerators` iterated, the
finite-type input by `saturationStalk_hasLocalGenerators`). -/
theorem stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support (J : IdealSheaf M)
    (i : Fin (S.length + 1)) {z : S.stage i} (hz : z ∉ (S.totalTransformSeq i).support) :
    (S.strictTransformSubspaceSeq J i).stalkIdeal z =
      (J.stalkIdeal (S.stageMap i z)).map (germMap (S.stageMap i) (S.stageMap i).contMDiff z) := by
  induction i using Fin.induction with
  | zero =>
    obtain ⟨z', rfl⟩ : ∃ z' : (M : Type u), z' = z := ⟨z, rfl⟩
    change J.stalkIdeal z' =
      (J.stalkIdeal z').map (germMap (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id z')
    have hf : germMap (𝕜 := 𝕜) (E' := E) (id : M → M) contMDiff_id z' = RingHom.id _ :=
      RingHom.ext fun s => germMap_id z' s
    rw [hf]
    exact (Ideal.map_id _).symm
  | succ i ih =>
    obtain ⟨hzD, hzE⟩ := notMem_exceptionalAt_and_map_notMem_of_notMem_support S i
      (S.isClosed_hyp_totalTransformSeqFrom (F := HypersurfaceFamily.empty M) (fun j => j.elim)
        i.castSucc) hz
    have hY := S.isClosedSubmanifold_center i
    have hb := S.isBlowUp_map i
    have hzD' : z ∉ (hY.idealSheaf.pullback _ hb.contMDiff).support := by
      rw [IsBlowUp.cosupport_exceptionalIdealSheaf hY hb]
      exact hzD
    rw [FiniteSuccession.strictTransformSubspaceSeq_succ,
      stalkIdeal_strictTransformSubspace_of_notMem_cosupport_of_hasLocalGenerators hY hb _
        (saturationStalk_hasLocalGenerators hY hb _) hzD', ih hzE, Ideal.map_map]
    congr 1
    exact RingHom.ext fun s =>
      germMap_germMap (S.stageMap i.castSucc).contMDiff (S.map i).contMDiff z s

/-- When every centre lies over `Z`, so does every exceptional divisor: a point of the new divisor
maps into the centre, the rest is the induction hypothesis. -/
theorem support_totalTransformSeq_subset_preimage_of_centersOver {Z : Set M}
    (hZ : S.CentersOver Z) (i : Fin (S.length + 1)) :
    (S.totalTransformSeq i).support ⊆ S.stageMap i ⁻¹' Z := by
  induction i using Fin.induction with
  | zero =>
    intro z hz
    rw [FiniteSuccession.totalTransformSeq_zero] at hz
    exact (Set.mem_iUnion.mp hz).elim fun j _ => PEmpty.elim j
  | succ i ih =>
    rw [support_totalTransformSeq_succ S i
      (S.isClosed_hyp_totalTransformSeqFrom (F := HypersurfaceFamily.empty M) (fun j => j.elim)
        i.castSucc)]
    rintro z (hz | hz)
    · exact ih hz
    · exact hZ i hz

/-- Over a subset `Z` of the support of `J` missed by every centre, the strict transform contains
the whole preimage of `Z`: off the exceptional family its stalk is the image of the stalk of `J`
under a bijection, hence proper where the stalk of `J` is. -/
theorem preimage_subset_cosupport_strictTransformSubspaceSeq_of_centersOver (J : IdealSheaf M)
    {Z : Set M} (hZ : S.CentersOver Zᶜ) (hZJ : Z ⊆ J.support) (i : Fin (S.length + 1)) :
    S.stageMap i ⁻¹' Z ⊆ (S.strictTransformSubspaceSeq J i).support := by
  intro z hz
  have hzE : z ∉ (S.totalTransformSeq i).support := fun h =>
    support_totalTransformSeq_subset_preimage_of_centersOver S hZ i h hz
  change (S.strictTransformSubspaceSeq J i).stalkIdeal z ≠ ⊤
  rw [stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support S J i hzE, Ne,
    Ideal.map_eq_top_iff_of_bijective _ (germMap_stageMap_bijective_of_notMem_support S i hzE)]
  exact hZJ hz

end AnalyticManifold.FiniteSuccession

namespace Hironaka.Manifold

open _root_.Manifold

/-- Clause (2) of `IsEmbeddedDesing` (clause (2) of [Wlo09, Theorem 2.0.2]) as `CentersOver`: every
centre of every value lies over the complement of the simple locus
`regSet (T|U).I = ι '' regularLocus`. -/
theorem BEDanFamStar.IsEmbeddedDesing.centersOver_compl_regSet {𝕜 : Type} [RCLike 𝕜]
    {bed : BEDanFamStar.{u} 𝕜} (hbed : bed.IsEmbeddedDesing) (n : ℕ)
    {M : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (U : Opens M) (hU : IsCompact (closure (U : Set M))) :
    (((bed.fam n).fam T hT).seqOn U hU).toSuccession.CentersOver
      (IdealSheaf.regSet
        (T.pullback (M.inclusion U) (isLocalDiffeomorph_inclusion M U)).I)ᶜ :=
  fun i x hx => (hbed.1 n T hT U hU).2.2.1 i x hx

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {X : AnalyticSpace.{u} 𝕜} {V : Set X}
  (E : PieceEmbedding 𝕜 n X V)

/-- The local resolution map `P = σ^r|_{Ỹ} : Ỹ → Y|_W` of the piece is an isomorphism over the
simple locus `(Y|_W).regularLocus` (clause (1) of [Wlo09, Theorem 2.0.1] for the piece, from clauses
(2)–(3) of [Wlo09, Theorem 2.0.2] as in the proof of [Kol07, Theorem 27]): over a simple point no
centre lies
(clause (2) of the embedded desingularization), so `σ^r` is an analytic isomorphism there, `Ỹ` is
the pullback of `Y` there, and the induced morphism of closed subspaces is bijective with bijective
stalk maps. -/
theorem PieceEmbedding.localResolutionMap_isIsoOver_reg (bed : BEDanFamStar.{u} 𝕜)
    (W : Opens (pieceAmbient 𝕜 E.G)) (hW : IsCompact (closure (W : Set (pieceAmbient 𝕜 E.G))))
    (hbed : bed.IsEmbeddedDesing) :
    (E.localResolutionMap bed W hW).IsIsoOver
      (regularLocus ((E.restrictedIdeal W).toAnalyticSpace)) := by
  set S := (E.localResolutionSeq bed W hW).toSuccession with hS
  set J := E.restrictedIdeal W with hJ
  set Yt : AnalyticSpace.{u} 𝕜 := E.localResolution bed W hW with hYt
  set Y : AnalyticSpace.{u} 𝕜 := J.toAnalyticSpace with hY
  set P : Yt ⟶ Y := E.localResolutionMap bed W hW with hP
  -- clause (2): the centres lie over the complement of the simple locus; `σ^r` is an isomorphism
  -- off them
  have hZ : S.CentersOver (IdealSheaf.regSet J)ᶜ :=
    hbed.centersOver_compl_regSet n E.ambientTriple E.domBEDan_ambientTriple W hW
  have hiso := FiniteSuccession.isAnalyticIsoOver_stageMap hZ (Fin.last _)
  rw [compl_compl] at hiso
  -- a point of `Ỹ` over the simple locus lies over `regSet` and off the exceptional family
  have hreg : ∀ y : Yt,
      KLocallyRingedSpace.Hom.toFun P y ∈ regularLocus Y →
        S.stageMap (Fin.last _) y.1 ∈ IdealSheaf.regSet J :=
    fun y hy => ⟨KLocallyRingedSpace.Hom.toFun P y, hy, rfl⟩
  have hoffE : ∀ y : Yt,
      KLocallyRingedSpace.Hom.toFun P y ∈ regularLocus Y →
        y.1 ∉ (S.totalTransformSeq (Fin.last _)).support :=
    fun y hy h => S.support_totalTransformSeq_subset_preimage_of_centersOver hZ (Fin.last _) h
      (hreg y hy)
  -- the predicate `IsIsoOver`, as an isomorphism of the restriction
  change IsIso (Hom.restrictSet P
    (regularLocus Y))
  rw [Hom.restrictSet_eq_restrictTo]
  refine isIso_of_isIso_toKLocallyRingedSpace _ ?_
  have hRopen : IsOpen (regularLocus Y) :=
    isOpen_reg Y
  have hPopen :
      IsOpen (KLocallyRingedSpace.Hom.toFun P ⁻¹' regularLocus Y) :=
    hRopen.preimage (KLocallyRingedSpace.Hom.continuous_toFun P)
  apply isIso_restrictTo_of_bijOn_of_bijective_stalkMap
  · -- the points: `P` is bijective from `P⁻¹(Reg)` onto `Reg`
    rw [openOf_of_isOpen _ hPopen,
      openOf_of_isOpen _ hRopen]
    refine ⟨fun y hy => hy, ?_, ?_⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      apply Subtype.ext
      apply hiso.2.injOn (hreg y₁ hy₁) (hreg y₂ hy₂)
      exact congrArg (fun v : Y => (v.1 : (pieceAmbient 𝕜 E.G).restrict W)) heq
    · intro v hv
      obtain ⟨z, hz, hzv⟩ := hiso.2.surjOn ⟨v, hv, rfl⟩
      have hzY : z ∈ (S.strictTransformSubspaceSeq J (Fin.last _)).support :=
        S.preimage_subset_cosupport_strictTransformSubspaceSeq_of_centersOver J hZ
          (regSet_subset_cosupport J) (Fin.last _) hz
      have hPz : KLocallyRingedSpace.Hom.toFun P ⟨z, hzY⟩ = v := Subtype.ext hzv
      refine ⟨⟨z, hzY⟩, ?_, hPz⟩
      change KLocallyRingedSpace.Hom.toFun P ⟨z, hzY⟩ ∈ regularLocus Y
      rw [hPz]
      exact hv
  · -- the stalks: `P` is the quotient map of `Sp(σ^r)`, whose stalk maps are bijective off `E_r`
    intro y hy
    rw [openOf_of_isOpen _ hPopen] at hy
    set z : (S.stage (Fin.last _) : Type u) := y.1
    have hyE : z ∉ (S.totalTransformSeq (Fin.last _)).support := hoffE y hy
    have hfun : ∀ s, ((toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        S.composite).1.stalkMap z).hom s =
          germMap (S.stageMap (Fin.last _)) (S.stageMap (Fin.last _)).contMDiff z s :=
      fun s => KLocallyRingedSpace.stalkMap_ofManifoldHom_eq_germMap _ _ _ s
    have hb : Function.Bijective ((toSpaceHom
        (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) S.composite).1.stalkMap z).hom := by
      rw [show (((toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          S.composite).1.stalkMap z).hom : _ → _) = germMap (S.stageMap (Fin.last _))
          (S.stageMap (Fin.last _)).contMDiff z from funext hfun]
      exact S.germMap_stageMap_bijective_of_notMem_support (Fin.last _) hyE
    have heq : (S.strictTransformSubspaceSeq J (Fin.last _)).stalkIdeal z =
        (J.stalkIdeal (S.stageMap (Fin.last _) z)).map
          ((toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
            S.composite).1.stalkMap z).hom := by
      rw [show ((toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          S.composite).1.stalkMap z).hom = germMap (S.stageMap (Fin.last _))
          (S.stageMap (Fin.last _)).contMDiff z from RingHom.ext hfun]
      exact S.stalkIdeal_strictTransformSubspaceSeq_eq_map_of_notMem_support J (Fin.last _) hyE
    exact (ConcreteCategory.isIso_iff_bijective _).mp
      (QuotientSpace.isIso_map_stalkMap_of_bijective _ _ _ _ y
        (QuotientSpace.fiberMap_bijective_of_stalkIdeal_eq_map _ _ _ _ y hb heq))

end Hironaka.Manifold

end
