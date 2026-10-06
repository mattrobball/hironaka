/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Restrict.DiffeomorphTransport
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceIndependence
import Hironaka.AnalyticSpace.ClosedSubspaceLemmas
import Hironaka.AnalyticSpace.LocalIso
import Hironaka.Manifold.FiniteSuccession.Restrict.StrictSubspaceSeqCompat
import Hironaka.Resolution.Analytic.Kol07Thm45.ClosedSubspaceHom
import Hironaka.Resolution.Analytic.ModelTransport.IdealSheaf
import Hironaka.Resolution.Analytic.OrderReduction.FamilyChain
import Hironaka.Resolution.Analytic.Restrict.StrictSubspaceSeqTransport
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The transport of the functor's data along an analytic isomorphism

The functoriality of the blow-up sequence under local isomorphisms [Kol07, Definition 30.1]: for a
triple `T` of the class of `bed` on `M`, a relatively compact open `W` and an analytic isomorphism
`Θ : A ≅ M|W`, the functor's sequence on `T|W` (`seqOn`, `LocalResolutionOn.lean`), the ideal
`T.I|W`, its strict-transform chain and the morphism `Π_r|_{Ỹ}` of closed subspaces are transported
onto `A` (`BlowUpSequence.pullback`, `strictTransformSubspaceSeq`): the transported last transform
is the pull-back of `lastIdealOn` along the lifted `Θ`, it is non-singular (clause (3) of `hbed`,
transported along the diffeomorphism), and the two identifications `homOfPullbackEq` with
`localResolutionOn`/`Sp(W)/T.I|W` make the transport square commute. These are the data (`seq`,
`ideal`, `transform`, `isNonsingular_last`, `map`, `map_comp`) of an `AmbientBlowUpFactorization`
on an ambient of the form that structure asks for, once `A := sigmaOpens G'` (`AmbientLift.lean`).

Not in the sources; bookkeeping.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace Hironaka.Manifold
open AnalyticManifold.BlowUpSequence
open scoped Manifold ContDiff

universe u

namespace Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- The sheaf-level non-singularity of `J` (every stalk `𝒪_x/J_x` on the support regular) from the
space-level one of `Sp(A)/J` (`regularLocus = univ`): the stalks of the closed subspace are the
quotients (`ClosedSubspace.isNonsingular_iff_forall`). Internal. -/
theorem IdealSheaf.isNonsingular_of_isNonsingular_toAnalyticSpace
    (J : AnalyticManifold.IdealSheaf A)
    (h : IsNonsingular J.toAnalyticSpace) : J.IsNonsingular :=
  fun x hx =>
    (ClosedSubspace.isNonsingular_iff_forall
      (X := toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A) J).mp
      ((AnalyticSpace.isNonsingular_iff J.toAnalyticSpace).mp h) x hx

end Manifold

namespace Hironaka.Manifold.BEDanFamStar

open _root_.Manifold

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
  {M A : AnalyticManifold.{u} 𝕜 (Fin n → 𝕜)}

/-- **The functor's sequence on `T|W`, transported onto `A`** along the analytic isomorphism
`Θ : A ≅ M|W` (`BlowUpSequence.pullback` at a diffeomorphism; [Kol07, Definition 30.1]). -/
def ambSeqOn (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    AnalyticManifold.BlowUpSequence (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A :=
  (bed.seqOn T hT W hW).pullback (Diffeomorph.toAnalyticMap Θ) Θ.isLocalDiffeomorph

/-- The ideal `T.I|W` transported onto `A`. -/
def ambIdealOn (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (W : Opens M)
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    AnalyticManifold.IdealSheaf A :=
  (restrictedIdealOn T W).pullback _ (Diffeomorph.toAnalyticMap Θ).contMDiff

/-- The strict-transform chain of the transported ideal along the transported sequence (the field
`transform` of `AmbientBlowUpFactorization`). -/
def ambTransformOn (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω)
    (k : Fin ((ambSeqOn bed T hT W hW Θ).toSuccession.length + 1)) :
    AnalyticManifold.IdealSheaf ((ambSeqOn bed T hT W hW Θ).toSuccession.stage k) :=
  (ambSeqOn bed T hT W hW Θ).toSuccession.strictTransformSubspaceSeq (ambIdealOn T W Θ) k

/-- Its last member. -/
def ambLastOn (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    AnalyticManifold.IdealSheaf ((ambSeqOn bed T hT W hW Θ).toSuccession.stage (Fin.last _)) :=
  ambTransformOn bed T hT W hW Θ (Fin.last _)

/-- The last-stage lift of `Θ`, a diffeomorphism. -/
def ambLiftLastOn (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜)
      ((ambSeqOn bed T hT W hW Θ).toSuccession.stage (Fin.last _))
      ((bed.seqOn T hT W hW).toSuccession.stage (Fin.last _)) ω :=
  (bed.seqOn T hT W hW).pullbackLiftLastDiffeomorph Θ

/-- The transported last transform is the pull-back of the functor's last transform along the
lifted `Θ`. -/
theorem ambLastOn_eq_comap (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    ambLastOn bed T hT W hW Θ =
      Manifold.IdealSheaf.pullback _ (Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW
          Θ)).contMDiff
        (bed.lastIdealOn T hT W hW) :=
  strictTransformSubspaceSeq_last_pullbackLiftLast' (bed.seqOn T hT W hW)
    (Diffeomorph.toAnalyticMap Θ) Θ.isLocalDiffeomorph (restrictedIdealOn T W)

/-- The transported last transform is non-singular (the field `isNonsingular_last`): clause (3) of
`hbed` for `T|W`, transported along the lifted `Θ` (`isNonsingular_pullbackDiffeomorph_iff`). -/
theorem isNonsingular_ambLastOn (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω)
    (hbed : bed.IsEmbeddedDesing) : (ambLastOn bed T hT W hW Θ).IsNonsingular := by
  rw [ambLastOn_eq_comap]
  obtain ⟨-, -, -, hns, -, -⟩ := hbed.1 n T hT W hW
  exact (AnalyticManifold.IdealSheaf.isNonsingular_pullbackDiffeomorph_iff
    (ambLiftLastOn bed T hT W hW Θ) (bed.lastIdealOn T hT W hW)).mpr
    (IdealSheaf.isNonsingular_of_isNonsingular_toAnalyticSpace _ hns)

/-- `Π_r|_{Ỹ}` on the transported data (the field `map`): the morphism of closed subspaces induced
by the composite of the transported sequence (the counterpart of `localResolutionMapOn`). -/
def ambMapOn (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    (ambLastOn bed T hT W hW Θ).toAnalyticSpace ⟶ (ambIdealOn T W Θ).toAnalyticSpace :=
  quotientMap
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (ambSeqOn bed T hT W hW Θ).toSuccession.composite) _ _
    ((ambSeqOn bed T hT W hW Θ).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (ambIdealOn T W Θ))

/-- It lies over the composite (the field `map_comp`). -/
theorem ambMapOn_comp (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    ambMapOn bed T hT W hW Θ ≫ (ambIdealOn T W Θ).toAnalyticSpaceι =
      (ambLastOn bed T hT W hW Θ).toAnalyticSpaceι ≫ toSpaceHom (ContinuousLinearEquiv.refl 𝕜
          (Fin n → 𝕜)) (ambSeqOn bed T hT W hW Θ).toSuccession.composite :=
  quotientMap_comp_quotientι _ _ _ _

/-- The transported local resolution IS the functor's (`homOfPullbackEq` along the lifted `Θ`). -/
def ambLastIso (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    (ambLastOn bed T hT W hW Θ).toAnalyticSpace ⟶ bed.localResolutionOn T hT W hW :=
  IdealSheaf.homOfPullbackEq ⇑(ambLiftLastOn bed T hT W hW Θ)
    (ambLiftLastOn bed T hT W hW Θ).contMDiff (ambLastOn_eq_comap bed T hT W hW Θ)

theorem isIso_ambLastIso (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    IsIso (ambLastIso bed T hT W hW Θ) :=
  isIso_homOfPullbackEq_of_diffeomorph (ambLiftLastOn bed T hT W hW Θ)
    (ambLastOn_eq_comap bed T hT W hW Θ)

/-- The transported closed subspace IS `Sp(W)/T.I|W` (`homOfPullbackEq` along `Θ`). -/
def ambIdealIso (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (W : Opens M)
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    (ambIdealOn T W Θ).toAnalyticSpace ⟶ (restrictedIdealOn T W).toAnalyticSpace :=
  IdealSheaf.homOfPullbackEq ⇑Θ Θ.contMDiff rfl

theorem isIso_ambIdealIso (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M)
    (W : Opens M) (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    IsIso (ambIdealIso T W Θ) :=
  isIso_homOfPullbackEq_of_diffeomorph Θ rfl

/-- The transport square: `Π_r|_{Ỹ}` on the transported data is `localResolutionMapOn`
through the two identifications (`Hom.ext_of_comp_quotientι`, four `quotientMap_comp_quotientι`
squares and the manifold square `stageMap_last_pullbackLiftLast`). -/
theorem ambMapOn_square (bed : BEDanFamStar.{u} 𝕜)
    (T : AnalyticTriple (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) M) (hT : DomBEDan 𝕜 T)
    (W : Opens M) (hW : IsCompact (closure (W : Set M)))
    (Θ : Diffeomorph 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) A (M.restrict W) ω) :
    ambLastIso bed T hT W hW Θ ≫ bed.localResolutionMapOn T hT W hW =
      ambMapOn bed T hT W hW Θ ≫ ambIdealIso T W Θ := by
  -- the composite of the ambient analytic maps: `σ_r ∘ lift = Θ ∘ σ'_r`
  have hfun : (⇑(bed.seqOn T hT W hW).toSuccession.composite ∘
        ⇑(Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW Θ))) =
      (⇑(Diffeomorph.toAnalyticMap Θ) ∘ ⇑(ambSeqOn bed T hT W hW Θ).toSuccession.composite) :=
    funext fun q => stageMap_last_pullbackLiftLast (bed.seqOn T hT W hW)
      (Diffeomorph.toAnalyticMap Θ) Θ.isLocalDiffeomorph q
  have hamb : toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW Θ)) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.seqOn T hT W hW).toSuccession.composite =
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (ambSeqOn bed T hT W hW Θ).toSuccession.composite ≫
        toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
          (Diffeomorph.toAnalyticMap Θ) := by
    refine (ofManifoldHom_comp (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) (E'' := Fin n → 𝕜) _
      (Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW Θ)).contMDiff _
      (bed.seqOn T hT W hW).toSuccession.composite.contMDiff).symm.trans (Eq.trans ?_
        (ofManifoldHom_comp (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) (E'' := Fin n → 𝕜) _
          (ambSeqOn bed T hT W hW Θ).toSuccession.composite.contMDiff _
          (Diffeomorph.toAnalyticMap Θ).contMDiff))
    exact congrArg (fun k : {f : (ambSeqOn bed T hT W hW Θ).toSuccession.stage (Fin.last _) →
          M.restrict W // ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f} =>
        ofManifoldHom (K := 𝕜) (E := Fin n → 𝕜) (E' := Fin n → 𝕜) k.1 k.2)
      (Subtype.ext hfun : (⟨_, (bed.seqOn T hT W hW).toSuccession.composite.contMDiff.comp
          (Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW Θ)).contMDiff⟩ :
        {f : (ambSeqOn bed T hT W hW Θ).toSuccession.stage (Fin.last _) → M.restrict W //
          ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) ω f}) =
        ⟨_, (Diffeomorph.toAnalyticMap Θ).contMDiff.comp
          (ambSeqOn bed T hT W hW Θ).toSuccession.composite.contMDiff⟩)
  -- the four quotient-map squares
  have e1 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (bed.seqOn T hT W hW).toSuccession.composite) _ _
    ((bed.seqOn T hT W hW).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (restrictedIdealOn T W))
  have e2 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW Θ))) _ _
    (compat_ofManifoldHom_of_eq _ _ (ambLastOn_eq_comap bed T hT W hW Θ))
  have e3 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (Diffeomorph.toAnalyticMap Θ)) _ _
    (compat_ofManifoldHom_of_eq _ _ (rfl : ambIdealOn T W Θ = _))
  have e4 := quotientMap_comp_quotientι
    (toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
      (ambSeqOn bed T hT W hW Θ).toSuccession.composite) _ _
    ((ambSeqOn bed T hT W hW Θ).toSuccession.compat_composite_strictTransformSubspaceSeq
      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) (ambIdealOn T W Θ))
  -- the K-typed names of the four morphisms of closed subspaces
  obtain ⟨χ, hχ⟩ : ∃ χ : (ambLastOn bed T hT W hW Θ).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (bed.localResolutionOn T hT W hW).toKLocallyRingedSpace,
      χ = ambLastIso bed T hT W hW Θ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : (bed.localResolutionOn T hT W hW).toKLocallyRingedSpace ⟶
      (restrictedIdealOn T W).toAnalyticSpace.toKLocallyRingedSpace,
      P = bed.localResolutionMapOn T hT W hW := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : (ambLastOn bed T hT W hW Θ).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (ambIdealOn T W Θ).toAnalyticSpace.toKLocallyRingedSpace,
      D = ambMapOn bed T hT W hW Θ := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (ambIdealOn T W Θ).toAnalyticSpace.toKLocallyRingedSpace ⟶
      (restrictedIdealOn T W).toAnalyticSpace.toKLocallyRingedSpace,
      R = ambIdealIso T W Θ := ⟨_, rfl⟩
  have e1' : P ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict W)).toKLocallyRingedSpace (restrictedIdealOn T W) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((bed.seqOn T hT W hW).stage (Fin.last _))).toKLocallyRingedSpace
        (bed.lastIdealOn T hT W hW) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (bed.seqOn T hT W hW).toSuccession.composite := by
    rw [hP]; exact e1
  have e2' : χ ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((bed.seqOn T hT W hW).stage (Fin.last _))).toKLocallyRingedSpace
        (bed.lastIdealOn T hT W hW) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((ambSeqOn bed T hT W hW Θ).toSuccession.stage (Fin.last _))).toKLocallyRingedSpace
        (ambLastOn bed T hT W hW Θ) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (Diffeomorph.toAnalyticMap (ambLiftLastOn bed T hT W hW Θ)) := by
    rw [hχ]; exact e2
  have e3' : R ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (M.restrict W)).toKLocallyRingedSpace (restrictedIdealOn T W) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜)) A).toKLocallyRingedSpace
        (ambIdealOn T W Θ) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (Diffeomorph.toAnalyticMap Θ) := by
    rw [hR]; exact e3
  have e4' : D ≫ quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        A).toKLocallyRingedSpace (ambIdealOn T W Θ) =
      quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        ((ambSeqOn bed T hT W hW Θ).toSuccession.stage (Fin.last _))).toKLocallyRingedSpace
        (ambLastOn bed T hT W hW Θ) ≫
      toSpaceHom (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
        (ambSeqOn bed T hT W hW Θ).toSuccession.composite := by
    rw [hD]; exact e4
  have hK : χ ≫ P = D ≫ R := by
    refine Hom.ext_of_comp_quotientι _ ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => χ ≫ k) e1').trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ toSpaceHom
              (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
              (bed.seqOn T hT W hW).toSuccession.composite) e2').trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k => quotientι (toSpace (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
                  ((ambSeqOn bed T hT W hW Θ).toSuccession.stage
                    (Fin.last _))).toKLocallyRingedSpace (ambLastOn bed T hT W hW Θ) ≫ k)
                hamb).trans
                ((Category.assoc _ _ _).symm.trans
                  ((congrArg (fun k => k ≫ toSpaceHom
                      (ContinuousLinearEquiv.refl 𝕜 (Fin n → 𝕜))
                      (Diffeomorph.toAnalyticMap Θ)) e4'.symm).trans
                    ((Category.assoc _ _ _).trans
                      ((congrArg (fun k => D ≫ k) e3'.symm).trans
                        (Category.assoc _ _ _).symm)))))))))
  subst hχ hP hD hR
  exact hK

end Hironaka.Manifold.BEDanFamStar

end
