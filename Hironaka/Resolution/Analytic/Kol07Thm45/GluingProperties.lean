/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Resolution.Defs
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
public import Hironaka.AnalyticSpace.SncDivisorSetLocal
public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientFactorization
import Hironaka.Resolution.Analytic.Kol07Thm45.AmbientLift
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionShear
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionClauses
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionFunctorial
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionIsoReg
import Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionSnc
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-!
# The resolution of analytic spaces: the gluing and its global properties

The theorems of the gluing of the local resolutions over an exhaustion and the properties of the
glued resolution `R(X) → X`, in their final form: each is the corresponding theorem of the
preceding modules with the independence of the local resolution from the embedding discharged by
`localResolution_independent_of_local` (`LocalResolutionIndependent.lean`) at the local form
`localResolution_independent_local` (`LocalResolutionShear.lean`) —

* `localResolutionIndependentOn_of_isEmbeddedDesing`: the independence, as the proposition
  `LocalResolutionIndependentOn X bed` (`PieceGlueProof.lean`);
* `resolutionGluesOn_of_isEmbeddedDesing` (the gluing datum of a local embedding datum,
  `PieceGlueDatum.lean`) and `resolutionGlues_of_isEmbeddedDesing` (the exhaustion gluing,
  `PieceGlueIndep.lean`);
* `resolution_clauses_of_isEmbeddedDesing`: the five clauses of `exists_functorial_resolution`
  (`ResolutionAssembly.lean`) for `R(X) → X` — non-singularity
  (`ResolutionClauses.lean`), the isomorphism over `X.regularLocus` (`ResolutionIsoReg.lean`), the
  simple normal crossings divisor set over `X.singularLocus` (`ResolutionSnc.lean`), the locally
  finite ambient blow-up composite (`AmbientFactorization.lean`), the functoriality for isomorphisms
  of open subspaces (`ResolutionFunctorial.lean`); `range_resolutionMap_eq_closure_reg`
  (`ResolutionSnc.lean`);
* `resolutionOn_indep` and `resolutionOn_indep_self` (the independence of the gluing from the
  data, `PieceGlueIndep.lean`), `nonempty_ambientBlowUpFactorization_resolutionOnFullMap`
  (`AmbientLift.lean`).

The sources are Kollár's Theorem 45 with its proof through Proposition 37 [Kol07, Theorem 45],
[Kol07, Proposition 37], Włodarczyk's gluing over an open cover by relatively compact opens
[Wlo09, §4.3], and the countability at infinity of an analytic space [Hir64, Ch. 0, §1, p. 120].
-/

public section

open TopologicalSpace Hironaka.Manifold
open scoped Manifold ContDiff CategoryTheory
open CategoryTheory (IsIso)

universe u

namespace Hironaka.Manifold

variable (𝕜 : Type) [RCLike 𝕜]

/-- **The independence of the local resolution from the embedding**, as the proposition
`LocalResolutionIndependentOn X bed` that the gluing theorems take as their hypothesis `hind` —
`localResolution_independent_of_local` (`LocalResolutionIndependent.lean`) at the local form
`localResolution_independent_local` (`LocalResolutionShear.lean`). -/
theorem localResolutionIndependentOn_of_isEmbeddedDesing (X : AnalyticSpace.{u} 𝕜)
    (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) : LocalResolutionIndependentOn X bed :=
  fun E₁ E₂ W₁ hW₁ W₂ hW₂ =>
    PieceEmbedding.localResolution_independent_of_local E₁ E₂ bed hbed W₁ hW₁ W₂ hW₂
      (fun x hx₁ hx₂ =>
        localResolution_independent_local 𝕜 E₁ E₂ bed hbed W₁ hW₁ W₂ hW₂ x hx₁ hx₂)

/-- **The local resolutions of the pieces of a local embedding datum glue** —
`resolutionGluesOn_of_isEmbeddedDesing_of_independent` (`PieceGlueDatum.lean`) at the
independence. -/
theorem resolutionGluesOn_of_isEmbeddedDesing {X : AnalyticSpace.{u} 𝕜} {U : Set X}
    (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) :
    D.ResolutionGluesOn bed :=
  D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed
    (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed)

/-- **The resolution glues along an exhaustion** —
`resolutionGlues_of_isEmbeddedDesing_of_independent` (`PieceGlueIndep.lean`) at the independence. -/
theorem resolutionGlues_of_isEmbeddedDesing (X : AnalyticSpace.{u} 𝕜) (hX : X.IsReduced)
    (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) : bed.ResolutionGlues X :=
  BEDanFamStar.resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed
    (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed)

/-- **The five clauses of `exists_functorial_resolution` for `R(X) → X`** — non-singularity, the
isomorphism over `X.regularLocus`, the simple normal crossings divisor set over `X.singularLocus`,
the locally finite ambient blow-up composite, the functoriality for isomorphisms of open subspaces —
each the theorem of the preceding modules at the independence (for `X`, and for `Y` in clause (5)).
-/
theorem resolution_clauses_of_isEmbeddedDesing (X : AnalyticSpace.{u} 𝕜) (hX : X.IsReduced)
    (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) :
    (bed.resolution X).IsNonsingular ∧
    (bed.resolutionMap X).IsIsoOver X.regularLocus ∧
    AnalyticSpace.IsSncDivisorSet (bed.resolution X)
      ((bed.resolutionMap X) ⁻¹' X.singularLocus) ∧
    (bed.resolutionMap X).IsLocallyFiniteAmbientBlowUpComposite ∧
    ∀ (Y : AnalyticSpace.{u} 𝕜), Y.IsReduced → ∀ (U : Set X) (V : Set Y),
        IsOpen U → IsOpen V →
      ∀ φ : X.restrictSet U ⟶ Y.restrictSet V, IsIso φ →
        ∃ ψ : (bed.resolution X).restrictSet ((bed.resolutionMap X) ⁻¹' U) ⟶
            (bed.resolution Y).restrictSet ((bed.resolutionMap Y) ⁻¹' V),
          IsIso ψ ∧ ψ ≫ (bed.resolutionMap Y).restrictSet V =
            (bed.resolutionMap X).restrictSet U ≫ φ :=
  ⟨BEDanFamStar.resolution_isNonsingular_of_independent X hX bed hbed
      (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed),
    BEDanFamStar.resolutionMap_isIsoOver_reg_of_independent X hX bed hbed
      (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed),
    BEDanFamStar.resolution_isSncDivisorSet_preimage_sing_of_independent X hX bed hbed
      (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed),
    BEDanFamStar.isLocallyFiniteAmbientBlowUpComposite_resolutionMap_of_independent bed X hX hbed
      (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed),
    fun Y hY U V hU hV φ hφ =>
      BEDanFamStar.resolution_functorial_of_independent X hX bed hbed
        (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed) Y hY
            (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 Y bed hbed)
        U V hU hV φ hφ⟩

/-- **The range of `Π_X` is the closure of the simple locus** —
`range_resolutionMap_eq_closure_reg_of_independent` (`ResolutionSnc.lean`) at the independence. -/
theorem range_resolutionMap_eq_closure_reg (X : AnalyticSpace.{u} 𝕜) (hX : X.IsReduced)
    (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) :
    Set.range (bed.resolutionMap X) = closure X.regularLocus :=
  BEDanFamStar.range_resolutionMap_eq_closure_reg_of_independent X hX bed hbed
    (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed)

/-- **The independence of the glued resolution from the local embedding data**, in the `U ⊆ U'`
form — `resolutionOn_indep_of_independent` (`PieceGlueIndep.lean`) at the independence. -/
theorem resolutionOn_indep {X : AnalyticSpace.{u} 𝕜} {U U' : Set X}
    (D : LocalEmbeddingData 𝕜 X U) (D' : LocalEmbeddingData 𝕜 X U') (hU : IsOpen U)
    (hUU' : U ⊆ U') (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing) :
    ∃! ψ : D.resolutionOn bed ⟶ (D'.resolutionOnFull bed).restrictSet
        (D'.resolutionOnFullMap bed ⁻¹' U),
      IsIso ψ ∧ ψ ≫ (D'.resolutionOnFullMap bed).restrictSet U = D.resolutionOnMap bed :=
  LocalEmbeddingData.resolutionOn_indep_of_independent D D' bed hU hUU' hbed
    (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed)

/-- The `U' = U` instance of `resolutionOn_indep`. -/
theorem resolutionOn_indep_self {X : AnalyticSpace.{u} 𝕜} {U : Set X}
    (D D' : LocalEmbeddingData 𝕜 X U) (hU : IsOpen U) (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) :
    ∃! ψ : D.resolutionOn bed ⟶ D'.resolutionOn bed,
      IsIso ψ ∧ ψ ≫ D'.resolutionOnMap bed = D.resolutionOnMap bed :=
  resolutionOn_indep 𝕜 D D' hU subset_rfl bed hbed

/-- **The ambient blow-up factorization of the glued space's map at `U`** —
`nonempty_ambientBlowUpFactorization_resolutionOnFullMap_of_independent` (`AmbientLift.lean`) at
the independence. -/
theorem nonempty_ambientBlowUpFactorization_resolutionOnFullMap {X : AnalyticSpace.{u} 𝕜}
    {U : Set X} (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)
    (hbed : bed.IsEmbeddedDesing) :
    Nonempty ((D.resolutionOnFullMap bed).AmbientBlowUpFactorization U) :=
  LocalEmbeddingData.nonempty_ambientBlowUpFactorization_resolutionOnFullMap_of_independent D bed
    hbed (localResolutionIndependentOn_of_isEmbeddedDesing 𝕜 X bed hbed)

end Hironaka.Manifold

