/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueProof
public import Hironaka.Resolution.Analytic.Kol07Thm45.Resolution
import Hironaka.AnalyticSpace.Glue.OverReg
import Hironaka.AnalyticSpace.ProperRestrict
import Hironaka.AnalyticSpace.RegOpenImmersion
import Hironaka.Resolution.Analytic.Kol07Thm45.LocalResolutionIndependent
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueDatum
import Hironaka.Resolution.Analytic.Kol07Thm45.PieceGlueIndep
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Properness and non-singularity of the resolution `R(X) → X`

Kollár's Theorem 45: `R(X)` is smooth and `Π_X` is projective over any compact subset of `X`
[Kol07, Theorem 45(1), (4)]; Włodarczyk's Theorem 2.0.1: the canonical desingularization is a
manifold with a proper bimeromorphic morphism to `Y` [Wlo09, Theorem 2.0.1], `des_V : Ṽ → V`
proper [Wlo09, §4, (3)⇒(4)] and `des : Ỹ → Y` proper [Wlo09, §4.3]; the smoothness of the final
strict transform is [Wlo09, Theorem 2.0.2(3)]. Two clauses of `exists_functorial_resolution`
(`ResolutionAssembly.lean`) in the form the assembly uses:

* `BEDanFamStar.isProperMap_resolutionMap`: **`Π_X : R(X) → X` is proper**, with NO hypotheses:
  off the class (`X` not reduced) and without a gluing datum the pair is `⟨X, 𝟙 X⟩`; with one, over
  every member `U_n` of the exhaustion the descended map is the map `Π_{U_n}`, proper by
  `isProperMap_resolutionOnMap` (`PieceGlueDatum.lean`), and properness is local on the target;
* `BEDanFamStar.resolution_isNonsingular_of_independent`: **`R(X)` is non-singular** — the
  exhaustion's pieces `resolutionOn (D n) bed` are open subspaces of the glued spaces `Ṽ_n`, glued
  from the local resolutions `Ỹ_i`, which are non-singular by clause (3) of `hbed`
  (`isNonsingular_localResolution`); a glued space of non-singular pieces is non-singular
  (`isNonsingular_gluedOver`, twice).

The independence of the local resolution enters as the hypothesis `hind` where a gluing datum is
needed. Not in the sources beyond the statements cited; bookkeeping.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace KLocallyRingedSpace

universe u

namespace Hironaka.Manifold.LocalEmbeddingData

variable {𝕜 : Type} [RCLike 𝕜] {X : AnalyticSpace.{u} 𝕜} {U : Set X}
  (D : LocalEmbeddingData 𝕜 X U) (bed : BEDanFamStar.{u} 𝕜)

/-- The map `resolutionOnToSpace` into `X` lands in the OPEN `U` (`openOf X U = U` for an open
`U`). -/
theorem range_toFun_resolutionOnToSpace_subset (hU : IsOpen U) :
    range (KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed)) ⊆ U := by
  rintro _ ⟨r, rfl⟩
  exact (SetLike.ext_iff.mp (openOf_of_isOpen X hU) _).mp
    (KLocallyRingedSpace.Hom.toFun (D.resolutionOnMap bed) r).2

/-- **The map `resolutionOnToSpace` onto the OPEN `U` is proper** (Włodarczyk's `des_V` proper,
[Wlo09, §4, (3)⇒(4)]) — `isProperMap_resolutionOnMap`, its target `X|U` read as the subtype `U`
(`openOf_of_isOpen`). -/
theorem isProperMap_resolutionOnToSpace_dom (hU : IsOpen U) :
    IsProperMap fun y : D.resolutionOn bed =>
      (⟨KLocallyRingedSpace.Hom.toFun (D.resolutionOnToSpace bed) y,
        D.range_toFun_resolutionOnToSpace_subset bed hU ⟨y, rfl⟩⟩ : U) := by
  have hcoe : ((openOf X U : Opens X.toKLocallyRingedSpace) :
      Set X.toKLocallyRingedSpace) = (U : Set X.toKLocallyRingedSpace) :=
    congrArg SetLike.coe (openOf_of_isOpen X hU)
  exact isProperMap_of_homeomorph_comp_eq (Homeomorph.refl _) (Homeomorph.setCongr hcoe).symm
    (D.isProperMap_resolutionOnMap bed hU) (fun y => Subtype.ext rfl)

/-- **The glued space of the pieces is non-singular** ([Wlo09, Theorem 2.0.2(3)];
[Kol07, Theorem 45(1)]) — every local resolution `Ỹ_i` is non-singular by clause (3) of `hbed`
(`isNonsingular_localResolution`), and a glued space of non-singular pieces is non-singular
(`isNonsingular_gluedOver`); the space `resolutionOnFull` unfolds to the chosen datum's glued
space (`resolutionOnFull_eq_of_glues`). -/
theorem isNonsingular_resolutionOnFull_of_independent (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) : (D.resolutionOnFull bed).IsNonsingular := by
  have h := D.resolutionGluesOn_of_isEmbeddedDesing_of_independent bed hbed hind
  rw [D.resolutionOnFull_eq_of_glues bed h]
  exact GlueOver.isNonsingular_gluedOver h.some.glue fun i =>
    (D.embedding i).isNonsingular_localResolution bed hbed (h.some.W i)
      (h.some.isCompact_closure_W i)

/-- Non-singularity of the space `resolutionOn` over `U`, under `hbed` and the independence `hind`:
an open subspace of a non-singular space (`isNonsingular_restrictSet`,
`isNonsingular_resolutionOnFull_of_independent`). -/
theorem isNonsingular_resolutionOn_of_independent (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) : (D.resolutionOn bed).IsNonsingular :=
  isNonsingular_restrictSet
    (D.isNonsingular_resolutionOnFull_of_independent bed hbed hind) _

end Hironaka.Manifold.LocalEmbeddingData

namespace Hironaka.Manifold.BEDanFamStar

variable {𝕜 : Type} [RCLike 𝕜]

/-- **`Π_X : R(X) → X` is proper** ([Kol07, Theorem 45(4)]: projective over every compact subset;
[Wlo09, Theorem 2.0.1]: proper; [Wlo09, §4.3]) — with NO hypotheses: off the class and without a
gluing datum the pair is `⟨X, 𝟙 X⟩` (`resolutionPair_eq_of_not_isReduced`,
`resolutionPair_eq_of_not_glues`), the identity being proper; with a gluing datum, over every
member `U_n` of the exhaustion the descended map is the map `Π_{U_n}`, proper by
`isProperMap_resolutionOnToSpace_dom`, and properness is local on the target
(`isProperMap_descMap_of_iUnion`). Neither the reducedness of `X` nor `IsEmbeddedDesing` is
needed. -/
theorem isProperMap_resolutionMap (X : AnalyticSpace.{u} 𝕜)
    (bed : BEDanFamStar.{u} 𝕜) : IsProperMap (bed.resolutionMap X) := by
  suffices key : ∀ p : Σ R :
      AnalyticSpace.{u} 𝕜, (R ⟶ X),
      p = bed.resolutionPair X → IsProperMap (KLocallyRingedSpace.Hom.toFun p.2) from key _ rfl
  intro p hp
  by_cases hX : X.IsReduced
  · by_cases h : bed.ResolutionGlues X
    · rw [bed.resolutionPair_eq_of_glues X hX h] at hp
      subst hp
      refine GlueOver.isProperMap_descMap_of_iUnion h.some.glue ?_ fun n =>
        (h.some.D n.down).isProperMap_resolutionOnToSpace_dom bed (h.some.U n.down).isOpen
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := mem_iUnion.mp (h.some.iUnion_U ▸ mem_univ x)
      exact mem_iUnion.mpr ⟨⟨n⟩, hn⟩
    · rw [bed.resolutionPair_eq_of_not_glues X hX h] at hp
      subst hp
      exact isProperMap_id
  · rw [bed.resolutionPair_eq_of_not_isReduced X hX] at hp
    subst hp
    exact isProperMap_id

/-- **`R(X)` is non-singular** ([Wlo09, Theorem 2.0.1]: `Ỹ` is a manifold; [Kol07, Theorem 45(1)]),
for a reduced `X`, under `hbed` and with the independence of the local resolution as `hind` — the
exhaustion's pieces `resolutionOn (D n) bed` are non-singular
(`isNonsingular_resolutionOn_of_independent`) and the glued space of non-singular pieces is
non-singular (`isNonsingular_gluedOver`); the space `bed.resolution X` unfolds to the chosen
datum's glued space (`resolution_eq_of_glues`). -/
theorem resolution_isNonsingular_of_independent (X : AnalyticSpace.{u} 𝕜)
    (hX : X.IsReduced) (bed : BEDanFamStar.{u} 𝕜) (hbed : bed.IsEmbeddedDesing)
    (hind : LocalResolutionIndependentOn X bed) : (bed.resolution X).IsNonsingular := by
  have h := resolutionGlues_of_isEmbeddedDesing_of_independent X hX bed hbed hind
  rw [bed.resolution_eq_of_glues X hX h]
  exact GlueOver.isNonsingular_gluedOver h.some.glue fun n =>
    (h.some.D n.down).isNonsingular_resolutionOn_of_independent bed hbed hind

end Hironaka.Manifold.BEDanFamStar

end
