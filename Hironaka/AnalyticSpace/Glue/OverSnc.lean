/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Over
public import Hironaka.AnalyticSpace.SncDivisorSetLocal
import Hironaka.AnalyticSpace.SncDivisorSetCover
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Simple-normal-crossings divisor sets on a glued space

On a gluing datum `G : GlueOver X R π dom` the pieces are the open immersions
`ιGlued i : R i → gluedOver`, so the local predicate `IsSncDivisorSet` of the analytic-space
vocabulary is checked piece by piece (`isSncDivisorSet_of_openImmersion_cover`,
`Hironaka.AnalyticSpace.SncDivisorSetCover`); for the inverse image under the descended map of a
subset of `X` the pieces' conditions are on the inverse images under the piece maps
(`toFun_descMap_ιGlued`). This is how the clause that the inverse image of the singular locus is a
divisor with simple normal crossings ([Kol07, Theorem 45, (3)]; [Wlo09, Theorem 2.0.1, (2)]) passes
from the local resolutions to the glued space: `isSncDivisorSet_gluedOver_preimage` is applied twice
in `Hironaka.Resolution.Analytic.Kol07Thm45.ResolutionSnc`, on each glued space of local resolutions
and on the space glued along the exhaustion. The plain form `isSncDivisorSet_gluedOver` has no code
users outside this module.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace Set Topology
open AnalyticSpace.KLocallyRingedSpace

universe u

namespace AnalyticSpace.GlueOver

variable {K : Type} [RCLike K] {X : AnalyticSpace.{u} K} {ι : Type u}
  {R : ι → AnalyticSpace.{u} K} {π : ∀ i, (R i).toKLocallyRingedSpace ⟶ X.toKLocallyRingedSpace}
  {dom : ι → Opens X} (G : GlueOver X R π dom) [Countable ι]

/-- **A subset of a glued space is a simple-normal-crossings divisor set when its inverse image in
every piece is**: the pieces `ιGlued i` are open immersions covering the glued space
(`exists_ιGlued_eq`). -/
theorem isSncDivisorSet_gluedOver (Z : Set G.gluedOver)
    (h :
        ∀ i, IsSncDivisorSet (R i)
            (KLocallyRingedSpace.Hom.toFun (G.ιGlued i) ⁻¹' Z)) :
    IsSncDivisorSet G.gluedOver Z :=
  AnalyticSpace.isSncDivisorSet_of_openImmersion_cover G.gluedOver Z R G.ιGlued
    G.exists_ιGlued_eq h

/-- **The inverse image under the descended map of a subset `S ⊆ X` is a simple-normal-crossings
divisor set of the glued space when its inverse image under every piece map is**
(`toFun_descMap_ιGlued`). -/
theorem isSncDivisorSet_gluedOver_preimage (S : Set X)
    (h : ∀ i, IsSncDivisorSet (R i) (KLocallyRingedSpace.Hom.toFun
        (π i) ⁻¹' S)) :
    IsSncDivisorSet G.gluedOver
        (KLocallyRingedSpace.Hom.toFun G.descMap ⁻¹' S) :=
  G.isSncDivisorSet_gluedOver _ fun i =>
    (congrArg (IsSncDivisorSet (R i)) (Set.ext fun y =>
      Iff.of_eq (congrArg (fun q => q ∈ S) (G.toFun_descMap_ιGlued i y)))).mpr (h i)

end AnalyticSpace.GlueOver

end
