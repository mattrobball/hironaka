/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.AnalyticSpace.Glue.Data
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The glued space of `K`-gluing data: pieces, images, constants

For gluing data `D : KGlueData K` (`Hironaka.AnalyticSpace.Glue.Data`) the glued locally ringed
space `D.glued` carries the open immersions `D.ι i : Y i ⟶ D.glued`, whose images `D.pieceOpens i`
cover it, and on each image the constant sections `D.constOn c i` transported from the `K`-structure
of `Y i` through the inverse of the open immersion on sections (`IsOpenImmersion.invApp`). This
module sets up these objects; the compatibility of the constants on the overlaps (from the
transitions being `K`-morphisms) is `Hironaka.AnalyticSpace.Glue.Compat`, and the resulting
`K`-structure on `D.glued` is `Hironaka.AnalyticSpace.Glue.KSpace`.

Conventions. `D.glued` is Mathlib's `GlueData.glued` (a multicoequalizer); `D.ι i` are its structure
morphisms, open immersions (`LocallyRingedSpace.GlueData.ι_isOpenImmersion`), jointly surjective on
points (`ι_jointly_surjective`); `pieceOpens i = ι i '' ⊤` through Mathlib's `opensFunctor`. With
one piece, `pieceOpens = ⊤` and `constOn c` is the constant of the piece; with an empty index type
the glued space is empty.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
open AnalyticSpace.KLocallyRingedSpace

namespace AnalyticSpace.Glue.KGlueData

universe u

variable {K : Type} [RCLike K] (D : KGlueData.{u} K)

/-- The glued locally ringed space. -/
noncomputable abbrev glued : LocallyRingedSpace.{u} := D.toLRSGlueData.toGlueData.glued

/-- The open immersion of the `i`-th piece into the glued space. -/
noncomputable abbrev ι (i : D.J) : (D.Y i).toLocallyRingedSpace ⟶ D.glued :=
  D.toLRSGlueData.toGlueData.ι i

instance (i : D.J) : LocallyRingedSpace.IsOpenImmersion (D.ι i) :=
  D.toLRSGlueData.ι_isOpenImmersion i

/-- The image of the `i`-th piece, an open of the glued space. -/
noncomputable def pieceOpens (i : D.J) : Opens D.glued :=
  (LocallyRingedSpace.IsOpenImmersion.opensFunctor (D.ι i)).obj ⊤

theorem mem_pieceOpens_iff (i : D.J) (z : D.glued) :
    z ∈ D.pieceOpens i ↔ ∃ y : D.Y i, (D.ι i).base y = z := by
  change z ∈ (D.ι i).base '' ((⊤ : Opens (D.Y i)) : Set (D.Y i)) ↔ _
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, rfl⟩

/-- The images of the pieces cover the glued space. -/
theorem iSup_pieceOpens_eq_top : (⨆ i, D.pieceOpens i) = ⊤ := by
  apply top_le_iff.mp
  intro z _
  obtain ⟨i, y, hy⟩ := D.toLRSGlueData.ι_jointly_surjective z
  exact Opens.mem_iSup.mpr ⟨i, (D.mem_pieceOpens_iff i z).mpr ⟨y, hy⟩⟩

/-- The constant `c` on the image of the `i`-th piece, transported from the `K`-structure of `Y i`.
-/
noncomputable def constOn (c : K) (i : D.J) : D.glued.presheaf.obj (op (D.pieceOpens i)) :=
  (LocallyRingedSpace.IsOpenImmersion.invApp (D.ι i) ⊤).hom ((D.Y i).algebraMap c)

end AnalyticSpace.Glue.KGlueData
