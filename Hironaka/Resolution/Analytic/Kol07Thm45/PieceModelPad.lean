/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Analytic.Kol07Thm45.PieceModel
public import Hironaka.Resolution.Analytic.Kol07Thm45.PadIdeal
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The padding tools instantiated

`PadIdeal.lean` pads an ideal sheaf on a piece ambient along an embedding of coordinates
`σ : Fin m ↪ Fin n'`: the padded open, the padded ideal `𝓘 + (z_j)_{j ∉ range σ}`, the slice
isomorphism of closed subspaces, the transport of reducedness and the nonvanishing of the padded
ideal at every stalk for a non-surjective `σ` (Włodarczyk's common ambient dimension
[Wlo09, §7.1]; Kollár's enlargement of the affine space of an embedding
[Kol07, Theorem 36, proof]). This module reads those constructions at `σ := Fin.castLEEmb h`
(`z ↦ (z, 0)`) into the interface `PadTools` of `PieceModel.lean`, so that
`exists_localEmbeddingData_of_padTools` yields the existence of local embedding data outright.
-/

@[expose] public section

open TopologicalSpace

universe u

noncomputable section

namespace Hironaka.Manifold

/-- The padding constructions of `PadIdeal.lean` at `σ := Fin.castLEEmb h`, as the interface
`PadTools` used by the existence proof of local embedding data ([Wlo09, §7.1]). -/
def padTools (𝕜 : Type) [RCLike 𝕜] : PadTools.{u} 𝕜 where
  padOpens h G := padOpens (Fin.castLEEmb h) G
  padIdeal := fun {_m _n'} h {_G} J => padIdeal (Fin.castLEEmb h) J
  isReduced := fun {_m _n'} h {_G} J hJ => isReduced_padIdeal (Fin.castLEEmb h) J hJ
  isNonzeroEverywhere := fun {_m _n'} h hlt {_G} J =>
    isNonzeroEverywhere_padIdeal_castLE (h := h) J hlt
  iso := fun {_m _n'} h {_G} J => padSliceIso (Fin.castLEEmb h) J

end Hironaka.Manifold

end
