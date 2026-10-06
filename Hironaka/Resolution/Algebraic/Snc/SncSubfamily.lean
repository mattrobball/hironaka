/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SncOn
import Hironaka.Resolution.Algebraic.Snc.SncOnTransport
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# A sub-family of a simple normal crossing family is snc

The conditions (1)–(4) of [Kol07, Definition 24] concern each member and the members through a
point; selecting members (`subfamily` of `Hironaka.Scheme.Snc.SncOn`) keeps them — the injective
inclusion of the selected members preserves the components (`isSncAt_of_injective_components` of
`Hironaka.Resolution.Algebraic.Snc.SncOnTransport`). Used for the exceptional sub-family `F_r` of
`E_r` as the boundary of the triple of [Kol07, Theorem 92], and by
`Hironaka.Resolution.Algebraic.Kol07.UnionIdealInvertible`.

Source: [Kol07, Definition 24].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka.Snc

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- A sub-family of an snc family is snc [Kol07, Definition 24]. -/
theorem IsSnc.subfamily {E : DivisorFamily X} (hE : E.IsSnc) (p : E.ι → Prop) :
    (E.subfamily p).IsSnc :=
  ⟨fun i => hE.1 i.1, fun x =>
    let ⟨n, z, h⟩ := hE.2 x
    ⟨n, z, isSncAt_of_injective_components (F' := E.subfamily p) (F := E) (fun i => i.1)
      Subtype.val_injective (fun _ => rfl) h⟩⟩

end AlgebraicGeometry.Scheme.DivisorFamily
