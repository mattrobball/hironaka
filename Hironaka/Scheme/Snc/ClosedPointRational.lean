/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Hironaka.Scheme.BlowUp.Glue.BlowUp
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Mathlib.Algebra.Order.Module.Field
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Closed points of the blow-up are rational over their image

[Hau14, Proposition 5.4] and [Hau03, Appendix C] work with closed points of varieties over an
algebraically closed field `K`, where the entries `a'_i ∈ K` of a point `a'` of the blow-up make
sense. The statements (8)–(9) of that proposition in `Hironaka.Scheme.Snc.ChartOrigin` carry the
hypothesis that `a'` is rational over `κ(a)`, `a = π(a')`: the residue field map `κ(a) → κ(a')` is
an isomorphism. This module discharges it in Hauser's setting: for `X` smooth over an algebraically
closed `k` and `a'` a closed point of `B_Z X`, both residue fields are `k` (Mathlib's
`residueFieldIsoBase`, for the closed points `a'` and `a = π(a')` — the image of a closed point
under the proper blow-up map is closed), and the residue field map is the composite of these
identifications (`isIso_residueFieldMap_of_isClosed`), by the naturality
`Spec.map (π^♯) ≫ fromSpecResidueField = fromSpecResidueField ≫ π` and the faithfulness of `Spec`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Hauser's setting for (6), (8), (9): for `k` algebraically closed and `a'` a closed point of
`B_Z X`, the residue field map `κ(π a') → κ(a')` of the blow-up is an isomorphism (both fields are
`k`). -/
theorem isIso_residueFieldMap_of_isClosed [IsAlgClosed k] (f : X ⟶ Spec (.of k)) [Smooth f]
    (Z : X.IdealSheafData) (a' : blowUp Z) (hcl : IsClosed ({a'} : Set (blowUp Z))) :
    IsIso ((blowUpπ Z).residueFieldMap a') := by
  have hN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hπ : IsProper (blowUpπ Z) := blowUp.isProper_π Z
  -- the image of the closed point is closed
  have hcl' : IsClosed ({blowUpπ Z a'} : Set X) := by
    have := (blowUpπ Z).isClosedMap _ hcl
    rwa [Set.image_singleton] at this
  -- both residue fields are `k`
  let i₁ := residueFieldIsoBase (blowUpπ Z ≫ f) a' hcl
  let i₀ := residueFieldIsoBase f (blowUpπ Z a') hcl'
  have key : i₀.inv ≫ (blowUpπ Z).residueFieldMap a' = i₁.inv := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, SpecMap_residueFieldIsoBase_inv,
      ← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Category.assoc]
  have h2 : (blowUpπ Z).residueFieldMap a' = i₀.hom ≫ i₁.inv := by
    rw [← key, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [h2]
  infer_instance

end AlgebraicGeometry
