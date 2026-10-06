/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.ChartHom
public import Hironaka.Algebra.Local.CompletionCoords
public import Hironaka.Algebra.Local.OrderFlat
import Hironaka.Algebra.Local.ChartCompletion
import Mathlib.Combinatorics.Matroid.Init

/-!
# The chart-ring local homomorphism reflects orders

[Kol07, Lemma 61] bounds the order of the marked transform in the local ring `R'_{𝔪'}` of the
chart ring at the chart origin (`Hironaka/Algebra/Local/Lemma61.lean`). On a manifold, the stalk of
the marked transform at a point `a'` over the centre is the image of the transform `transformIdeal`
under a chart-ring map `χ : R' → 𝒪_{a'}` into the ring of germs at `a'`, which factors through the
local homomorphism `R'_{𝔪'} → 𝒪_{a'}` (`chartLocalHom`, `Hironaka/Algebra/Local/ChartHom.lean`).
This module carries the order bound across that local homomorphism: when the induced map of
completions `(R'_{𝔪'})^ → 𝒪̂_{a'}` is bijective (`Hironaka/Algebra/Local/ChartCompletionHom.lean`),
the local homomorphism reflects the powers of the maximal ideal (`ordFaithful_chartLocalHom`, in the
vocabulary `OrdFaithful` of `Hironaka/Algebra/Local/OrderFlat.lean`), so `ord (J 𝒪_{a'}) ≤ ord J`
for every ideal `J` of `R'_{𝔪'}` (`ord_map_le_of_ordFaithful`).

The three factors: `R'_{𝔪'} → (R'_{𝔪'})^` reflects the powers, since `𝔪ʳ R̂ ∩ R = 𝔪ʳ` for a
Noetherian local ring (`comap_map_adicCompletion`, `Hironaka/Algebra/Local/CompletionCoords.lean`)
and `𝔪_{R̂} = 𝔪 R̂`; the bijective `(R'_{𝔪'})^ → 𝒪̂_{a'}` is an isomorphism of local rings
(`OrdFaithful.of_ringEquiv`); and the completion map `𝒪_{a'} → 𝒪̂_{a'}` is a local homomorphism
(`isLocalHom_algebraMap_adicCompletion`, `OrdFaithful.of_comp`).

Used in `Hironaka/Resolution/Analytic/GoingUp/MaxOrder.lean` (Lemma 61 on manifolds: the order of
the marked transform is bounded at every point over the centre) and in
`Hironaka/Manifold/BlowUp/Transform/StrictSubspaceCompletion.lean`. The statement is not in the
sources.
-/

public section

noncomputable section

open IsLocalRing

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] {n : ℕ} (x : Fin n → R) (r : Fin n)
  {S : Type*} [CommRing S] [IsLocalRing S] [IsRegularLocalRing R] (χ : chartRing x r →+* S)
  [(chartOrigin x r).IsPrime] (hχ : (maximalIdeal S).comap χ = chartOrigin x r)

/-- The completion map of a Noetherian local ring is a local homomorphism: `𝔪_{R̂} = 𝔪 R̂`. -/
theorem isLocalHom_algebraMap_adicCompletion {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] : IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  have := isLocalRing_adicCompletion (R := A)
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr h)
  have hm' : algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
    rw [maximalIdeal_adicCompletion]
    exact Ideal.mem_map_of_mem _ hm
  exact mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hm') ha

/-- The completion map of a Noetherian local ring reflects the powers of the maximal ideal:
`𝔪ʳ R̂ ∩ R = 𝔪ʳ` (`comap_map_adicCompletion`) with `𝔪_{R̂} = 𝔪 R̂`
(`maximalIdeal_adicCompletion`). -/
theorem ordFaithful_algebraMap_adicCompletion {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    haveI := isLocalRing_adicCompletion (R := A)
    OrdFaithful (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  have := isLocalRing_adicCompletion (R := A)
  intro k
  rw [maximalIdeal_adicCompletion, ← Ideal.map_pow, comap_map_adicCompletion]

/-- **The chart-ring local homomorphism reflects orders** (the transport of the bound of
[Kol07, Lemma 61] to the analytic stalk): when the induced map of completions `(R'_{𝔪'})^ → Ŝ` is
bijective, `R'_{𝔪'} → S` reflects the powers of the maximal ideal: `R'_{𝔪'} → (R'_{𝔪'})^` does,
the bijective map of completions is an isomorphism of local rings, and `S → Ŝ` is local. -/
theorem ordFaithful_chartLocalHom [IsNoetherianRing S]
    (hbij : Function.Bijective
      (haveI := isLocalHom_chartLocalHom x r χ hχ; completionMap (chartLocalHom x r χ hχ))) :
    OrdFaithful (chartLocalHom x r χ hχ) := by
  have := isLocalHom_chartLocalHom x r χ hχ
  have := isLocalRing_adicCompletion (R := Localization.AtPrime (chartOrigin x r))
  have := isLocalRing_adicCompletion (R := S)
  have := isLocalHom_algebraMap_adicCompletion (A := S)
  have hg : OrdFaithful (completionMap (chartLocalHom x r χ hχ)) :=
    (OrdFaithful.of_ringEquiv (RingEquiv.ofBijective _ hbij)).congr (RingHom.ext fun _ => rfl)
  have hcomp := (ordFaithful_algebraMap_adicCompletion
    (A := Localization.AtPrime (chartOrigin x r))).comp hg
  have heq : (completionMap (chartLocalHom x r χ hχ)).comp
      (algebraMap (Localization.AtPrime (chartOrigin x r)) _) =
      (algebraMap S (AdicCompletion (maximalIdeal S) S)).comp (chartLocalHom x r χ hχ) := by
    ext z
    simp only [RingHom.comp_apply]
    rw [completionMap_algebraMap]
  exact OrdFaithful.of_comp (hcomp.congr heq)

end IsLocalRing

end
