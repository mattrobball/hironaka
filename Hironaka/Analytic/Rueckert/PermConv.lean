/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Analytic.Rueckert.Embed
public import Hironaka.Analytic.Germ.Coordinate
import Mathlib.Tactic.Positivity.Finset

/-!
# Permuting the variables of a convergent series

The Weierstrass division divides with respect to the first variable `x_0`. To divide with
respect to an arbitrary fibre variable `x_i` (the division argument of [Fre17, Ch. I, 8.3] in
`FibreDivision.lean`), the coordinates are permuted: for a permutation `τ` of `Fin n`,
`permConv τ` is the `K`-algebra automorphism `f(x) ↦ f(x_{τ 0}, …, x_{τ (n-1)})` of `Conv K n`
(the renaming `convEmbed` of `Embed.lean` along the bijection `τ`). It sends the coordinate
series `X_i` to `X_{τ i}` and a series embedded from the base along `e` to the series embedded
along `τ ∘ e`; its inverse is `permConv τ⁻¹`.
-/

@[expose] public section

open MvPowerSeries

namespace Analytic

variable {K : Type*} [RCLike K] {n d : ℕ}

/-- Renaming along a permutation and then along its inverse is the identity on `Conv K n`
(`rename_rename` and `rename_id`, through the instance-carrying `rename`). -/
theorem convEmbed_toEmbedding_symm_apply (τ : Equiv.Perm (Fin n)) (f : Conv K n) :
    convEmbed K τ.toEmbedding (convEmbed K τ.symm.toEmbedding f) = f := by
  apply Subtype.ext
  rw [coe_convEmbed, coe_convEmbed]
  rw [MvPowerSeries.rename_rename]
  have key : ∀ (φ : Fin n → Fin n) [Filter.TendstoCofinite φ], φ = id →
      MvPowerSeries.rename φ f.1 = f.1 := by
    intro φ _ hφ
    subst hφ
    rw [MvPowerSeries.rename_id]
    rfl
  exact key _ (by funext x; change τ (τ.symm x) = x; exact τ.apply_symm_apply x)

variable (K) in
/-- The `K`-algebra automorphism of `Conv K n` permuting the variables along `τ`,
`f(x) ↦ f(x_{τ 0}, …, x_{τ (n-1)})`: `convEmbed` along the bijection `τ`, with inverse the
embedding along `τ⁻¹`. -/
noncomputable def permConv (τ : Equiv.Perm (Fin n)) : Conv K n ≃ₐ[K] Conv K n :=
  AlgEquiv.ofAlgHom (convEmbed K τ.toEmbedding) (convEmbed K τ.symm.toEmbedding)
    (AlgHom.ext fun f => convEmbed_toEmbedding_symm_apply τ f)
    (AlgHom.ext fun f => by
      have := convEmbed_toEmbedding_symm_apply τ.symm f
      rwa [Equiv.symm_symm] at this)

theorem permConv_apply (τ : Equiv.Perm (Fin n)) (f : Conv K n) :
    permConv K τ f = convEmbed K τ.toEmbedding f := rfl

theorem permConv_symm_apply (τ : Equiv.Perm (Fin n)) (f : Conv K n) :
    (permConv K τ).symm f = convEmbed K τ.symm.toEmbedding f := rfl

/-- `permConv τ` sends the coordinate series `X_i` to `X_{τ i}`. -/
theorem permConv_convX (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    permConv K τ (convX K i) = convX K (τ i) := by
  apply Subtype.ext
  rw [permConv_apply, coe_convEmbed, coe_convX, coe_convX]
  exact MvPowerSeries.rename_X _ _

/-- `permConv τ` sends a series embedded from the base along `e` to the series embedded along
`τ ∘ e`. -/
theorem permConv_convEmbed (τ : Equiv.Perm (Fin n)) (e : Fin d ↪ Fin n) (a : Conv K d) :
    permConv K τ (convEmbed K e a) = convEmbed K (e.trans τ.toEmbedding) a := by
  apply Subtype.ext
  rw [permConv_apply, coe_convEmbed, coe_convEmbed, coe_convEmbed]
  change MvPowerSeries.rename ⇑τ.toEmbedding (MvPowerSeries.rename ⇑e a.1) =
    MvPowerSeries.rename (⇑τ.toEmbedding ∘ ⇑e) a.1
  rw [MvPowerSeries.rename_rename]

/-- The inverse automorphism is the one of the inverse permutation. -/
theorem permConv_symm (τ : Equiv.Perm (Fin n)) : (permConv K τ).symm = permConv K τ.symm :=
  AlgEquiv.ext fun _ => rfl

end Analytic
