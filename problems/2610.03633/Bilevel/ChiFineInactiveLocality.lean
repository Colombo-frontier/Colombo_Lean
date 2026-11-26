import Bilevel.ChiFineScaled

/-! Exact unseen-coordinate cancellation for the globally fixed inactive
frontier. No revealed-prefix-dependent sample function is introduced. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainFlatteningMap

theorem physical_flattening_composition (n : ℕ) (ℓ β δ : ℝ)
    (hβ : 0<β) (hδ : 0<δ) (hs : δ ≤ β/16) :
    flatFrontier n ℓ β δ=frontier n ℓ β ∘ flattenMap n δ := by
  funext z
  change ℓ*β^2*flattened n (δ/β) (β⁻¹ • z)=
    ℓ*β^2*centeredResidual n (β⁻¹ • flattenMap n δ z)
  rw [flattened_eq_latent_composition (div_pos hδ hβ)
    ((div_le_iff₀ hβ).mpr (by linarith)),
    ZeroChainFlatteningError.flattenMap_scale_commute n β δ hβ.ne' hδ.ne']

theorem inactive_gradient_coordinate_zero (n : ℕ) (ℓ β δ : ℝ)
    (hβ : 0<β) (hδ : 0<δ) (hs : δ ≤ β/16)
    (z : Space n) (j : Fin (n+1)) (hj : |z j| ≤ δ) :
    gradient (flatFrontier n ℓ β δ) z j=0 := by
  rw [physical_flattening_composition n ℓ β δ hβ hδ hs]
  have hd := ((frontier_contDiff n ℓ β).differentiable (by norm_num) (flattenMap n δ z)).hasFDerivAt.comp z
    ((flattenMap_contDiff n δ).differentiable (by norm_num) z).hasFDerivAt
  rw [ZeroChainResidualLocality.gradient_coordinate_eq hd,ContinuousLinearMap.comp_apply,
    flattenMap_gradient_kills_small δ hδ z j hj,map_zero]

theorem inactive_gradient_support (n r : ℕ) (ℓ β δ : ℝ)
    (hβ : 0<β) (hδ : 0<δ) (hs : δ ≤ β/16)
    (z : Space n) (hz : ∀ j : Fin (n+1),r ≤ j.val → |z j| ≤ δ)
    (j : Fin (n+1)) (hj : r ≤ j.val) : gradient (flatFrontier n ℓ β δ) z j=0 :=
  inactive_gradient_coordinate_zero n ℓ β δ hβ hδ hs z j (hz j hj)

end Bilevel.ChiFine
