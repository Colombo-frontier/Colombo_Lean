import NCConcave16991.WeakConvexity
import NCConcave16991.MoreauEnvelope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Appendix A.3: transfer between smooth and Moreau stationarity -/

open Set InnerProductSpace
open scoped InnerProductSpace

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem smooth_proximal_optimality {F : E → ℝ} {g : E} {L : ℝ} {c p : E}
    (hf : HasGradientAt F g p) (hp : IsProxPoint F L c p) :
    g = proxResidual L c p := by
  have hnorm := ((hasFDerivAt_id (𝕜 := ℝ) p).sub_const c).norm_sq
  have hderiv := hf.hasFDerivAt.add (hnorm.const_mul L)
  have hm : IsLocalMin (F + fun x ↦ L * ‖x - c‖ ^ 2) p :=
    Filter.Eventually.of_forall hp
  have hzero := hm.hasFDerivAt_eq_zero hderiv
  have hmap : (toDual ℝ E) (g + (2 * L) • (p - c)) = 0 := by
    convert hzero using 1
    ext v
    simp only [map_add, map_smul, add_apply,
      smul_apply, toDual_apply_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      innerSL_apply_apply, id_eq]
    ring
  have hv : g + (2 * L) • (p - c) = 0 :=
    (toDual ℝ E).injective (by simpa using hmap)
  dsimp [proxResidual]
  have hneg : (2 * L) • (p - c) = -((2 * L) • (c - p)) := by module
  rw [hneg] at hv
  apply sub_eq_zero.mp
  simpa only [sub_eq_add_neg] using hv

theorem smooth_moreau_residual_comparison {F : E → ℝ} {G : E → E} {L : ℝ}
    (hL : 0 ≤ L) (hf : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    {c p : E} (hp : IsProxPoint F L c p) :
    (1 / 2 : ℝ) * ‖proxResidual L c p‖ ≤ ‖G c‖ ∧
      ‖G c‖ ≤ (3 / 2 : ℝ) * ‖proxResidual L c p‖ := by
  have hopt := smooth_proximal_optimality (hf p) hp
  have hnorm : ‖proxResidual L c p‖ = 2 * L * ‖c - p‖ := by
    simp only [proxResidual, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ 2 * L by positivity)]
  have h2 : ‖G c‖ ≤ ‖G c - G p‖ + ‖G p‖ := by
    calc
      ‖G c‖ = ‖G c - G p + G p‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h3 : ‖G p‖ ≤ ‖G c - G p‖ + ‖G c‖ := by
    calc
      ‖G p‖ = ‖G c - (G c - G p)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖G c‖ + ‖G c - G p‖ := norm_sub_le _ _
      _ = _ := by ring
  have h4 := hG c p
  rw [hopt] at h2 h3 h4
  constructor <;> nlinarith

/-- The actual gradients of the smooth objective and its infimum-defined
Moreau envelope satisfy both constant-factor inequalities. -/
theorem smooth_gradient_moreau_comparison [ProperSpace E]
    {F : E → ℝ} {G : E → E} {L : ℝ}
    (hL : 0 < L) (hf : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hb : BddBelow (range F)) (c : E) :
    (1 / 2 : ℝ) * ‖gradient (moreauEnvelope F L) c‖ ≤ ‖gradient F c‖ ∧
      ‖gradient F c‖ ≤ (3 / 2 : ℝ) * ‖gradient (moreauEnvelope F L) c‖ := by
  have hcont : Continuous F := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  have hw := weaklyConvex_of_lipschitz_gradient hL.le hf hG
  have he := moreauEnvelope_gradient_formula hL hcont hb hw c
  rw [he.gradient, (hf c).gradient]
  exact smooth_moreau_residual_comparison hL.le hf hG (proximalMap_spec hL hcont hb c)

end NCConcave16991
