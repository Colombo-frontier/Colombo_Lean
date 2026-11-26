import NCConcave16991.Moreau
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Differentiability of the actual minimized Moreau value -/

open Set Filter Asymptotics
open scoped InnerProductSpace Topology

namespace NCConcave16991

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem proxPoint_lipschitz {f : E → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : WeaklyConvex L f) {c d p q : E}
    (hp : IsProxPoint f L c p) (hq : IsProxPoint f L d q) :
    ‖p - q‖ ≤ 2 * ‖c - d‖ := by
  have h1 := strongConvex_min_growth (weaklyConvex_prox_strong hf c) hp q
  have h2 := strongConvex_min_growth (weaklyConvex_prox_strong hf d) hq p
  rw [norm_sub_rev q p] at h2
  have hid : ‖q - c‖ ^ 2 + ‖p - d‖ ^ 2 - ‖p - c‖ ^ 2 - ‖q - d‖ ^ 2 =
      2 * ⟪p - q, c - d⟫_ℝ := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    ring
  dsimp [proxObjective] at h1 h2
  have hsqL : L * ‖p - q‖ ^ 2 ≤ L * (2 * ⟪p - q, c - d⟫_ℝ) := by
    rw [← hid]
    linarith
  have hsq := (mul_le_mul_iff_right₀ hL).mp hsqL
  have hip := real_inner_le_norm (p - q) (c - d)
  nlinarith [norm_nonneg (p - q), norm_nonneg (c - d)]

def minimizedValue (f : E → ℝ) (L : ℝ) (P : E → E) (c : E) : ℝ :=
  proxObjective f L c (P c)

/-- A global quadratic error bound establishes the derivative of the envelope. -/
theorem minimizedValue_error {f : E → ℝ} {L : ℝ} {P : E → E}
    (hL : 0 < L) (hf : WeaklyConvex L f)
    (hP : ∀ c, IsProxPoint f L c (P c)) (c d : E) :
    |minimizedValue f L P d - minimizedValue f L P c -
      ⟪proxResidual L c (P c), d - c⟫_ℝ| ≤ 5 * L * ‖d - c‖ ^ 2 := by
  have hu := hP d (P c)
  have hl := hP c (P d)
  have hprox := proxPoint_lipschitz hL hf (hP d) (hP c)
  have he1 : ‖P c - d‖ ^ 2 - ‖P c - c‖ ^ 2 =
      2 * ⟪c - P c, d - c⟫_ℝ + ‖d - c‖ ^ 2 := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm c d]
    ring
  have he2 : ‖P d - d‖ ^ 2 - ‖P d - c‖ ^ 2 =
      2 * ⟪c - P c, d - c⟫_ℝ + ‖d - c‖ ^ 2 -
        2 * ⟪P d - P c, d - c⟫_ℝ := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm c d]
    ring
  have hip := real_inner_le_norm (P d - P c) (d - c)
  have hip' : ⟪P d - P c, d - c⟫_ℝ ≤ 2 * ‖d - c‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hprox (norm_nonneg (d - c))]
  have hi : ⟪proxResidual L c (P c), d - c⟫_ℝ =
      2 * L * ⟪c - P c, d - c⟫_ℝ := by
    simp [proxResidual, real_inner_smul_left]
  apply abs_le.mpr
  dsimp [minimizedValue, proxObjective] at *
  rw [hi]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hip' hL.le
    have he2L := congrArg (fun v : ℝ ↦ L * v) he2
    nlinarith [sq_nonneg ‖d - c‖]
  · have he1L := congrArg (fun v : ℝ ↦ L * v) he1
    nlinarith [mul_nonneg hL.le (sq_nonneg ‖d - c‖)]

theorem minimizedValue_hasGradientAt [CompleteSpace E]
    {f : E → ℝ} {L : ℝ} {P : E → E}
    (hL : 0 < L) (hf : WeaklyConvex L f)
    (hP : ∀ c, IsProxPoint f L c (P c)) (c : E) :
    HasGradientAt (minimizedValue f L P) (proxResidual L c (P c)) c := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have ho : (fun h : E ↦ minimizedValue f L P (c + h) - minimizedValue f L P c -
      ⟪proxResidual L c (P c), h⟫_ℝ) =O[𝓝 0] (fun h : E ↦ ‖h‖ ^ 2) := by
    apply isBigO_iff.mpr
    refine ⟨5 * L, Filter.Eventually.of_forall fun h ↦ ?_⟩
    have hh := minimizedValue_error hL hf hP c (c + h)
    simpa only [add_sub_cancel_left, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖h‖)] using hh
  exact ho.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < 2))

end NCConcave16991
