import NCConcave16991.AcceleratedBudgetParameters

/-! # Dimensionless bounds for the actual accelerated loop lengths and radii -/

noncomputable section

namespace NCConcave16991.Accelerated

def quarterScale (p : ProblemParameters) : ℝ := (p.n : ℝ) ^ (1 / 4 : ℝ)

theorem quarterScale_pos (p : ProblemParameters) : 0 < quarterScale p :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.n_pos) _

theorem quarterScale_one_le (p : ProblemParameters) : 1 ≤ quarterScale p :=
  Real.one_le_rpow (by exact_mod_cast p.n_pos) (by norm_num)

theorem quarterScale_sq (p : ProblemParameters) : quarterScale p ^ 2 = Real.sqrt (p.n : ℝ) := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  dsimp [quarterScale]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn, Real.sqrt_eq_rpow]
  norm_num

theorem n_div_quarterScale (p : ProblemParameters) :
    (p.n : ℝ) / quarterScale p = (p.n : ℝ) ^ (3 / 4 : ℝ) := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  dsimp [quarterScale]
  calc
    (p.n : ℝ) / (p.n : ℝ) ^ (1 / 4 : ℝ) = (p.n : ℝ) ^ (1 - (1 / 4 : ℝ)) := by
      rw [Real.rpow_sub hn, Real.rpow_one]
    _ = (p.n : ℝ) ^ (3 / 4 : ℝ) := by norm_num

theorem horizon_upper (τ D δ : ℝ) :
    (horizon τ D δ : ℝ) ≤ 2 + 2 * Real.sqrt (τ * D ^ 2 / δ) := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.sqrt (τ * D ^ 2 / δ) by positivity)
  unfold horizon
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith [Real.sqrt_nonneg (τ * D ^ 2 / δ)]
  · linarith

theorem dualHorizon_bound (p : ProblemParameters) :
    (dualHorizon p : ℝ) ≤ 2 + 34 * dimensionlessB p / quarterScale p := by
  have hQ : 0 < quarterScale p := quarterScale_pos p
  have hB := dimensionlessB_nonneg p
  have ht := dualRegularization_pos p
  have hδ := outerTolerance_pos p
  have hid : dualRegularization p * p.diameter ^ 2 / outerTolerance p =
      288 * dimensionlessB p ^ 2 / quarterScale p ^ 2 := by
    dsimp [dualRegularization, outerTolerance, dimensionlessB]
    rw [← quarterScale_sq p]
    field_simp [p.L_pos.ne', p.epsilon_pos.ne', hQ.ne']
    <;> ring
  have hs : Real.sqrt (dualRegularization p * p.diameter ^ 2 / outerTolerance p) ≤
      17 * dimensionlessB p / quarterScale p := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), hid]
    have hb : 288 * dimensionlessB p ^ 2 ≤ (17 * dimensionlessB p) ^ 2 := by
      nlinarith [sq_nonneg (dimensionlessB p)]
    have hh := div_le_div_of_nonneg_right hb (sq_nonneg (quarterScale p))
    convert hh using 1 <;> ring
  have hh := horizon_upper (dualRegularization p) p.diameter (outerTolerance p)
  change (dualHorizon p : ℝ) ≤ _ at hh
  rw [show 34 * dimensionlessB p / quarterScale p =
    2 * (17 * dimensionlessB p / quarterScale p) by ring]
  linarith

theorem dualHorizon_coarse_bound (p : ProblemParameters) :
    (dualHorizon p : ℝ) ≤ 36 * (1 + dimensionlessB p) := by
  have hQ := quarterScale_one_le p
  have hQp := quarterScale_pos p
  have hB := dimensionlessB_nonneg p
  have hd : dimensionlessB p / quarterScale p ≤ dimensionlessB p := by
    apply (div_le_iff₀ hQp).2
    nlinarith [mul_nonneg hB (sub_nonneg.mpr hQ)]
  have hh := dualHorizon_bound p
  rw [show 34 * dimensionlessB p / quarterScale p =
    34 * (dimensionlessB p / quarterScale p) by ring] at hh
  nlinarith

theorem n_mul_dualHorizon_bound (p : ProblemParameters) :
    (p.n : ℝ) * dualHorizon p ≤
      36 * ((p.n : ℝ) + (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p) := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hB := dimensionlessB_nonneg p
  have hp : 0 ≤ (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p :=
    mul_nonneg (Real.rpow_nonneg hn _) hB
  have hh := mul_le_mul_of_nonneg_left (dualHorizon_bound p) hn
  have hid : (p.n : ℝ) * (2 + 34 * dimensionlessB p / quarterScale p) =
      2 * p.n + 34 * (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p := by
    rw [show (p.n : ℝ) ^ (3 / 4 : ℝ) = (p.n : ℝ) / quarterScale p from (n_div_quarterScale p).symm]
    ring
  rw [hid] at hh
  nlinarith

theorem gapCap_scale (p : ProblemParameters) :
    p.L * gapCap p / p.epsilon ^ 2 = dimensionlessA p + (outerHorizon p : ℝ) / 288 := by
  dsimp [gapCap, outerTolerance, dimensionlessA]
  field_simp [p.L_pos.ne', p.epsilon_pos.ne']
  <;> ring

theorem gapCap_scale_bound (p : ProblemParameters) :
    p.L * gapCap p / p.epsilon ^ 2 ≤ 2 * (1 + dimensionlessA p) := by
  rw [gapCap_scale]
  have hS := (outerHorizon_bounds p).2.2
  have hA := dimensionlessA_pos p
  linarith

theorem publicProductDiameter_scale (p : ProblemParameters) :
    p.L * publicProductDiameter p / p.epsilon =
      6 * Real.sqrt (p.L * gapCap p / p.epsilon ^ 2) + 5 * dimensionlessB p + 2 := by
  have hgap := (gapCap_pos p).le
  have hid : p.L * Real.sqrt (gapCap p / p.L) / p.epsilon =
      Real.sqrt (p.L * gapCap p / p.epsilon ^ 2) := by
    rw [mul_sqrt_div p.L_pos hgap, Real.sqrt_div, Real.sqrt_sq_eq_abs, abs_of_pos p.epsilon_pos]
    exact mul_nonneg p.L_pos.le hgap
  dsimp [publicProductDiameter, publicRadius, dimensionlessB]
  rw [← hid]
  field_simp [p.L_pos.ne', p.epsilon_pos.ne']
  <;> ring

theorem publicProductDiameter_scale_bound (p : ProblemParameters) :
    p.L * publicProductDiameter p / p.epsilon ≤ 20 * (2 + dimensionlessA p + dimensionlessB p) := by
  have hA := (dimensionlessA_pos p).le
  have hB := dimensionlessB_nonneg p
  have hg := gapCap_scale_bound p
  have hg0 : 0 ≤ p.L * gapCap p / p.epsilon ^ 2 := by
    have hL := p.L_pos; have hG := gapCap_pos p; positivity
  have hs : Real.sqrt (p.L * gapCap p / p.epsilon ^ 2) ≤ 2 * (1 + dimensionlessA p) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hg0]
    nlinarith [sq_nonneg (dimensionlessA p)]
  rw [publicProductDiameter_scale]
  linarith

end NCConcave16991.Accelerated
