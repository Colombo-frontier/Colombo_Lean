import NCConcave16991.AcceleratedBudgetLog

/-! # Explicit all-regime query budget of the actual accelerated solver -/

noncomputable section

namespace NCConcave16991.Accelerated

theorem proximal_condition_ratio (p : ProblemParameters) :
    (4 * p.L) ^ 2 / dualRegularization p ^ 2 = 16 * (p.n : ℝ) := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  dsimp [dualRegularization]
  rw [div_pow]
  field_simp [p.L_pos.ne', (Real.sqrt_pos.mpr hnpos).ne']
  rw [Real.sq_sqrt hn]
  <;> ring

/-- Each actual residual engine has O(n log(2+n+A+B)) original component calls. -/
theorem publicResidualBudget_bound (p : ProblemParameters) :
    (publicResidualBudget p : ℝ) ≤ (2 : ℝ) ^ 22 * (p.n : ℝ) * complexityLog p := by
  letI : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩
  have hn : (1 : ℝ) ≤ p.n := by exact_mod_cast p.n_pos
  have hn0 : (0 : ℝ) ≤ p.n := by positivity
  have hℓ := complexityLog_one_le_public p
  have hJ := publicSolverEpochs_bound p
  have hlog6 : Real.log 6 ≤ 5 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 6)
    norm_num at hh
    exact hh
  have heq : 24 * (4 * p.L) ^ 2 * Real.log 6 / dualRegularization p ^ 2 =
      384 * (p.n : ℝ) * Real.log 6 := by
    calc
      _ = 24 * ((4 * p.L) ^ 2 / dualRegularization p ^ 2) * Real.log 6 := by ring
      _ = _ := by rw [proximal_condition_ratio]; ring
  have hinner : (p.n : ℝ) + 24 * (4 * p.L) ^ 2 * Real.log 6 / dualRegularization p ^ 2 + 2 ≤
      1923 * (p.n : ℝ) := by
    rw [heq]
    nlinarith only [hn, hn0, mul_le_mul_of_nonneg_left hlog6 hn0]
  have hbase := SVRG.residualQueryBudget_bound (n := p.n)
    (by linarith [p.L_pos] : 0 < 4 * p.L) (dualRegularization_pos p) (publicSolverEpochs p)
  have hm := mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg (publicSolverEpochs p) : (0 : ℝ) ≤ publicSolverEpochs p)
  have hj := mul_le_mul_of_nonneg_right hJ (show 0 ≤ 1923 * (p.n : ℝ) by positivity)
  have hh := mul_le_mul_of_nonneg_left hℓ (show 0 ≤ 2 * (p.n : ℝ) by positivity)
  have hpos : 0 ≤ (p.n : ℝ) * complexityLog p := mul_nonneg hn0 (by linarith)
  change (publicResidualBudget p : ℝ) ≤ _ at hbase
  norm_num at hm hj hh ⊢
  nlinarith only [hbase, hm, hj, hh, hpos]

/-- The actual prescribed integer loops satisfy the accelerated rate from
Theorem 3.2, including initialization, natural ceilings and the single log. -/
theorem publicAcceleratedBudget_bound (p : ProblemParameters) :
    (publicAcceleratedBudget p : ℝ) ≤ (2 : ℝ) ^ 48 * (1 + dimensionlessA p) *
      ((p.n : ℝ) + (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p) * complexityLog p := by
  let W := (p.n : ℝ) + (p.n : ℝ) ^ (3 / 4 : ℝ) * dimensionlessB p
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hW : 0 ≤ W := add_nonneg hn
    (mul_nonneg (Real.rpow_nonneg hn _) (dimensionlessB_nonneg p))
  have hA : 0 ≤ 1 + dimensionlessA p := by linarith [dimensionlessA_pos p]
  have hℓ : 0 ≤ complexityLog p := le_trans (by norm_num) (complexityLog_one_le_public p)
  have hS := (outerHorizon_bounds p).2.2
  have hNK := n_mul_dualHorizon_bound p
  have hR := publicResidualBudget_bound p
  have hSK := mul_le_mul hS hNK
    (mul_nonneg hn (Nat.cast_nonneg (dualHorizon p) : (0 : ℝ) ≤ dualHorizon p))
    (show 0 ≤ 97 * (1 + dimensionlessA p) by positivity)
  have h1 := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ (outerHorizon p : ℝ) * dualHorizon p by positivity)
  have h2 := mul_le_mul_of_nonneg_right hSK (show 0 ≤ (2 : ℝ) ^ 22 * complexityLog p by positivity)
  have h3 : 0 ≤ (1 + dimensionlessA p) * W * complexityLog p :=
    mul_nonneg (mul_nonneg hA hW) hℓ
  simp only [publicAcceleratedBudget, Nat.cast_mul]
  change _ ≤ (2 : ℝ) ^ 48 * (1 + dimensionlessA p) * W * complexityLog p
  norm_num at h1 h2 ⊢
  nlinarith only [h1, h2, h3]

end NCConcave16991.Accelerated
