import RandomizedFO2003.SmoothGate

namespace RandomizedFO2003.Primitives

/-- A smooth derivative profile equal to one on `[-K,K]`, between zero and
one everywhere, and zero outside a fixed-width enlargement of that interval. -/
noncomputable def saturationSlope (K x : ℝ) : ℝ :=
  1 - (gate (x + (-K + 1 / 4)) + gate (-x + (-K + 1 / 4)))

theorem saturationSlope_contDiff (K : ℝ) (n : ℕ) : ContDiff ℝ n (saturationSlope K) :=
  contDiff_const.sub (((gate_contDiff n).comp (contDiff_id.add contDiff_const)).add
    ((gate_contDiff n).comp (contDiff_id.neg.add contDiff_const)))

theorem saturationSlope_mem (K : ℝ) (hK : 0 ≤ K) (x : ℝ) :
    0 ≤ saturationSlope K x ∧ saturationSlope K x ≤ 1 := by
  rcases le_total x 0 with hx | hx
  · have hg : gate (x + (-K + 1 / 4)) = 0 := gate_zero_of_le (by linarith)
    dsimp only [saturationSlope]
    rw [hg, zero_add]
    constructor <;> linarith [gate_nonneg (-x + (-K + 1 / 4)), gate_le_one (-x + (-K + 1 / 4))]
  · have hg : gate (-x + (-K + 1 / 4)) = 0 := gate_zero_of_le (by linarith)
    dsimp only [saturationSlope]
    rw [hg, add_zero]
    constructor <;> linarith [gate_nonneg (x + (-K + 1 / 4)), gate_le_one (x + (-K + 1 / 4))]

theorem saturationSlope_one {K x : ℝ} (hx : |x| ≤ K) : saturationSlope K x = 1 := by
  have h := abs_le.mp hx
  have hl := gate_zero_of_le (x := x + (-K + 1 / 4)) (by linarith)
  have hr := gate_zero_of_le (x := -x + (-K + 1 / 4)) (by linarith)
  simp only [saturationSlope, hl, hr]
  norm_num

theorem saturationSlope_zero_right {K x : ℝ} (hK : 0 ≤ K) (hx : K + 1 ≤ x) :
    saturationSlope K x = 0 := by
  have hl := gate_one_of_le (x := x + (-K + 1 / 4)) (by linarith)
  have hr := gate_zero_of_le (x := -x + (-K + 1 / 4)) (by linarith)
  simp only [saturationSlope, hl, hr]
  norm_num

theorem saturationSlope_zero_left {K x : ℝ} (hK : 0 ≤ K) (hx : x ≤ -(K + 1)) :
    saturationSlope K x = 0 := by
  have hl := gate_zero_of_le (x := x + (-K + 1 / 4)) (by linarith)
  have hr := gate_one_of_le (x := -x + (-K + 1 / 4)) (by linarith)
  simp only [saturationSlope, hl, hr]
  norm_num

theorem saturationSlope_iteratedDeriv (k : ℕ) (hk : 0 < k) (K x : ℝ) :
    iteratedDeriv k (saturationSlope K) x =
      -(iteratedDeriv k gate (x + (-K + 1 / 4)) +
        (-1 : ℝ) ^ k * iteratedDeriv k gate (-x + (-K + 1 / 4))) := by
  change iteratedDeriv k (fun y => 1 -
    (gate (y + (-K + 1 / 4)) + gate (-y + (-K + 1 / 4)))) x = _
  rw [iteratedDeriv_const_sub hk]
  change iteratedDeriv k (fun y => -(gate (y + (-K + 1 / 4)) + gate (-y + (-K + 1 / 4)))) x = _
  rw [iteratedDeriv_neg]
  change -(iteratedDeriv k ((fun y => gate (y + (-K + 1 / 4))) +
    (fun y => gate (-y + (-K + 1 / 4)))) x) = _
  have hl : ContDiffAt ℝ k (fun y : ℝ => gate (y + (-K + 1 / 4))) x :=
    ((gate_contDiff k).comp (contDiff_id.add contDiff_const)).contDiffAt
  have hr : ContDiffAt ℝ k (fun y : ℝ => gate (-y + (-K + 1 / 4))) x :=
    ((gate_contDiff k).comp (contDiff_id.neg.add contDiff_const)).contDiffAt
  rw [iteratedDeriv_add hl hr]
  rw [iteratedDeriv_comp_add_const]
  have hr := iteratedDeriv_comp_neg k (fun y : ℝ => gate (y + (-K + 1 / 4))) x
  rw [iteratedDeriv_comp_add_const] at hr
  rw [hr]
  rfl

/-- Uniform derivative constants are inherited from the one fixed gate. They
are chosen before `K`, so increasing the saturation radius does not change them. -/
theorem saturationSlope_derivative_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ K x : ℝ, |iteratedDeriv k (saturationSlope K) x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := gate_derivative_bound k hk
  refine ⟨2 * C, by positivity, ?_⟩
  intro K x
  rw [saturationSlope_iteratedDeriv k (by omega), abs_neg]
  calc
    _ ≤ |iteratedDeriv k gate (x + (-K + 1 / 4))| +
        |(-1 : ℝ) ^ k * iteratedDeriv k gate (-x + (-K + 1 / 4))| := abs_add _ _
    _ = |iteratedDeriv k gate (x + (-K + 1 / 4))| +
        |iteratedDeriv k gate (-x + (-K + 1 / 4))| := by simp [abs_mul, abs_pow]
    _ ≤ C + C := add_le_add (hbound _) (hbound _)
    _ = 2 * C := by ring

end RandomizedFO2003.Primitives
