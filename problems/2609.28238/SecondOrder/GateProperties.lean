import SecondOrder.GlobalSmoothstep
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace SecondOrder
noncomputable section

theorem gateFirst_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : gateFirst x = gateD1 x :=
  unitClipped_eq_of_mem _ hx

theorem gateSecond_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : gateSecond x = gateD2 x :=
  unitClipped_eq_of_mem _ hx

theorem gateThird_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : gateThird x = gateD3 x :=
  unitClipped_eq_of_mem _ hx

theorem gate_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) : gate x = gatePoly x := by
  rw [gate_eq_unitClipped]
  exact unitClipped_eq_of_mem _ hx

theorem gate_flat_left {x : ℝ} (hx : x ≤ 0) :
    gate x = 0 ∧ gateFirst x = 0 ∧ gateSecond x = 0 ∧ gateThird x = 0 := by
  simp [gate, gateFirst, gateSecond, gateThird, unitClipped, joinAt, hx, gateD1, gateD2, gateD3]

theorem gate_flat_right {x : ℝ} (hx : 1 ≤ x) :
    gate x = 1 ∧ gateFirst x = 0 ∧ gateSecond x = 0 ∧ gateThird x = 0 := by
  by_cases he : x = 1
  · subst x
    norm_num [gate, gateFirst, gateSecond, gateThird, unitClipped, joinAt, gateD1, gateD2, gateD3]
  · have h0 : ¬x ≤ 0 := by linarith
    have h1 : ¬x ≤ 1 := not_le.mpr (lt_of_le_of_ne hx (Ne.symm he))
    simp [gate, gateFirst, gateSecond, gateThird, unitClipped, joinAt, hx, h0, h1, gateD1, gateD2, gateD3]

theorem gateFirst_nonneg (x : ℝ) : 0 ≤ gateFirst x := by
  change 0 ≤ unitClipped gateD1 x
  rw [unitClipped_eq_comp]
  have hx := unitClip_mem x
  dsimp [Function.comp_def, gateD1]
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hx.1 3)) (pow_nonneg (sub_nonneg.mpr hx.2) 3)

theorem gateSecond_nonneg {x : ℝ} (hx : x ≤ 1/2) : 0 ≤ gateSecond x := by
  by_cases h0 : x ≤ 0
  · rw [(gate_flat_left h0).2.2.1]
  · rw [gateSecond_eq_poly ⟨le_of_not_ge h0, by linarith⟩]
    exact (gate_derivatives_nonnegative (le_of_not_ge h0) hx).2

theorem gate_monotone : Monotone gate :=
  monotone_of_hasDerivAt_nonneg gate_hasDerivAt gateFirst_nonneg

theorem gate_convex_half : ConvexOn ℝ (Set.Icc (0:ℝ) (1/2)) gate := by
  apply convexOn_of_deriv2_nonneg' (convex_Icc _ _)
    (fun x _ => (gate_hasDerivAt x).differentiableAt.differentiableWithinAt)
  · rw [deriv_gate]
    exact fun x _ => (gateFirst_hasDerivAt x).differentiableAt.differentiableWithinAt
  · intro x hx
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, deriv_gate, deriv_gateFirst]
      using gateSecond_nonneg hx.2

theorem gate_half : gate (1/2) = 1/2 := by
  rw [gate_eq_poly (by constructor <;> norm_num)]
  norm_num [gatePoly]

/-- The Fisher-type control is for the derivative of the global piecewise gate. -/
theorem gate_fisher (x : ℝ) : (deriv gate x)^2 ≤ 1225*gate x*(1-gate x) := by
  rw [deriv_gate, gate_eq_unitClipped]
  change (unitClipped gateD1 x)^2 ≤ 1225*unitClipped gatePoly x*(1-unitClipped gatePoly x)
  simp only [unitClipped_eq_comp, Function.comp_apply]
  exact gate_fisher_polynomial (unitClip_mem x).1 (unitClip_mem x).2

theorem gateD1_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖gateD1 t‖ ≤ 140 := by
  have ha : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hb : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  calc
    ‖gateD1 t‖ = 140*|t|^3*|1-t|^3 := by simp [gateD1, abs_mul, abs_pow]
    _ ≤ 140*1^3*1^3 := by gcongr
    _ = 140 := by norm_num

theorem gateD2_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖gateD2 t‖ ≤ 420 := by
  have ha : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hb : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hc : |1-2*t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  calc
    ‖gateD2 t‖ = 420*|t|^2*|1-t|^2*|1-2*t| := by simp [gateD2, abs_mul, abs_pow]
    _ ≤ 420*1^2*1^2*1 := by gcongr
    _ = 420 := by norm_num

theorem gateD3_bound {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖gateD3 t‖ ≤ 9240 := by
  have ha : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hb : |1-t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have ht2 : |t^2| ≤ 1 := by simpa only [abs_pow, one_pow] using pow_le_pow_left₀ (abs_nonneg t) ha 2
  have hc : |1-5*t+5*t^2| ≤ 11 := by
    have hp := (abs_add (1-5*t) (5*t^2)).trans (add_le_add_right (abs_sub (1:ℝ) (5*t)) _)
    simp only [abs_mul, abs_one, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 5)] at hp
    linarith
  calc
    ‖gateD3 t‖ = 840*|t| *|1-t| *|1-5*t+5*t^2| := by simp [gateD3, abs_mul]
    _ ≤ 840*1*1*11 := by gcongr
    _ = 9240 := by norm_num

theorem gate_derivative_bounds (x : ℝ) :
    ‖deriv gate x‖ ≤ 140 ∧ ‖deriv (deriv gate) x‖ ≤ 420 ∧
      ‖deriv (deriv (deriv gate)) x‖ ≤ 9240 := by
  rw [deriv_gate, deriv_gateFirst, deriv_gateSecond]
  simp only [gateFirst, gateSecond, gateThird,
    unitClipped_eq_comp, Function.comp_apply]
  exact ⟨gateD1_bound (unitClip_mem x), gateD2_bound (unitClip_mem x), gateD3_bound (unitClip_mem x)⟩

theorem gate_iteratedFDeriv_two_bound (x : ℝ) : ‖iteratedFDeriv ℝ 2 gate x‖ ≤ 420 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (gate_derivative_bounds x).2.1

theorem gate_iteratedFDeriv_three_bound (x : ℝ) : ‖iteratedFDeriv ℝ 3 gate x‖ ≤ 9240 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using (gate_derivative_bounds x).2.2

theorem gate_strictMonoOn : StrictMonoOn gate (Set.Icc (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) gate_contDiff_three.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_gate, gateFirst_eq_poly ⟨hx.1.le, hx.2.le⟩]
  unfold gateD1
  exact mul_pos (mul_pos (by norm_num) (pow_pos hx.1 3)) (pow_pos (sub_pos.mpr hx.2) 3)

theorem gate_gt_half {x : ℝ} (hx : 1/2 < x) : 1/2 < gate x := by
  by_cases h1 : x ≤ 1
  · rw [← gate_half]
    exact gate_strictMonoOn (by constructor <;> norm_num) ⟨by linarith, h1⟩ hx
  · rw [(gate_flat_right (le_of_not_ge h1)).1]
    norm_num

end
end SecondOrder
