import Bilevel.SmallGapInstanceBounds

/-!
# Third derivative bounds for the actual small-gap lift

The compensation term uses a support split: the fine third derivative can
interact with the coarse profile only inside its narrow support. Thus no
spurious `R²/δ` bound is introduced.
-/

noncomputable section
open scoped Topology

namespace Bilevel.SmallGapThirdBounds
open SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport Filter

theorem iteratedDeriv_three (f : ℝ → ℝ) :
    iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [show (3 : ℕ) = (1 + 1) + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_succ, iteratedDeriv_one]

theorem r0_third_bound (S a u : ℝ) (hS : 0 < S) (ha : 0 < a) :
    |deriv (deriv (deriv (r0 S a))) u| ≤ C * S / a := by
  have h := r0_C_bound S a u hS ha 3
  change |iteratedDeriv 3 (r0 S a) u| ≤ C * S * a ^ 2 / a ^ 3 at h
  rw [iteratedDeriv_three] at h
  convert h using 1
  field_simp [ha.ne']
  ring

theorem r1_third_bound (S a u : ℝ) (hS : 0 < S) (ha : 0 < a) :
    |deriv (deriv (deriv (r1 S a))) u| ≤ C * S / a := by
  have h := r1_C_bound S a u hS ha 3
  change |iteratedDeriv 3 (r1 S a) u| ≤ C * S * a ^ 2 / a ^ 3 at h
  rw [iteratedDeriv_three] at h
  convert h using 1
  field_simp [ha.ne']
  ring

theorem normal_third_bound (a u : ℝ) (ha : 0 < a) :
    |deriv (deriv (deriv (normal a))) u| ≤ C / a ^ 2 := by
  have h := normal_C_bound a u ha 3
  change |iteratedDeriv 3 (normal a) u| ≤ C * a / a ^ 3 at h
  rw [iteratedDeriv_three] at h
  convert h using 1
  field_simp [ha.ne']
  ring

/-- Every fine-profile jet vanishes strictly outside its support. -/
theorem r1_iteratedDeriv_zero (S δ u : ℝ) (hδ : 0 < δ) (hu : 34 * δ < |u|) (j : ℕ) :
    iteratedDeriv j (r1 S δ) u = 0 := by
  have he : r1 S δ =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [(continuous_abs.tendsto u).eventually (eventually_gt_nhds hu)] with z hz
    exact r1_zero S δ z hδ hz.le
  have h := he.iteratedDeriv_eq j
  have hz : iteratedDeriv j (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    clear h
    induction j with
    | zero => rw [iteratedDeriv_zero]
    | succ j ih => rw [iteratedDeriv_succ, ih]; funext z; simp
  simpa only [hz] using h

theorem r0_local_bound (S R u : ℝ) (hS : 0 < S) (hR : 0 < R) :
    |r0 S R u| ≤ S * u ^ 2 / 2 := by
  rw [r0, abs_mul, abs_mul, abs_of_pos hS, abs_of_nonneg (sq_nonneg R),
    abs_of_nonneg (phi_nonneg _)]
  have h := mul_le_mul_of_nonneg_left (phi_le_quadratic (u / R))
    (show 0 ≤ S * R ^ 2 by positivity)
  convert h using 1
  field_simp [hR.ne']
  ring

theorem r0_local_deriv_bound (S R u : ℝ) (hS : 0 < S) (hR : 0 < R) :
    |deriv (r0 S R) u| ≤ S * |u| := by
  have hd := r0_iteratedDeriv S R u 1 (by norm_num)
  simp only [iteratedDeriv_one, pow_one] at hd
  rw [hd, phi_deriv]
  have he : S * R ^ 2 / R * (u / R * (1 - SmallGap.septicStep (|u / R| - 1))) =
      S * u * (1 - SmallGap.septicStep (|u / R| - 1)) := by
    field_simp [hR.ne']
    ring
  rw [he, abs_mul, abs_mul, abs_of_pos hS,
    abs_of_nonneg (sub_nonneg.mpr (SmallGap.septicStep_range _).2)]
  have hstep := (SmallGap.septicStep_range (|u / R| - 1)).1
  exact mul_le_of_le_one_right (mul_nonneg hS.le (abs_nonneg u)) (by linarith)

theorem coupling_third_bounds {f : ℝ → ℝ} (S a u s : ℝ) (hS : 0 < S) (ha : 0 < a)
    (hf : |f u| ≤ C * S * a ^ 2 ∧ |deriv f u| ≤ C * S * a ∧
      |deriv (deriv f) u| ≤ C * S)
    (hf3 : |deriv (deriv (deriv f)) u| ≤ C * S / a) :
    |deriv (deriv (deriv f)) u * normal a s| ≤ C ^ 2 * S ∧
    |deriv (deriv f) u * deriv (normal a) s| ≤ C ^ 2 * S ∧
    |deriv f u * deriv (deriv (normal a)) s| ≤ C ^ 2 * S ∧
    |f u * deriv (deriv (deriv (normal a))) s| ≤ C ^ 2 * S := by
  have hq := normal_jet_bounds a s ha
  have hq3 := normal_third_bound a s ha
  have hC := C_pos
  constructor
  · rw [abs_mul]
    convert mul_le_mul hf3 hq.1 (abs_nonneg _) (by positivity) using 1
    field_simp [ha.ne']
    ring
  constructor
  · rw [abs_mul]
    convert mul_le_mul hf.2.2 hq.2.1 (abs_nonneg _) (by positivity) using 1
    ring
  constructor
  · rw [abs_mul]
    convert mul_le_mul hf.2.1 hq.2.2 (abs_nonneg _) (by positivity) using 1
    field_simp [ha.ne']
    ring
  · rw [abs_mul]
    convert mul_le_mul hf.1 hq3 (abs_nonneg _) (by positivity) using 1
    field_simp [ha.ne']
    ring

theorem r0_coupling_third_bounds (S a u s : ℝ) (hS : 0 < S) (ha : 0 < a) :
    |deriv (deriv (deriv (r0 S a))) u * normal a s| ≤ C ^ 2 * S ∧
    |deriv (deriv (r0 S a)) u * deriv (normal a) s| ≤ C ^ 2 * S ∧
    |deriv (r0 S a) u * deriv (deriv (normal a)) s| ≤ C ^ 2 * S ∧
    |r0 S a u * deriv (deriv (deriv (normal a))) s| ≤ C ^ 2 * S :=
  coupling_third_bounds S a u s hS ha (r0_jet_bounds S a u hS ha) (r0_third_bound S a u hS ha)

theorem r1_coupling_third_bounds (S a u s : ℝ) (hS : 0 < S) (ha : 0 < a) :
    |deriv (deriv (deriv (r1 S a))) u * normal a s| ≤ C ^ 2 * S ∧
    |deriv (deriv (r1 S a)) u * deriv (normal a) s| ≤ C ^ 2 * S ∧
    |deriv (r1 S a) u * deriv (deriv (normal a)) s| ≤ C ^ 2 * S ∧
    |r1 S a u * deriv (deriv (deriv (normal a))) s| ≤ C ^ 2 * S :=
  coupling_third_bounds S a u s hS ha (r1_jet_bounds S a u hS ha) (r1_third_bound S a u hS ha)

end Bilevel.SmallGapThirdBounds

namespace Bilevel.SmallGapInstance.Parameters
open SmallGapProfiles SmallGapProfileBounds SmallGapLiftSupport SmallGapThirdBounds

variable (P : Parameters)

theorem residual_deriv3 (ω u : ℝ) :
    deriv (deriv (deriv (P.residual ω))) u =
      deriv (deriv (deriv (r0 P.S P.R))) u -
        ω * deriv (deriv (deriv (r1 P.S P.δ))) u := by
  have he : deriv (deriv (P.residual ω)) = fun v =>
      deriv (deriv (r0 P.S P.R)) v - ω * deriv (deriv (r1 P.S P.δ)) v :=
    funext (P.residual_deriv2 ω)
  rw [he]
  exact ((deriv2_hasDerivAt (r0_contDiff P.S P.R) u).sub
    ((deriv2_hasDerivAt (r1_contDiff P.S P.δ) u).const_mul ω)).deriv

/-- The fine third derivative only meets the coarse profile in its quadratic
region. The global bound therefore scales as `S²(R+δ)`. -/
theorem residual_times_third_bound (ω u : ℝ) (hω : |ω| ≤ 1) :
    |P.residual ω u * deriv (deriv (deriv (P.residual ω))) u| ≤
      1158 * C ^ 2 * P.S ^ 2 * (P.R + P.δ) := by
  have hC := C_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  have hδR : P.δ ≤ P.R := by linarith [P.width]
  have hc3 := r0_third_bound P.S P.R u hS hR
  have hf3 := r1_third_bound P.S P.δ u hS hδ
  by_cases hu : |u| ≤ 34 * P.δ
  · have hu2 : u ^ 2 ≤ (34 * P.δ) ^ 2 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg u) hu, sq_abs u]
    have h0local : |r0 P.S P.R u| ≤ 578 * P.S * P.δ ^ 2 := by
      have hb := r0_local_bound P.S P.R u hS hR
      have hh := mul_le_mul_of_nonneg_left hu2 hS.le
      nlinarith
    have h0 : |r0 P.S P.R u| ≤ 578 * C * P.S * P.δ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right C_one_le
        (show 0 ≤ 578 * P.S * P.δ ^ 2 by positivity)
      nlinarith
    have h1 := (r1_jet_bounds P.S P.δ u hS hδ).1
    have hr : |P.residual ω u| ≤ 579 * C * P.S * P.δ ^ 2 := by
      change |r0 P.S P.R u - ω * r1 P.S P.δ u| ≤ _
      convert abs_signed_sub_le h0 h1 hω using 1
      ring
    have hinv : C * P.S / P.R ≤ C * P.S / P.δ :=
      div_le_div_of_nonneg_left (by positivity) hδ hδR
    have ht : |deriv (deriv (deriv (P.residual ω))) u| ≤ 2 * C * P.S / P.δ := by
      rw [P.residual_deriv3]
      have hh := abs_signed_sub_le hc3 hf3 hω
      calc
        _ ≤ C * P.S / P.R + C * P.S / P.δ := hh
        _ ≤ C * P.S / P.δ + C * P.S / P.δ := add_le_add_right hinv _
        _ = _ := by ring
    calc
      _ = |P.residual ω u| * |deriv (deriv (deriv (P.residual ω))) u| := abs_mul _ _
      _ ≤ (579 * C * P.S * P.δ ^ 2) * (2 * C * P.S / P.δ) :=
        mul_le_mul hr ht (abs_nonneg _) (by positivity)
      _ = 1158 * C ^ 2 * P.S ^ 2 * P.δ := by field_simp [hδ.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hR.le) (by positivity)
  · have hu' : 34 * P.δ < |u| := lt_of_not_ge hu
    have hz0 := r1_zero P.S P.δ u hδ hu'.le
    have hz3 := r1_iteratedDeriv_zero P.S P.δ u hδ hu' 3
    rw [iteratedDeriv_three] at hz3
    have hr : P.residual ω u = r0 P.S P.R u := by simp [residual, hz0]
    have ht : deriv (deriv (deriv (P.residual ω))) u =
        deriv (deriv (deriv (r0 P.S P.R))) u := by
      simp only [P.residual_deriv3, hz3, mul_zero, sub_zero]
    rw [hr, ht, abs_mul]
    calc
      _ ≤ (C * P.S * P.R ^ 2) * (C * P.S / P.R) :=
        mul_le_mul (r0_jet_bounds P.S P.R u hS hR).1 hc3 (abs_nonneg _) (by positivity)
      _ = C ^ 2 * P.S ^ 2 * P.R := by field_simp [hR.ne']; ring
      _ ≤ 1158 * C ^ 2 * P.S ^ 2 * (P.R + P.δ) := by
        have hh : P.R ≤ 1158 * (P.R + P.δ) := by linarith
        convert mul_le_mul_of_nonneg_left hh (show 0 ≤ C ^ 2 * P.S ^ 2 by positivity) using 1
        ring

/-- The third derivative contribution of the squared compensation term. -/
theorem compensation_third_bound (ω u : ℝ) (hω : |ω| ≤ 1) :
    |3 * deriv (P.residual ω) u * deriv (deriv (P.residual ω)) u +
      P.residual ω u * deriv (deriv (deriv (P.residual ω))) u| ≤
      1164 * C ^ 2 * P.S ^ 2 * (P.R + P.δ) := by
  have hC := C_pos
  have hS := P.S_pos
  have hR := P.R_pos
  have hδ := P.δ_pos
  have hj := P.residual_jet_bounds ω u hω
  have hp : |3 * deriv (P.residual ω) u * deriv (deriv (P.residual ω)) u| ≤
      6 * C ^ 2 * P.S ^ 2 * (P.R + P.δ) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hj.2.1 (by norm_num : (0 : ℝ) ≤ 3))
      hj.2.2 (abs_nonneg _) (by positivity)
    convert hh using 1
    ring
  have ht := P.residual_times_third_bound ω u hω
  exact (abs_add _ _).trans (by linarith)

end Bilevel.SmallGapInstance.Parameters
