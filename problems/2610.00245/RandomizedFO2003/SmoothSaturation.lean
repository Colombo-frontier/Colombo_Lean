import RandomizedFO2003.SaturationSlope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

namespace RandomizedFO2003.Primitives

open Set MeasureTheory

/-- Integrating the bounded derivative profile gives an actual smooth
saturation, with exact identity on the prescribed central interval. -/
noncomputable def saturation (K x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, saturationSlope K y

theorem saturation_hasDerivAt (K x : ℝ) : HasDerivAt (saturation K) (saturationSlope K x) x :=
  ((saturationSlope_contDiff K 0).continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem saturation_deriv (K : ℝ) : deriv (saturation K) = saturationSlope K :=
  funext (fun x => (saturation_hasDerivAt K x).deriv)

theorem saturation_contDiff (K : ℝ) (n : ℕ) : ContDiff ℝ n (saturation K) := by
  have hd : Differentiable ℝ (saturation K) := fun x => (saturation_hasDerivAt K x).differentiableAt
  cases n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 from rfl, contDiff_succ_iff_deriv]
    refine ⟨hd, by simp, ?_⟩
    rw [saturation_deriv]
    exact saturationSlope_contDiff K n

@[simp] theorem saturation_zero (K : ℝ) : saturation K 0 = 0 := by simp [saturation]

theorem saturation_eq_self {K x : ℝ} (hK : 0 ≤ K) (hx : |x| ≤ K) : saturation K x = x := by
  calc
    saturation K x = ∫ _y in (0 : ℝ)..x, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      apply saturationSlope_one
      apply abs_le.mpr
      change min 0 x ≤ y ∧ y ≤ max 0 x at hy
      exact ⟨(le_min (by linarith) (abs_le.mp hx).1).trans hy.1,
        hy.2.trans (max_le hK (abs_le.mp hx).2)⟩
    _ = x := by simp

theorem saturation_deriv_bound {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |deriv (saturation K) x| ≤ 1 := by
  rw [saturation_deriv, abs_of_nonneg (saturationSlope_mem K hK x).1]
  exact (saturationSlope_mem K hK x).2

theorem saturation_nonexpansive {K : ℝ} (hK : 0 ≤ K) (x y : ℝ) :
    |saturation K y - saturation K x| ≤ |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_hz : z ∈ (Set.univ : Set ℝ)) => (saturation_hasDerivAt K z).differentiableAt)
    (fun z _ => show ‖deriv (saturation K) z‖ ≤ 1 by simpa only [Real.norm_eq_abs] using saturation_deriv_bound hK z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem saturation_constant_right {K x : ℝ} (hK : 0 ≤ K) (hx : K + 1 ≤ x) :
    saturation K x = saturation K (K + 1) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun z (_hz : z ∈ Ici (K + 1)) => (saturation_hasDerivAt K z).differentiableAt)
    (fun z hz => by rw [saturation_deriv, saturationSlope_zero_right hK hz]; simp)
    (convex_Ici (K + 1)) (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx)
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h

theorem saturation_constant_left {K x : ℝ} (hK : 0 ≤ K) (hx : x ≤ -(K + 1)) :
    saturation K x = saturation K (-(K + 1)) := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun z (_hz : z ∈ Iic (-(K + 1))) => (saturation_hasDerivAt K z).differentiableAt)
    (fun z hz => by rw [saturation_deriv, saturationSlope_zero_left hK hz]; simp)
    (convex_Iic (-(K + 1))) (Set.mem_Iic.mpr le_rfl) (Set.mem_Iic.mpr hx)
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h

theorem saturation_bound {K : ℝ} (hK : 0 ≤ K) (x : ℝ) : |saturation K x| ≤ K + 1 := by
  have hinside (y : ℝ) (hy : |y| ≤ K + 1) : |saturation K y| ≤ K + 1 := by
    have h := saturation_nonexpansive hK 0 y
    simp only [saturation_zero, sub_zero] at h
    exact h.trans hy
  by_cases h : |x| ≤ K + 1
  · exact hinside x h
  · rcases le_total 0 x with hx | hx
    · have hx' : K + 1 ≤ x := by rw [abs_of_nonneg hx] at h; linarith
      rw [saturation_constant_right hK hx']
      exact hinside _ (by rw [abs_of_nonneg (by linarith : 0 ≤ K + 1)])
    · have hx' : x ≤ -(K + 1) := by rw [abs_of_nonpos hx] at h; linarith
      rw [saturation_constant_left hK hx']
      exact hinside _ (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ K + 1)])

/-- Uniform in the saturation radius, for every derivative order at least two. -/
theorem saturation_derivative_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ K x : ℝ, |iteratedDeriv k (saturation K) x| ≤ C := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨C, hC, hbound⟩ := saturationSlope_derivative_bound j (by omega)
  refine ⟨C, hC, ?_⟩
  intro K x
  rw [iteratedDeriv_succ', saturation_deriv]
  exact hbound K x

end RandomizedFO2003.Primitives
