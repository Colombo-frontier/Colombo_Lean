import Bilevel.SmallGapProfileBounds

/-! Exact support and core estimates used by the three-dimensional clipped lift. -/

noncomputable section
namespace Bilevel.SmallGapLiftSupport

open SmallGapProfiles SmallGapProfileBounds Filter
open scoped Topology

theorem deriv_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (x : ℝ) :
    HasDerivAt (deriv f) (deriv (deriv f) x) x := by
  simpa only [iteratedDeriv_one] using
    (hf.differentiable_iteratedDeriv 1 (by norm_num) x).hasDerivAt

theorem deriv2_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (x : ℝ) :
    HasDerivAt (deriv (deriv f)) (deriv (deriv (deriv f)) x) x := by
  simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] using
    (hf.differentiable_iteratedDeriv 2 (by decide) x).hasDerivAt

theorem normal_deriv_core (a s : ℝ) (ha : 0 < a) (hs : |s| ≤ a / 4) :
    deriv (normal a) s = 1 := by
  have hu := uniqueDiffOn_Icc (by linarith : -(a/4)<a/4)
  have hm : s∈Set.Icc (-(a/4)) (a/4) := abs_le.mp hs
  exact (hu s hm).eq_deriv _
    ((normal_contDiff a ha).differentiable (by norm_num) s).hasDerivAt.hasDerivWithinAt
    ((hasDerivWithinAt_id s _).congr_of_mem
      (fun t ht => normal_core a t ha (abs_le.mpr ht)) hm)

theorem psi_abs_bound (t : ℝ) : |psi t| ≤ 34 := by
  by_cases ht : 34 ≤ |t|
  · rw [psi_support t ht, abs_zero]
    norm_num
  · have hs := SmallGap.septicStep_range ((|t| - 2) / 32)
    rw [psi, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    have hp := mul_nonneg (abs_nonneg t) hs.1
    nlinarith

theorem r0_abs_bound (S R u : ℝ) (hS : 0 ≤ S) : |r0 S R u| ≤ 2 * S * R ^ 2 := by
  rw [r0, abs_mul, abs_mul, abs_of_nonneg hS, abs_of_nonneg (sq_nonneg R),
    abs_of_nonneg (phi_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_left (phi_bounded (u / R))
    (mul_nonneg hS (sq_nonneg R))]

theorem r1_abs_bound (S δ u : ℝ) (hS : 0 ≤ S) : |r1 S δ u| ≤ 34 * S * δ ^ 2 := by
  rw [r1, abs_mul, abs_mul, abs_of_nonneg hS, abs_of_nonneg (sq_nonneg δ)]
  nlinarith [mul_le_mul_of_nonneg_left (psi_abs_bound (u / δ))
    (mul_nonneg hS (sq_nonneg δ))]

theorem r0_core (S R u : ℝ) (hR : 0 < R) (hu : |u| ≤ R) :
    r0 S R u = S * u ^ 2 / 2 := by
  have hh : |u / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).mpr hu
  rw [r0, phi_core _ hh]
  field_simp
  ring

theorem r1_zero (S δ u : ℝ) (hδ : 0 < δ) (hu : 34 * δ ≤ |u|) : r1 S δ u = 0 := by
  have hh : 34 ≤ |u / δ| := by
    rw [abs_div, abs_of_pos hδ]
    exact (le_div_iff₀ hδ).mpr hu
  simp only [r1, psi_support _ hh, mul_zero]

theorem r1_deriv_zero (S δ u : ℝ) (hδ : 0 < δ) (hu : 34 * δ ≤ |u|) :
    deriv (r1 S δ) u = 0 := by
  have hh : 34 ≤ |u / δ| := by
    rw [abs_div, abs_of_pos hδ]
    exact (le_div_iff₀ hδ).mpr hu
  have he := r1_iteratedDeriv S δ u 1 (by norm_num)
  simpa only [iteratedDeriv_one, psi_deriv_zero _ hh, mul_zero] using he

/-- A single positive numerical constant controls every profile jet used below. -/
def C : ℝ := 1 + profileBound 0 + profileBound 1 + profileBound 2 + profileBound 3

theorem C_one_le : 1 ≤ C := by
  have h0 := profileBound_nonneg 0
  have h1 := profileBound_nonneg 1
  have h2 := profileBound_nonneg 2
  have h3 := profileBound_nonneg 3
  dsimp [C]
  linarith

theorem C_pos : 0 < C := lt_of_lt_of_le zero_lt_one C_one_le

theorem profileBound_le_C (j : Fin 4) : profileBound j ≤ C := by
  have h0 := profileBound_nonneg 0
  have h1 := profileBound_nonneg 1
  have h2 := profileBound_nonneg 2
  have h3 := profileBound_nonneg 3
  fin_cases j <;> dsimp [C] <;> linarith

theorem r0_C_bound (S a x : ℝ) (hS : 0 < S) (ha : 0 < a) (j : Fin 4) :
    |iteratedDeriv j.val (r0 S a) x| ≤ C * S * a ^ 2 / a ^ j.val := by
  have hb := r0_bound S a x ha j
  rw [abs_of_pos hS] at hb
  have h := mul_le_mul_of_nonneg_left (profileBound_le_C j)
    (show 0 ≤ S * a ^ 2 / a ^ j.val by positivity)
  convert hb.trans h using 1
  ring

theorem r1_C_bound (S a x : ℝ) (hS : 0 < S) (ha : 0 < a) (j : Fin 4) :
    |iteratedDeriv j.val (r1 S a) x| ≤ C * S * a ^ 2 / a ^ j.val := by
  have hb := r1_bound S a x ha j
  rw [abs_of_pos hS] at hb
  have h := mul_le_mul_of_nonneg_left (profileBound_le_C j)
    (show 0 ≤ S * a ^ 2 / a ^ j.val by positivity)
  convert hb.trans h using 1
  ring

theorem normal_C_bound (a x : ℝ) (ha : 0 < a) (j : Fin 4) :
    |iteratedDeriv j.val (normal a) x| ≤ C * a / a ^ j.val := by
  have hb := normal_bound a x ha j
  have h := mul_le_mul_of_nonneg_left (profileBound_le_C j)
    (show 0 ≤ a / a ^ j.val by positivity)
  convert hb.trans h using 1
  ring

theorem r0_jet_bounds (S a x : ℝ) (hS : 0 < S) (ha : 0 < a) :
    |r0 S a x| ≤ C * S * a ^ 2 ∧
    |deriv (r0 S a) x| ≤ C * S * a ∧
    |deriv (deriv (r0 S a)) x| ≤ C * S := by
  have h0 := r0_C_bound S a x hS ha 0
  have h1 := r0_C_bound S a x hS ha 1
  have h2 := r0_C_bound S a x hS ha 2
  simp only [Fin.val_zero, iteratedDeriv_zero, pow_zero, div_one] at h0
  simp only [Fin.val_one, iteratedDeriv_one, pow_one] at h1
  have he1 : C * S * a ^ 2 / a = C * S * a := by field_simp; ring
  have he2 : C * S * a ^ 2 / a ^ 2 = C * S := by field_simp
  change |iteratedDeriv 2 (r0 S a) x| ≤ C * S * a ^ 2 / a ^ 2 at h2
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h2
  exact ⟨h0, he1 ▸ h1, he2 ▸ h2⟩

theorem r1_jet_bounds (S a x : ℝ) (hS : 0 < S) (ha : 0 < a) :
    |r1 S a x| ≤ C * S * a ^ 2 ∧
    |deriv (r1 S a) x| ≤ C * S * a ∧
    |deriv (deriv (r1 S a)) x| ≤ C * S := by
  have h0 := r1_C_bound S a x hS ha 0
  have h1 := r1_C_bound S a x hS ha 1
  have h2 := r1_C_bound S a x hS ha 2
  simp only [Fin.val_zero, iteratedDeriv_zero, pow_zero, div_one] at h0
  simp only [Fin.val_one, iteratedDeriv_one, pow_one] at h1
  have he1 : C * S * a ^ 2 / a = C * S * a := by field_simp; ring
  have he2 : C * S * a ^ 2 / a ^ 2 = C * S := by field_simp
  change |iteratedDeriv 2 (r1 S a) x| ≤ C * S * a ^ 2 / a ^ 2 at h2
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h2
  exact ⟨h0, he1 ▸ h1, he2 ▸ h2⟩

theorem normal_jet_bounds (a x : ℝ) (ha : 0 < a) :
    |normal a x| ≤ C * a ∧ |deriv (normal a) x| ≤ C ∧
    |deriv (deriv (normal a)) x| ≤ C / a := by
  have h0 := normal_C_bound a x ha 0
  have h1 := normal_C_bound a x ha 1
  have h2 := normal_C_bound a x ha 2
  simp only [Fin.val_zero, iteratedDeriv_zero, pow_zero, div_one] at h0
  simp only [Fin.val_one, iteratedDeriv_one, pow_one] at h1
  have he1 : C * a / a = C := by field_simp
  have he2 : C * a / a ^ 2 = C / a := by field_simp; ring
  change |iteratedDeriv 2 (normal a) x| ≤ C * a / a ^ 2 at h2
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one] at h2
  exact ⟨h0, he1 ▸ h1, he2 ▸ h2⟩

theorem abs_signed_sub_le {a b A B ω : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hω : |ω| ≤ 1) : |a - ω * b| ≤ A + B := by
  have hw : |ω * b| ≤ |b| := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hω (abs_nonneg b)]
  exact (abs_sub a (ω * b)).trans (add_le_add ha (hw.trans hb))

theorem coupling_jet_bounds {f : ℝ → ℝ} (S a u s : ℝ) (hS : 0 < S) (ha : 0 < a)
    (hf : |f u| ≤ C * S * a ^ 2 ∧ |deriv f u| ≤ C * S * a ∧
      |deriv (deriv f) u| ≤ C * S) :
    |deriv (deriv f) u * normal a s| ≤ C ^ 2 * S * a ∧
    |deriv f u * deriv (normal a) s| ≤ C ^ 2 * S * a ∧
    |f u * deriv (deriv (normal a)) s| ≤ C ^ 2 * S * a := by
  have hq := normal_jet_bounds a s ha
  have hC := C_pos
  constructor
  · rw [abs_mul]
    convert mul_le_mul hf.2.2 hq.1 (abs_nonneg _) (by positivity) using 1
    ring
  constructor
  · rw [abs_mul]
    convert mul_le_mul hf.2.1 hq.2.1 (abs_nonneg _) (by positivity) using 1
    ring
  · rw [abs_mul]
    convert mul_le_mul hf.1 hq.2.2 (abs_nonneg _) (by positivity) using 1
    field_simp
    ring

end Bilevel.SmallGapLiftSupport
