import SampleReuse.RandomFrameProbability

noncomputable section
namespace SampleReuse.RandomFrame

def sphereDimension (m N : ℕ) (R t δ : ℝ) : ℕ :=
  m + N + ⌈2 * R^2 * Real.log (2*(m:ℝ)*(N+1)/δ) / t^2⌉₊

theorem sphereDimension_ge_frame (m N : ℕ) (R t δ : ℝ) :
    m ≤ sphereDimension m N R t δ := by unfold sphereDimension; omega

theorem sphereDimension_budget (m N : ℕ) (R : ℝ) {t : ℝ} (ht : 0 < t) (δ : ℝ) :
    2 * R^2 * Real.log (2*(m:ℝ)*(N+1)/δ) ≤
      ((sphereDimension m N R t δ - N : ℕ) : ℝ) * t^2 := by
  have hc := Nat.le_ceil (2 * R^2 * Real.log (2*(m:ℝ)*(N+1)/δ) / t^2)
  have hsq : 0 < t^2 := sq_pos_of_pos ht
  apply ((div_le_iff₀ hsq).mp hc).trans
  apply mul_le_mul_of_nonneg_right _ hsq.le
  exact_mod_cast (show ⌈2 * R^2 * Real.log (2*(m:ℝ)*(N+1)/δ) / t^2⌉₊ ≤
    sphereDimension m N R t δ - N by unfold sphereDimension; omega)

theorem sphereDimension_upper {m : ℕ} (hm : 0 < m) (N : ℕ) (R t : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (sphereDimension m N R t δ : ℝ) <
      (m : ℝ) + N + 2*R^2*Real.log (2*(m:ℝ)*(N+1)/δ)/t^2 + 1 := by
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hratio : 1 ≤ 2*(m:ℝ)*(N+1)/δ :=
    (le_div_iff₀ hδ).mpr (by nlinarith)
  have hnonneg : 0 ≤ 2*R^2*Real.log (2*(m:ℝ)*(N+1)/δ)/t^2 :=
    div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hratio)) (sq_nonneg t)
  have hc := Nat.ceil_lt_add_one hnonneg
  simp only [sphereDimension, Nat.cast_add] 
  linarith

/-- The manuscript scale: radius `2R`, hidden threshold `h/2`, failure `1/12`.
This has precisely the `(R/h)^2 log(m(N+1))` dimension dependence. -/
def hardFrameDimension (m N : ℕ) (R h : ℝ) : ℕ :=
  m + N + ⌈32*(R/h)^2*Real.log (24*(m:ℝ)*(N+1))⌉₊

theorem hardFrameDimension_eq_sphereDimension (m N : ℕ) (R : ℝ) {h : ℝ} (hh : 0 < h) :
    hardFrameDimension m N R h = sphereDimension m N (2*R) (h/2) (1/12) := by
  have he : 32*(R/h)^2*Real.log (24*(m:ℝ)*(N+1)) =
      2*(2*R)^2*Real.log (2*(m:ℝ)*(N+1)/(1/12))/(h/2)^2 := by
    have hl : 2*(m:ℝ)*(N+1)/(1/12) = 24*(m:ℝ)*(N+1) := by ring
    rw [hl]
    field_simp
    ring
  simp only [hardFrameDimension, sphereDimension, he]

theorem hardFrameDimension_ge_frame (m N : ℕ) (R h : ℝ) :
    m ≤ hardFrameDimension m N R h := by unfold hardFrameDimension; omega

theorem hardFrameDimension_budget (m N : ℕ) (R : ℝ) {h : ℝ} (hh : 0 < h) :
    2*(2*R)^2*Real.log (2*(m:ℝ)*(N+1)/(1/12)) ≤
      ((hardFrameDimension m N R h - N : ℕ) : ℝ) * (h/2)^2 := by
  rw [hardFrameDimension_eq_sphereDimension m N R hh]
  exact sphereDimension_budget m N (2*R) (half_pos hh) (1/12)

end SampleReuse.RandomFrame
