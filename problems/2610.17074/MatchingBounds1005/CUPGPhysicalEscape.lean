import MatchingBounds1005.CUPGLines
import MatchingBounds1005.CUPGEscape

/-! The two symmetric escape points, computed only from a first-order witness. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def escapeMinus (u v : E) (η : ℝ) : E := (1 / 2 : ℝ) • (u + v) - (η / ‖u - v‖) • (u - v)
def escapePlus (u v : E) (η : ℝ) : E := (1 / 2 : ℝ) • (u + v) + (η / ‖u - v‖) • (u - v)

/-- First-order convexity violation plus directional third smoothness gives
an explicit two-value-query escape. No Hessian information is used. -/
theorem physical_symmetric_escape {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {α L η : ℝ} (hα : 0 < α) (hL : 0 ≤ L) (hη : 0 < η)
    (hdir : DirectionalLip f 3 L) (u v : E)
    (hnc : f u - f v - ⟪gradient f v, u - v⟫_ℝ < -α / 2 * ‖u - v‖ ^ 2)
    (hdist : ‖u - v‖ ≤ η / 2) (hscale : L * η ^ 2 ≤ α) :
    min (f (escapeMinus u v η)) (f (escapePlus u v η)) ≤
      max (f v) (f u) - α * η ^ 2 / 3 := by
  have hne : u - v ≠ 0 := by
    intro hz
    have he : u = v := sub_eq_zero.mp hz
    subst u
    simp at hnc
  have hdpos : 0 < ‖u - v‖ := norm_pos_iff.mpr hne
  let mid : E := (1 / 2 : ℝ) • (u + v)
  let dir : E := (1 / 2 : ℝ) • (u - v)
  let h := line f mid dir
  let R : ℝ := 2 * η / ‖u - v‖
  have hnorm : ‖dir‖ = ‖u - v‖ / 2 := by simp [dir, norm_smul, Real.norm_eq_abs]; ring
  have hmid1 : mid + (1 : ℝ) • dir = u := by dsimp [mid, dir]; module
  have hmidneg1 : mid + (-1 : ℝ) • dir = v := by dsimp [mid, dir]; module
  have h1 : h 1 = f u := by dsimp [h, line]; rw [hmid1]
  have hm1 : h (-1) = f v := by dsimp [h, line]; rw [hmidneg1]
  have hderiv : deriv h (-1) = (1 / 2 : ℝ) * ⟪gradient f v, u - v⟫_ℝ := by
    rw [(line_hasDerivAt (hf.differentiable (by norm_num)) mid dir (-1)).deriv, hmidneg1]
    simp [dir, real_inner_smul_right]
  have hthird (s t : ℝ) : |iteratedDeriv 3 h s - iteratedDeriv 3 h t| ≤
      (L * ‖u - v‖ ^ 4 / 16) * |s - t| := by
    have hh := directional_lip_scaled hf hdir mid dir t s
    change _ ≤ L * ‖dir‖ ^ 4 * |s - t| at hh
    rw [hnorm] at hh
    convert hh using 1 <;> ring
  have hv : h 1 - h (-1) - 2 * deriv h (-1) ≤ -(α * ‖u - v‖ ^ 2 / 2) := by
    rw [h1, hm1, hderiv]
    linarith
  have hR : 4 ≤ R := by dsimp [R]; apply (le_div_iff₀ hdpos).2; linarith
  have hS : (L * ‖u - v‖ ^ 4 / 16) * R ^ 2 ≤ (α * ‖u - v‖ ^ 2 / 2) / 2 := by
    have he : (L * ‖u - v‖ ^ 4 / 16) * R ^ 2 = L * η ^ 2 * ‖u - v‖ ^ 2 / 4 := by
      dsimp [R]
      field_simp
      ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖u - v‖)
    linarith
  have hex := normalized_symmetric_escape (line_smooth hf mid dir) (by positivity) (by positivity)
    hR hthird hv hS
  have hminus : h (-R) = f (escapeMinus u v η) := by
    dsimp [h, line, mid, dir, escapeMinus, R]
    congr 1
    module
  have hplus : h R = f (escapePlus u v η) := by
    dsimp [h, line, mid, dir, escapePlus, R]
    congr 1
    module
  have hdec : (α * ‖u - v‖ ^ 2 / 2) * R ^ 2 / 6 = α * η ^ 2 / 3 := by
    dsimp [R]
    field_simp
    ring
  change min (h (-R)) (h R) ≤ max (h (-1)) (h 1) -
    (α * ‖u - v‖ ^ 2 / 2) * R ^ 2 / 6 at hex
  rw [hminus, hplus, hm1, h1, hdec] at hex
  exact hex

end MatchingBounds1005.CUPG
