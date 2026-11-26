import Surrogate254

noncomputable section
open scoped RealInnerProductSpace
namespace Paper254

def rankOneSurrogate {d : ℕ} (γ : ℝ) (g w v : Space d) : ℝ :=
  ⟪g, v-w⟫ + γ/2 * ⟪g, v-w⟫ ^ 2

theorem curvature_pos (D G η : ℝ) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) :
    0 < curvature D G η := by
  unfold curvature
  exact lt_min (by positivity) (by positivity)

theorem curvature_times_radius (D G η : ℝ) (hD : 0 < D) (hG : 0 < G) :
    curvature D G η * (G * D) ≤ 1/4 := by
  have hh := min_le_right (η/2) (1/(4*G*D))
  have hp : 0 < 4*G*D := by positivity
  have hx := (le_div_iff₀ hp).mp hh
  change curvature D G η * (G*D) ≤ 1/4
  dsimp [curvature] at *
  nlinarith

theorem gradient_inner_bound {d : ℕ} {D G : ℝ} (W : Domain d D)
    (hG : 0 ≤ G) {g w v : Space d} (hg : ‖g‖ ≤ G)
    (hw : w ∈ W.carrier) (hv : v ∈ W.carrier) : |⟪g, v-w⟫| ≤ G*D := by
  exact le_trans (abs_real_inner_le_norm g (v-w))
    (mul_le_mul hg (W.diameter v hv w hw) (norm_nonneg _) hG)

/-- Lemma B.1, regret-domination part, from the manuscript's actual domain,
exp-concavity and within-domain gradient assumptions. -/
theorem surrogate_domination {d : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) {f : Loss d}
    (hf : ExpConcaveOn η W.carrier f) {g w v : Space d}
    (hd : HasGradientWithinAt f g W.carrier w) (hg : ‖g‖ ≤ G)
    (hw : w ∈ W.carrier) (hv : v ∈ W.carrier) :
    f w - f v ≤ -rankOneSurrogate (curvature D G η) g w v := by
  let γ := curvature D G η
  let κ := 2*γ
  let a := ⟪g, v-w⟫
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hkη : κ ≤ η := by
    have hh := min_le_left (η/2) (1/(4*G*D))
    dsimp [κ, γ, curvature]
    linarith
  have hconc := hf.mono hη hκ.le hkη
  have hab : |a| ≤ G*D := gradient_inner_bound W hG.le hg hw hv
  have hgd := curvature_times_radius D G η hD hG
  have hka : |κ*a| ≤ 1/2 := by
    rw [abs_mul, abs_of_pos hκ]
    have hh := mul_le_mul_of_nonneg_left hab hκ.le
    dsimp [κ, γ] at *
    nlinarith
  have hpositive : 0 < 1-κ*a := by
    have hh := (abs_le.mp hka).2
    linarith
  have hder := (hd.hasFDerivWithinAt.const_mul (-κ)).exp
  have hs := concave_support hconc hw hv hder
  simp only [ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply,
    smul_eq_mul] at hs
  have hsupport : Real.exp (-κ*f v) ≤ Real.exp (-κ*f w)*(1-κ*a) := by
    dsimp [a]
    nlinarith [hs]
  have hlog := Real.log_le_log (Real.exp_pos (-κ*f v)) hsupport
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpositive),
    Real.log_exp, Real.log_exp] at hlog
  have hquad := quadratic_log_lower (κ*a) hka
  have hscaled : κ * (a + γ/2*a^2) ≤ κ * (f v-f w) := by
    dsimp [κ] at *
    nlinarith
  have hbound := (mul_le_mul_iff_right₀ hκ).mp hscaled
  change f w - f v ≤ -(a + γ/2*a^2)
  linarith

end Paper254
#print axioms Paper254.surrogate_domination
