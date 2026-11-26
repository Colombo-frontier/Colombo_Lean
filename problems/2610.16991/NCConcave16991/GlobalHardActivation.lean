import NCConcave16991.GlobalHardScalar

/-! # The actual delayed state activation and its squared-function derivative bounds -/

namespace NCConcave16991.GlobalHard

noncomputable section

open Set LocalizationScalar LocalizationStep LocalizationStepSecond
open scoped ContDiff Topology

theorem deltaGate_pos : 0 < deltaGate := by norm_num [deltaGate]

theorem stepDerivative_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) : deriv Real.smoothTransition t = 0 := by
  rw [step_deriv]
  rcases ht with ht | ht
  · rw [Real.smoothTransition.zero_of_nonpos ht]; ring
  · rw [Real.smoothTransition.one_of_one_le ht]; ring

theorem stepSecond_zero {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) : deriv (deriv Real.smoothTransition) t = 0 := by
  have hz := stepDerivative_zero ht
  have hm : IsLocalMin (deriv Real.smoothTransition) t := by
    apply IsMinOn.isLocalMin (s := univ)
    · intro s _
      rw [hz]
      exact (step_deriv_bounds s).1
    · exact Filter.univ_mem
  exact hm.deriv_eq_zero

def activation (t : ℝ) : ℝ := t * Real.smoothTransition ((t - deltaGate) / deltaGate)
def activationDerivative (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - deltaGate) / deltaGate) +
    (t / deltaGate) * deriv Real.smoothTransition ((t - deltaGate) / deltaGate)
def activationSecond (t : ℝ) : ℝ :=
  (2 / deltaGate) * deriv Real.smoothTransition ((t - deltaGate) / deltaGate) +
    (t / deltaGate ^ 2) * deriv (deriv Real.smoothTransition) ((t - deltaGate) / deltaGate)
def activationSq (t : ℝ) : ℝ := activation t ^ 2
def activationSqDerivative (t : ℝ) : ℝ := 2 * activation t * activationDerivative t
def activationSqSecond (t : ℝ) : ℝ :=
  2 * activationDerivative t ^ 2 + 2 * activation t * activationSecond t

theorem activation_contDiff : ContDiff ℝ ∞ activation := by
  unfold activation
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem activationSq_contDiff : ContDiff ℝ ∞ activationSq := activation_contDiff.pow 2

theorem activation_hasDerivAt (t : ℝ) : HasDerivAt activation (activationDerivative t) t := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hd : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((t - deltaGate) / deltaGate))
      ((t - deltaGate) / deltaGate) :=
    (hc.differentiable (by simp) ((t - deltaGate) / deltaGate)).hasDerivAt
  have hh := (hasDerivAt_id t).mul (hd.comp t (((hasDerivAt_id t).sub_const deltaGate).div_const deltaGate))
  convert hh using 1 <;> first | rfl | dsimp [activationDerivative]; ring

theorem activationDerivative_hasDerivAt (t : ℝ) : HasDerivAt activationDerivative (activationSecond t) t := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hcD : ContDiff ℝ ∞ (deriv Real.smoothTransition) := (contDiff_infty_iff_deriv.mp hc).2
  have hw (x : ℝ) : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    (hc.differentiable (by simp) x).hasDerivAt
  have hd (x : ℝ) : HasDerivAt (deriv Real.smoothTransition) (deriv (deriv Real.smoothTransition) x) x :=
    (hcD.differentiable (by simp) x).hasDerivAt
  have hu := ((hasDerivAt_id t).sub_const deltaGate).div_const deltaGate
  have hh := (hw ((t - deltaGate) / deltaGate)).comp t hu |>.add
    (((hasDerivAt_id t).div_const deltaGate).mul ((hd ((t - deltaGate) / deltaGate)).comp t hu))
  convert hh using 1 <;> first | rfl | dsimp [activationSecond]; ring

theorem activationSq_hasDerivAt (t : ℝ) : HasDerivAt activationSq (activationSqDerivative t) t := by
  convert (activation_hasDerivAt t).pow 2 using 1 <;> first | rfl | dsimp [activationSqDerivative]; ring

theorem activationSqDerivative_hasDerivAt (t : ℝ) :
    HasDerivAt activationSqDerivative (activationSqSecond t) t := by
  have hh := (((activation_hasDerivAt t).const_mul 2).mul (activationDerivative_hasDerivAt t))
  convert hh using 1 <;> first | rfl | dsimp [activationSqSecond]; ring

theorem activation_zero {t : ℝ} (ht : t ≤ deltaGate) : activation t = 0 := by
  unfold activation
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) deltaGate_pos.le)]
  ring

theorem activation_eq_self {t : ℝ} (ht : 2 * deltaGate ≤ t) : activation t = t := by
  unfold activation
  rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ deltaGate_pos).2 (by linarith))]
  ring

theorem activationDerivative_zero {t : ℝ} (ht : t ≤ deltaGate) : activationDerivative t = 0 := by
  have hu : (t - deltaGate) / deltaGate ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) deltaGate_pos.le
  unfold activationDerivative
  rw [Real.smoothTransition.zero_of_nonpos hu, stepDerivative_zero (Or.inl hu)]
  ring

theorem activationDerivative_one {t : ℝ} (ht : 2 * deltaGate ≤ t) : activationDerivative t = 1 := by
  have hu : 1 ≤ (t - deltaGate) / deltaGate := (le_div_iff₀ deltaGate_pos).2 (by linarith)
  unfold activationDerivative
  rw [Real.smoothTransition.one_of_one_le hu, stepDerivative_zero (Or.inr hu)]
  ring

theorem activationSecond_zero {t : ℝ} (ht : t ≤ deltaGate ∨ 2 * deltaGate ≤ t) : activationSecond t = 0 := by
  have hu : (t - deltaGate) / deltaGate ≤ 0 ∨ 1 ≤ (t - deltaGate) / deltaGate := by
    rcases ht with ht | ht
    · exact Or.inl (div_nonpos_of_nonpos_of_nonneg (by linarith) deltaGate_pos.le)
    · exact Or.inr ((le_div_iff₀ deltaGate_pos).2 (by linarith))
  unfold activationSecond
  rw [stepDerivative_zero hu, stepSecond_zero hu]
  ring

theorem activation_bounds (t : ℝ) : 0 ≤ activation t ∧ activation t ≤ max t 0 := by
  by_cases ht : t ≤ deltaGate
  · rw [activation_zero ht]
    exact ⟨le_refl _, le_max_right _ _⟩
  · have hp : 0 ≤ t := le_trans deltaGate_pos.le (le_of_not_ge ht)
    have h0 := Real.smoothTransition.nonneg ((t - deltaGate) / deltaGate)
    have h1 := Real.smoothTransition.le_one ((t - deltaGate) / deltaGate)
    dsimp [activation]
    rw [max_eq_left hp]
    exact ⟨mul_nonneg hp h0, by nlinarith⟩

theorem activation_abs_le (t : ℝ) : |activation t| ≤ |t| := by
  rw [abs_of_nonneg (activation_bounds t).1]
  exact (activation_bounds t).2.trans (max_le (le_abs_self t) (abs_nonneg t))

theorem activationDerivative_bounds (t : ℝ) : 0 ≤ activationDerivative t ∧ activationDerivative t ≤ 17 := by
  by_cases hl : t ≤ deltaGate
  · rw [activationDerivative_zero hl]; norm_num
  · by_cases hr : 2 * deltaGate ≤ t
    · rw [activationDerivative_one hr]; norm_num
    · have ht : 0 ≤ t := by linarith [deltaGate_pos]
      have hratio : 0 ≤ t / deltaGate ∧ t / deltaGate ≤ 2 :=
        ⟨div_nonneg ht deltaGate_pos.le, (div_le_iff₀ deltaGate_pos).2 (by linarith)⟩
      have h0 := Real.smoothTransition.nonneg ((t - deltaGate) / deltaGate)
      have h1 := Real.smoothTransition.le_one ((t - deltaGate) / deltaGate)
      have hd := step_deriv_bounds ((t - deltaGate) / deltaGate)
      have hm := mul_le_mul hratio.2 hd.2 hd.1 (by norm_num : (0 : ℝ) ≤ 2)
      dsimp [activationDerivative]
      exact ⟨add_nonneg h0 (mul_nonneg hratio.1 hd.1), by nlinarith⟩

theorem activationSecond_abs_bound (t : ℝ) : |activationSecond t| ≤ 272 / deltaGate := by
  by_cases hl : t ≤ deltaGate
  · rw [activationSecond_zero (Or.inl hl)]; norm_num [deltaGate]
  · by_cases hr : 2 * deltaGate ≤ t
    · rw [activationSecond_zero (Or.inr hr)]; norm_num [deltaGate]
    · have ht : 0 ≤ t := by linarith [deltaGate_pos]
      have hupper : t ≤ 2 * deltaGate := le_of_not_ge hr
      have hd := step_deriv_bounds ((t - deltaGate) / deltaGate)
      have hdd := stepSecond_bound ((t - deltaGate) / deltaGate)
      have ha := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ 2 / deltaGate by positivity [deltaGate_pos])
      have hb := mul_le_mul_of_nonneg_left hdd (show 0 ≤ t / deltaGate ^ 2 by positivity)
      have htri := abs_add_le
        ((2 / deltaGate) * deriv Real.smoothTransition ((t - deltaGate) / deltaGate))
        ((t / deltaGate ^ 2) * deriv (deriv Real.smoothTransition) ((t - deltaGate) / deltaGate))
      rw [abs_mul, abs_of_nonneg (by norm_num [deltaGate] : 0 ≤ 2 / deltaGate), abs_of_nonneg hd.1,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / deltaGate ^ 2)] at htri
      change |activationSecond t| ≤ _ at htri
      norm_num [deltaGate] at ha hb htri hupper ⊢
      nlinarith

theorem activationSqDerivative_bound (t : ℝ) : |activationSqDerivative t| ≤ 34 * |t| := by
  have hh := activation_abs_le t
  have hd := activationDerivative_bounds t
  have hm := mul_le_mul hh hd.2 hd.1 (abs_nonneg t)
  rw [activationSqDerivative, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_nonneg hd.1]
  nlinarith

/-- The source's dimension-free global numeric bound for the squared delayed activation. -/
theorem activationSqSecond_abs_bound (t : ℝ) : |activationSqSecond t| ≤ 1666 := by
  by_cases hl : t ≤ deltaGate
  · rw [activationSqSecond, activationDerivative_zero hl, activationSecond_zero (Or.inl hl)]
    norm_num
  · by_cases hr : 2 * deltaGate ≤ t
    · rw [activationSqSecond, activationDerivative_one hr, activationSecond_zero (Or.inr hr)]
      norm_num
    · have ht : 0 ≤ t := by linarith [deltaGate_pos]
      have hh0 := (activation_bounds t).1
      have hh : activation t ≤ 2 * deltaGate := by
        have hb := (activation_bounds t).2
        rw [max_eq_left ht] at hb
        linarith
      have hd := activationDerivative_bounds t
      have hdsq : activationDerivative t ^ 2 ≤ 289 := by nlinarith
      have hdd := activationSecond_abs_bound t
      have hm := mul_le_mul hh hdd (abs_nonneg _) (show 0 ≤ 2 * deltaGate by positivity [deltaGate_pos])
      have htri := abs_add_le (2 * activationDerivative t ^ 2) (2 * activation t * activationSecond t)
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * activationDerivative t ^ 2),
        abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg hh0] at htri
      change |activationSqSecond t| ≤ _ at htri
      norm_num [deltaGate] at hm
      nlinarith

end

end NCConcave16991.GlobalHard
