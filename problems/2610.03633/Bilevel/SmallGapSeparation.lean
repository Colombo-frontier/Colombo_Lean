import Bilevel.SmallGapProfiles
import Bilevel.Bowl

/-! # Global stationary-set separation for the actual small-gap objectives -/

noncomputable section
namespace Bilevel.SmallGapSeparation
open Filter
open scoped Topology

structure Parameters where
  κ : ℝ
  S : ℝ
  δ : ℝ
  R : ℝ
  L : ℝ
  κ_pos : 0 < κ
  S_pos : 0 < S
  δ_pos : 0 < δ
  R_pos : 0 < R
  L_pos : 0 < L
  width : 34 * δ ≤ R
  radius : R / κ ≤ 1
  margin : κ * S * δ ≤ L * R / (2 * κ)

namespace Parameters
variable (P : Parameters)

def gamma : ℝ := P.κ * P.S * P.δ
def curvature : ℝ := P.κ ^ 2 * P.S
def objective (ω x : ℝ) : ℝ := Bowl.value P.L x +
  P.S * P.R ^ 2 * SmallGapProfiles.phi (P.κ * x / P.R) -
    ω * P.S * P.δ ^ 2 * SmallGapProfiles.psi (P.κ * x / P.δ)
def gradient (ω x : ℝ) : ℝ := Bowl.slope P.L x +
  P.κ * P.S * P.R * deriv SmallGapProfiles.phi (P.κ * x / P.R) -
    ω * P.κ * P.S * P.δ * deriv SmallGapProfiles.psi (P.κ * x / P.δ)

theorem gamma_pos : 0 < P.gamma := mul_pos (mul_pos P.κ_pos P.S_pos) P.δ_pos

theorem hasDerivAt_objective (ω x : ℝ) : HasDerivAt (P.objective ω) (P.gradient ω x) x := by
  have hR := ((hasDerivAt_id x).const_mul P.κ).div_const P.R
  have hδ := ((hasDerivAt_id x).const_mul P.κ).div_const P.δ
  have hφ := ((SmallGapProfiles.phi_contDiff.differentiable (by norm_num))
    (P.κ * x / P.R)).hasDerivAt.comp x hR
  have hψ := ((SmallGapProfiles.psi_contDiff.differentiable (by norm_num))
    (P.κ * x / P.δ)).hasDerivAt.comp x hδ
  convert ((Bowl.hasDerivAt_value P.L x).add (hφ.const_mul (P.S * P.R ^ 2))).sub
    (hψ.const_mul (ω * P.S * P.δ ^ 2)) using 1
  unfold gradient
  field_simp [P.R_pos.ne', P.δ_pos.ne']
  ring

theorem derivative (ω x : ℝ) : deriv (P.objective ω) x = P.gradient ω x :=
  (P.hasDerivAt_objective ω x).deriv

theorem gradient_core (ω x : ℝ) (hx : |P.κ * x| ≤ 2 * P.δ) :
    P.gradient ω x = Bowl.slope P.L x + P.curvature * x - ω * P.gamma := by
  have hR : |P.κ * x / P.R| ≤ 1 := by
    rw [abs_div, abs_of_pos P.R_pos]
    apply (div_le_iff₀ P.R_pos).mpr
    linarith [P.width, P.δ_pos]
  have hδ : |P.κ * x / P.δ| ≤ 2 := by
    rw [abs_div, abs_of_pos P.δ_pos]
    exact (div_le_iff₀ P.δ_pos).mpr (by linarith)
  rw [gradient, SmallGapProfiles.phi_deriv_core _ hR, SmallGapProfiles.psi_deriv_core _ hδ]
  unfold gamma curvature
  field_simp [P.R_pos.ne']
  ring

theorem separation_core (x : ℝ) (hx : |P.κ * x| ≤ 2 * P.δ) :
    2 * P.gamma ≤ |P.gradient 1 x| + |P.gradient (-1) x| := by
  rw [P.gradient_core 1 x hx, P.gradient_core (-1) x hx]
  simpa only [one_mul, neg_one_mul, sub_neg_eq_add] using
    SmallGap.opposite_shift_separation (Bowl.slope P.L x + P.curvature * x)
      P.gamma P.gamma_pos.le

theorem transition_gradients (x : ℝ) (hleft : 2 * P.δ ≤ P.κ * x) (hright : P.κ * x ≤ P.R) :
    P.gamma ≤ P.gradient 1 x ∧ P.gamma ≤ P.gradient (-1) x := by
  have hx : 0 < x := by nlinarith [P.κ_pos, P.δ_pos]
  have hu : 0 ≤ P.κ * x := mul_nonneg P.κ_pos.le hx.le
  have hR : |P.κ * x / P.R| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg hu P.R_pos.le)]
    exact (div_le_iff₀ P.R_pos).mpr (by simpa using hright)
  have ht : 2 ≤ P.κ * x / P.δ := (le_div_iff₀ P.δ_pos).mpr (by linarith)
  have htb : 0 ≤ P.κ * x / P.δ := div_nonneg hu P.δ_pos.le
  have hd := SmallGapProfiles.psi_deriv_bounds (P.κ * x / P.δ) htb
  have hplus := mul_le_mul_of_nonneg_left hd.2 P.gamma_pos.le
  have hminus := mul_le_mul_of_nonneg_left hd.1 P.gamma_pos.le
  have hscale := mul_le_mul_of_nonneg_left ht P.gamma_pos.le
  have hb := (Bowl.slope_positive P.L x P.L_pos hx).le
  have heq : P.κ * P.S * P.R * (P.κ * x / P.R) =
      P.gamma * (P.κ * x / P.δ) := by
    unfold gamma
    field_simp [P.R_pos.ne', P.δ_pos.ne']
    ring
  simp only [gradient, SmallGapProfiles.phi_deriv_core _ hR, heq,
    one_mul, neg_one_mul, neg_mul, sub_neg_eq_add]
  change P.gamma ≤ Bowl.slope P.L x + P.gamma * (P.κ * x / P.δ) -
      P.gamma * deriv SmallGapProfiles.psi (P.κ * x / P.δ) ∧
    P.gamma ≤ Bowl.slope P.L x + P.gamma * (P.κ * x / P.δ) +
      P.gamma * deriv SmallGapProfiles.psi (P.κ * x / P.δ)
  constructor <;> nlinarith [P.gamma_pos]

theorem exterior_gradients (x : ℝ) (hx : P.R ≤ P.κ * x) :
    P.gamma ≤ P.gradient 1 x ∧ P.gamma ≤ P.gradient (-1) x := by
  have hx0 : 0 < x := by nlinarith [P.R_pos, P.κ_pos]
  have hψarg : 34 ≤ P.κ * x / P.δ := (le_div_iff₀ P.δ_pos).mpr (P.width.trans hx)
  have hψ := SmallGapProfiles.psi_deriv_zero_pos _ hψarg
  have hφ := SmallGapProfiles.phi_deriv_nonneg (P.κ * x / P.R)
    (div_nonneg (mul_nonneg P.κ_pos.le hx0.le) P.R_pos.le)
  have hprod : 0 ≤ P.κ * P.S * P.R * deriv SmallGapProfiles.phi (P.κ * x / P.R) :=
    mul_nonneg (mul_nonneg (mul_nonneg P.κ_pos.le P.S_pos.le) P.R_pos.le) hφ
  have hxR : P.R / P.κ ≤ x := (div_le_iff₀ P.κ_pos).mpr (by nlinarith)
  have hmono := Bowl.slope_monotone P.L P.L_pos hxR
  have hlocal := Bowl.slope_local_lower P.L (P.R / P.κ) P.L_pos.le
    ⟨div_nonneg P.R_pos.le P.κ_pos.le, P.radius⟩
  have hmargin : P.gamma ≤ P.L * (P.R / P.κ) / 2 := by
    calc
      P.gamma ≤ P.L * P.R / (2 * P.κ) := P.margin
      _ = P.L * (P.R / P.κ) / 2 := by ring
  simp only [gradient, hψ, mul_zero, sub_zero]
  constructor <;> linarith

theorem separation_nonneg (x : ℝ) (hx : 0 ≤ x) :
    2 * P.gamma ≤ |P.gradient 1 x| + |P.gradient (-1) x| := by
  by_cases hcore : P.κ * x ≤ 2 * P.δ
  · apply P.separation_core x
    rw [abs_of_nonneg (mul_nonneg P.κ_pos.le hx)]
    exact hcore
  · have hleft : 2 * P.δ ≤ P.κ * x := le_of_not_ge hcore
    have hb : P.gamma ≤ P.gradient 1 x ∧ P.gamma ≤ P.gradient (-1) x := by
      by_cases hright : P.κ * x ≤ P.R
      · exact P.transition_gradients x hleft hright
      · exact P.exterior_gradients x (le_of_not_ge hright)
    have hsum := add_le_add (hb.1.trans (le_abs_self _)) (hb.2.trans (le_abs_self _))
    linarith

theorem gradient_reflection (ω x : ℝ) : P.gradient ω (-x) = -P.gradient (-ω) x := by
  have hR : P.κ * (-x) / P.R = -(P.κ * x / P.R) := by ring
  have hδ : P.κ * (-x) / P.δ = -(P.κ * x / P.δ) := by ring
  have hb : Bowl.slope P.L (-x) = -Bowl.slope P.L x := by
    simp only [Bowl.slope, neg_sq]
    ring
  rw [gradient, hR, hδ, SmallGapProfiles.phi_deriv_odd, SmallGapProfiles.psi_deriv_even, hb]
  unfold gradient
  ring

/-- Global separation of the actual two hyperobjectives, with no assumed
profile or separation certificate. -/
theorem global_separation (x : ℝ) :
    2 * P.gamma ≤ |deriv (P.objective 1) x| + |deriv (P.objective (-1)) x| := by
  rw [P.derivative, P.derivative]
  by_cases hx : 0 ≤ x
  · exact P.separation_nonneg x hx
  · have h := P.separation_nonneg (-x) (by linarith)
    rw [P.gradient_reflection 1 x, P.gradient_reflection (-1) x] at h
    simpa only [neg_neg, abs_neg, add_comm] using h

theorem right_gradients (x : ℝ) (hx : 2 * P.δ ≤ P.κ * x) :
    P.gamma ≤ P.gradient 1 x ∧ P.gamma ≤ P.gradient (-1) x := by
  by_cases hR : P.κ * x ≤ P.R
  · exact P.transition_gradients x hx hR
  · exact P.exterior_gradients x (le_of_not_ge hR)

theorem stationary_in_core (ω x : ℝ) (hω : ω = 1 ∨ ω = -1) (hx : P.gradient ω x = 0) :
    |P.κ * x| < 2 * P.δ := by
  by_contra hnot
  have hlarge : 2 * P.δ ≤ |P.κ * x| := le_of_not_gt hnot
  by_cases hsign : 0 ≤ x
  · rw [abs_of_nonneg (mul_nonneg P.κ_pos.le hsign)] at hlarge
    have h := P.right_gradients x hlarge
    rcases hω with hω | hω <;> subst ω <;> linarith [P.gamma_pos]
  · have hneg : P.κ * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos P.κ_pos.le (le_of_not_ge hsign)
    rw [abs_of_nonpos hneg] at hlarge
    have h := P.right_gradients (-x) (by nlinarith)
    rw [P.gradient_reflection 1 x, P.gradient_reflection (-1) x] at h
    simp only [neg_neg] at h
    rcases hω with hω | hω <;> subst ω <;> linarith [P.gamma_pos]

theorem curvature_pos : 0 < P.curvature := mul_pos (sq_pos_of_pos P.κ_pos) P.S_pos

theorem stationary_unique (ω x y : ℝ) (hω : ω = 1 ∨ ω = -1)
    (hx : P.gradient ω x = 0) (hy : P.gradient ω y = 0) : x = y := by
  have hxc := P.gradient_core ω x (P.stationary_in_core ω x hω hx).le
  have hyc := P.gradient_core ω y (P.stationary_in_core ω y hω hy).le
  rcases lt_trichotomy x y with h | h | h
  · have hm := Bowl.slope_monotone P.L P.L_pos h.le
    have hc := mul_lt_mul_of_pos_left h P.curvature_pos
    linarith
  · exact h
  · have hm := Bowl.slope_monotone P.L P.L_pos h.le
    have hc := mul_lt_mul_of_pos_left h P.curvature_pos
    linarith

theorem stationary_sign (ω x : ℝ) (hω : ω = 1 ∨ ω = -1) (hx : P.gradient ω x = 0) :
    0 < ω * x := by
  have hc := P.gradient_core ω x (P.stationary_in_core ω x hω hx).le
  rcases hω with hω | hω
  · subst ω
    simp only [one_mul] at hc ⊢
    by_contra hn
    have hsign : x ≤ 0 := le_of_not_gt hn
    have hb : Bowl.slope P.L x ≤ 0 := by
      simpa [Bowl.slope] using Bowl.slope_monotone P.L P.L_pos hsign
    have hcurv := mul_nonpos_of_nonneg_of_nonpos P.curvature_pos.le hsign
    linarith [P.gamma_pos]
  · subst ω
    simp only [neg_one_mul, sub_neg_eq_add] at hc ⊢
    by_contra hn
    have hsign : 0 ≤ x := by linarith
    have hb : 0 ≤ Bowl.slope P.L x := by
      simpa [Bowl.slope] using Bowl.slope_monotone P.L P.L_pos hsign
    have hcurv := mul_nonneg P.curvature_pos.le hsign
    linarith [P.gamma_pos]

theorem psi_bounded (t : ℝ) : |SmallGapProfiles.psi t| ≤ 34 := by
  by_cases ht : 34 ≤ |t|
  · rw [SmallGapProfiles.psi_support t ht, abs_zero]
    norm_num
  · have hs := SmallGap.septicStep_range ((|t| - 2) / 32)
    rw [SmallGapProfiles.psi, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2)]
    have hprod := mul_nonneg (abs_nonneg t) hs.1
    linarith

theorem objective_coercive (ω : ℝ) : Tendsto (P.objective ω) (cocompact ℝ) atTop := by
  apply tendsto_atTop.2
  intro b
  have hB := (Bowl.coercive P.L P.L_pos).eventually_ge_atTop
    (b + |ω| * P.S * P.δ ^ 2 * 34)
  filter_upwards [hB] with x hx
  have hφ : 0 ≤ P.S * P.R ^ 2 * SmallGapProfiles.phi (P.κ * x / P.R) :=
    mul_nonneg (mul_nonneg P.S_pos.le (sq_nonneg _)) (SmallGapProfiles.phi_nonneg _)
  have hcoef : 0 ≤ |ω| * P.S * P.δ ^ 2 :=
    mul_nonneg (mul_nonneg (abs_nonneg _) P.S_pos.le) (sq_nonneg _)
  have hψ := mul_le_mul_of_nonneg_left (psi_bounded (P.κ * x / P.δ)) hcoef
  have htilt : ω * P.S * P.δ ^ 2 * SmallGapProfiles.psi (P.κ * x / P.δ) ≤
      |ω| * P.S * P.δ ^ 2 * 34 := by
    calc
      _ ≤ |ω * P.S * P.δ ^ 2 * SmallGapProfiles.psi (P.κ * x / P.δ)| := le_abs_self _
      _ = |ω| * P.S * P.δ ^ 2 * |SmallGapProfiles.psi (P.κ * x / P.δ)| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos P.S_pos, abs_of_nonneg (sq_nonneg P.δ)]
      _ ≤ _ := hψ
  unfold objective
  linarith

theorem objective_minimum_exists (ω : ℝ) : ∃ x, ∀ y, P.objective ω x ≤ P.objective ω y := by
  have hc : Continuous (P.objective ω) := continuous_iff_continuousAt.mpr
    (fun x => (P.hasDerivAt_objective ω x).continuousAt)
  exact hc.exists_forall_le (P.objective_coercive ω)

theorem stationary_exists_unique (ω : ℝ) (hω : ω = 1 ∨ ω = -1) :
    ∃! x, deriv (P.objective ω) x = 0 := by
  obtain ⟨x, hx⟩ := P.objective_minimum_exists ω
  have hm : IsLocalMin (P.objective ω) x := Filter.Eventually.of_forall hx
  have hs := hm.hasDerivAt_eq_zero (P.hasDerivAt_objective ω x)
  refine ⟨x, ?_, ?_⟩
  · change deriv (P.objective ω) x = 0
    rw [P.derivative]
    exact hs
  · intro y hy
    rw [P.derivative] at hy
    exact P.stationary_unique ω y x hω hy hs

theorem stationary_minimizes (ω x : ℝ) (hω : ω = 1 ∨ ω = -1)
    (hx : P.gradient ω x = 0) : ∀ y, P.objective ω x ≤ P.objective ω y := by
  obtain ⟨z, hz⟩ := P.objective_minimum_exists ω
  have hm : IsLocalMin (P.objective ω) z := Filter.Eventually.of_forall hz
  have hs := hm.hasDerivAt_eq_zero (P.hasDerivAt_objective ω z)
  have heq := P.stationary_unique ω x z hω hx hs
  simpa only [heq] using hz

theorem objective_core (ω x : ℝ) (hx : |P.κ * x| ≤ 2 * P.δ) :
    P.objective ω x = P.curvature / 2 * x ^ 2 - ω * P.gamma * x + Bowl.value P.L x := by
  have hR : |P.κ * x / P.R| ≤ 1 := by
    rw [abs_div, abs_of_pos P.R_pos]
    apply (div_le_iff₀ P.R_pos).mpr
    linarith [P.width, P.δ_pos]
  have hδ : |P.κ * x / P.δ| ≤ 2 := by
    rw [abs_div, abs_of_pos P.δ_pos]
    exact (div_le_iff₀ P.δ_pos).mpr (by linarith)
  rw [objective, SmallGapProfiles.phi_core _ hR, SmallGapProfiles.psi_core _ hδ]
  unfold gamma curvature
  field_simp [P.R_pos.ne', P.δ_pos.ne']
  ring

theorem objective_zero (ω : ℝ) : P.objective ω 0 = 0 := by
  rw [P.objective_core ω 0 (by simp [P.δ_pos.le])]
  simp [Bowl.value]

theorem testpoint_in_core (ω : ℝ) (hω : ω = 1 ∨ ω = -1) :
    |P.κ * (ω * P.gamma / (P.curvature + P.L))| ≤ 2 * P.δ := by
  have hsum : 0 < P.curvature + P.L := add_pos P.curvature_pos P.L_pos
  have habs : |ω| = 1 := by rcases hω with h | h <;> simp [h]
  rw [abs_mul, abs_div, abs_mul, abs_of_pos P.κ_pos, habs, abs_of_pos P.gamma_pos,
    abs_of_pos hsum, one_mul]
  have hsmall : P.κ * (P.gamma / (P.curvature + P.L)) ≤ P.δ := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hsum).mpr
    have hid : P.κ * P.gamma = P.δ * P.curvature := by unfold gamma curvature; ring
    rw [hid]
    nlinarith [mul_pos P.δ_pos P.L_pos]
  linarith [P.δ_pos]

/-- Actual global minimizers satisfy the source's two-sided initial-gap bound. -/
theorem minimum_gap_sandwich (ω xstar : ℝ) (hω : ω = 1 ∨ ω = -1)
    (hmin : ∀ x, P.objective ω xstar ≤ P.objective ω x) :
    P.gamma ^ 2 / (2 * (P.curvature + P.L)) ≤ P.objective ω 0 - P.objective ω xstar ∧
      P.objective ω 0 - P.objective ω xstar ≤ P.gamma ^ 2 / (2 * P.curvature) := by
  have hm : IsLocalMin (P.objective ω) xstar := Filter.Eventually.of_forall hmin
  have hs := hm.hasDerivAt_eq_zero (P.hasDerivAt_objective ω xstar)
  have hcore := (P.stationary_in_core ω xstar hω hs).le
  have hωsq : ω ^ 2 = 1 := by rcases hω with h | h <;> simp [h]
  exact SmallGap.gap_sandwich (P.objective ω) (Bowl.value P.L) P.curvature P.L
    P.gamma ω xstar P.curvature_pos P.L_pos.le hωsq (P.objective_zero ω) hmin
    (P.objective_core ω xstar hcore) (Bowl.nonnegative P.L xstar P.L_pos.le)
    (P.objective_core ω _ (P.testpoint_in_core ω hω))
    (by simpa only [div_mul_eq_mul_div] using
      Bowl.quadratic_upper P.L (ω * P.gamma / (P.curvature + P.L)) P.L_pos.le)

end Parameters
end Bilevel.SmallGapSeparation
