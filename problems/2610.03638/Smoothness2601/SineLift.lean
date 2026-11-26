import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
The actual scalar lower root of the sine lift, 2601.tex equations `eq:theta`
and `eq:new-root`. The root is constructed by the intermediate value theorem;
uniqueness is derived from the actual derivative of its residual.
-/
noncomputable section
namespace Smoothness2601.SineLift
open scoped Topology
open Filter Asymptotics

def residual (c B t : ℝ) : ℝ := t - B * Real.cos (c * t)

theorem hasDerivAt_residual (c B t : ℝ) :
    HasDerivAt (residual c B) (1 + c * B * Real.sin (c * t)) t := by
  convert ((hasDerivAt_id t).sub
    (((hasDerivAt_id t).const_mul c).cos.const_mul B)) using 1
  dsimp [residual]
  ring

theorem abs_cos_mul_le (B z : ℝ) : |B * Real.cos z| ≤ |B| := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one z) (abs_nonneg B)).trans_eq
    (mul_one _)

theorem exists_root (c B : ℝ) : ∃ t, residual c B t = 0 := by
  have hc : Continuous (residual c B) := by
    unfold residual
    fun_prop
  have hleft : residual c B (-|B|) ≤ 0 := by
    have h := (abs_le.mp (abs_cos_mul_le B (c * -|B|))).1
    dsimp [residual]
    linarith
  have hright : 0 ≤ residual c B |B| := by
    have h := (abs_le.mp (abs_cos_mul_le B (c * |B|))).2
    dsimp [residual]
    linarith
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc
    (show -|B| ≤ |B| by linarith [abs_nonneg B]) hc.continuousOn ⟨hleft, hright⟩
  exact ⟨t, ht⟩

def theta (c B : ℝ) : ℝ := Classical.choose (exists_root c B)

theorem residual_theta (c B : ℝ) : residual c B (theta c B) = 0 :=
  Classical.choose_spec (exists_root c B)

theorem theta_eq (c B : ℝ) : theta c B = B * Real.cos (c * theta c B) := by
  have h := residual_theta c B
  exact sub_eq_zero.mp h

theorem abs_theta_le (c B : ℝ) : |theta c B| ≤ |B| := by
  conv_lhs => rw [theta_eq c B]
  exact abs_cos_mul_le B _

theorem theta_zero (c : ℝ) : theta c 0 = 0 := by
  simpa using theta_eq c 0

theorem theta_zero_frequency (B : ℝ) : theta 0 B = B := by
  simpa using theta_eq 0 B

theorem residual_derivative_lower (c B t : ℝ) :
    1 - |c * B| ≤ 1 + c * B * Real.sin (c * t) := by
  have hb : |c * B * Real.sin (c * t)| ≤ |c * B| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq
      (mul_one _)
  linarith [(abs_le.mp hb).1]

theorem residual_strictMono {c B : ℝ} (hsmall : |c * B| < 1) :
    StrictMono (residual c B) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_residual c B)
  intro t
  have h := residual_derivative_lower c B t
  linarith

theorem theta_unique {c B t : ℝ} (hsmall : |c * B| < 1)
    (ht : t = B * Real.cos (c * t)) : t = theta c B := by
  apply (residual_strictMono hsmall).injective
  rw [residual_theta]
  exact sub_eq_zero.mpr ht

theorem cos_distance_le (x y : ℝ) : |Real.cos y - Real.cos x| ≤ |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ Set.univ) => (Real.hasDerivAt_cos z).hasDerivWithinAt)
    (fun z (_ : z ∈ Set.univ) => show ‖-Real.sin z‖ ≤ (1 : ℝ) by
      simpa using Real.abs_sin_le_one z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa using h

/-- An anchored Lipschitz estimate follows directly from the two root
equations. Only the reference parameter needs to satisfy the smallness bound. -/
theorem theta_distance_le {c B : ℝ} (hsmall : |c * B| < 1) (Z : ℝ) :
    |theta c Z - theta c B| ≤ |Z - B| / (1 - |c * B|) := by
  have he : theta c Z - theta c B =
      (Z - B) * Real.cos (c * theta c Z) +
      B * (Real.cos (c * theta c Z) - Real.cos (c * theta c B)) := by
    conv_lhs => rw [theta_eq c Z, theta_eq c B]
    ring
  have hb : |B * (Real.cos (c * theta c Z) - Real.cos (c * theta c B))| ≤
      |c * B| * |theta c Z - theta c B| := by
    rw [abs_mul]
    calc
      _ ≤ |B| * |c * theta c Z - c * theta c B| :=
        mul_le_mul_of_nonneg_left (cos_distance_le _ _) (abs_nonneg B)
      _ = |c * B| * |theta c Z - theta c B| := by
        rw [← mul_sub, abs_mul, abs_mul]
        ring
  have hi : |theta c Z - theta c B| ≤ |Z - B| +
      |c * B| * |theta c Z - theta c B| := by
    conv_lhs => rw [he]
    exact (abs_add_le _ _).trans (add_le_add (abs_cos_mul_le _ _) hb)
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).mpr
  nlinarith

theorem theta_continuousAt {c B : ℝ} (hsmall : |c * B| < 1) :
    ContinuousAt (theta c) B := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : ContinuousAt (fun Z : ℝ => |Z - B| / (1 - |c * B|)) B := by fun_prop
  have ht : Tendsto (fun Z : ℝ => |Z - B| / (1 - |c * B|)) (𝓝 B) (𝓝 0) := by
    simpa only [ContinuousAt, sub_self, abs_zero, zero_div] using hc
  exact squeeze_zero (fun _ => norm_nonneg _) (fun Z => by
    simpa only [Real.norm_eq_abs] using theta_distance_le hsmall Z) ht

theorem hasFDerivAt_joint_residual (c B t : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => residual c p.1 p.2)
      ((-Real.cos (c * t)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1 + c * B * Real.sin (c * t)) • ContinuousLinearMap.snd ℝ ℝ ℝ) (B, t) := by
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) (B, t) := hasFDerivAt_snd
  have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (B, t) := hasFDerivAt_fst
  apply (hs.sub (hf.mul ((hs.const_mul c).cos))).congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  change p.2 - (B * (-Real.sin (c * t) * (c * p.2)) + Real.cos (c * t) * p.1) =
    -Real.cos (c * t) * p.1 + (1 + c * B * Real.sin (c * t)) * p.2
  ring

/-- Implicit differentiation proved from the joint Taylor remainder and the
proved root Lipschitz estimate; differentiability is not assumed. -/
theorem hasDerivAt_theta {c B : ℝ} (hsmall : |c * B| < 1) :
    HasDerivAt (theta c)
      (Real.cos (c * theta c B) / (1 + c * B * Real.sin (c * theta c B))) B := by
  let den := 1 + c * B * Real.sin (c * theta c B)
  have hd : 0 < den := by
    have hl := residual_derivative_lower c B (theta c B)
    dsimp [den]
    linarith
  have hgraph : ContinuousAt (fun Z => (Z, theta c Z)) B :=
    continuousAt_id.prodMk (theta_continuousAt hsmall)
  have he := (hasFDerivAt_joint_residual c B (theta c B)).isLittleO.comp_tendsto hgraph
  have hb : (fun Z => (Z, theta c Z) - (B, theta c B)) =O[𝓝 B] (fun Z => Z - B) := by
    apply IsBigO.of_bound (max 1 (1 / (1 - |c * B|)))
    apply Filter.Eventually.of_forall
    intro Z
    rw [Prod.norm_def]
    apply max_le
    · exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
    · have h := theta_distance_le hsmall Z
      rw [div_eq_mul_inv] at h
      change ‖theta c Z - theta c B‖ ≤ _
      calc
        _ ≤ (1 / (1 - |c * B|)) * ‖Z - B‖ := by
          simpa only [Real.norm_eq_abs, one_div, mul_comm] using h
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  have hscaled := (he.trans_isBigO hb).const_mul_left (-den⁻¹)
  rw [hasDerivAt_iff_isLittleO]
  apply hscaled.congr_left
  intro Z
  change -den⁻¹ * (residual c Z (theta c Z) - residual c B (theta c B) -
    (-Real.cos (c * theta c B) * (Z - B) + den * (theta c Z - theta c B))) =
    theta c Z - theta c B - (Z - B) * (Real.cos (c * theta c B) / den)
  rw [residual_theta, residual_theta]
  field_simp [ne_of_gt hd]
  ring

/-- The exact uniform perturbation estimate `eq:theta-error`, stated for the
actual derivative of the constructed root. -/
theorem theta_derivative_error {c B B₀ : ℝ} (hB : |B| ≤ B₀)
    (hsmall : |c| * B₀ ≤ 1 / 4) :
    |deriv (theta c) B - 1| ≤ 2 * c ^ 2 * B₀ ^ 2 := by
  let k := |c| * B₀
  let z := c * theta c B
  let den := 1 + c * B * Real.sin z
  have hB₀ : 0 ≤ B₀ := (abs_nonneg B).trans hB
  have hk : 0 ≤ k := mul_nonneg (abs_nonneg c) hB₀
  have hcb : |c * B| ≤ k := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hB (abs_nonneg c)
  have hcb1 : |c * B| < 1 := by dsimp [k] at hcb; linarith
  have hz : |z| ≤ k := by
    dsimp [z, k]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_theta_le c B).trans hB) (abs_nonneg c)
  have hsq : z ^ 2 ≤ k ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg z) hz
    simpa only [← sq, sq_abs] using h
  have htrig : |c * B * Real.sin z| ≤ k ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hcb (Real.abs_sin_le_abs.trans hz) (abs_nonneg _)
      hk).trans_eq (pow_two k).symm
  have hden : 3 / 4 ≤ den := by
    have h := residual_derivative_lower c B (theta c B)
    dsimp [den, z]
    dsimp [k] at hcb
    linarith
  have hdenpos : 0 < den := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) hden
  have hcos : |Real.cos z - 1| ≤ k ^ 2 / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one z))]
    have h := Real.one_sub_sq_div_two_le_cos (x := z)
    linarith
  have hnum : |Real.cos z - den| ≤ 3 * k ^ 2 / 2 := by
    have he : Real.cos z - den = (Real.cos z - 1) - c * B * Real.sin z := by
      dsimp [den]
      ring
    rw [he]
    have htri : |(Real.cos z - 1) - c * B * Real.sin z| ≤
        |Real.cos z - 1| + |c * B * Real.sin z| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (Real.cos z - 1) (-(c * B * Real.sin z))
    exact htri.trans (by linarith)
  rw [(hasDerivAt_theta hcb1).deriv]
  change |Real.cos z / den - 1| ≤ _
  rw [div_sub_one (ne_of_gt hdenpos), abs_div, abs_of_pos hdenpos]
  apply (div_le_iff₀ hdenpos).mpr
  have hk2 : k ^ 2 = c ^ 2 * B₀ ^ 2 := by
    dsimp [k]
    rw [mul_pow, sq_abs]
  have hm := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 2 * k ^ 2)
  calc
    |Real.cos z - den| ≤ 3 * k ^ 2 / 2 := hnum
    _ ≤ (2 * k ^ 2) * den := by nlinarith
    _ = 2 * c ^ 2 * B₀ ^ 2 * den := by rw [hk2]; ring

/-- Here `a = A / b` in the manuscript. -/
def lowerObjective (m a h B y : ℝ) : ℝ :=
  m / 2 * y ^ 2 - m * a * h * B * Real.sin (y / h)

def lowerGradient (m a h B y : ℝ) : ℝ :=
  m * (y - a * B * Real.cos (y / h))

def lowerRoot (a h B : ℝ) : ℝ := a * theta (a / h) B

theorem hasDerivAt_lowerObjective (m a B y : ℝ) {h : ℝ} (hh : h ≠ 0) :
    HasDerivAt (lowerObjective m a h B) (lowerGradient m a h B y) y := by
  convert (((hasDerivAt_id y).pow 2).const_mul (m / 2)).sub
    (((hasDerivAt_id y).div_const h).sin.const_mul (m * a * h * B)) using 1
  dsimp [lowerGradient]
  field_simp
  ring

theorem hasDerivAt_lowerGradient (m a h B y : ℝ) :
    HasDerivAt (lowerGradient m a h B)
      (m * (1 + (a / h) * B * Real.sin (y / h))) y := by
  convert ((hasDerivAt_id y).sub
    (((hasDerivAt_id y).div_const h).cos.const_mul (a * B))).const_mul m using 1
  dsimp
  ring

theorem lower_second_derivative (m a B y : ℝ) {h : ℝ} (hh : h ≠ 0) :
    deriv (deriv (lowerObjective m a h B)) y =
      m * (1 + (a / h) * B * Real.sin (y / h)) := by
  have he : deriv (lowerObjective m a h B) = lowerGradient m a h B := by
    funext t
    exact (hasDerivAt_lowerObjective m a B t hh).deriv
  rw [he]
  exact (hasDerivAt_lowerGradient m a h B y).deriv

theorem lower_second_derivative_lower {m a h B : ℝ} (hm : 0 ≤ m) (hh : h ≠ 0)
    (y : ℝ) :
    m * (1 - |(a / h) * B|) ≤ deriv (deriv (lowerObjective m a h B)) y := by
  rw [lower_second_derivative m a B y hh]
  apply mul_le_mul_of_nonneg_left _ hm
  simpa only [one_mul] using residual_derivative_lower 1 ((a / h) * B) (y / h)

theorem supporting_line_of_monotone_derivative (F G : ℝ → ℝ)
    (hd : ∀ y, HasDerivAt F (G y) y) (hmono : Monotone G) (x y : ℝ) :
    F x + G x * (y - x) ≤ F y := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope F G hxy hc.continuousOn
      (fun z _ => hd z)
    have hm := hmono ht.1.le
    rw [he] at hm
    have hb := (le_div_iff₀ (sub_pos.mpr hxy)).mp hm
    linarith
  · simp
  · obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope F G hyx hc.continuousOn
      (fun z _ => hd z)
    have hm := hmono ht.2.le
    rw [he] at hm
    have hb := (div_le_iff₀ (sub_pos.mpr hyx)).mp hm
    nlinarith

/-- Global first-order strong-convexity inequality of the actual sine
objective; any modulus below the proved Hessian lower bound is permitted. -/
theorem lower_strong_convexity {m a h B μ : ℝ} (hm : 0 ≤ m) (hh : h ≠ 0)
    (hμ : μ ≤ m * (1 - |(a / h) * B|)) (x y : ℝ) :
    lowerObjective m a h B x + lowerGradient m a h B x * (y - x) +
      μ / 2 * (y - x) ^ 2 ≤ lowerObjective m a h B y := by
  let F := fun t => lowerObjective m a h B t - μ / 2 * t ^ 2
  let G := fun t => lowerGradient m a h B t - μ * t
  have hd : ∀ t, HasDerivAt F (G t) t := by
    intro t
    convert (hasDerivAt_lowerObjective m a B t hh).sub
      (((hasDerivAt_id t).pow 2).const_mul (μ / 2)) using 1
    dsimp [G]
    ring
  have hgd : ∀ t, HasDerivAt G
      (m * (1 + (a / h) * B * Real.sin (t / h)) - μ) t := by
    intro t
    simpa only [G, mul_one] using (hasDerivAt_lowerGradient m a h B t).sub
      ((hasDerivAt_id t).const_mul μ)
  have hmono : Monotone G := by
    apply monotone_of_hasDerivAt_nonneg hgd
    intro t
    have hb := lower_second_derivative_lower (a := a) (B := B) hm hh t
    rw [lower_second_derivative m a B t hh] at hb
    change 0 ≤ m * (1 + (a / h) * B * Real.sin (t / h)) - μ
    exact sub_nonneg.mpr (hμ.trans hb)
  have ht := supporting_line_of_monotone_derivative F G hd hmono x y
  dsimp [F, G] at ht
  nlinarith

theorem lowerRoot_stationary (m a h B : ℝ) :
    lowerGradient m a h B (lowerRoot a h B) = 0 := by
  have ht := theta_eq (a / h) B
  have he : lowerRoot a h B / h = (a / h) * theta (a / h) B := by
    dsimp [lowerRoot]
    ring
  unfold lowerGradient
  rw [he]
  dsimp [lowerRoot]
  rw [mul_assoc a B, ← ht]
  ring

theorem lowerGradient_strictMono {m a h B : ℝ} (hm : 0 < m)
    (hsmall : |(a / h) * B| < 1) : StrictMono (lowerGradient m a h B) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_lowerGradient m a h B)
  intro y
  have hb : 0 < 1 + (a / h) * B * Real.sin (y / h) := by
    have hz : |(a / h) * B * Real.sin (y / h)| ≤ |(a / h) * B| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq
        (mul_one _)
    linarith [(abs_le.mp hz).1]
  exact mul_pos hm hb

theorem lowerRoot_unique_stationary {m a h B y : ℝ} (hm : 0 < m)
    (hsmall : |(a / h) * B| < 1) (hy : lowerGradient m a h B y = 0) :
    y = lowerRoot a h B :=
  (lowerGradient_strictMono hm hsmall).injective (hy.trans (lowerRoot_stationary m a h B).symm)

theorem strict_minimum_of_strictMono_derivative (F G : ℝ → ℝ) (r : ℝ)
    (hd : ∀ y, HasDerivAt F (G y) y) (hmono : StrictMono G) (hz : G r = 0)
    {y : ℝ} (hy : y ≠ r) : F r < F y := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  rcases lt_or_gt_of_ne hy with hyr | hry
  · obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope F G hyr hc.continuousOn
      (fun x _ => hd x)
    have hneg : G t < 0 := by simpa [hz] using hmono ht.2
    rw [he] at hneg
    have hdiff : F r - F y < 0 := by
      simpa using (div_lt_iff₀ (sub_pos.mpr hyr)).mp hneg
    linarith
  · obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope F G hry hc.continuousOn
      (fun x _ => hd x)
    have hpos : 0 < G t := by simpa [hz] using hmono ht.1
    rw [he] at hpos
    have hdiff : 0 < F y - F r := (div_pos_iff_of_pos_right (sub_pos.mpr hry)).mp hpos
    linarith

theorem lowerRoot_strict_minimum {m a h B y : ℝ} (hm : 0 < m) (hh : h ≠ 0)
    (hsmall : |(a / h) * B| < 1) (hy : y ≠ lowerRoot a h B) :
    lowerObjective m a h B (lowerRoot a h B) < lowerObjective m a h B y :=
  strict_minimum_of_strictMono_derivative _ _ _
    (fun y => hasDerivAt_lowerObjective m a B y hh)
    (lowerGradient_strictMono hm hsmall) (lowerRoot_stationary m a h B) hy

/-- The constructed root is the actual unique global lower minimizer, not
merely a solution of a stipulated stationarity relation. -/
theorem lowerRoot_unique_minimizer {m a h B : ℝ} (hm : 0 < m) (hh : h ≠ 0)
    (hsmall : |(a / h) * B| < 1) :
    (∀ y, lowerObjective m a h B (lowerRoot a h B) ≤ lowerObjective m a h B y) ∧
    (∀ y, (∀ z, lowerObjective m a h B y ≤ lowerObjective m a h B z) →
      y = lowerRoot a h B) := by
  constructor
  · intro y
    by_cases hy : y = lowerRoot a h B
    · simp [hy]
    · exact (lowerRoot_strict_minimum hm hh hsmall hy).le
  · intro y hy
    by_contra hne
    exact (not_le.mpr (lowerRoot_strict_minimum hm hh hsmall hne)) (hy _)

theorem abs_lowerRoot_le (a h B : ℝ) : |lowerRoot a h B| ≤ |a| * |B| := by
  unfold lowerRoot
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_theta_le _ _) (abs_nonneg a)

theorem lowerRoot_zero (a h : ℝ) : lowerRoot a h 0 = 0 := by
  simp [lowerRoot, theta_zero]

theorem actual_hyperobjective_identity (A b H B h : ℝ) (hb : b ≠ 0) :
    A * H + b * lowerRoot (A / b) h B = A * (H + theta ((A / b) / h) B) := by
  unfold lowerRoot
  field_simp
  ring

end Smoothness2601.SineLift
