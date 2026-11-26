import Mathlib

/-!
# Checked local excerpts of the task006 upper-bound argument

Source: `../input/source.tex`, in particular lines 117--179 (algorithm and
feasibility) and 329--340 (pointwise clipping inequalities U6).

These declarations formalize actual scalar clipping and geometric local lemmas.
They do not formalize the spherical concentration, Haar sampling, conditional
expectations, ghost coupling, or the complete minimax upper-bound theorem.
-/

namespace Task006.Full

/-- The manuscript's actual scalar clipping rule `sgn x * min (|x|) b`. -/
noncomputable def scalarClip (b x : ℝ) : ℝ :=
  (SignType.sign x : ℝ) * min |x| b

lemma abs_sign_cast_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    |(SignType.sign x : ℝ)| = 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [sign_neg h]
  · exact (hx h).elim
  · simp [sign_pos h]

lemma scalarClip_eq_self_of_abs_le {b x : ℝ} (h : |x| ≤ b) :
    scalarClip b x = x := by
  rw [scalarClip, min_eq_left h, sign_mul_abs]

lemma abs_scalarClip {b x : ℝ} (hb : 0 ≤ b) :
    |scalarClip b x| = min |x| b := by
  by_cases hx : x = 0
  · simp [scalarClip, hx, hb]
  · rw [scalarClip, abs_mul, abs_sign_cast_of_ne_zero hx, one_mul,
      abs_of_nonneg (le_min (abs_nonneg x) hb)]

lemma abs_sub_scalarClip {b x : ℝ} (hb : 0 ≤ b) :
    |x - scalarClip b x| = |x| - min |x| b := by
  by_cases hx : x = 0
  · simp [scalarClip, hx, hb]
  · have heq : x - scalarClip b x =
        (SignType.sign x : ℝ) * (|x| - min |x| b) := by
      dsimp [scalarClip]
      rw [mul_sub, sign_mul_abs]
    rw [heq, abs_mul, abs_sign_cast_of_ne_zero hx, one_mul,
      abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]

lemma scalarClip_sq {b x : ℝ} (hb : 0 ≤ b) :
    (scalarClip b x) ^ (2 : ℕ) = (min |x| b) ^ (2 : ℕ) := by
  rw [← sq_abs, abs_scalarClip hb]

lemma rpow_three_half_mul_half {a : ℝ} (ha : 0 ≤ a) :
    a ^ (3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a ^ (2 : ℕ) := by
  rw [← Real.rpow_add_of_nonneg ha (by norm_num) (by norm_num)]
  norm_num

lemma rpow_neg_half_mul_three_half {b : ℝ} (hb : 0 < b) :
    b ^ (-1 / 2 : ℝ) * b ^ (3 / 2 : ℝ) = b := by
  rw [← Real.rpow_add hb]
  norm_num

/-- Pointwise second-moment bound in U6 at the actual order r = 3/2. -/
theorem scalarClip_second_moment_pointwise {b x : ℝ} (hb : 0 < b) :
    (scalarClip b x) ^ (2 : ℕ) ≤
      b ^ (1 / 2 : ℝ) * |x| ^ (3 / 2 : ℝ) := by
  have hb0 : 0 ≤ b := le_of_lt hb
  rw [scalarClip_sq hb0]
  by_cases hxb : |x| ≤ b
  · rw [min_eq_left hxb]
    calc
      |x| ^ (2 : ℕ) = |x| ^ (3 / 2 : ℝ) * |x| ^ (1 / 2 : ℝ) :=
        (rpow_three_half_mul_half (abs_nonneg x)).symm
      _ ≤ |x| ^ (3 / 2 : ℝ) * b ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg x) hxb (by norm_num))
          (Real.rpow_nonneg (abs_nonneg x) _)
      _ = _ := mul_comm _ _
  · have hbx : b ≤ |x| := le_of_not_ge hxb
    rw [min_eq_right hbx]
    calc
      b ^ (2 : ℕ) = b ^ (1 / 2 : ℝ) * b ^ (3 / 2 : ℝ) := by
        rw [mul_comm, rpow_three_half_mul_half hb0]
      _ ≤ b ^ (1 / 2 : ℝ) * |x| ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hb0 hbx (by norm_num))
          (Real.rpow_nonneg hb0 _)

/-- Pointwise clipping-bias domination in U6 at the actual order r = 3/2. -/
theorem scalarClip_bias_pointwise {b x : ℝ} (hb : 0 < b) :
    |x - scalarClip b x| ≤
      b ^ (-1 / 2 : ℝ) * |x| ^ (3 / 2 : ℝ) := by
  by_cases hxb : |x| ≤ b
  · rw [scalarClip_eq_self_of_abs_le hxb, sub_self, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hb) _)
      (Real.rpow_nonneg (abs_nonneg x) _)
  · have hbx : b ≤ |x| := le_of_not_ge hxb
    have hxpos : 0 < |x| := lt_of_lt_of_le hb hbx
    have hhalf : b ^ (1 / 2 : ℝ) ≤ |x| ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hb) hbx (by norm_num)
    have hcancel : b ^ (-1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hb]
      norm_num
    have hbig : |x| ≤ b ^ (-1 / 2 : ℝ) * |x| ^ (3 / 2 : ℝ) := by
      calc
        |x| = |x| * (b ^ (-1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)) := by rw [hcancel]; ring
        _ ≤ |x| * (b ^ (-1 / 2 : ℝ) * |x| ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg (le_of_lt hb) _))
            (abs_nonneg x)
        _ = b ^ (-1 / 2 : ℝ) * |x| ^ (3 / 2 : ℝ) := by
          have hid : |x| * |x| ^ (1 / 2 : ℝ) = |x| ^ (3 / 2 : ℝ) := by
            calc
              |x| * |x| ^ (1 / 2 : ℝ) =
                  |x| ^ (1 : ℝ) * |x| ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
              _ = |x| ^ ((1 : ℝ) + (1 / 2 : ℝ)) :=
                (Real.rpow_add hxpos _ _).symm
              _ = |x| ^ (3 / 2 : ℝ) := by norm_num
          calc
            _ = b ^ (-1 / 2 : ℝ) * (|x| * |x| ^ (1 / 2 : ℝ)) := by ring
            _ = _ := by rw [hid]
    rw [abs_sub_scalarClip (le_of_lt hb), min_eq_right hbx]
    linarith

open MeasureTheory

/-- The two U6 integrands are integrable as a consequence of the actual
three-halves moment assumption. No finite-measure assumption is needed. -/
theorem scalarClip_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {D : Ω → ℝ} {b : ℝ}
    (hb : 0 < b) (hD : Measurable D)
    (hm : Integrable (fun ω => |D ω| ^ (3 / 2 : ℝ)) μ) :
    Integrable (fun ω => |D ω - scalarClip b (D ω)|) μ ∧
      Integrable (fun ω => (scalarClip b (D ω)) ^ (2 : ℕ)) μ := by
  have hmeasBias : Measurable (fun ω => |D ω - scalarClip b (D ω)|) := by
    have heq : (fun ω => |D ω - scalarClip b (D ω)|) =
        (fun ω => |D ω| - min |D ω| b) := by
      funext ω
      exact abs_sub_scalarClip (le_of_lt hb)
    rw [heq]
    exact hD.abs.sub (hD.abs.min measurable_const)
  have hmeasSq : Measurable (fun ω => (scalarClip b (D ω)) ^ (2 : ℕ)) := by
    have heq : (fun ω => (scalarClip b (D ω)) ^ (2 : ℕ)) =
        (fun ω => (min |D ω| b) ^ (2 : ℕ)) := by
      funext ω
      exact scalarClip_sq (le_of_lt hb)
    rw [heq]
    exact (hD.abs.min measurable_const).pow measurable_const
  constructor
  · refine (hm.const_mul (b ^ (-1 / 2 : ℝ))).mono'
      hmeasBias.aestronglyMeasurable ?_
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_abs] using scalarClip_bias_pointwise (x := D ω) hb
  · refine (hm.const_mul (b ^ (1 / 2 : ℝ))).mono'
      hmeasSq.aestronglyMeasurable ?_
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (scalarClip b (D ω)))] using
      scalarClip_second_moment_pointwise (x := D ω) hb

/-- Actual integrated U6, on any measure space, with the moment budget
explicitly supplied rather than the target inequalities assumed. -/
theorem scalarClip_integral_bounds {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {D : Ω → ℝ} {b M : ℝ}
    (hb : 0 < b) (hD : Measurable D)
    (hm : Integrable (fun ω => |D ω| ^ (3 / 2 : ℝ)) μ)
    (hM : (∫ ω, |D ω| ^ (3 / 2 : ℝ) ∂μ) ≤ M) :
    (∫ ω, |D ω - scalarClip b (D ω)| ∂μ) ≤ M * b ^ (-1 / 2 : ℝ) ∧
      (∫ ω, (scalarClip b (D ω)) ^ (2 : ℕ) ∂μ) ≤ M * b ^ (1 / 2 : ℝ) := by
  obtain ⟨hbias, hsq⟩ := scalarClip_integrable hb hD hm
  constructor
  · calc
      (∫ ω, |D ω - scalarClip b (D ω)| ∂μ) ≤
          ∫ ω, b ^ (-1 / 2 : ℝ) * |D ω| ^ (3 / 2 : ℝ) ∂μ :=
        integral_mono hbias (hm.const_mul _) (fun ω => scalarClip_bias_pointwise hb)
      _ = b ^ (-1 / 2 : ℝ) * (∫ ω, |D ω| ^ (3 / 2 : ℝ) ∂μ) :=
        integral_const_mul _ _
      _ ≤ b ^ (-1 / 2 : ℝ) * M :=
        mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg (le_of_lt hb) _)
      _ = _ := mul_comm _ _
  · calc
      (∫ ω, (scalarClip b (D ω)) ^ (2 : ℕ) ∂μ) ≤
          ∫ ω, b ^ (1 / 2 : ℝ) * |D ω| ^ (3 / 2 : ℝ) ∂μ :=
        integral_mono hsq (hm.const_mul _) (fun ω => scalarClip_second_moment_pointwise hb)
      _ = b ^ (1 / 2 : ℝ) * (∫ ω, |D ω| ^ (3 / 2 : ℝ) ∂μ) :=
        integral_const_mul _ _
      _ ≤ b ^ (1 / 2 : ℝ) * M :=
        mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg (le_of_lt hb) _)
      _ = _ := mul_comm _ _

/-- The stronger query-domain estimate used by the actual algorithm. -/
theorem query_feasible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x u q : E} {R ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hx : ‖x‖ ≤ R - (ρ + δ)) (hu : ‖u‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖x + ρ • u + δ • q‖ ≤ R ∧ ‖x + ρ • u - δ • q‖ ≤ R := by
  have hru : ‖ρ • u‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
    nlinarith
  have hdq : ‖δ • q‖ ≤ δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
    nlinarith
  constructor
  · have h1 := norm_add_le (x + ρ • u) (δ • q)
    have h2 := norm_add_le x (ρ • u)
    linarith
  · have h1 := norm_sub_le (x + ρ • u) (δ • q)
    have h2 := norm_add_le x (ρ • u)
    linarith


end Task006.Full
