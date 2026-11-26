import Matvec.SourceEstimatorReliable

/-! Explicit logarithmic bounds for the actual estimator schedule. -/

namespace Matvec
noncomputable section

theorem log_dimension_ge_one (d : ℕ) (hd : 2 ≤ d) :
    1 ≤ Real.log ((d : ℝ) + 2) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (show (4 : ℝ) ≤ d + 2 by linarith)
  have heq : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  rw [heq] at h
  linarith

def sourcePowerLogConstant (ν : ℝ) : ℝ := 6 + 2 * |Real.log (2 * ν)|

theorem sourcePowerLogConstant_pos (ν : ℝ) : 0 < sourcePowerLogConstant ν := by
  unfold sourcePowerLogConstant
  positivity

theorem sourcePower_length_log_bound (ν : ℝ) (hν : 0 < ν) (d : ℕ) (hd : 2 ≤ d) :
    (inversePowerLengthFor ν d : ℝ) ≤ sourcePowerLogConstant ν * Real.log ((d : ℝ) + 2) := by
  have hq := (inversePowerLengthFor_bounds ν hν d hd).2.1
  have hlog := log_dimension_ge_one d hd
  have ha := abs_nonneg (Real.log (2 * ν))
  unfold sourcePowerLogConstant
  nlinarith

/-- A polynomial lower bound for the chosen accuracy is enough to control
the refinement count logarithmically. -/
theorem sourcePower_accuracy_polynomial_lower (ν : ℝ) (hν : 0 < ν) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
      c / ((d : ℝ) + 2) ^ 2 ≤ inversePowerAccuracyFor ν d ∧ inversePowerAccuracyFor ν d ≤ 1 := by
  let C := sourcePowerLogConstant ν
  let c := min (ν / (8 * C)) (1 / (2 * C))
  have hC : 0 < C := sourcePowerLogConstant_pos ν
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, hc, ?_⟩
  intro d hd
  let t : ℝ := d + 2
  let q := inversePowerLengthFor ν d
  have ht : 4 ≤ t := by dsimp [t]; exact_mod_cast (show 4 ≤ d + 2 by omega)
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (inversePowerLengthFor_bounds ν hν d hd).1
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (inversePowerLengthFor_bounds ν hν d hd).1
  have hq : (q : ℝ) ≤ C * t := by
    have hlog := Real.log_le_sub_one_of_pos (show 0 < t by linarith)
    exact (sourcePower_length_log_bound ν hν d hd).trans
      (mul_le_mul_of_nonneg_left (by linarith : Real.log t ≤ t) hC.le)
  have hspos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < d by omega))
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hsd : Real.sqrt (d : ℝ) ≤ t := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [t]
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  constructor
  · apply le_min
    · calc
        c / t ^ 2 ≤ (ν / (8 * C)) / t ^ 2 :=
          div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
        _ = ν / (8 * C * t ^ 2) := by ring
        _ ≤ ν / (8 * (q : ℝ) * Real.sqrt d) := by
          apply div_le_div_of_nonneg_left hν.le (by positivity)
          have hh := mul_le_mul hq hsd hspos.le (by positivity : 0 ≤ C * t)
          nlinarith
    · calc
        c / t ^ 2 ≤ (1 / (2 * C)) / t ^ 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        _ = 1 / (2 * C * t ^ 2) := by ring
        _ ≤ 1 / (2 * (q : ℝ)) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          have hh : C * t ≤ C * t ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hC.le
          linarith
  · exact (min_le_right _ _).trans ((div_le_iff₀ (by positivity : 0 < 2 * (q : ℝ))).mpr (by nlinarith))

theorem source_refinement_length_log_bound (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (refinementLength (inversePowerAccuracyFor ν d) : ℝ) ≤ C * Real.log ((d : ℝ) + 2) := by
  obtain ⟨c, hc, hcBound⟩ := sourcePower_accuracy_polynomial_lower ν hν
  refine ⟨5 + 2 * |Real.log c|, by positivity, ?_⟩
  intro d hd
  let η := inversePowerAccuracyFor ν d
  have hη : 0 < η := (inversePowerAccuracyFor_bounds ν hν d hd).1
  obtain ⟨hlow, hupp⟩ := hcBound d hd
  have ht : 0 < (d : ℝ) + 2 := by positivity
  have hlog := Real.log_le_log (div_pos hc (sq_pos_of_pos ht)) hlow
  rw [Real.log_div (ne_of_gt hc) (ne_of_gt (sq_pos_of_pos ht)), Real.log_pow] at hlog
  change Real.log c - 2 * Real.log ((d : ℝ) + 2) ≤ Real.log η at hlog
  have ha : |Real.log η| ≤ |Real.log c| + 2 * Real.log ((d : ℝ) + 2) := by
    rw [abs_of_nonpos (Real.log_nonpos hη.le hupp)]
    have hh := neg_le_abs (Real.log c)
    linarith
  have hJ := (refinementLength_bounds η hη).1
  have hdim := log_dimension_ge_one d hd
  have habs := abs_nonneg (Real.log c)
  change (refinementLength η : ℝ) ≤ _
  nlinarith

/-- Both q and J are bounded by a common constant times log(d+2). -/
theorem source_schedule_log_bounds (ν : ℝ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (inversePowerLengthFor ν d : ℝ) ≤ C * Real.log ((d : ℝ) + 2) ∧
      (refinementLength (inversePowerAccuracyFor ν d) : ℝ) ≤ C * Real.log ((d : ℝ) + 2) := by
  obtain ⟨CJ, hCJ, hJ⟩ := source_refinement_length_log_bound ν hν
  refine ⟨sourcePowerLogConstant ν + CJ, add_pos (sourcePowerLogConstant_pos ν) hCJ, ?_⟩
  intro d hd
  have hlog : 0 ≤ Real.log ((d : ℝ) + 2) := le_trans (by norm_num) (log_dimension_ge_one d hd)
  constructor
  · exact (sourcePower_length_log_bound ν hν d hd).trans
      (mul_le_mul_of_nonneg_right (by linarith) hlog)
  · exact (hJ d hd).trans
      (mul_le_mul_of_nonneg_right (by linarith [sourcePowerLogConstant_pos ν]) hlog)

/-- Verification requires only logarithmically many repetitions in log d. -/
theorem source_verification_loglog_bound (ν θ : ℝ) (hν : 0 < ν) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      (sourceVerificationLength θ (inversePowerLengthFor ν d)
        (refinementLength (inversePowerAccuracyFor ν d)) : ℝ) + 2 ≤
      C * Real.log (Real.log ((d : ℝ) + 2) + 2) := by
  obtain ⟨C, hC, hbound⟩ := source_schedule_log_bounds ν hν
  let D := C ^ 2 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨10 + 4 * |Real.log θ| + 4 * |Real.log D|, by positivity, ?_⟩
  intro d hd
  let L := Real.log ((d : ℝ) + 2)
  let q := inversePowerLengthFor ν d
  let J := refinementLength (inversePowerAccuracyFor ν d)
  have hL : 1 ≤ L := log_dimension_ge_one d hd
  have hLpos : 0 < L + 2 := by linarith
  obtain ⟨hq, hJ⟩ := hbound d hd
  have hqJ : (q : ℝ) * J ≤ C ^ 2 * L ^ 2 := by
    have hh := mul_le_mul hq hJ (by positivity) (by positivity : 0 ≤ C * L)
    nlinarith
  have hden : 1 ≤ (q : ℝ) * J + 1 := by
    have hh : 0 ≤ (q : ℝ) * J := by positivity
    linarith
  have hdenupper : (q : ℝ) * J + 1 ≤ D * (L + 2) ^ 2 := by
    have hcsq := sq_nonneg C
    dsimp [D]
    nlinarith [sq_nonneg L, mul_nonneg hcsq (show 0 ≤ L by linarith)]
  have hlogden := Real.log_le_log (show 0 < (q : ℝ) * J + 1 by positivity) hdenupper
  rw [Real.log_mul hD.ne' (ne_of_gt (sq_pos_of_pos hLpos)), Real.log_pow] at hlogden
  norm_num only [Nat.cast_ofNat] at hlogden
  have hlogdenpos : 0 ≤ Real.log ((q : ℝ) * J + 1) := Real.log_nonneg hden
  have hlog : |Real.log (θ / ((q : ℝ) * J + 1))| ≤
      |Real.log θ| + |Real.log D| + 2 * Real.log (L + 2) := by
    rw [Real.log_div hθ.ne' (by positivity)]
    have ha := abs_sub (Real.log θ) (Real.log ((q : ℝ) * J + 1))
    rw [abs_of_nonneg hlogdenpos] at ha
    have hb := le_abs_self (Real.log D)
    linarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogL : (1 / 2 : ℝ) ≤ Real.log (L + 2) :=
    hlogtwo.trans (Real.log_le_log (by norm_num) (by linarith))
  have hR := (sourceVerificationLength_bounds θ hθ q J).1
  have ha := abs_nonneg (Real.log θ)
  have hb := abs_nonneg (Real.log D)
  change (sourceVerificationLength θ q J : ℝ) + 2 ≤ _
  nlinarith

theorem loglog_dimension_compare (d : ℕ) (hd : 14 ≤ d) :
    Real.log (Real.log ((d : ℝ) + 2) + 2) ≤ 2 * Real.log (Real.log ((d : ℝ) + 2)) := by
  have hd' : (14 : ℝ) ≤ d := by exact_mod_cast hd
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
    (show (16 : ℝ) ≤ d + 2 by linarith)
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 4 = 16 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 4
  rw [hlog16] at hlog
  have hL : 2 ≤ Real.log ((d : ℝ) + 2) := by linarith
  have h := Real.log_le_log (show 0 < Real.log ((d : ℝ) + 2) + 2 by linarith)
    (show Real.log ((d : ℝ) + 2) + 2 ≤ Real.log ((d : ℝ) + 2) ^ 2 by nlinarith)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- Explicit O(log² d log log d) overhead for one spectral estimate.
The theorem is a pointwise inequality for all d≥14, not a cost assumption. -/
theorem source_estimator_overhead_bound (ν θ : ℝ) (hν : 0 < ν) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 14 ≤ d →
      let q := inversePowerLengthFor ν d
      let J := refinementLength (inversePowerAccuracyFor ν d)
      let R := sourceVerificationLength θ q J
      (q : ℝ) * J * ((R : ℝ) + 2) ≤
        C * Real.log ((d : ℝ) + 2) ^ 2 * Real.log (Real.log ((d : ℝ) + 2)) := by
  obtain ⟨C, hC, hbound⟩ := source_schedule_log_bounds ν hν
  obtain ⟨CR, hCR, hR⟩ := source_verification_loglog_bound ν θ hν hθ
  refine ⟨2 * C ^ 2 * CR, by positivity, ?_⟩
  intro d hd
  dsimp only
  let L := Real.log ((d : ℝ) + 2)
  let q := inversePowerLengthFor ν d
  let J := refinementLength (inversePowerAccuracyFor ν d)
  let R := sourceVerificationLength θ q J
  obtain ⟨hq, hJ⟩ := hbound d (by omega)
  have hL : 0 ≤ L := le_trans (by norm_num) (log_dimension_ge_one d (by omega))
  have hqJ : (q : ℝ) * J ≤ C ^ 2 * L ^ 2 := by
    have hh := mul_le_mul hq hJ (by positivity) (by positivity : 0 ≤ C * L)
    nlinarith
  have hR' : (R : ℝ) + 2 ≤ CR * (2 * Real.log L) :=
    (hR d (by omega)).trans (mul_le_mul_of_nonneg_left (loglog_dimension_compare d hd) hCR.le)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (log_dimension_ge_one d (by omega))
  change (q : ℝ) * J * ((R : ℝ) + 2) ≤ _
  calc
    _ ≤ (C ^ 2 * L ^ 2) * (CR * (2 * Real.log L)) :=
      mul_le_mul hqJ hR' (by positivity) (by positivity)
    _ = _ := by ring

/-- The actual Policy cap from verification and residual updates has the
same overhead, including the verification matvec and each residual update. -/
theorem source_estimator_policy_cost_bound (ν θ : ℝ) (hν : 0 < ν) (hθ : 0 < θ) (S : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ d K : ℕ, 14 ≤ d →
      let q := inversePowerLengthFor ν d
      let J := refinementLength (inversePowerAccuracyFor ν d)
      let R := sourceVerificationLength θ q J
      (((S + 1) * (q * (J * ((R + 1) * (K + 1) + 1)))) : ℕ) ≤
        C * Real.log ((d : ℝ) + 2) ^ 2 * Real.log (Real.log ((d : ℝ) + 2)) * (K + 1 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := source_estimator_overhead_bound ν θ hν hθ
  refine ⟨(S + 1 : ℝ) * C, by positivity, ?_⟩
  intro d K hd
  dsimp only
  let q := inversePowerLengthFor ν d
  let J := refinementLength (inversePowerAccuracyFor ν d)
  let R := sourceVerificationLength θ q J
  have hc : ((R + 1) * (K + 1) + 1 : ℕ) ≤ (R + 2) * (K + 1) := by nlinarith
  have hn := Nat.mul_le_mul_left (S + 1) (Nat.mul_le_mul_left q (Nat.mul_le_mul_left J hc))
  have hn' : (((S + 1) * (q * (J * ((R + 1) * (K + 1) + 1)))) : ℕ) ≤
      (S + 1 : ℝ) * ((q : ℝ) * J * ((R : ℝ) + 2)) * (K + 1 : ℝ) := by
    have hh : (((S + 1) * (q * (J * ((R + 1) * (K + 1) + 1)))) : ℕ) ≤
        (((S + 1) * (q * (J * ((R + 2) * (K + 1))))) : ℝ) := by exact_mod_cast hn
    convert hh using 1 <;> push_cast <;> ring
  apply hn'.trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hbound d hd) (by positivity : (0 : ℝ) ≤ S + 1))
      (show (0 : ℝ) ≤ K + 1 by positivity)
  convert hh using 1 <;> ring

end
end Matvec
