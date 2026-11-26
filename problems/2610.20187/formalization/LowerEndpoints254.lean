import EffectiveLower254

noncomputable section
open MeasureTheory
namespace Paper254

theorem small_path_rate (d T : ℕ) (hT : 0 < T) (P : ℝ) (hP : 0 ≤ P)
    (hsmall : P ≤ 4*d/Real.sqrt T) : unloggedRate d T P ≤ 3*d := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hs := (le_div_iff₀ (Real.sqrt_pos.2 hT0)).mp hsmall
  have hsq : (P*Real.sqrt T)^2 ≤ (4*(d : ℝ))^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4*(d : ℝ)-P*Real.sqrt T by linarith)
      (show 0 ≤ 4*(d : ℝ)+P*Real.sqrt T by positivity)]
  simp only [mul_pow,Real.sq_sqrt hT0.le] at hsq
  have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg d (α := ℝ))
  have hc := unloggedRate_cube d T P hP
  have hh : (unloggedRate d T P)^3 ≤ (3*(d : ℝ))^3 := by nlinarith [pow_nonneg (Nat.cast_nonneg d (α := ℝ)) 3]
  exact nonneg_le_of_cube_le _ _ (unloggedRate_nonneg d T P hP) (by positivity) hh

theorem saturation_parameters (T : ℕ) (hT : (4096 : ℝ) ≤ T) :
    4/Real.sqrt T ≤ (T : ℝ)/1024 ∧ (T : ℝ)/1024 ≤ T/8 ∧
    (T : ℝ)/128 ≤ unloggedRate 1 T (T/1024) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs := Real.sq_sqrt hT0.le
  have hn := Real.sqrt_nonneg (T : ℝ)
  have hs1 : 1 ≤ Real.sqrt (T : ℝ) := by nlinarith
  have hlo : 4/Real.sqrt T ≤ (T : ℝ)/1024 := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hT0)).mpr
    nlinarith [mul_nonneg hT0.le (show 0 ≤ Real.sqrt (T : ℝ)-1 by linarith)]
  have hc := unloggedRate_cube 1 T (T/1024) (by positivity)
  norm_num only [Nat.cast_one,one_mul] at hc
  have hcube : ((T : ℝ)/128)^3 ≤ (unloggedRate 1 T (T/1024))^3 := by
    nlinarith [pow_nonneg hT0.le 3]
  have hr := nonneg_le_of_cube_le _ _ (show 0 ≤ (T : ℝ)/128 by positivity)
    (unloggedRate_nonneg 1 T (T/1024) (by positivity)) hcube
  exact ⟨hlo,by linarith,hr⟩

theorem saturation_lower {d T : ℕ} (hd : 0 < d) (hT : 0 < T) (hlarge : (4096 : ℝ) ≤ T)
    (P : ℝ) (hP : (T : ℝ)/1024 ≤ P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → OnlineLearner (ballDomain d) T) (hA : SeedMeasurable A) :
    ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
      pathLength v ≤ P ∧ (T : ℝ)/262144 ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ := by
  obtain ⟨hlo,hhi,hrate⟩ := saturation_parameters T hlarge
  obtain ⟨s,v,hpath,hreg⟩ := effective_dimension_lower (d := d) (m := 1) (by norm_num) hd hT
    (T/1024) (by positivity) (by simpa using hlo) (by simpa using hhi) μ A hA
  exact ⟨s,v,hpath.trans hP,by linarith⟩

end Paper254
#print axioms Paper254.saturation_lower
