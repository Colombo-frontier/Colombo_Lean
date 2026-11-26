import SecondOrder.AdaptiveSignConcentration

open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

def planarVector (u v : ℝ) : Point 2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![u,v]

theorem planarVector_norm_sq (u v : ℝ) : ‖planarVector u v‖^2 = u^2+v^2 := by
  simp [planarVector, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two,
    Real.norm_eq_abs, sq_abs]

def phaseVector (y : ℝ) : Point 2 := planarVector (Real.cos y) (Real.sin y)

theorem phaseVector_norm (y : ℝ) : ‖phaseVector y‖ = 1 := by
  have h := planarVector_norm_sq (Real.cos y) (Real.sin y)
  rw [Real.cos_sq_add_sin_sq] at h
  change ‖phaseVector y‖^2 = 1 at h
  nlinarith [norm_nonneg (phaseVector y)]

/-- The two-dimensional periodic mean from the curvature hard family. -/
def periodicMean {m : ℕ} (y : Fin (2*m) → ℝ) (w : BalancedVector m) : Point 2 :=
  planarVector (balancedVectorSum (fun i => Real.cos (y i)) w/(2*m:ℕ))
    (balancedVectorSum (fun i => Real.sin (y i)) w/(2*m:ℕ))

def periodicPotential {m : ℕ} (y : Fin (2*m) → ℝ) (w : BalancedVector m) : ℝ :=
  -‖periodicMean y w‖^2/2

theorem periodicMean_eq_average {m : ℕ} (y : Fin (2*m) → ℝ) (w : BalancedVector m) :
    periodicMean y w = ((2*m:ℕ):ℝ)⁻¹ • ∑ i, signValue (w.1 i) • phaseVector (y i) := by
  have hsum (i : Fin 2) :
      (∑ j, signValue (w.1 j) • phaseVector (y j)) i =
        ∑ j, (signValue (w.1 j) • phaseVector (y j)) i :=
    by simpa only [PiLp.proj_apply] using
      map_sum (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i)
        (fun j => signValue (w.1 j) • phaseVector (y j)) Finset.univ
  ext i
  simp only [periodicMean, hsum, PiLp.smul_apply]
  fin_cases i <;>
    simp [periodicMean, planarVector, phaseVector, balancedVectorSum,
      Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem periodicMean_norm_le_one {m : ℕ} (y : Fin (2*m) → ℝ) (w : BalancedVector m) :
    ‖periodicMean y w‖ ≤ 1 := by
  rw [periodicMean_eq_average, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ((2*m:ℕ):ℝ)⁻¹)]
  calc
    _ ≤ ((2*m:ℕ):ℝ)⁻¹ * ∑ i, ‖signValue (w.1 i) • phaseVector (y i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ((2*m:ℕ):ℝ)⁻¹ * (2*m:ℕ) := by
      congr 1
      calc
        _ = ∑ _i : Fin (2*m), (1:ℝ) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, phaseVector_norm, mul_one, Real.norm_eq_abs]
          cases hwi : w.1 i <;> norm_num [hwi, signValue]
        _ = _ := by simp
    _ ≤ 1 := by
      by_cases h : ((2*m:ℕ):ℝ) = 0
      · simp [h]
      · rw [inv_mul_cancel₀ h]

theorem periodicPotential_abs_le {m : ℕ} (y : Fin (2*m) → ℝ) (w : BalancedVector m) :
    |periodicPotential y w| ≤ 1/2 := by
  have hn := periodicMean_norm_le_one y w
  have h0 := norm_nonneg (periodicMean y w)
  rw [periodicPotential, abs_div, abs_neg, abs_of_nonneg (sq_nonneg _)]
  norm_num
  nlinarith

theorem periodicMean_joint_measurable {A : Type*} [MeasurableSpace A]
    {m : ℕ} {y : A → Fin (2*m) → ℝ} (hy : Measurable y) :
    Measurable (fun w : A × BalancedVector m => periodicMean (y w.1) w.2) := by
  have hc : Measurable (fun w : A × BalancedVector m =>
      balancedVectorSum (fun i => Real.cos (y w.1 i)) w.2/(2*m:ℕ)) :=
    (balancedVectorSum_joint_measurable (measurable_pi_lambda _
      (fun i => Real.continuous_cos.measurable.comp ((measurable_pi_apply i).comp hy)))).div_const _
  have hs : Measurable (fun w : A × BalancedVector m =>
      balancedVectorSum (fun i => Real.sin (y w.1 i)) w.2/(2*m:ℕ)) :=
    (balancedVectorSum_joint_measurable (measurable_pi_lambda _
      (fun i => Real.continuous_sin.measurable.comp ((measurable_pi_apply i).comp hy)))).div_const _
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 2 => ℝ)).measurable.comp
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact hc
  · exact hs

theorem planarVector_large_coordinate {u v : ℝ} {r : ℝ} (hr : 0 < r)
    (h : r < ‖planarVector u v‖) : r/Real.sqrt 2 ≤ |u| ∨ r/Real.sqrt 2 ≤ |v| := by
  by_contra hneg
  push_neg at hneg
  have hs : 0 < Real.sqrt 2 := by positivity
  have hs2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hu := (mul_lt_mul_right hs).mpr hneg.1
  have hv := (mul_lt_mul_right hs).mpr hneg.2
  rw [div_mul_cancel₀ _ hs.ne'] at hu hv
  have hu2 := mul_self_lt_mul_self (mul_nonneg (abs_nonneg u) hs.le) hu
  have hv2 := mul_self_lt_mul_self (mul_nonneg (abs_nonneg v) hs.le) hv
  have hn := planarVector_norm_sq u v
  nlinarith [sq_abs u, sq_abs v, norm_nonneg (planarVector u v)]

/-- The curvature activation tail, with the explicit exponent D/512. -/
theorem periodicMean_tail {m : ℕ} (y : Fin (2*m) → ℝ) :
    balancedVectorLaw m {w | 1/8 < ‖periodicMean y w‖} ≤
      ENNReal.ofReal (4*Real.exp (-((2*m:ℕ):ℝ)/512)) := by
  by_cases hm : m = 0
  · subst m
    have hz : ∀ w : BalancedVector 0, periodicMean y w = 0 := by
      intro w
      ext i
      fin_cases i <;> simp [periodicMean, balancedVectorSum, planarVector]
    simp_rw [hz]
    norm_num
  have hD : (0:ℝ) < (2*m:ℕ) := by exact_mod_cast Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hm)
  have hs : 0 < Real.sqrt 2 := by positivity
  let t : ℝ := (2*m:ℕ)/(8*Real.sqrt 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have he : -t^2/(4*(2*m:ℕ)) = -((2*m:ℕ):ℝ)/512 := by
    dsimp [t]
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hc := balancedVector_hoeffding (fun i => Real.abs_cos_le_one (y i)) ht
  have hs' := balancedVector_hoeffding (fun i => Real.abs_sin_le_one (y i)) ht
  rw [he] at hc hs'
  have hsub : {w | 1/8 < ‖periodicMean y w‖} ⊆
      {w | t ≤ |balancedVectorSum (fun i => Real.cos (y i)) w|} ∪
      {w | t ≤ |balancedVectorSum (fun i => Real.sin (y i)) w|} := by
    intro w hw
    have h := planarVector_large_coordinate (by norm_num : (0:ℝ) < 1/8) hw
    simp only [abs_div, abs_of_pos hD] at h
    rcases h with h | h
    · left
      have hh := (le_div_iff₀ hD).mp h
      convert hh using 1 <;> dsimp [t] <;> ring
    · right
      have hh := (le_div_iff₀ hD).mp h
      convert hh using 1 <;> dsimp [t] <;> ring
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hc hs')) |>.trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

theorem periodicMean_past_tail {A : Type*} [MeasurableSpace A]
    {η : Measure A} {m : ℕ} {y : A → Fin (2*m) → ℝ} (hy : Measurable y)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (balancedVectorLaw m)) {w | w.1 ∈ past ∧ 1/8 < ‖periodicMean (y w.1) w.2‖} ≤
      ENNReal.ofReal (4*Real.exp (-((2*m:ℕ):ℝ)/512))*η past :=
  fresh_event_past_bound
    (measurableSet_lt measurable_const (periodicMean_joint_measurable hy).norm)
    (fun z => periodicMean_tail (y z)) hp

end
end SecondOrder
