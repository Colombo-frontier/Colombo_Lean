import SecondOrder.OjaMomentTail
import SecondOrder.TopRayleigh

open MeasureTheory
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- The moment ratio differs from one only on the learning-rate-squared
scale. The first-order terms cancel exactly. -/
theorem oja_moment_ratio_le_exp {η ℓ : ℝ} (hη : 0 ≤ η) (hℓ : 0 ≤ ℓ) (N : ℕ) :
    (1 + (4 * η + 11 * η^2) * ℓ)^N / ((1 + η * ℓ)^(2 * N))^2 ≤
      Real.exp (11 * η^2 * ℓ * (N : ℝ)) := by
  have ht : 0 ≤ η * ℓ := mul_nonneg hη hℓ
  have hd : 0 < 1 + η * ℓ := by positivity
  have hfour : 1 + 4 * (η * ℓ) ≤ (1 + η * ℓ)^4 := by
    simpa using (one_add_mul_le_pow (by linarith : -2 ≤ η * ℓ) 4)
  have hone : 1 ≤ (1 + η * ℓ)^4 := by nlinarith
  have hc : 0 ≤ 11 * η^2 * ℓ := by positivity
  have hbase : (1 + (4 * η + 11 * η^2) * ℓ) / (1 + η * ℓ)^4 ≤
      Real.exp (11 * η^2 * ℓ) := by
    calc
      _ ≤ 1 + 11 * η^2 * ℓ := by
        apply (div_le_iff₀ (pow_pos hd 4)).mpr
        have hh := mul_le_mul_of_nonneg_left hone hc
        nlinarith
      _ ≤ _ := by simpa [add_comm] using Real.add_one_le_exp (11 * η^2 * ℓ)
  have hpow : ((1 + η * ℓ)^(2 * N))^2 = ((1 + η * ℓ)^4)^N := by
    simp only [← pow_mul]
    congr 1
    omega
  rw [hpow, ← div_pow]
  calc
    _ ≤ (Real.exp (11 * η^2 * ℓ))^N :=
      pow_le_pow_left₀ (by positivity) hbase N
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem oja_moment_tail_scale {η ℓ p : ℝ} (hη : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) (hscale : η^2 * ℓ * (N : ℝ) ≤ p / 100) :
    4 * ((1 + (4 * η + 11 * η^2) * ℓ)^N / ((1 + η * ℓ)^(2 * N))^2 - 1) ≤ p := by
  have ht0 : 0 ≤ 11 * η^2 * ℓ * (N : ℝ) := by positivity
  have ht1 : 11 * η^2 * ℓ * (N : ℝ) ≤ 1 := by nlinarith
  have he := (le_abs_self (Real.exp (11 * η^2 * ℓ * (N : ℝ)) - 1)).trans
    (Real.abs_exp_sub_one_le (by rwa [abs_of_nonneg ht0]))
  rw [abs_of_nonneg ht0] at he
  have hr := oja_moment_ratio_le_exp hη hℓ N
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.ojaRawRun_growth_probability (h : CommonLoss μ P ν F f)
    {η ℓ p : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hℓ0 : 0 ≤ ℓ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (x v : Point d)
    (hℓ : ∀ u, ⟪shiftedHessian (eigenHessianBound P) (hessian F x) u, u⟫_ℝ ≤ ℓ * ‖u‖^2)
    (hv : shiftedHessian (eigenHessianBound P) (hessian F x) v = ℓ • v)
    (hv1 : ‖v‖ = 1) (N : ℕ) (hscale : η^2 * ℓ * (N : ℝ) ≤ p / 100) :
    drawsLaw μ N {w | ‖ojaRawRun P f η x v N w‖^2 ≤ (1 + η * ℓ)^(2 * N) / 2} ≤
      ENNReal.ofReal p :=
  (h.ojaRawRun_growth_lower_tail hη hη1 hℓ0 x v hℓ hv hv1 N).trans
    (ENNReal.ofReal_le_ofReal (oja_moment_tail_scale hη hℓ0 hp hp1 N hscale))

/-- The required analytic eigenvector exists under the original model in
positive dimension. No eigenvector is supplied to the actual oracle routine. -/
theorem CommonLoss.ojaRawRun_top_growth (h : CommonLoss μ P ν F f) (hd : 0 < d)
    {η p : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Point d) (N : ℕ)
    (hscale : η^2 * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)) *
      (N : ℝ) ≤ p / 100) :
    ∃ v : Point d, ‖v‖ = 1 ∧
      drawsLaw μ N {w | ‖ojaRawRun P f η x v N w‖^2 ≤
        (1 + η * topRayleigh (shiftedHessian (eigenHessianBound P) (hessian F x)))^(2 * N) / 2} ≤
        ENNReal.ofReal p := by
  obtain ⟨hℓ0, _, hℓ, v, hv1, hv⟩ := h.mean_shifted_top_eigenpair hd x
  exact ⟨v, hv1, h.ojaRawRun_growth_probability hη hη1 hℓ0 hp hp1 x v hℓ hv hv1 N hscale⟩

end
end SecondOrder
