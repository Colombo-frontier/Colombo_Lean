import MinimaxAudit.PotentialApproximation
import MinimaxAudit.SourceNormal
import MinimaxAudit.ChainExtra

/-! Explicit geometric parameter inequalities for the actual ideal witness. -/
namespace MinimaxAudit

theorem balancedQ_lt_one (n : ℕ) : balancedQ n < 1 := by
  unfold balancedQ
  have h : (0 : ℝ) < 1 / (4 * (n + 1 : ℝ)) := by positivity
  linarith

theorem source_tau_le_eta_seed {n : ℕ} {tau c : ℝ} (hc : 0 ≤ c)
    (ht : tau = geometryEta * c / (n+1 : ℝ)) : tau ≤ geometryEta * c := by
  rw [ht]
  apply div_le_self
  · unfold geometryEta
    positivity
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem source_deficit_bounds {n : ℕ} {tau c a s : ℝ} (hc : 0 ≤ c)
    (ht : tau = geometryEta * c / (n+1 : ℝ)) (ha : |a| ≤ tau)
    (hs : s = balancedQ n ^ n * c - a) : c / 2 ≤ s ∧ s ≤ c + tau := by
  have hpower := balancedQ_power_lower n
  have hpower1 := pow_le_one₀ (balancedQ_nonneg n) (balancedQ_le_one n) (n := n)
  have hp0 := mul_le_mul_of_nonneg_right hpower hc
  have hp1 := mul_le_mul_of_nonneg_right hpower1 hc
  have hsmall := source_tau_le_eta_seed (n := n) hc ht
  have heta : geometryEta ≤ (1 : ℝ) / 4 := by norm_num [geometryEta]
  have htquarter : tau ≤ c / 4 := by nlinarith
  obtain ⟨ha0,ha1⟩ := abs_le.mp ha
  constructor <;> rw [hs] <;> nlinarith

theorem sourceWeight_square_sum_le (q : ℝ) (n : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ i : Fin (n+1), sourceWeight q n i ^ 2) ≤ (n+1 : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin (n+1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      unfold sourceWeight
      exact pow_le_one₀ (pow_nonneg hq0 _) (pow_le_one₀ hq0 hq1) (n := 2)
    _ = _ := by simp

theorem source_seed_square_identity {n : ℕ} {c R : ℝ}
    (hc : c = geometryKappa * R / Real.sqrt (n+1)) :
    c ^ 2 * (n+1 : ℝ) = geometryKappa ^ 2 * R ^ 2 := by
  have hn : (0 : ℝ) < n+1 := by positivity
  rw [hc, div_pow, Real.sq_sqrt hn.le]
  field_simp

theorem source_parameter_perturbation_identity {n : ℕ} {tau c R : ℝ}
    (hc : c = geometryKappa * R / Real.sqrt (n+1))
    (ht : tau = geometryEta * c / (n+1 : ℝ)) :
    tau * R * Real.sqrt (n+1) = geometryEta / geometryKappa * c ^ 2 := by
  have hroot : Real.sqrt (n+1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
  have hk : geometryKappa ≠ 0 := by norm_num [geometryKappa]
  have hRdiv : R / Real.sqrt (n+1) = c / geometryKappa := by rw [hc]; field_simp
  calc
    tau * R * Real.sqrt (n+1) = geometryEta * c * (R / Real.sqrt (n+1)) := by
      rw [ht]
      field_simp
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n+1)]
      ring
    _ = geometryEta / geometryKappa * c ^ 2 := by rw [hRdiv]; ring

theorem source_weightWitness_small {n d : ℕ} {U : Fin (n+1) → Primal d}
    (hU : Orthonormal ℝ U) {tau c R s : ℝ} (hR : 0 ≤ R) (hc0 : 0 ≤ c)
    (hc : c = geometryKappa * R / Real.sqrt (n+1))
    (ht : tau = geometryEta * c / (n+1 : ℝ))
    (hs0 : 0 ≤ s) (hs1 : s ≤ c + tau) :
    ‖weightWitness hU (balancedQ n) s‖ ≤ geometryKappa * R := by
  have htC := source_tau_le_eta_seed (n := n) hc0 ht
  have heta : geometryEta ≤ (1 : ℝ) / 4 := by norm_num [geometryEta]
  have htquarter : tau ≤ c / 4 := by nlinarith
  have hsq : s ^ 2 ≤ 2 * c ^ 2 := by nlinarith
  have hw := sourceWeight_square_sum_le (balancedQ n) n (balancedQ_nonneg n) (balancedQ_le_one n)
  have hn := source_seed_square_identity hc
  have he := weightWitness_norm_sq hU (balancedQ n) s
  have hnorm : ‖weightWitness hU (balancedQ n) s‖ ^ 2 ≤ geometryKappa ^ 2 * R ^ 2 := by
    calc
      _ ≤ s ^ 2 / 2 * (n+1 : ℝ) := by rw [he]; exact mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ c ^ 2 * (n+1 : ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hsq (show 0 ≤ (n+1 : ℝ) by positivity)]
      _ = _ := hn
  have hkR : 0 ≤ geometryKappa * R := by unfold geometryKappa; positivity
  nlinarith [norm_nonneg (weightWitness hU (balancedQ n) s)]

end MinimaxAudit
