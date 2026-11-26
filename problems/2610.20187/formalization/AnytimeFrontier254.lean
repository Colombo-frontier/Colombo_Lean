import AnytimeRates254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem sum_min_three_le {ι : Type*} (s : Finset ι) (a b c : ι → ℝ) :
    (∑ j ∈ s,min (a j) (min (b j) (c j))) ≤
      min (∑ j ∈ s,a j) (min (∑ j ∈ s,b j) (∑ j ∈ s,c j)) := by
  apply le_min
  · exact Finset.sum_le_sum (fun j _ => min_le_left _ _)
  · apply le_min
    · exact Finset.sum_le_sum (fun j _ => (min_le_right _ _).trans (min_le_left _ _))
    · exact Finset.sum_le_sum (fun j _ => (min_le_right _ _).trans (min_le_right _ _))

theorem epoch_frontier_sum {ι : Type*} (s : Finset ι) (H P : ι → ℝ) (a b : ℝ)
    (hb : 0 ≤ b) (hH : ∀ j ∈ s,0 ≤ H j) (hP : ∀ j ∈ s,0 ≤ P j) :
    (∑ j ∈ s, (a + min (b*(H j)^(1/3:ℝ)*(P j)^(2/3:ℝ))
      (min (Real.sqrt (H j*(1+P j))) (H j)))) ≤
      s.card*a+min (b*(∑ j ∈ s,H j)^(1/3:ℝ)*(∑ j ∈ s,P j)^(2/3:ℝ))
        (min (Real.sqrt ((∑ j ∈ s,H j)*(s.card+∑ j ∈ s,P j))) (∑ j ∈ s,H j)) := by
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul]
  apply add_le_add_left
  apply (sum_min_three_le s _ _ _).trans
  apply min_le_min
  · have hh := mul_le_mul_of_nonneg_left (epoch_curved_sum s H P hH hP) hb
    simpa only [Finset.mul_sum,mul_assoc] using hh
  · exact min_le_min (epoch_sqrt_sum s H P hH hP) le_rfl

def anytimeFrontier (d T : ℕ) (P : ℝ) : ℝ :=
    (Nat.log 2 T+1 : ℝ)*d*logFactor T^2+
      min ((d:ℝ)^(1/3:ℝ)*logFactor T^(4/3:ℝ)*(2*T)^(1/3:ℝ)*P^(2/3:ℝ))
        (min (Real.sqrt ((2*T)*(Nat.log 2 T+1+P))) (2*T))

theorem logFactor_mono {H T : ℕ} (hH : 0 < H) (hHT : H ≤ T) : logFactor H ≤ logFactor T := by
  have hh : (0:ℝ)<H := by exact_mod_cast hH
  have ht : (H:ℝ)≤T := by exact_mod_cast hHT
  exact add_le_add_left (Real.log_le_log (by positivity) (by linarith)) 1

theorem upperFrontier_log_envelope (d H T : ℕ) (P : ℝ)
    (hH : 0 < H) (hHT : H ≤ T) (hP : 0 ≤ P) :
    upperFrontier d H P ≤ d*logFactor T^2+
      min ((d:ℝ)^(1/3:ℝ)*logFactor T^(4/3:ℝ)*(H:ℝ)^(1/3:ℝ)*P^(2/3:ℝ))
        (min (Real.sqrt (H*(1+P))) H) := by
  have hL : 0 ≤ logFactor H := (by norm_num : (0:ℝ) ≤ 1).trans (logFactor_ge_one H hH)
  have hmono := logFactor_mono hH hHT
  unfold upperFrontier curvedRate
  gcongr

end Paper254
#print axioms Paper254.epoch_frontier_sum
