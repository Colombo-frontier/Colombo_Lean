import BernoulliAffinity254

noncomputable section
open scoped BigOperators
namespace Paper254

def bernoulliPrefixRisk (θ : ℝ) (hθ : |θ| ≤ 1) (n : ℕ) (x : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ ω, ((productWeights (fun _ : Fin n => bernoulliWeights θ hθ)).weight ω*(x ω-θ)^2+
    (productWeights (fun _ : Fin n => bernoulliWeights (-θ) (by simpa using hθ))).weight ω*(x ω+θ)^2))/2

theorem bernoulli_prefix_risk (n : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1)
    (hinfo : (n : ℝ)*θ^2 ≤ 1/32) (x : (Fin n → Bool) → ℝ) :
    θ^2/2 ≤ bernoulliPrefixRisk θ hθ n x := by
  have ha := repeated_bernoulli_affinity n θ hθ
  exact affinity_risk_half _ _ θ x (by linarith)

/-- Every round uses its own prefix distribution. This excludes access to
future observations and keeps the sequential indexing explicit. -/
theorem sequential_two_point_risk (N : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1)
    (hinfo : (N : ℝ)*θ^2 ≤ 1/32) (x : (r : Fin N) → (Fin r.val → Bool) → ℝ) :
    (N : ℝ)*θ^2/2 ≤ ∑ r : Fin N, bernoulliPrefixRisk θ hθ r.val (x r) := by
  have hh : ∀ r : Fin N, θ^2/2 ≤ bernoulliPrefixRisk θ hθ r.val (x r) := by
    intro r
    apply bernoulli_prefix_risk
    have hr : (r.val : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt r.isLt
    have hm := mul_le_mul_of_nonneg_right hr (sq_nonneg θ)
    linarith
  have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin N))) => hh r)
  simpa [mul_div_assoc] using hs

theorem squared_loss_conditional_risk (x θ : ℝ) :
    ((1+θ)/2)*((x-1)^2/2-(θ-1)^2/2)+
      ((1-θ)/2)*((x+1)^2/2-(θ+1)^2/2) = (x-θ)^2/2 := by ring

end Paper254
#print axioms Paper254.sequential_two_point_risk
