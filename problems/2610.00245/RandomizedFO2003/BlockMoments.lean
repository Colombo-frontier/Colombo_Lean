import RandomizedFO2003.InverseApproximation
import RandomizedFO2003.WeightedEstimates
import RandomizedFO2003.Algebra

namespace RandomizedFO2003

open scoped BigOperators

variable {J : Type*} [Fintype J]

theorem inverse_weighted_energy_le (lam ω : J → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (hnode : ∀ j, γ ≤ lam j)
    (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1) :
    weightedEnergy ω (fun j => (lam j)⁻¹) ≤ γ⁻¹ ^ 2 := by
  calc
    _ ≤ ∑ j, ω j * γ⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hω j)
      have hj := hγ.trans_le (hnode j)
      have h := (inv_le_inv₀ hj hγ).mpr (hnode j)
      exact (sq_le_sq₀ (by positivity : 0 ≤ (lam j)⁻¹) (by positivity : 0 ≤ γ⁻¹)).mpr h
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem inverse_weighted_mean_le (lam ω : J → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (hnode : ∀ j, γ ≤ lam j)
    (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1) :
    (∑ j, ω j * (lam j)⁻¹) ≤ γ⁻¹ := by
  calc
    _ ≤ ∑ j, ω j * γ⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hω j)
      exact (inv_le_inv₀ (hγ.trans_le (hnode j)) hγ).mpr (hnode j)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

namespace FiniteSpectralDesign

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

/-- Spectral-coordinate formulas for the three inverse moments of the block.
The empirical weights are the squared spectral components of a unit vector. -/
noncomputable def alpha (ω : Fin D.size → ℝ) (h : ℝ) : ℝ :=
  h * weightedPair ω D.residual (fun j => (D.node j)⁻¹) /
    Real.sqrt (weightedEnergy ω D.residual)

noncomputable def beta (ω : Fin D.size → ℝ) : ℝ :=
  weightedEnergy (fun j => ω j * (D.node j)⁻¹) D.residual /
    weightedEnergy ω D.residual

noncomputable def rho (ω : Fin D.size → ℝ) (h : ℝ) : ℝ :=
  h ^ 2 * ∑ j, ω j * (D.node j)⁻¹

theorem inverse_norm_le (hγ : 0 < γ) :
    Real.sqrt (weightedEnergy D.weight (fun j => (D.node j)⁻¹)) ≤ γ⁻¹ := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨by positivity, inverse_weighted_energy_le D.node D.weight γ hγ
    (fun j => (D.node_mem j).1) (fun j => (D.weight_pos j).le) D.weight_sum⟩

theorem residual_norm_lower (hγ : 0 < γ) :
    1 / (16 * γ) ≤ Real.sqrt (weightedEnergy D.weight D.residual) := by
  exact (Real.le_sqrt (by positivity) (D.residual_energy_pos (by positivity)).le).mpr
    D.residual_energy_lower

/-- The potentially signed inverse pairing stays positive for relative error
at most 1/32. This justifies the lower bound more precisely than norm
equivalence alone. -/
theorem empirical_inverse_pairing_lower (hγ : 0 < γ)
    (ω : Fin D.size → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |ω j - D.weight j| ≤ δ * D.weight j) :
    weightedEnergy D.weight D.residual / 2 ≤
      weightedPair ω D.residual (fun j => (D.node j)⁻¹) := by
  have hstab := weighted_pair_stability D.weight ω D.residual
    (fun j => (D.node j)⁻¹) δ (fun j => (D.weight_pos j).le) hδ hweight
  change |weightedPair ω D.residual (fun j => (D.node j)⁻¹) -
    weightedPair D.weight D.residual (fun j => (D.node j)⁻¹)| ≤ _ at hstab
  have hpair0 : weightedPair D.weight D.residual (fun j => (D.node j)⁻¹) =
      weightedEnergy D.weight D.residual := D.inverse_pairing
  rw [hpair0] at hstab
  have hn := D.residual_norm_lower hγ
  have hi := D.inverse_norm_le hγ
  have hinv : γ⁻¹ / 16 ≤ Real.sqrt (weightedEnergy D.weight D.residual) := by
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hn
  have hδinv : δ * Real.sqrt (weightedEnergy D.weight (fun j => (D.node j)⁻¹)) ≤
      Real.sqrt (weightedEnergy D.weight D.residual) / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hi hδ
    have h2 := mul_le_mul_of_nonneg_right hδsmall (by positivity : 0 ≤ γ⁻¹)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hδinv
    (Real.sqrt_nonneg (weightedEnergy D.weight D.residual))
  have hsq := Real.sq_sqrt (weighted_energy_nonneg D.weight D.residual
    (fun j => (D.weight_pos j).le))
  have hleft := (abs_le.mp hstab).1
  nlinarith

theorem alpha_lower (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h δ : ℝ)
    (hh : 0 < h) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |ω j - D.weight j| ≤ δ * D.weight j) :
    h / (64 * γ) ≤ D.alpha ω h := by
  have hrpos := D.empirical_residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
    ω δ (by linarith) hweight
  have hnormpos := Real.sqrt_pos.mpr hrpos
  have hnpos := D.residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
  have hsqr := Real.sq_sqrt hnpos.le
  have hsqw := Real.sq_sqrt hrpos.le
  have hupper := (weighted_energy_stability D.weight ω D.residual δ hweight).2
  have hnupper : Real.sqrt (weightedEnergy ω D.residual) ≤
      2 * Real.sqrt (weightedEnergy D.weight D.residual) := by
    nlinarith [Real.sqrt_nonneg (weightedEnergy D.weight D.residual)]
  have hpair := D.empirical_inverse_pairing_lower hγ ω δ hδ hδsmall hweight
  have hn := D.residual_norm_lower hγ
  have hnorm : Real.sqrt (weightedEnergy D.weight D.residual) / 4 ≤
      weightedPair ω D.residual (fun j => (D.node j)⁻¹) /
        Real.sqrt (weightedEnergy ω D.residual) := by
    apply (le_div_iff₀ hnormpos).mpr
    have hp := mul_le_mul_of_nonneg_left hnupper
      (Real.sqrt_nonneg (weightedEnergy D.weight D.residual))
    nlinarith
  have hf := mul_le_mul_of_nonneg_left hnorm hh.le
  have hg := mul_le_mul_of_nonneg_left hn hh.le
  change h / (64 * γ) ≤ h * _ / _
  rw [mul_div_assoc] at *
  calc
    h / (64 * γ) = h * (1 / (16 * γ)) / 4 := by ring
    _ ≤ h * Real.sqrt (weightedEnergy D.weight D.residual) / 4 :=
      div_le_div_of_nonneg_right hg (by norm_num)
    _ ≤ _ := by simpa [mul_div_assoc] using hf

theorem short_polynomial_pairing_bound (ω : Fin D.size → ℝ) (δ : ℝ)
    (hω : ∀ j, 0 ≤ ω j) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hweight : ∀ j, |ω j - D.weight j| ≤ δ * D.weight j)
    (p : Polynomial ℝ) (hp : p.natDegree < m) :
    |weightedPair ω D.residual (fun j => p.eval (D.node j))| ≤ 2 * δ *
      (Real.sqrt (weightedEnergy ω D.residual) *
        Real.sqrt (weightedEnergy ω (fun j => p.eval (D.node j)))) :=
  empirical_orthogonality_bound D.weight ω D.residual (fun j => p.eval (D.node j)) δ
    (fun j => (D.weight_pos j).le) hω hδ hδhalf hweight (D.orthogonal p hp)

end FiniteSpectralDesign
end RandomizedFO2003

