import RandomizedFO2003.BlockMoments

namespace RandomizedFO2003.FiniteSpectralDesign

open scoped BigOperators

variable {m : ℕ} {γ L : ℝ} (D : FiniteSpectralDesign m γ L (1 / (16 * γ)))

theorem alpha_upper (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h : ℝ)
    (hh : 0 ≤ h) (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1)
    (hR : 0 < weightedEnergy ω D.residual) : D.alpha ω h ≤ h / γ := by
  have hcs := weighted_pair_abs_le ω D.residual (fun j => (D.node j)⁻¹) hω
  have hinv : Real.sqrt (weightedEnergy ω (fun j => (D.node j)⁻¹)) ≤ γ⁻¹ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, inverse_weighted_energy_le D.node ω γ hγ
      (fun j => (D.node_mem j).1) hω hsum⟩
  have hpair : weightedPair ω D.residual (fun j => (D.node j)⁻¹) ≤
      Real.sqrt (weightedEnergy ω D.residual) * γ⁻¹ :=
    (le_abs_self _).trans (hcs.trans
      (mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)))
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hR)).mpr
  change h * weightedPair ω D.residual (fun j => (D.node j)⁻¹) ≤ _
  calc
    _ ≤ h * (Real.sqrt (weightedEnergy ω D.residual) * γ⁻¹) :=
      mul_le_mul_of_nonneg_left hpair hh
    _ = _ := by ring

theorem beta_nonneg (hγ : 0 < γ) (ω : Fin D.size → ℝ)
    (hω : ∀ j, 0 ≤ ω j) : 0 ≤ D.beta ω := by
  apply div_nonneg
  · apply weighted_energy_nonneg
    intro j
    exact mul_nonneg (hω j) (inv_nonneg.mpr (hγ.le.trans (D.node_mem j).1))
  · exact weighted_energy_nonneg ω D.residual hω

theorem beta_upper (hγ : 0 < γ) (ω : Fin D.size → ℝ)
    (hω : ∀ j, 0 ≤ ω j) (hR : 0 < weightedEnergy ω D.residual) :
    D.beta ω ≤ γ⁻¹ := by
  apply (div_le_iff₀ hR).mpr
  change weightedEnergy (fun j => ω j * (D.node j)⁻¹) D.residual ≤ _
  simp only [weightedEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hi := (inv_le_inv₀ (hγ.trans_le (D.node_mem j).1) hγ).mpr (D.node_mem j).1
  have hh := mul_le_mul_of_nonneg_left hi (mul_nonneg (hω j) (sq_nonneg (D.residual j)))
  nlinarith

theorem rho_nonneg (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h : ℝ)
    (hω : ∀ j, 0 ≤ ω j) : 0 ≤ D.rho ω h := by
  apply mul_nonneg (sq_nonneg h)
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hω j) (inv_nonneg.mpr (hγ.le.trans (D.node_mem j).1))

theorem rho_upper (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h : ℝ)
    (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1) :
    D.rho ω h ≤ h ^ 2 / γ := by
  exact mul_le_mul_of_nonneg_left (inverse_weighted_mean_le D.node ω γ hγ
    (fun j => (D.node_mem j).1) hω hsum) (sq_nonneg h)

/-- Cauchy--Schwarz in the inverse spectral metric, for the actual moment
formulas. This supplies both remaining lower bounds from the alpha bound. -/
theorem moments_cauchy_schwarz (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h : ℝ)
    (hω : ∀ j, 0 ≤ ω j) (hR : 0 < weightedEnergy ω D.residual) :
    D.alpha ω h ^ 2 ≤ D.beta ω * D.rho ω h := by
  have hw' : ∀ j, 0 ≤ ω j * (D.node j)⁻¹ := by
    intro j
    exact mul_nonneg (hω j) (inv_nonneg.mpr (hγ.le.trans (D.node_mem j).1))
  have hcs := weighted_pair_sq_le (fun j => ω j * (D.node j)⁻¹)
    D.residual (fun _ => 1) hw'
  have hp : weightedPair (fun j => ω j * (D.node j)⁻¹) D.residual (fun _ => 1) =
      weightedPair ω D.residual (fun j => (D.node j)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he : weightedEnergy (fun j => ω j * (D.node j)⁻¹) (fun _ => 1) =
      ∑ j, ω j * (D.node j)⁻¹ := by simp [weightedEnergy]
  rw [hp, he] at hcs
  unfold alpha beta rho
  rw [div_pow, mul_pow, Real.sq_sqrt hR.le, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hR.le
  have hs := mul_le_mul_of_nonneg_left hcs (sq_nonneg h)
  nlinarith

theorem moment_lower_bounds (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h δ : ℝ)
    (hh : 0 < h) (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |ω j - D.weight j| ≤ δ * D.weight j) :
    1 / (4096 * γ) ≤ D.beta ω ∧ h ^ 2 / (4096 * γ) ≤ D.rho ω h := by
  have hR := D.empirical_residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
    ω δ (by linarith) hweight
  have ha := D.alpha_lower hγ ω h δ hh hδ hδsmall hweight
  have hcs := D.moments_cauchy_schwarz hγ ω h hω hR
  have hb := D.beta_upper hγ ω hω hR
  have hr := D.rho_upper hγ ω h hω hsum
  have hb0 := D.beta_nonneg hγ ω hω
  have hr0 := D.rho_nonneg hγ ω h hω
  have hasq : (h / (64 * γ)) ^ 2 ≤ D.alpha ω h ^ 2 :=
    (sq_le_sq₀ (by positivity) ((by positivity : 0 ≤ h / (64 * γ)).trans ha)).mpr ha
  have hβ : (h / (64 * γ)) ^ 2 ≤ D.beta ω * (h ^ 2 / γ) :=
    hasq.trans (hcs.trans (mul_le_mul_of_nonneg_left hr hb0))
  have hρ : (h / (64 * γ)) ^ 2 ≤ γ⁻¹ * D.rho ω h :=
    hasq.trans (hcs.trans (mul_le_mul_of_nonneg_right hb hr0))
  constructor
  · apply (mul_le_mul_right (show 0 < h ^ 2 / γ by positivity)).mp
    calc
      1 / (4096 * γ) * (h ^ 2 / γ) = (h / (64 * γ)) ^ 2 := by ring
      _ ≤ _ := hβ
  · apply (mul_le_mul_left (show 0 < γ⁻¹ by positivity)).mp
    calc
      γ⁻¹ * (h ^ 2 / (4096 * γ)) = (h / (64 * γ)) ^ 2 := by ring
      _ ≤ _ := hρ

/-- The deterministic part of Lemma blockmoments, with all constants explicit.
The random event's probability is a separate, still required theorem. -/
theorem normalized_moment_bounds (hγ : 0 < γ) (ω : Fin D.size → ℝ) (h δ : ℝ)
    (hh : 0 < h) (hω : ∀ j, 0 ≤ ω j) (hsum : ∑ j, ω j = 1)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 32)
    (hweight : ∀ j, |ω j - D.weight j| ≤ δ * D.weight j) :
    let α₀ := h / (64 * γ)
    let scale := h ^ 2 / γ
    let s := D.alpha ω h / α₀
    let k := scale * D.beta ω / α₀ ^ 2
    let r := D.rho ω h / scale
    (1 ≤ s ∧ s ≤ 64) ∧ (1 ≤ k ∧ k ≤ 4096) ∧
      (1 / 4096 ≤ r ∧ r ≤ 1) ∧ s ^ 2 ≤ k * r := by
  dsimp only
  have hR := D.empirical_residual_energy_pos (by positivity : 0 < 1 / (16 * γ))
    ω δ (by linarith) hweight
  have halo := D.alpha_lower hγ ω h δ hh hδ hδsmall hweight
  have hahi := D.alpha_upper hγ ω h hh.le hω hsum hR
  obtain ⟨hblo, hrlo⟩ := D.moment_lower_bounds hγ ω h δ hh hω hsum hδ hδsmall hweight
  have hbhi := D.beta_upper hγ ω hω hR
  have hrhi := D.rho_upper hγ ω h hω hsum
  have hα₀ : 0 < h / (64 * γ) := by positivity
  have hscale : 0 < h ^ 2 / γ := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact (le_div_iff₀ hα₀).mpr (by simpa using halo)
  · apply (div_le_iff₀ hα₀).mpr
    convert hahi using 1; ring
  · apply (le_div_iff₀ (sq_pos_of_pos hα₀)).mpr
    have hx := mul_le_mul_of_nonneg_left hblo hscale.le
    convert hx using 1; ring
  · apply (div_le_iff₀ (sq_pos_of_pos hα₀)).mpr
    have hx := mul_le_mul_of_nonneg_left hbhi hscale.le
    convert hx using 1; ring
  · apply (le_div_iff₀ hscale).mpr
    convert hrlo using 1; ring
  · exact (div_le_iff₀ hscale).mpr (by simpa using hrhi)
  · exact normalized_cauchy_schwarz _ _ _ _ _ hscale hα₀
      (D.moments_cauchy_schwarz hγ ω h hω hR)

end RandomizedFO2003.FiniteSpectralDesign
