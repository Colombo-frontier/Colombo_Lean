import NCBall.SampleMean
import NCBall.GaussianMaximum
import NCBall.NoiseEmbedding

/-! # Integrability and the population mean for the actual Gaussian samples -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace NCBall

theorem gaussianReal_zero_map_neg (v : ℝ≥0) :
    Measure.map (fun x : ℝ => -x) (gaussianReal 0 v) = gaussianReal 0 v := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := v) (-1)
  norm_num at h
  exact h

theorem isotropicGaussian_neg_preserving (n : ℕ) :
    MeasurePreserving (fun x : Fin n → ℝ => -x) (isotropicGaussian n) (isotropicGaussian n) := by
  unfold isotropicGaussian diagonalGaussian
  exact measurePreserving_pi _ _ (fun _ => ⟨measurable_neg, gaussianReal_zero_map_neg _⟩)

theorem gaussianRooms_neg_preserving (n M : ℕ) :
    MeasurePreserving (fun z : Fin M → Fin n → ℝ => -z) (gaussianRooms n M) (gaussianRooms n M) := by
  unfold gaussianRooms
  exact measurePreserving_pi _ _ (fun _ => isotropicGaussian_neg_preserving n)

theorem transverseVector_neg {n : ℕ} (x : Fin n → ℝ) : transverseVector (-x) = -transverseVector x := by
  have heq : (Fin.cons 0 (-x) : Fin (n + 1) → ℝ) = -(Fin.cons 0 x : Fin (n + 1) → ℝ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold transverseVector
  rw [heq, map_neg]

theorem roomNoise_neg {n M : ℕ} (z : Fin M → Fin n → ℝ) (j : ℕ) : roomNoise (-z) j = -roomNoise z j := by
  unfold roomNoise
  split <;> simp [transverseVector_neg]

theorem gaussian_roomNoise_integrable {n M : ℕ} (hn : 0 < n) (j : ℕ) :
    Integrable (fun z : Fin M → Fin n → ℝ => roomNoise z j) (gaussianRooms n M) := by
  by_cases hj : j < M
  · have hi := (integrable_const (1 : ℝ) (μ := gaussianRooms n M)).add
      (gaussianRooms_maximum_integrable hn)
    apply hi.mono' (roomNoise_continuous n M j).aestronglyMeasurable
    filter_upwards [] with z
    have hb := le_nonnegativeMaximum Finset.univ (fun i => coordinateNormSq (z i))
      (Finset.mem_univ (⟨j, hj⟩ : Fin M))
    change coordinateNormSq (z ⟨j, hj⟩) ≤ maximumNormSq z at hb
    have he := roomNoise_norm_sq z hj
    have hm := nonnegativeMaximum_nonneg Finset.univ (fun i => coordinateNormSq (z i))
    change 0 ≤ maximumNormSq z at hm
    change ‖roomNoise z j‖ ≤ 1 + maximumNormSq z
    nlinarith [sq_nonneg (‖roomNoise z j‖ - 1)]
  · simpa only [roomNoise, dif_neg hj] using (integrable_const (0 : Space n) (μ := gaussianRooms n M))

theorem gaussian_roomNoise_mean_zero (n M j : ℕ) :
    (∫ z : Fin M → Fin n → ℝ, roomNoise z j ∂gaussianRooms n M) = 0 := by
  have h := integral_map (μ := gaussianRooms n M)
    (φ := fun z : Fin M → Fin n → ℝ => -z)
    (f := fun z : Fin M → Fin n → ℝ => roomNoise z j)
    measurable_neg.aemeasurable (roomNoise_continuous n M j).aestronglyMeasurable
  rw [(gaussianRooms_neg_preserving n M).map_eq] at h
  simp only [roomNoise_neg, integral_neg] at h
  have hz : (2 : ℝ) • (∫ z : Fin M → Fin n → ℝ, roomNoise z j ∂gaussianRooms n M) = 0 := by
    rw [two_smul]
    conv_lhs => lhs; rw [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Equation (6.15) with no centering or integrability assumptions left open. -/
theorem gaussian_sample_mean_eq_population {n M : ℕ} (hn : 0 < n)
    (ρ γ lam σ : ℝ) (c U : ℕ → Space n) (x : Space n) :
    (∫ z : Fin M → Fin n → ℝ,
      chainValue M ρ γ lam c (fun j => U j + σ • roomNoise z j) x ∂gaussianRooms n M) =
      chainValue M ρ γ lam c U x := by
  exact sample_mean_eq_population (gaussianRooms n M) ρ γ lam σ c U
    (fun j z => roomNoise z j) (fun j _ => gaussian_roomNoise_integrable hn j)
    (fun j _ => gaussian_roomNoise_mean_zero n M j) x

end NCBall
