import NCBall.FixedExperiment

/-! # Fixed-instance sample noise agrees with the verified stochastic class -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace NCBall

def normalizedTransverseCoordinates (n : ℕ) (a : Transverse n) : Fin n → ℝ :=
  fun i => (Real.sqrt (n : ℝ))⁻¹ * a i

theorem normalizedTransverseCoordinates_law (n : ℕ) :
    MeasurePreserving (normalizedTransverseCoordinates n)
      (euclideanGaussianLaw (Transverse n)) (isotropicGaussian n) := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  let v : Fin n → Transverse n := fun i => scale • EuclideanSpace.single i 1
  have hv (i j : Fin n) (hij : i ≠ j) : ⟪v i, v j⟫_ℝ = 0 := by
    dsimp only [v]
    rw [real_inner_smul_left, real_inner_smul_right,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, if_neg hij]
    simp
  have hi : (fun a : Transverse n => fun i => ⟪v i, a⟫_ℝ) = normalizedTransverseCoordinates n := by
    funext a i
    dsimp only [v]
    rw [real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    rfl
  have hs : scale ^ 2 = 1 / (n : ℝ) := by
    dsimp only [scale]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_div]
  have hnrm (i : Fin n) : ‖v i‖ ^ 2 = 1 / (n : ℝ) := by
    simp only [v, norm_smul, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one, sq_abs]
    exact hs
  have hg := gaussian_orthogonal_coordinates v hv
  rw [hi] at hg
  have hm : Measurable (normalizedTransverseCoordinates n) := by
    apply measurable_pi_lambda
    intro i
    have hp : Measurable (fun a : Transverse n => a i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i).measurable
    exact hp.const_mul _
  refine ⟨hm, ?_⟩
  convert hg using 1
  unfold isotropicGaussian
  congr 1
  funext i
  exact NNReal.eq (hnrm i).symm

def fixedSampleCoordinates {n K M : ℕ} (h : Fin K) (z : SampleTable n K M) :
    Fin M → Fin n → ℝ := fun j => normalizedTransverseCoordinates n (z j h)

theorem fixedSampleCoordinates_law {n K M : ℕ} (h : Fin K) :
    MeasurePreserving (fixedSampleCoordinates (n := n) (M := M) h)
      (sampleTableLaw n K M) (gaussianRooms n M) := by
  have he : MeasurePreserving (fun z : Fin K → Transverse n => z h)
      (Measure.pi (fun _ : Fin K => euclideanGaussianLaw (Transverse n)))
      (euclideanGaussianLaw (Transverse n)) :=
    ⟨measurable_pi_apply h, iidProduct_eval_map _ h⟩
  exact measurePreserving_pi _ _ (fun _ : Fin M => (normalizedTransverseCoordinates_law n).comp he)

theorem combined_latentSamples {n K M : ℕ} (σ : ℝ)
    (u : HiddenTable n M) (z : SampleTable n K M) (h : Fin K) :
    latentSamples σ (Real.sqrt (n : ℝ))⁻¹ ((splitRoomEquiv n K M).symm (u, z)) h =
      fun j => fixedDirections (Real.sqrt (n : ℝ))⁻¹ u j + σ • roomNoise (fixedSampleCoordinates h z) j := by
  funext j
  unfold latentSamples fixedDirections finiteRoomExtension roomNoise
  split_ifs
  · dsimp only
    rw [combined_hidden_block, combined_noise_block]
    rfl
  · simp

end NCBall
