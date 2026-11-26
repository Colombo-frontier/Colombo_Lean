import Paper254

open scoped Matrix.Norms.Operator
open Paper254

example {d : ℕ} (hd : 0<d) (a L s : ℕ) (hdim : (d:ℝ)≤(2:ℝ)^a)
    (A : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (v : Coordinates d) (hv : ∀ j,0<v j) (hA : realMatrix A=rotatedPrecision U v)
    (hlo : ∀ j,((2:ℝ)^L)⁻¹≤Real.sqrt (v j))
    (hhi : ∀ j,Real.sqrt (v j)≤(2:ℝ)^L) :
    ‖realMatrix (certifiedMatrixSqrt a L s A)-rotatedPrecision U (fun j=>Real.sqrt (v j))‖≤
      ((2:ℝ)^s)⁻¹ := certifiedMatrixSqrt_error hd a L s hdim A U v hv hA hlo hhi

example {d : ℕ} (S : RationalHistoryData d) (hS : (realMatrix S.covariance).PosDef)
    (lam : ℚ) (g : Fin d→ℚ) : (realMatrix (rationalTiltPrecision S lam g)).PosDef :=
  rationalTiltPrecision_posDef S hS lam g

#print axioms Paper254.inverse_perturbation
#print axioms Paper254.rounded_newton_trajectory
#print axioms Paper254.certifiedMatrixSqrt_error
#print axioms Paper254.rationalSpectralClip_interval
#print axioms Paper254.rounded_spectralClip_original_error
#print axioms Paper254.rationalSpectralClip_symmetric
#print axioms Paper254.precision_potential_perturbation
#print axioms Paper254.rounded_projection_input_gap
#print axioms Paper254.projected_mean_coordinate_error
#print axioms Paper254.history_one_step_entry_error
#print axioms Paper254.rounded_history_movement
#print axioms Paper254.precision_bounds_from_covariance
#print axioms Paper254.rationalMetricRound_posDef
#print axioms Paper254.rationalHistoryStep_feasible_of_guards
#print axioms Paper254.rationalProjection_inputs_encoding
#print axioms Paper254.covariance_precision_entry_error

-- Execute the rational matrix program on a nondiagonal SPD input.
#eval let A : Matrix (Fin 2) (Fin 2) ℚ := !![2,1;1,2]
      let B := certifiedMatrixSqrt 1 1 8 A
      decide (1<B 0 0 ∧ B 0 0<2 ∧ 0<B 0 1 ∧ B 0 1<1)

-- Execute smoothing, matrix iteration, symmetrization and final dyadic rounding.
#eval let A : Matrix (Fin 2) (Fin 2) ℚ := !![2,1;1,2]
      let C := roundRationalMatrix 10 (rationalSpectralClip 1 9 8 (1/256) (5/4) (7/4) A)
      decide (1<C 0 0 ∧ C 0 0<2 ∧ 0<C 0 1 ∧ C 0 1<1 ∧ C 0 1=C 1 0)
