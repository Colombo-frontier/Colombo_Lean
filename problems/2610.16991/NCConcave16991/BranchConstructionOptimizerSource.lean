import NCConcave16991.BranchConstructionGradient

/-! # Actual source projections of the inverse-defined multiplier -/

namespace NCConcave16991.BranchConstruction
noncomputable section
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4
set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

theorem inverse_port_root_source (a u : V 0) (b : V (Fin.last (m + 1))) :
    ⟪u, inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (portSource V a b) 0⟫_ℝ =
      EndpointConstants.endpointC m * EndpointConstants.endpointK m * ⟪a, u⟫_ℝ -
        EndpointConstants.endpointK m * ⟪b, terminalTransport V B u⟫_ℝ := by
  rw [← injection_inner V 0 u, inverse_symmetric, portSource, inner_sub_right]
  have h0 : ⟪inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (injection V 0 u), injection V 0 a⟫_ℝ =
      EndpointConstants.endpointC m * EndpointConstants.endpointK m * ⟪a, u⟫_ℝ := by
    calc
      _ = ⟪injection V 0 a, inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (injection V 0 u)⟫_ℝ := real_inner_comm _ _
      _ = _ := by rw [injection_inner, inverse_root_root, real_inner_smul_right]
  have hN : ⟪inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (injection V 0 u), injection V (Fin.last (m + 1)) b⟫_ℝ =
      EndpointConstants.endpointK m * ⟪b, terminalTransport V B u⟫_ℝ := by
    calc
      _ = ⟪injection V (Fin.last (m + 1)) b, inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (injection V 0 u)⟫_ℝ := real_inner_comm _ _
      _ = _ := by rw [injection_inner, inverse_root_terminal, real_inner_smul_right]
  rw [h0, hN]

theorem inverse_port_terminal_source (a u : V 0) (b : V (Fin.last (m + 1))) :
    ⟪inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (portSource V a b) (Fin.last (m + 1)),
        terminalTransport V B u⟫_ℝ =
      EndpointConstants.endpointK m * ⟪a, u⟫_ℝ -
        EndpointConstants.endpointC m * EndpointConstants.endpointK m * ⟪b, terminalTransport V B u⟫_ℝ := by
  simp only [portSource, map_sub, PiLp.sub_apply, inner_sub_left]
  rw [inverse_root_terminal, real_inner_smul_left, (terminalTransport V B).inner_map_map]
  change _ - ⟪terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) b,
    terminalTransport V B u⟫_ℝ = _
  rw [← terminalGreenOperator_symmetric, terminalGreenOperator_on_transport, real_inner_smul_right]

theorem paperCoupling_normalization :
    Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
      (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) / BranchGeometry.beta ι) *
        EndpointConstants.endpointK m = 1 := by
  have hβ := BranchGeometry.beta_pos ι
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hs := Real.sq_sqrt (div_nonneg hβ.le hk.le)
  field_simp [hk.ne'] at hs
  field_simp [hβ.ne']
  nlinarith only [hs]

theorem paperOptimizer_root_source (a u : V 0) (b : V (Fin.last (m + 1))) :
    Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
      ⟪u, paperOptimizer V B a b 0⟫_ℝ =
        EndpointConstants.endpointC m * ⟪a, u⟫_ℝ - ⟪b, terminalTransport V B u⟫_ℝ := by
  change Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
    ⟪u, (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) / BranchGeometry.beta ι) •
      inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (portSource V a b) 0⟫_ℝ = _
  rw [real_inner_smul_right, inverse_port_root_source]
  have hh := paperCoupling_normalization (ι := ι) (m := m)
  calc
    _ = (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) / BranchGeometry.beta ι) * EndpointConstants.endpointK m) *
        (EndpointConstants.endpointC m * ⟪a, u⟫_ℝ - ⟪b, terminalTransport V B u⟫_ℝ) := by ring
    _ = _ := by rw [hh, one_mul]

theorem paperOptimizer_terminal_source (a u : V 0) (b : V (Fin.last (m + 1))) :
    Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
      ⟪paperOptimizer V B a b (Fin.last (m + 1)), terminalTransport V B u⟫_ℝ =
        ⟪a, u⟫_ℝ - EndpointConstants.endpointC m * ⟪b, terminalTransport V B u⟫_ℝ := by
  change Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
    ⟪(Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) / BranchGeometry.beta ι) •
      inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (portSource V a b) (Fin.last (m + 1)),
      terminalTransport V B u⟫_ℝ = _
  rw [real_inner_smul_left, inverse_port_terminal_source]
  have hh := paperCoupling_normalization (ι := ι) (m := m)
  calc
    _ = (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) *
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m) / BranchGeometry.beta ι) * EndpointConstants.endpointK m) *
        (⟪a, u⟫_ℝ - EndpointConstants.endpointC m * ⟪b, terminalTransport V B u⟫_ℝ) := by ring
    _ = _ := by rw [hh, one_mul]

end
end NCConcave16991.BranchConstruction
