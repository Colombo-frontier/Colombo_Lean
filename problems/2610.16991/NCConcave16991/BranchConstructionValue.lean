import NCConcave16991.BranchConstructionRadius

/-! # The exact attained endpoint value of the literal finite-sum pipe -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open Set
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

def paperAverage (a : V 0) (b : V (Fin.last (m + 1))) (w : Layers V) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * ∑ i, BranchGeometry.fullPipeComponent B (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2) a b (fun j ↦ w j) i

theorem paperAverage_eq_saddle (a : V 0) (b : V (Fin.last (m + 1))) (w : Layers V) :
    paperAverage V B a b w = EndpointConstants.endpointD m * (‖a‖ ^ 2 + ‖b‖ ^ 2) +
      saddle V B (1 / ((m : ℝ) + 2) ^ 2) (BranchGeometry.beta ι)
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m)) (portSource V a b) w := by
  rw [paperAverage, BranchGeometry.fullPipe_average]
  simp only [saddle, portSource, inner_sub_left, injection_inner, massOperator_energy_literal]
  ring

theorem paperValue_coefficient :
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m)) ^ 2 /
      (2 * BranchGeometry.beta ι) = 1 / (2 * EndpointConstants.endpointK m) := by
  have hβ := BranchGeometry.beta_pos ι
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [Real.sq_sqrt (div_nonneg hβ.le hk.le)]
  field_simp [hβ.ne', hk.ne']

/-- The actual component average attains the exact source endpoint formula
at the actual inverse-defined dual point with the proved public radius. -/
theorem paperAverage_at_optimizer (a : V 0) (b : V (Fin.last (m + 1))) :
    paperAverage V B a b (paperOptimizer V B a b) = portValue V B a b := by
  rw [paperAverage_eq_saddle, paperOptimizer,
    saddle_at_optimizer V B _ (by positivity) _ (BranchGeometry.beta_pos ι)]
  rw [paperValue_coefficient]
  rfl

theorem paperAverage_le_portValue (a : V 0) (b : V (Fin.last (m + 1))) (w : Layers V) :
    paperAverage V B a b w ≤ portValue V B a b := by
  have hh := saddle_le_maximum V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity)
    (BranchGeometry.beta ι) (BranchGeometry.beta_pos ι)
    (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m)) (portSource V a b) w
  rw [paperValue_coefficient] at hh
  rw [paperAverage_eq_saddle]
  exact add_le_add le_rfl hh

theorem paperAverage_isGreatest (a : V 0) (b : V (Fin.last (m + 1))) :
    IsGreatest (range (paperAverage V B a b)) (portValue V B a b) := by
  refine ⟨⟨paperOptimizer V B a b, paperAverage_at_optimizer V B a b⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact paperAverage_le_portValue V B a b w

theorem portValue_lower (a : V 0) (b : V (Fin.last (m + 1))) :
    EndpointConstants.endpointD m * (‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ portValue V B a b := by
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hE : 0 ≤ portInverseEnergy V B a b := inverse_energy_nonneg V B _ (by positivity) _
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) hE)

theorem portValue_upper (a : V 0) (b : V (Fin.last (m + 1))) :
    portValue V B a b ≤ (3 / 2 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hh := mul_le_mul_of_nonneg_left (portInverseEnergy_upper V B a b)
    (by positivity : 0 ≤ 1 / (2 * EndpointConstants.endpointK m))
  have he : (1 / (2 * EndpointConstants.endpointK m)) *
      (EndpointConstants.endpointK m * (EndpointConstants.endpointC m + 1) * (‖a‖ ^ 2 + ‖b‖ ^ 2)) =
      (EndpointConstants.endpointC m + 1) / 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by field_simp [hk.ne']
  rw [he] at hh
  dsimp [portValue, EndpointConstants.endpointD]
  nlinarith only [hh]

theorem portValue_lower_one_fifth (a : V 0) (b : V (Fin.last (m + 1)))
    (hab : 0 < ‖a‖ ^ 2 + ‖b‖ ^ 2) :
    (1 / 5 : ℝ) * (‖a‖ ^ 2 + ‖b‖ ^ 2) < portValue V B a b := by
  have hd := (EndpointConstants.endpointD_bounds m).1
  exact (mul_lt_mul_of_pos_right hd hab).trans_le (portValue_lower V B a b)

/-- Exact scalar source line energy, derived from the actual terminal
operator identity D(Pu)=Pu and the actual propagated unit vector. -/
theorem portValue_aligned (u : V 0) (hu : ‖u‖ = 1) (A C : ℝ) :
    portValue V B (A • u) (C • terminalTransport V B u) = A ^ 2 - A * C + C ^ 2 := by
  rw [portValue_formula]
  simp only [map_smul, terminalCorrection_on_transport, norm_smul, LinearIsometry.norm_map, hu,
    Real.norm_eq_abs, mul_one, sq_abs, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

end

end NCConcave16991.BranchConstruction
