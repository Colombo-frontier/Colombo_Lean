import NCConcave16991.BranchConstructionColumns
import NCConcave16991.BranchConstructionElimination

/-! # Actual two-port eliminated energy and its terminal correction -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open Set
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

def portSource (a : V 0) (b : V (Fin.last (m + 1))) : Layers V :=
  injection V 0 a - injection V (Fin.last (m + 1)) b

def terminalCorrection : V (Fin.last (m + 1)) →L[ℝ] V (Fin.last (m + 1)) :=
  EndpointConstants.endpointD m • ContinuousLinearMap.id ℝ _ +
    (1 / (2 * EndpointConstants.endpointK m)) •
      terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity)

theorem terminalGreenOperator_symmetric (x y : V (Fin.last (m + 1))) :
    ⟪x, terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) y⟫_ℝ =
      ⟪terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) x, y⟫_ℝ := by
  let μ : ℝ := 1 / ((m : ℝ) + 2) ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  change ⟪x, inverse V B μ hμ (injection V (Fin.last (m + 1)) y) (Fin.last (m + 1))⟫_ℝ = _
  calc
    _ = ⟪injection V (Fin.last (m + 1)) x, inverse V B μ hμ (injection V (Fin.last (m + 1)) y)⟫_ℝ :=
      (injection_inner V _ x _).symm
    _ = ⟪inverse V B μ hμ (injection V (Fin.last (m + 1)) x), injection V (Fin.last (m + 1)) y⟫_ℝ :=
      inverse_symmetric V B μ hμ _ _
    _ = ⟪injection V (Fin.last (m + 1)) y, inverse V B μ hμ (injection V (Fin.last (m + 1)) x)⟫_ℝ := real_inner_comm _ _
    _ = ⟪y, inverse V B μ hμ (injection V (Fin.last (m + 1)) x) (Fin.last (m + 1))⟫_ℝ := injection_inner V _ y _
    _ = _ := real_inner_comm _ _

theorem terminalCorrection_lower (b : V (Fin.last (m + 1))) :
    EndpointConstants.endpointD m * ‖b‖ ^ 2 ≤ ⟪b, terminalCorrection V B b⟫_ℝ := by
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hg := terminalGreenOperator_nonneg V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) b
  simp only [terminalCorrection, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) hg)

theorem terminalCorrection_upper (b : V (Fin.last (m + 1))) :
    ⟪b, terminalCorrection V B b⟫_ℝ ≤ ‖b‖ ^ 2 := by
  have hk : 0 < EndpointConstants.endpointK m := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hh := mul_le_mul_of_nonneg_left (terminalGreenOperator_upper V B b)
    (by positivity : 0 ≤ 1 / (2 * EndpointConstants.endpointK m))
  simp only [terminalCorrection, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have he : (1 / (2 * EndpointConstants.endpointK m)) *
      (EndpointConstants.endpointC m * EndpointConstants.endpointK m * ‖b‖ ^ 2) =
      EndpointConstants.endpointC m / 2 * ‖b‖ ^ 2 := by field_simp [hk.ne']
  rw [he] at hh
  dsimp [EndpointConstants.endpointD]
  linarith

theorem terminalCorrection_on_transport (a : V 0) :
    terminalCorrection V B (terminalTransport V B a) = terminalTransport V B a := by
  have hk : EndpointConstants.endpointK m ≠ 0 := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  simp only [terminalCorrection, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, terminalGreenOperator_on_transport, smul_smul]
  rw [← add_smul]
  have he : EndpointConstants.endpointD m + (1 / (2 * EndpointConstants.endpointK m)) *
      (EndpointConstants.endpointC m * EndpointConstants.endpointK m) = 1 := by
    dsimp [EndpointConstants.endpointD]
    field_simp [hk]
    ring
  rw [he, one_smul]

def portInverseEnergy (a : V 0) (b : V (Fin.last (m + 1))) : ℝ :=
  ⟪portSource V a b,
    inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (portSource V a b)⟫_ℝ

theorem portInverseEnergy_formula (a : V 0) (b : V (Fin.last (m + 1))) :
    portInverseEnergy V B a b =
      (EndpointConstants.endpointC m * EndpointConstants.endpointK m) * ‖a‖ ^ 2 -
      2 * EndpointConstants.endpointK m * ⟪b, terminalTransport V B a⟫_ℝ +
      ⟪b, terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) b⟫_ℝ := by
  let μ : ℝ := 1 / ((m : ℝ) + 2) ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hroot : ⟪injection V 0 a, inverse V B μ hμ (injection V 0 a)⟫_ℝ =
      (EndpointConstants.endpointC m * EndpointConstants.endpointK m) * ‖a‖ ^ 2 := by
    rw [injection_inner, inverse_root_root, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hcross : ⟪injection V (Fin.last (m + 1)) b, inverse V B μ hμ (injection V 0 a)⟫_ℝ =
      EndpointConstants.endpointK m * ⟪b, terminalTransport V B a⟫_ℝ := by
    rw [injection_inner, inverse_root_terminal, real_inner_smul_right]
  have hother : ⟪injection V 0 a, inverse V B μ hμ (injection V (Fin.last (m + 1)) b)⟫_ℝ =
      EndpointConstants.endpointK m * ⟪b, terminalTransport V B a⟫_ℝ := by
    calc
      _ = ⟪inverse V B μ hμ (injection V 0 a), injection V (Fin.last (m + 1)) b⟫_ℝ := inverse_symmetric V B μ hμ _ _
      _ = ⟪injection V (Fin.last (m + 1)) b, inverse V B μ hμ (injection V 0 a)⟫_ℝ := real_inner_comm _ _
      _ = _ := hcross
  have hterminal : ⟪injection V (Fin.last (m + 1)) b,
      inverse V B μ hμ (injection V (Fin.last (m + 1)) b)⟫_ℝ =
      ⟪b, terminalGreenOperator V B μ hμ b⟫_ℝ := injection_inner V _ b _
  change ⟪portSource V a b, inverse V B μ hμ (portSource V a b)⟫_ℝ = _
  simp only [portSource, map_sub, inner_sub_left, inner_sub_right]
  rw [hroot, hcross, hother, hterminal]
  ring

def portValue (a : V 0) (b : V (Fin.last (m + 1))) : ℝ :=
  EndpointConstants.endpointD m * (‖a‖ ^ 2 + ‖b‖ ^ 2) +
    (1 / (2 * EndpointConstants.endpointK m)) * portInverseEnergy V B a b

/-- Exact E.12 endpoint energy for the literal branching inverse. -/
theorem portValue_formula (a : V 0) (b : V (Fin.last (m + 1))) :
    portValue V B a b = ‖a‖ ^ 2 - ⟪b, terminalTransport V B a⟫_ℝ + ⟪b, terminalCorrection V B b⟫_ℝ := by
  have hk : EndpointConstants.endpointK m ≠ 0 := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [portValue, portInverseEnergy_formula]
  simp only [terminalCorrection, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  dsimp [EndpointConstants.endpointD]
  field_simp [hk]
  ring

end

end NCConcave16991.BranchConstruction
