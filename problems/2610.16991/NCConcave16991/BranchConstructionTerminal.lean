import NCConcave16991.BranchConstructionOperator
import NCConcave16991.EndpointConstants

/-! # Actual terminal Green bound by scalar variational domination

The vector path energy dominates the scalar path energy of block norms.
Completing the scalar square therefore bounds the terminal block of the
actual branching inverse, with no assumed innovation decomposition.
-/

namespace NCConcave16991.BranchConstruction

noncomputable section

open Matrix
open scoped BigOperators InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 4

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)]
  (B : ∀ t : Fin N, BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

def injectionIsometry (j : Fin (N + 1)) : V j →ₗᵢ[ℝ] Layers V where
  toFun a := PiLp.single 2 j a
  map_add' := by
    intro a b
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [PiLp.single_eq_of_ne 2 hk]
  map_smul' := by
    intro c a
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [PiLp.single_eq_of_ne 2 hk]
  norm_map' a := PiLp.norm_single 2 V j a

def injection (j : Fin (N + 1)) : V j →L[ℝ] Layers V := (injectionIsometry V j).toContinuousLinearMap

theorem injection_inner (j : Fin (N + 1)) (a : V j) (w : Layers V) :
    ⟪injection V j a, w⟫_ℝ = ⟪a, w j⟫_ℝ := by
  change ⟪PiLp.single 2 j a, w⟫_ℝ = _
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [PiLp.single_eq_of_ne 2 hkj]
  · simp

theorem norm_energy_domination (μ : ℝ) (w : Layers V) :
    (fun j ↦ ‖w j‖) ⬝ᵥ (PipeEnergy.massPath N μ *ᵥ (fun j ↦ ‖w j‖)) ≤
      ⟪w, massOperator V B μ w⟫_ℝ := by
  rw [PipeEnergy.massPath_quadratic, massOperator_energy_literal]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro t _
  have hh := abs_norm_sub_norm_le (w t.succ) ((B t).normalizedIsometry (w t.castSucc))
  rw [(B t).normalizedIsometry.norm_map] at hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
  simpa only [sq_abs] using hs

theorem scalar_terminal_quadratic_bound (m : ℕ) (μ : ℝ) (hμ : 0 < μ) (s : ℝ)
    (c : Fin (m + 2) → ℝ) :
    2 * s * c (Fin.last (m + 1)) - c ⬝ᵥ (PipeEnergy.massPath (m + 1) μ *ᵥ c) ≤
      PipeEnergy.terminalGreen m μ (Fin.last (m + 1)) * s ^ 2 := by
  have hh := PipeEnergy.saddle_le_maximum (PipeEnergy.massPath_posDef (m + 1) hμ)
    (Pi.single (Fin.last (m + 1)) s) c
  have ht : PipeEnergy.terminalGreen m μ (Fin.last (m + 1)) =
      (PipeEnergy.massPath (m + 1) μ)⁻¹ (Fin.last (m + 1)) (Fin.last (m + 1)) := by
    simp [PipeEnergy.terminalGreen, PipeEnergy.optimizer]
  rw [ht]
  simp only [PipeEnergy.saddle, single_dotProduct, PipeEnergy.optimizer, Matrix.mulVec_single] at hh
  change s * c (Fin.last (m + 1)) - 1 / 2 * c ⬝ᵥ (PipeEnergy.massPath (m + 1) μ *ᵥ c) ≤
    1 / 2 * (s * ((PipeEnergy.massPath (m + 1) μ)⁻¹ (Fin.last (m + 1)) (Fin.last (m + 1)) * s)) at hh
  nlinarith only [hh]

theorem terminalGreen_last_normalized (m : ℕ) :
    PipeEnergy.terminalGreen m (1 / ((m : ℝ) + 2) ^ 2) (Fin.last (m + 1)) =
      EndpointConstants.endpointC m * EndpointConstants.endpointK m := by
  have hμ : 0 < 1 / ((m : ℝ) + 2) ^ 2 := by positivity
  rw [← EndpointConstants.inverse_endpoint_diagonal_eq m hμ]
  have hk : EndpointConstants.endpointK m ≠ 0 := by
    have hh := EndpointConstants.endpointK_lower m
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold EndpointConstants.endpointC
  field_simp [hk]

variable [∀ j, FiniteDimensional ℝ (V j)]

def terminalGreenOperator (μ : ℝ) (hμ : 0 < μ) : V (Fin.last N) →L[ℝ] V (Fin.last N) :=
  (PiLp.proj 2 V (Fin.last N)).comp ((inverse V B μ hμ).comp (injection V (Fin.last N)))

theorem terminalGreenOperator_nonneg (μ : ℝ) (hμ : 0 < μ) (b : V (Fin.last N)) :
    0 ≤ ⟪b, terminalGreenOperator V B μ hμ b⟫_ℝ := by
  have hh := inverse_energy_nonneg V B μ hμ (injection V (Fin.last N) b)
  rw [injection_inner] at hh
  exact hh

end

section Normalized

noncomputable section

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

/-- The exact source terminal Green upper bound, for the literal varying
branch-space inverse and arbitrary terminal connector direction. -/
theorem terminalGreenOperator_upper (b : V (Fin.last (m + 1))) :
    ⟪b, terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) b⟫_ℝ ≤
      EndpointConstants.endpointC m * EndpointConstants.endpointK m * ‖b‖ ^ 2 := by
  let μ : ℝ := 1 / ((m : ℝ) + 2) ^ 2
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let w := inverse V B μ hμ (injection V (Fin.last (m + 1)) b)
  have he : ⟪w, massOperator V B μ w⟫_ℝ = ⟪b, w (Fin.last (m + 1))⟫_ℝ := by
    rw [show massOperator V B μ w = injection V (Fin.last (m + 1)) b from mass_inverse V B μ hμ _]
    rw [real_inner_comm]
    exact injection_inner V _ b w
  have hc := real_inner_le_norm b (w (Fin.last (m + 1)))
  have henergy := norm_energy_domination V B μ w
  have hs := scalar_terminal_quadratic_bound m μ hμ ‖b‖ (fun j ↦ ‖w j‖)
  have ht := terminalGreen_last_normalized m
  change ⟪b, w (Fin.last (m + 1))⟫_ℝ ≤ _
  dsimp [μ] at hs
  rw [ht] at hs
  nlinarith only [he, hc, henergy, hs]

end

end Normalized

end NCConcave16991.BranchConstruction
