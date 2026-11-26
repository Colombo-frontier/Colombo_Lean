import NCConcave16991.BranchConstructionPropagation
import NCConcave16991.BranchConstructionTerminal

/-! # Literal propagated Green columns of the branching inverse -/

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

theorem edge_propagation_pairing (t : Fin N) (z : Layers V) (a : V 0) :
    ⟪edge V B t z, propagation V B t.succ a⟫_ℝ =
      ⟪z t.succ, propagation V B t.succ a⟫_ℝ - ⟪z t.castSucc, propagation V B t.castSucc a⟫_ℝ := by
  rw [edge_apply, propagation_succ]
  change ⟪z t.succ - (B t).normalizedIsometry (z t.castSucc),
      (B t).normalizedIsometry (propagation V B t.castSucc a)⟫_ℝ =
    ⟪z t.succ, (B t).normalizedIsometry (propagation V B t.castSucc a)⟫_ℝ - _
  rw [inner_sub_left, (B t).normalizedIsometry.inner_map_map]

/-- Discrete integration by parts identifies the full vector operator on a
propagated scalar path with the actual scalar path matrix. -/
theorem massOperator_aligned_pairing (μ : ℝ) (c : Fin (N + 1) → ℝ) (a : V 0) (z : Layers V) :
    ⟪z, massOperator V B μ (aligned V B c a)⟫_ℝ =
      (fun j ↦ ⟪z j, propagation V B j a⟫_ℝ) ⬝ᵥ (PipeEnergy.massPath N μ *ᵥ c) := by
  rw [massOperator_bilinear, EndpointConstants.massPath_bilinear, PiLp.inner_apply]
  simp only [aligned_apply, aligned_edge, real_inner_smul_right, edge_propagation_pairing,
    PipeEnergy.incidence_mulVec]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro t _
    rw [PipeEnergy.incidence_mulVec, PipeEnergy.incidence_mulVec]
    ring

theorem massOperator_aligned_of_scalar_equation (μ : ℝ) (c : Fin (N + 1) → ℝ)
    (a : V 0) (j : Fin (N + 1))
    (hc : PipeEnergy.massPath N μ *ᵥ c = Pi.single j 1) :
    massOperator V B μ (aligned V B c a) = injection V j (propagation V B j a) := by
  apply ext_inner_left ℝ
  intro z
  rw [massOperator_aligned_pairing, hc, dotProduct_single_one]
  calc
    _ = ⟪propagation V B j a, z j⟫_ℝ := real_inner_comm _ _
    _ = ⟪injection V j (propagation V B j a), z⟫_ℝ := (injection_inner V j _ z).symm
    _ = _ := real_inner_comm _ _

variable [∀ j, FiniteDimensional ℝ (V j)]

theorem inverse_aligned_of_scalar_equation (μ : ℝ) (hμ : 0 < μ) (c : Fin (N + 1) → ℝ)
    (a : V 0) (j : Fin (N + 1))
    (hc : PipeEnergy.massPath N μ *ᵥ c = Pi.single j 1) :
    inverse V B μ hμ (injection V j (propagation V B j a)) = aligned V B c a := by
  rw [← massOperator_aligned_of_scalar_equation V B μ c a j hc, inverse_mass]

end

section Endpoints

noncomputable section

open Matrix
open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {m : ℕ} (V : Fin ((m + 1) + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)] [∀ j, FiniteDimensional ℝ (V j)]
  (B : ∀ t : Fin (m + 1), BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

theorem inverse_root_column (μ : ℝ) (hμ : 0 < μ) (a : V 0) :
    inverse V B μ hμ (injection V 0 a) =
      aligned V B (PipeEnergy.optimizer (PipeEnergy.massPath (m + 1) μ) (Pi.single 0 1)) a := by
  have hh := inverse_aligned_of_scalar_equation V B μ hμ
    (PipeEnergy.optimizer (PipeEnergy.massPath (m + 1) μ) (Pi.single 0 1)) a 0
    (PipeEnergy.optimizer_equation (PipeEnergy.massPath_posDef (m + 1) hμ) _)
  simpa only [propagation_zero, LinearIsometry.id_apply] using hh

theorem inverse_terminal_aligned_column (μ : ℝ) (hμ : 0 < μ) (a : V 0) :
    inverse V B μ hμ (injection V (Fin.last (m + 1)) (terminalTransport V B a)) =
      aligned V B (PipeEnergy.terminalGreen m μ) a := by
  exact inverse_aligned_of_scalar_equation V B μ hμ (PipeEnergy.terminalGreen m μ) a _
    (PipeEnergy.optimizer_equation (PipeEnergy.massPath_posDef (m + 1) hμ) _)

theorem inverse_root_terminal (a : V 0) :
    inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (injection V 0 a) (Fin.last (m + 1)) =
      EndpointConstants.endpointK m • terminalTransport V B a := by
  rw [inverse_root_column, EndpointConstants.rootGreen_reverse m (by positivity)]
  simp only [aligned_apply, EndpointConstants.reverseVector, Fin.rev_last, terminalTransport,
    ← EndpointConstants.endpointK_eq_green]

theorem inverse_root_root (a : V 0) :
    inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (injection V 0 a) 0 =
      (EndpointConstants.endpointC m * EndpointConstants.endpointK m) • a := by
  rw [inverse_root_column, EndpointConstants.rootGreen_reverse m (by positivity), aligned_apply]
  simp only [EndpointConstants.reverseVector, Fin.rev_zero, propagation_zero, LinearIsometry.id_apply,
    terminalGreen_last_normalized]

theorem terminalGreenOperator_on_transport (a : V 0) :
    terminalGreenOperator V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity) (terminalTransport V B a) =
      (EndpointConstants.endpointC m * EndpointConstants.endpointK m) • terminalTransport V B a := by
  change inverse V B (1 / ((m : ℝ) + 2) ^ 2) (by positivity)
    (injection V (Fin.last (m + 1)) (terminalTransport V B a)) (Fin.last (m + 1)) = _
  rw [inverse_terminal_aligned_column, aligned_apply, terminalGreen_last_normalized]
  rfl

end

end Endpoints

end NCConcave16991.BranchConstruction
