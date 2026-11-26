import NCConcave16991.BranchConstructionOperator

/-! # Actual source propagation and scalar-chain embedding in the branch pipe -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open scoped BigOperators InnerProductSpace

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)]
  (B : ∀ t : Fin N, BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

def propagation (j : Fin (N + 1)) : V 0 →ₗᵢ[ℝ] V j :=
  Fin.induction (LinearIsometry.id : V 0 →ₗᵢ[ℝ] V 0) (fun t p ↦ (B t).normalizedIsometry.comp p) j

theorem propagation_zero : propagation V B 0 = (LinearIsometry.id : V 0 →ₗᵢ[ℝ] V 0) := by
  simp [propagation]

theorem propagation_succ (t : Fin N) :
    propagation V B t.succ = (B t).normalizedIsometry.comp (propagation V B t.castSucc) := by
  simp [propagation]

theorem propagation_norm (j : Fin (N + 1)) (a : V 0) : ‖propagation V B j a‖ = ‖a‖ :=
  (propagation V B j).norm_map a

theorem isometry_adjoint_left_inverse {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (U : E →ₗᵢ[ℝ] F) (x : E) : U.toContinuousLinearMap.adjoint (U x) = x := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact U.inner_map_map y x

def aligned (c : Fin (N + 1) → ℝ) (a : V 0) : Layers V :=
  WithLp.toLp 2 (fun j ↦ c j • propagation V B j a)

theorem aligned_apply (c : Fin (N + 1) → ℝ) (a : V 0) (j : Fin (N + 1)) :
    aligned V B c a j = c j • propagation V B j a := rfl

theorem aligned_edge (c : Fin (N + 1) → ℝ) (a : V 0) (t : Fin N) :
    edge V B t (aligned V B c a) = (c t.succ - c t.castSucc) • propagation V B t.succ a := by
  rw [edge_apply, aligned_apply, aligned_apply, propagation_succ]
  simp only [LinearIsometry.comp_apply, map_smul, sub_smul]
  rfl

theorem aligned_norm_sq (c : Fin (N + 1) → ℝ) (a : V 0) :
    ‖aligned V B c a‖ ^ 2 = ‖a‖ ^ 2 * ∑ j, (c j) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [aligned_apply, norm_smul, propagation_norm, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.sum_mul]
  ring

theorem aligned_energy (μ : ℝ) (c : Fin (N + 1) → ℝ) (a : V 0) :
    ⟪aligned V B c a, massOperator V B μ (aligned V B c a)⟫_ℝ =
      ‖a‖ ^ 2 * (μ * (∑ j, (c j) ^ 2) + ∑ t : Fin N, (c t.succ - c t.castSucc) ^ 2) := by
  rw [massOperator_energy, aligned_norm_sq]
  simp only [aligned_edge, norm_smul, propagation_norm, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← Finset.sum_mul]
  ring

/-- The mass lower spectral bound is attained on the actual propagated
constant path, not merely on a formal scalar surrogate. -/
theorem massOperator_aligned_constant (μ : ℝ) (a : V 0) :
    massOperator V B μ (aligned V B (fun _ ↦ 1) a) = μ • aligned V B (fun _ ↦ 1) a := by
  simp [massOperator, aligned_edge]

def terminalTransport : V 0 →ₗᵢ[ℝ] V (Fin.last N) := propagation V B (Fin.last N)

theorem terminalTransport_unit (a : V 0) (ha : ‖a‖ = 1) : ‖terminalTransport V B a‖ = 1 := by
  rw [terminalTransport, propagation_norm, ha]

end

end NCConcave16991.BranchConstruction
