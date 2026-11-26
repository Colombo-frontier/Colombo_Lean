import NCConcave16991.BranchConstructionPropagation

/-! # Actual orthogonal conjugation of branch maps and propagated sources -/

namespace NCConcave16991.BranchConstruction

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem normalizedIsometry_conjugate
    {H K H' K' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [NormedAddCommGroup H'] [InnerProductSpace ℝ H']
    [NormedAddCommGroup K'] [InnerProductSpace ℝ K']
    (B : BranchGeometry.BranchFamily (ι := ι) H K)
    (R : H' ≃ₗᵢ[ℝ] H) (S : K ≃ₗᵢ[ℝ] K') (x : H') :
    (B.conjugate R S).normalizedIsometry x = S (B.normalizedIsometry (R x)) := by
  rw [BranchGeometry.BranchFamily.normalizedIsometry_apply,
    BranchGeometry.BranchFamily.normalizedIsometry_apply]
  change (BranchGeometry.beta ι) • (∑ i, S (B.branch i (R x))) =
    S ((BranchGeometry.beta ι) • ∑ i, B.branch i (R x))
  rw [map_smul, map_sum]

variable {N : ℕ} (V : Fin (N + 1) → Type*)
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
  [∀ j, CompleteSpace (V j)]
  (B : ∀ t : Fin N, BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ))

def rotatedBranches (O : ∀ j, V j ≃ₗᵢ[ℝ] V j) (t : Fin N) :
    BranchGeometry.BranchFamily (ι := ι) (V t.castSucc) (V t.succ) :=
  (B t).conjugate (O t.castSucc).symm (O t.succ)

theorem propagation_rotated (O : ∀ j, V j ≃ₗᵢ[ℝ] V j) (j : Fin (N + 1)) (a : V 0) :
    propagation V (rotatedBranches V B O) j (O 0 a) = O j (propagation V B j a) := by
  induction j using Fin.induction with
  | zero => simp [propagation_zero]
  | succ t ih =>
      rw [propagation_succ, propagation_succ]
      change (rotatedBranches V B O t).normalizedIsometry
        (propagation V (rotatedBranches V B O) t.castSucc (O 0 a)) =
          O t.succ ((B t).normalizedIsometry (propagation V B t.castSucc a))
      rw [ih]
      unfold rotatedBranches
      rw [normalizedIsometry_conjugate, LinearIsometryEquiv.symm_apply_apply]

def source (O : ∀ j, V j ≃ₗᵢ[ℝ] V j) (a : V 0) (j : Fin (N + 1)) : V j :=
  O j (propagation V B j a)

theorem source_unit (O : ∀ j, V j ≃ₗᵢ[ℝ] V j) (a : V 0) (ha : ‖a‖ = 1) (j : Fin (N + 1)) :
    ‖source V B O a j‖ = 1 := by
  rw [source, (O j).norm_map, propagation_norm, ha]

theorem source_forward (O : ∀ j, V j ≃ₗᵢ[ℝ] V j) (a : V 0) (t : Fin N) :
    (rotatedBranches V B O t).normalizedIsometry (source V B O a t.castSucc) = source V B O a t.succ := by
  simp only [source, rotatedBranches, normalizedIsometry_conjugate, LinearIsometryEquiv.symm_apply_apply]
  rw [propagation_succ]
  rfl

end

end NCConcave16991.BranchConstruction
