import NCConcave16991.GlobalHardEuclidean

/-! # The genuine Section 2 instance at all public Appendix E parameters -/

namespace NCConcave16991.GlobalHardEuclidean

noncomputable section

open GlobalHard
open scoped InnerProductSpace

theorem paperRadius_pos (n : ℕ) (hn : 0 < n) (m : ℕ) :
    0 < publicDualRadius n (m + 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold publicDualRadius
  positivity

def paperParameters (n : ℕ) (hn : 0 < n) (M : ℕ) (hM : 0 < M) (m : ℕ) : ProblemParameters :=
  parameters n hn M hM (publicDualRadius n (m + 2)) (paperRadius_pos n hn m)

variable {n M m : ℕ} (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, FiniteDimensional ℝ (V j k)]
  (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
    BranchGeometry.BranchFamily (ι := Fin n) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

def paperDualDomain (hn : 0 < n) : KnownDualDomain (dualDimension V)
    (2 * publicDualRadius n (m + 2)) :=
  dualDomain V _ (paperRadius_pos n hn m)

/-- A complete actual `Problem`, with public dimensions, source constants,
dual radius, epsilon=1/40 and gap31000M. The geometry enters only through
literal branch isometries and unit source vectors. -/
def paperProblem (hn : 0 < n) (hM : 0 < M)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    Problem (paperParameters n hn M hM m) (primalDimension V) (dualDimension V) (paperDualDomain V hn) :=
  problem V B u v hn hM (EndpointConstants.endpointD m)
    (Real.sqrt (BranchGeometry.beta (Fin n) / EndpointConstants.endpointK m))
    (1 / ((m : ℝ) + 2) ^ 2)
    (by have hd := EndpointConstants.endpointD_bounds m; linarith)
    (by positivity) (publicDualRadius n (m + 2)) (paperRadius_pos n hn m) hu hv

theorem paperProblem_individualSmooth (hn : 0 < n) (hM : 0 < M)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    (paperProblem V B u v hn hM hu hv).individualSmooth := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply problem_individualSmooth
  · have hd := EndpointConstants.endpointD_bounds m
    rw [abs_of_nonneg (by linarith : 0 ≤ EndpointConstants.endpointD m)]
    exact hd.2
  · exact PipeSmoothness.endpoint_coupling_le_one m
  · have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    apply (div_le_one (by positivity : 0 < ((m : ℝ) + 2) ^ 2)).mpr
    nlinarith

theorem paperProblem_averagedSmooth (hn : 0 < n) (hM : 0 < M)
    (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    (paperProblem V B u v hn hM hu hv).averagedSmooth :=
  (paperProblem V B u v hn hM hu hv).individual_implies_averaged
    (paperProblem_individualSmooth V B u v hn hM hu hv)

end

end NCConcave16991.GlobalHardEuclidean
