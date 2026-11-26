import NCConcave16991.GlobalHardGap
import NCConcave16991.GlobalHardSmoothness

/-! # Global regularity and gap at the literal public Appendix E parameters -/

namespace NCConcave16991.GlobalHard

noncomputable section

open scoped InnerProductSpace

def publicDualRadius (n N : ℕ) : ℝ := 20 * Real.sqrt 3 * (n : ℝ) ^ (1 / 4 : ℝ) * N

theorem publicDualRadius_nonneg (n N : ℕ) : 0 ≤ publicDualRadius n N := by
  unfold publicDualRadius
  positivity

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {M m : ℕ} (V : Fin M → Fin ((m + 1) + 1) → Type*)
  [∀ j k, NormedAddCommGroup (V j k)] [∀ j k, InnerProductSpace ℝ (V j k)]
  [∀ j k, CompleteSpace (V j k)]
variable (B : ∀ j : Fin M, ∀ t : Fin (m + 1),
  BranchGeometry.BranchFamily (ι := ι) (V j t.castSucc) (V j t.succ))
  (u : ∀ j, V j 0) (v : ∀ j, V j (Fin.last (m + 1)))

theorem paper_component_global_smooth (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1)
    (i : ι) (x y : Joint V) :
    ‖gradient (component V B u v (EndpointConstants.endpointD m)
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) i) x -
      gradient (component V B u v (EndpointConstants.endpointD m)
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) i) y‖ ≤ 100000000 * ‖x - y‖ := by
  apply component_global_smooth V B u v
  · have hd := EndpointConstants.endpointD_bounds m
    rw [abs_of_nonneg (by linarith : 0 ≤ EndpointConstants.endpointD m)]
    exact hd.2
  · exact PipeSmoothness.endpoint_coupling_le_one m
  · positivity
  · have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    apply (div_le_one (by positivity : 0 < ((m : ℝ) + 2) ^ 2)).mpr
    nlinarith
  · exact hu
  · exact hv

variable [∀ j k, FiniteDimensional ℝ (V j k)]

/-- The actual public radius and actual inverse-defined endpoint constants,
with no smoothness or gap assumption on the constructed instance. -/
theorem paper_initial_gap (hu : ∀ j, ‖u j‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    value V B u v (EndpointConstants.endpointD m)
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) (publicDualRadius (Fintype.card ι) (m + 2)) 0 -
      sInf (Set.range (value V B u v (EndpointConstants.endpointD m)
        (Real.sqrt (BranchGeometry.beta ι / EndpointConstants.endpointK m))
        (1 / ((m : ℝ) + 2) ^ 2) (publicDualRadius (Fintype.card ι) (m + 2)))) ≤ 31000 * M := by
  apply initial_gap V B u v
  · have hd := EndpointConstants.endpointD_bounds m
    linarith
  · positivity
  · exact publicDualRadius_nonneg _ _
  · exact hu
  · exact hv

end

end NCConcave16991.GlobalHard
