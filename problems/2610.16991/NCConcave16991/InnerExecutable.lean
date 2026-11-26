import NCConcave16991.InnerPersistent

/-!
# Direct execution from a stored anchor estimate

This presentation of the inner iteration only uses the given estimate and two
component evaluations per step. The true anchor mean and its error are used
solely to prove equality with the analyzed algorithm.
-/

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

namespace NCConcave16991.InnerAlgorithm

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} (S : Set E) (hne : S.Nonempty) (hclosed : IsClosed S) (hconvex : Convex ℝ S)

/-- A step that directly uses a stored estimate, with exactly the two indicated component values. -/
def estimatedStep (G : Fin n → E → E) (regularizer : E → E) (anchor estimate : E)
    (η : ℝ) (z : S) (i : Fin n) : S :=
  VariationalInequality.projection S hne hclosed hconvex
    ((z : E) - η • (estimate + (G i z - G i anchor) + regularizer z))

/-- The direct stored-estimate recursion. -/
def estimatedTrajectory (G : Fin n → E → E) (regularizer : E → E) (anchor : S)
    (estimate : E) (η : ℝ) : (k : ℕ) → Seed n k → S
  | 0, _ => anchor
  | k + 1, ω => estimatedStep S hne hclosed hconvex G regularizer anchor estimate η
      (estimatedTrajectory G regularizer anchor estimate η k ω.1) ω.2

/-- The arithmetic primal average returned by direct execution from the stored estimate. -/
def estimatedOutput (coordinate : E → P) (G : Fin n → E → E) (regularizer : E → E)
    (anchor : S) (estimate : E) (η : ℝ) : (k : ℕ) → Seed n k → P
  | 0, _ => 0
  | k + 1, ω => ((k : ℝ) / (k + 1)) • estimatedOutput coordinate G regularizer anchor estimate η k ω.1 +
      (1 / ((k : ℝ) + 1)) • coordinate (estimatedTrajectory S hne hclosed hconvex G regularizer anchor estimate η k ω.1)

 theorem estimatedTrajectory_eq (G : Fin n → E → E) (regularizer : E → E) (anchor : S)
    (bias : E) (η : ℝ) (k : ℕ) (ω : Seed n k) :
    estimatedTrajectory S hne hclosed hconvex G regularizer anchor (averageMap G anchor + bias) η k ω =
      trajectory S hne hclosed hconvex G regularizer anchor bias η k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change estimatedStep S hne hclosed hconvex G regularizer anchor (averageMap G anchor + bias) η
      (estimatedTrajectory S hne hclosed hconvex G regularizer anchor (averageMap G anchor + bias) η k ω.1) ω.2 = _
    rw [ih]
    rfl

 theorem estimatedOutput_eq (coordinate : E → P) (G : Fin n → E → E) (regularizer : E → E)
    (anchor : S) (bias : E) (η : ℝ) (k : ℕ) (ω : Seed n k) :
    estimatedOutput S hne hclosed hconvex coordinate G regularizer anchor (averageMap G anchor + bias) η k ω =
      averagedOutput S hne hclosed hconvex coordinate G regularizer anchor bias η k ω := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [estimatedOutput, averagedOutput, estimatedTrajectory_eq, ih]

end NCConcave16991.InnerAlgorithm

namespace NCConcave16991

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

/-- The state-based solver is exactly a direct algorithm using the stored estimate. -/
theorem persistentInnerSolve_eq_estimatedOutput (P : Problem p dx dy K) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (k : ℕ) (s : PersistentProcess.State dx dy) (ω : InnerAlgorithm.Seed p.n k) :
    persistentInnerSolve P y0 hy0 k s ω =
      InnerAlgorithm.estimatedOutput (productDomain dx K)
        (productDomain_nonempty dx K) (productDomain_closed dx K) (productDomain_convex dx K)
        (fun z : JointSpace dx dy ↦ z.fst) (signedComponentGradient P)
        (saddleCorrection p.L (selectedDualRegularization p) y0 s.center)
        ⟨jointPoint s.center y0, hy0⟩ s.estimate (InnerAlgorithm.sourceStepSize p.L (selectedDualRegularization p)) k ω := by
  have h := InnerAlgorithm.estimatedOutput_eq (productDomain dx K)
    (productDomain_nonempty dx K) (productDomain_closed dx K) (productDomain_convex dx K)
    (fun z : JointSpace dx dy ↦ z.fst) (signedComponentGradient P)
    (saddleCorrection p.L (selectedDualRegularization p) y0 s.center)
    ⟨jointPoint s.center y0, hy0⟩ (PersistentProcess.error (signedComponentGradient P) y0 s)
    (InnerAlgorithm.sourceStepSize p.L (selectedDualRegularization p)) k ω
  have he : averageMap (signedComponentGradient P) (jointPoint s.center y0) +
      PersistentProcess.error (signedComponentGradient P) y0 s = s.estimate := by
    dsimp [PersistentProcess.error]
    abel
  rw [he] at h
  exact h.symm

end NCConcave16991
