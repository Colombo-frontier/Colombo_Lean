import Matvec.PosteriorBlockCoordinates

/-! Explicit measurable score on the independent enhanced-history/residual
product space, together with the uniform low event and exact original replay. -/
namespace Matvec
open Matrix MeasureTheory LowRank
open scoped Matrix
noncomputable section
universe u

def decodedAmbientState (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :
    GaussianHistory r s t S → TwoSidedState (r + t) (s + t) r s :=
  readTwoSidedState (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)

theorem measurable_decodedAmbientState (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :
    Measurable (decodedAmbientState r s t policy) :=
  measurable_readTwoSidedState (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)

theorem decodedAmbientState_orthogonal (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) (h : GaussianHistory r s t S) :
    (decodedAmbientState r s t policy h).Orthogonal :=
  readTwoSidedState_orthogonal (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)
    (fun _ => initialTwoSidedState_orthogonal _ _) h

theorem decodedAmbientState_centered (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) (h : GaussianHistory r s t S) :
    (decodedAmbientState r s t policy h).Centered :=
  readTwoSidedState_centered (r + t) (s + t) r s t policy
    (initialOracleState (r + t) (s + t) S) (initialOracleMemory S)
    (fun _ => initialTwoSidedState_orthogonal _ _)
    (fun _ => initialTwoSidedState_centered _ _) h

def decodedAmbientMatrix (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : GaussianHistory r s t S × Matrix (Fin r) (Fin s) ℝ) :=
  representedTwoSided (decodedAmbientState r s t policy p.1) p.2

theorem measurable_decodedAmbientMatrix (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S) :
    Measurable (decodedAmbientMatrix r s t policy) := by
  have hst : Measurable (fun p : GaussianHistory r s t S × Matrix (Fin r) (Fin s) ℝ =>
      decodedAmbientState r s t policy p.1) :=
    (measurable_decodedAmbientState r s t policy).comp measurable_fst
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [decodedAmbientMatrix, representedTwoSided, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

theorem decodedAmbientMatrix_replay (r s t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (s + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (s + t)) ℝ) :
    decodedAmbientMatrix r s t policy
      (runTwoSidedPolicy r s t (compiledAmbientPolicy r s t policy) p) = p.2 :=
  ambientTwoSided_factorization r s t policy p

def decodedAmbientScore (r t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (r + t) t S)
    (p : GaussianHistory r r t S × Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  leastStretch (matrixEuclideanMap (decodedAmbientMatrix r r t policy p))

theorem measurable_decodedAmbientScore (r t : ℕ) (hr : 0 < r + t)
    {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (r + t) t S) :
    Measurable (decodedAmbientScore r t policy) :=
  (measurable_matrix_leastStretch _ _ hr).comp (measurable_decodedAmbientMatrix r r t policy)

theorem decodedAmbientScore_replay (r t : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy (r + t) (r + t) t S)
    (p : S × Matrix (Fin (r + t)) (Fin (r + t)) ℝ) :
    decodedAmbientScore r t policy
      (runTwoSidedPolicy r r t (compiledAmbientPolicy r r t policy) p) =
      leastStretch (matrixEuclideanMap p.2) := by
  unfold decodedAmbientScore
  rw [decodedAmbientMatrix_replay]

theorem decodedAmbientScore_low (q n : ℕ) (hn : lowEventRank ≤ n)
    {S : Type u} [MeasurableSpace S]
    (policy : TwoSidedOraclePolicy ((q + (n + 1)) + q) ((q + (n + 1)) + q) q S)
    (h : GaussianHistory (q + (n + 1)) (q + (n + 1)) q S)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    smallBallDensity ^ 2 * a ^ 2 / (64 * lowEventRank) ≤
      (iidMatrixLaw (q + (n + 1)) (q + (n + 1)) 1).real
        {D | decodedAmbientScore (q + (n + 1)) q policy (h, D) ≤
          2 * a / Real.sqrt (n + 1 : ℝ)} :=
  representedTwoSided_gaussian_low q n hn (decodedAmbientState _ _ _ policy h)
    (decodedAmbientState_orthogonal _ _ _ policy h) (decodedAmbientState_centered _ _ _ policy h)
    ha ha1

end
end Matvec
