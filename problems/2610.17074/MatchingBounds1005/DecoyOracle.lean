import MatchingBounds1005.DecoyLinearCoordinates
import MatchingBounds1005.OracleReconstruction

/-! The actual copied-chain oracle reconstructed from its physical two-channel
tensor response, one matrix-vector response, and disclosed readouts. -/
noncomputable section
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.BlockGeometry
open TensorGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (G : BlockGeometry E)

def decoyDataResponse (r A R η : ℝ) (n K : ℕ) {d : ℕ}
    (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d) (S : Finset (Fin (n + 1)))
    (x Y₃ Y₄ : Vec d) : Model.Response d :=
  confineResponse R η x
    (dataResponse (10 * G.tau * Fintype.card (Fin (n + 1)))
      (radial R x) (G.transportedLinearVector n K I)
      (G.transportedOperator n K I (radial R x)) Y₃ Y₄
      (Model.oracle (correctionSum (transportedReadout n K G.a A I) G.tau r A S)
        (radial R x)))

theorem decoyDataResponse_exact {r A : ℝ} (hr : 1 ≤ r) (hA : 0 < A)
    (R η : ℝ) (n K : ℕ) {d : ℕ} (I : CopySpace (E := E) n K ≃ₗᵢ[ℝ] Vec d)
    (S : Finset (Fin (n + 1))) (T₃ : Tensor d 3) (T₄ : Tensor d 4) (x : Vec d)
    (hcore : ∀ i, i ∉ S → |A * ⟪transportedReadout n K G.a A I i, radial R x⟫_ℝ| ≤ r) :
    Model.oracle (Confinement.objective
      (fun y => IsometricTransfer.transport I (G.decoyObjective r n K) y + mask T₃ T₄ y) R η) x =
      G.decoyDataResponse r A R η n K I S x
        (channel 3 (cubicSignal G.tau A (transportedReadout n K G.a A I) + T₃) (radial R x))
        (channel 4 (quarticSignal G.tau A (transportedReadout n K G.a A I) + T₄) (radial R x)) := by
  let Q := IsometricTransfer.transport I (G.decoyQuadratic n K)
  let b := transportedReadout n K G.a A I
  have hQ : ContDiff ℝ ∞ Q :=
    IsometricTransfer.smooth I (SymmetricQuadratic.smooth _ _)
  have hF : (fun y => IsometricTransfer.transport I (G.decoyObjective r n K) y + mask T₃ T₄ y) =
      ridgeMasked Q b G.tau r A T₃ T₄ := by
    rw [G.transportedObjective_decomposition hA]
    rfl
  rw [hF, confineResponse_exact ((ridgeMasked_smooth hQ b G.tau r A T₃ T₄).differentiable
    (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)),
    disclosed_oracle_exact hQ b G.tau A hr T₃ T₄ S (radial R x) hcore]
  have henergy := G.transportedQuadratic_eq_energy n K I
  change Q = _ at henergy
  unfold disclosedMasked
  rw [henergy]
  rw [dataResponse_exact _ _ (G.transportedOperator_symmetric n K I)
    ((correctionSum_smooth b G.tau r A S).differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))]
  rfl

end MatchingBounds1005.BlockGeometry
