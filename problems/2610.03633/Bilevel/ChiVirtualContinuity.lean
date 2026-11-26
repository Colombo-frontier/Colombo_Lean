import Bilevel.ChiVirtualDataContinuity

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem virtualPayload_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ) (d j : ℕ) (I : List ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualPayload D r p.1 d j I p.2) := by
  induction d generalizing j I with
  | zero =>
    dsimp only [virtualPayload]
    exact (virtualH_data_continuous D r j I).sub (virtualH_zero_data_continuous D r j I)
  | succ d ih =>
    dsimp only [virtualPayload]
    apply Continuous.add
    · apply Continuous.add
      · exact (virtualH_data_continuous D r j I).sub (continuous_finset_sum _ (fun i _ => virtualResidual_data_continuous D r j I i))
      · exact continuous_finset_sum _ (fun i _ => (virtualResidual_data_continuous D r j I i).mul (virtualRelease_data_continuous D r (j+1) (child I i.val)))
    · exact continuous_finset_sum _ (fun i _ => (virtualSelector_data_continuous D r j I i).mul (ih (j+1) (child I i.val)))

theorem virtualCarrier_continuous (D : Geometry E) (r : ℕ → List ℕ → ℕ) (d j : ℕ) (I : List ℕ) (k : ℕ) :
    Continuous (fun p : ColumnData D × (ℕ → E) => virtualCarrier D r p.1 d j I k p.2) := by
  induction d generalizing j I k with
  | zero =>
    cases k with
    | zero =>
      dsimp only [virtualCarrier]
      exact (virtualH_data_continuous D r j I).sub (virtualH_zero_data_continuous D r j I)
    | succ k => exact continuous_const
  | succ d ih =>
    cases k with
    | zero =>
      dsimp only [virtualCarrier]
      apply Continuous.add
      · exact (virtualH_data_continuous D r j I).sub (continuous_finset_sum _ (fun i _ => virtualResidual_data_continuous D r j I i))
      · exact continuous_finset_sum _ (fun i _ => (virtualResidual_data_continuous D r j I i).mul (virtualRelease_data_continuous D r (j+1) (child I i.val)))
    | succ k =>
      dsimp only [virtualCarrier]
      exact continuous_finset_sum _ (fun i _ => (virtualSelector_data_continuous D r j I i).mul (ih (j+1) (child I i.val) k))

end Bilevel.ChiPrefixEvaluation
