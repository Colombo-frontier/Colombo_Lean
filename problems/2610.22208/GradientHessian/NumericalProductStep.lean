import GradientHessian.NumericalRuntime
import GradientHessian.NumericalOrdinaryProcedure
noncomputable section
namespace GradientHessian.NumericalProductStep
open Matrix
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

def ordinary (K : ℝ) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (A : Matrix (Fin d) (Fin d) ℝ) (before after : State (t+1) (4096*J^2+1) ell)
    (Z : Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t) :=
  NumericalPolicyReplies.ordinary P B fallback t leaf K w c before after Z
    (LowRank.matrixEuclideanMap A (CensoredOracle.numericalMap t Z))

def fullStep (K : ℝ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) :=
  ControllerPolicyDriver.step policy (NumericalShadowRules.shadowRules P B fallback t leaf K w c) stop
    (ordinary P B fallback t leaf K w c A) (NumericalPolicyReplies.rich P B fallback t leaf K w c) q

theorem product_coordinates (A : Matrix (Fin d) (Fin d) ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    (NumericalOrdinaryProcedure.coordinates d).symm (A *ᵥ (NumericalOrdinaryProcedure.coordinates d y))=
      LowRank.matrixEuclideanMap A y := rfl

theorem one_product_step (K : ℝ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) (A : Matrix (Fin d) (Fin d) ℝ)
    (q : Config (t+1) (4096*J^2+1) ell S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
      (Action t (4096*J^2))) :
    NumericalRuntime.advance P B fallback t leaf policy K stop w c
      (if NumericalDriverInstructions.product leaf stop q then
        LowRank.matrixEuclideanMap A (CensoredOracle.numericalMap t (NumericalDriverInstructions.point q)) else 0) q=
      fullStep P B fallback t leaf policy K stop w c A q := by
  cases q with
  | ready N a s => rfl
  | finished a s => rfl
  | pending N a output phase =>
      cases phase with
      | repairing p s => rfl
      | normal p s => rfl
      | frozen p s => rfl
      | delivered p before after =>
          cases hb : stop before <;> cases ha : stop after
          all_goals simp only [NumericalRuntime.advance,fullStep,ControllerPolicyDriver.step,
            ControllerPolicyDriver.deliver,hb,ha,Bool.or_false,Bool.or_true,if_true,
            Bool.false_eq_true,if_false]
          cases output with
          | true => rfl
          | false =>
              cases hp : p.kind with
              | rich => simp only [hp]
              | ordinary =>
                  by_cases hc : TaskState.current before=some leaf
                  · simp [ordinary,hp,NumericalPolicyReplies.ordinary,hc,NumericalDriverInstructions.product,
                      NumericalDriverInstructions.point,phaseEquiv,hb,ha]
                  · simp [ordinary,hp,NumericalPolicyReplies.ordinary,hc]

end GradientHessian.NumericalProductStep
