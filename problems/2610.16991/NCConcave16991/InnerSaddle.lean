import NCConcave16991.InnerRate
import NCConcave16991.SaddleProx

/-! # Appendix B.3 instantiated with the actual signed component gradients -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators InnerProductSpace

namespace NCConcave16991

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  [MeasurableSpace (Fin p.n)] [MeasurableSingletonClass (Fin p.n)]

local instance : NeZero p.n := ⟨Nat.ne_of_gt p.n_pos⟩

/-- The actual independent inner algorithm returns the arithmetic mean of its primal iterates. -/
def independentInnerOutput (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (ξ : JointSpace dx dy)
    (k : ℕ) (ω : InnerAlgorithm.Seed p.n k) : PrimalSpace dx :=
  InnerAlgorithm.averagedOutput (productDomain dx K)
    (productDomain_nonempty dx K) (productDomain_closed dx K) (productDomain_convex dx K)
    (fun z : JointSpace dx dy ↦ z.fst) (signedComponentGradient P) (saddleCorrection p.L μ y0 c)
    ⟨jointPoint c y0, hy0⟩ ξ (InnerAlgorithm.sourceStepSize p.L μ) k ω

/-- Its actual finite-seed expected primal squared error. -/
def independentInnerMeanError (P : Problem p dx dy K) (μ : ℝ) (y0 : DualSpace dy)
    (hy0 : y0 ∈ K.carrier) (c : PrimalSpace dx) (ξ : JointSpace dx dy)
    (target : PrimalSpace dx) (k : ℕ) : ℝ :=
  ∫ ω, ‖independentInnerOutput P μ y0 hy0 c ξ k ω - target‖ ^ 2 ∂InnerAlgorithm.seedLaw k

/-- Lemma B.3, first line: no algorithmic recurrence or constrained-gradient-zero is assumed. -/
theorem independentInner_first_bound (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ p.L) (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier)
    (c : PrimalSpace dx) (ξ : JointSpace dx dy) {k : ℕ}
    (hk : 4294967296 * (p.L / μ) ^ 2 ≤ (k : ℝ)) :
    independentInnerMeanError P μ y0 hy0 c ξ
      (tiltedSaddleSolution P hAS hμ hμL y0 c ξ).fst k ≤
        3 / (65536 * (p.L / μ)) *
          (‖(tiltedSaddleSolution P hAS hμ hμL y0 c ξ).fst - c‖ ^ 2 + p.diameter ^ 2) := by
  let zξ := tiltedSaddleSolution P hAS hμ hμL y0 c ξ
  have hs := tiltedSaddleSolution_spec P hAS hμ hμL y0 c ξ
  let star : productDomain dx K := ⟨zξ, hs.1⟩
  let anchor : productDomain dx K := ⟨jointPoint c y0, hy0⟩
  let W := fun z : JointSpace dx dy ↦
    p.L * ‖z.fst - zξ.fst‖ ^ 2 + μ * ‖z.snd - zξ.snd‖ ^ 2
  let Vstar := ‖zξ.fst - c‖ ^ 2 + p.diameter ^ 2
  have hT (z : JointSpace dx dy) :
      InnerAlgorithm.operator (signedComponentGradient P) (saddleCorrection p.L μ y0 c) z =
      saddleOperator P μ y0 c z := by
    rw [InnerAlgorithm.operator, averageMap_signedComponentGradient,
      ← saddleOperator_eq_signed_plus_correction]
  have hstar : VariationalInequality.IsSolution (productDomain dx K)
      (fun z ↦ InnerAlgorithm.operator (signedComponentGradient P) (saddleCorrection p.L μ y0 c) z + ξ) star := by
    refine ⟨hs.1, fun w hw ↦ ?_⟩
    simpa only [hT, tiltedSaddleOperator] using hs.2 w hw
  have hLip (z : JointSpace dx dy) (hz : z ∈ productDomain dx K) :
      ‖InnerAlgorithm.operator (signedComponentGradient P) (saddleCorrection p.L μ y0 c) z -
        InnerAlgorithm.operator (signedComponentGradient P) (saddleCorrection p.L μ y0 c) star‖ ≤
      3 * p.L * ‖z - star‖ := by
    rw [hT, hT]
    exact saddleOperator_lipschitz P hAS hμ.le hμL y0 c z star hz star.property
  have hMono (z : JointSpace dx dy) (hz : z ∈ productDomain dx K) :
      W z ≤ ⟪InnerAlgorithm.operator (signedComponentGradient P) (saddleCorrection p.L μ y0 c) z -
        InnerAlgorithm.operator (signedComponentGradient P) (saddleCorrection p.L μ y0 c) star, z - star⟫_ℝ := by
    rw [hT, hT]
    exact saddleOperator_anisotropic_monotone P hAS μ y0 c z star hz star.property
  have hcoercive (z : JointSpace dx dy) (_hz : z ∈ productDomain dx K) :
      μ * ‖z - star‖ ^ 2 ≤ W z := by
    rw [joint_difference_norm_sq]
    dsimp [W, star]
    nlinarith only [mul_le_mul_of_nonneg_right hμL (sq_nonneg ‖z.fst - zξ.fst‖)]
  have hcoordinate (z : JointSpace dx dy) (_hz : z ∈ productDomain dx K) :
      p.L * ‖z.fst - (star : JointSpace dx dy).fst‖ ^ 2 ≤ W z := by
    dsimp [W, star]
    exact le_add_of_nonneg_right (mul_nonneg hμ.le (sq_nonneg _))
  have hanchor : ‖(star : JointSpace dx dy) - anchor‖ ^ 2 ≤ Vstar := by
    rw [joint_difference_norm_sq]
    change ‖zξ.fst - c‖ ^ 2 + ‖zξ.snd - y0‖ ^ 2 ≤ ‖zξ.fst - c‖ ^ 2 + p.diameter ^ 2
    have hd := pow_le_pow_left₀ (norm_nonneg _) (K.diameter_bound zξ.snd hs.1 y0 hy0) 2
    linarith
  have hb := InnerAlgorithm.source_inner_output_bound (productDomain dx K)
    (productDomain_nonempty dx K) (productDomain_closed dx K) (productDomain_convex dx K)
    (fun z : JointSpace dx dy ↦ z.fst) (saddleCorrection p.L μ y0 c) p.L_pos hμ
    (signedComponentGradient_averagedSmooth P hAS) anchor ξ star hstar W Vstar
    hLip hMono hcoercive hcoordinate hanchor hk
  exact hb

end NCConcave16991

