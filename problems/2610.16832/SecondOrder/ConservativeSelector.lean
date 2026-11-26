import SecondOrder.ReverseSelectorBounds
import SecondOrder.FiniteMeanCalculus

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {n : ℕ} {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem reverseBlockSelector_contDiff (p : Fin n → E → ℝ)
    (V : ℕ → HomogeneousBlocks (Fin n) E → ℝ) {k : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ k (p i)) (hV : ∀ j ≤ n, ContDiff ℝ k (V j)) :
    ContDiff ℝ k (reverseBlockSelector p V) := by
  rw [reverseBlockSelector_eq_mixture]
  exact contDiff_bernoulliMixture _ _
    (fun i => (hp i).comp (blockProj (E := E) i).contDiff)
    (fun w => hV _ (lastSuccess_le w))

theorem reverseBlockSelector_pmfMean_zero [Fintype Ω] (P : PMF Ω)
    (p : Fin n → E → ℝ) (V : Ω → ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (x : HomogeneousBlocks (Fin n) E)
    (hV : ∀ j ≤ n, pmfMean P (fun z => V z j x) = 0) :
    pmfMean P (fun z => reverseBlockSelector p (V z) x) = 0 := by
  simp only [reverseBlockSelector_eq_mixture, bernoulliMixture]
  rw [pmfMean_finset_sum]
  apply Finset.sum_eq_zero
  intro w _
  rw [pmfMean_mul, hV _ (lastSuccess_le w), mul_zero]

/-- One random scalar function; the coefficient law is fixed independently of
the query. The selector weights are differentiated as part of this function. -/
def conservativeSelectorLoss (F : HomogeneousBlocks (Fin n) E → ℝ)
    (p : Fin n → E → ℝ) (V : Ω → ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (z : Ω) (x : HomogeneousBlocks (Fin n) E) : ℝ := F x+reverseBlockSelector p (V z) x

theorem conservativeSelectorLoss_contDiff (F : HomogeneousBlocks (Fin n) E → ℝ)
    (p : Fin n → E → ℝ) (V : Ω → ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    {k : WithTop ℕ∞} (hF : ContDiff ℝ k F) (hp : ∀ i, ContDiff ℝ k (p i))
    (hV : ∀ z j, j ≤ n → ContDiff ℝ k (V z j)) (z : Ω) :
    ContDiff ℝ k (conservativeSelectorLoss F p V z) :=
  hF.add (reverseBlockSelector_contDiff p (V z) hp (hV z))

theorem conservativeSelectorLoss_mean [Fintype Ω] (P : PMF Ω)
    (F : HomogeneousBlocks (Fin n) E → ℝ) (p : Fin n → E → ℝ)
    (V : Ω → ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (hV : ∀ x j, j ≤ n → pmfMean P (fun z => V z j x) = 0)
    (x : HomogeneousBlocks (Fin n) E) :
    pmfMean P (fun z => conservativeSelectorLoss F p V z x) = F x := by
  unfold conservativeSelectorLoss
  rw [pmfMean_add, pmfMean_const,
    reverseBlockSelector_pmfMean_zero P p V x (hV x), add_zero]

end
noncomputable section
variable {n : ℕ} {E Ω : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Exact unbiasedness of the value, gradient, and Hessian of the same sampled loss. -/
theorem conservativeSelectorLoss_unbiased (P : PMF Ω)
    (F : HomogeneousBlocks (Fin n) E → ℝ) (p : Fin n → E → ℝ)
    (V : Ω → ℕ → HomogeneousBlocks (Fin n) E → ℝ)
    (hF : ContDiff ℝ 2 F) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (hV : ∀ z j, j ≤ n → ContDiff ℝ 2 (V z j))
    (hmean : ∀ x j, j ≤ n → pmfMean P (fun z => V z j x) = 0)
    (x : HomogeneousBlocks (Fin n) E) :
    (∫ z, conservativeSelectorLoss F p V z x ∂P.toMeasure) = F x ∧
    (∫ z, gradient (conservativeSelectorLoss F p V z) x ∂P.toMeasure) = gradient F x ∧
    (∫ z, fderiv ℝ (gradient (conservativeSelectorLoss F p V z)) x ∂P.toMeasure) =
      fderiv ℝ (gradient F) x := by
  letI : NormedSpace ℝ (HomogeneousBlocks (Fin n) E) := inferInstance
  have he : (fun y => ∫ z, conservativeSelectorLoss F p V z y ∂P.toMeasure) = F := by
    funext y
    simpa only [PMF.integral_eq_sum, pmfMean] using conservativeSelectorLoss_mean P F p V hmean y
  have hs (z : Ω) := conservativeSelectorLoss_contDiff F p V hF hp hV z
  refine ⟨congrFun he x, ?_, ?_⟩
  · rw [← gradient_finiteMean P _ x (fun z => (hs z).differentiable (by norm_num) x), he]
  · rw [← fderiv_gradient_finiteMean P _ x hs, he]

end
end SecondOrder
