import GradientHessian.InnerFunctions

/-! Global value bounds and the exact shared numerical force of the inner
residual. Constants are independent of task count and register dimension. -/

noncomputable section
namespace GradientHessian.Inner

open EuclideanRegisters InnerCoordinates
open scoped InnerProductSpace

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sumResidual (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2)) : ℝ :=
  ∑ i, LatchChain.residual (k + 1) (v i) (radius k) (tasks Y E m (k + 2) Z i)

theorem residual_eq_sumResidual_sub (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : residual b a v Z = sumResidual v Z - forcingSum b a v Z := by
  simp only [residual, sumResidual, selfSum, publicQuadratic, LatchChain.residual, block,
    Finset.sum_sub_distrib]

theorem sumResidual_bounds (v : Fin m → Fin (k + 2) → E) (Z : Space Y E m (k + 2)) :
    -(112 * lastRadius k) * m ≤ sumResidual v Z ∧ sumResidual v Z ≤ 0 := by
  have hb (i : Fin m) := (LatchChain.source_value_bounds k (v i)
    (by norm_num : (1 : ℝ) ≤ 1) (tasks Y E m (k + 2) Z i)).2
  have he : LatchChain.sourceScale (1 : ℝ) (Fin.last (k + 1)) = lastRadius k := by
    simp [LatchChain.sourceScale, lastRadius]
  constructor
  · have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => (hb i).1)
    simpa only [he, radius, sumResidual, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, neg_mul, mul_neg, mul_comm] using h
  · exact (Finset.sum_nonpos (fun i _ => (hb i).2))

def valueConstant (k : ℕ) : ℝ := 112 * lastRadius k + payloadBound

theorem valueConstant_pos (k : ℕ) : 0 < valueConstant k := by
  have hR : 0 < lastRadius k := by unfold lastRadius; positivity
  unfold valueConstant
  linarith [payloadBound_pos]

theorem residual_bounds (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E)
    (Z : Space Y E m (k + 2)) : -(valueConstant k) * m ≤ residual b a v Z ∧ residual b a v Z ≤ 0 := by
  rw [residual_eq_sumResidual_sub]
  have hs := sumResidual_bounds v Z
  have hf := forcingSum_bounds b a v Z
  cases m with
  | zero => simp [sumResidual, forcingSum, InnerSelector.select]
  | succ m =>
    have hCB : payloadBound ≤ payloadBound * (m + 1) := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith [mul_nonneg payloadBound_pos.le hm]
    dsimp [valueConstant]
    push_cast at hs
    push_cast
    constructor <;> nlinarith [hs.1, hs.2, hf.1, hf.2]

theorem publicQuadratic_contDiff (m k : ℕ) :
    ContDiff ℝ 3 (publicQuadratic (Y := Y) (E := E) m k) := by
  unfold publicQuadratic LatchChain.publicQuadratic
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact contDiff_const.mul (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k + 2) => E) j).contDiff.comp
    (taskProjection (Y := Y) (E := E) m k i).contDiff).norm_sq ℝ)

theorem residual_contDiff (b a : Fin m → Y) (v : Fin m → Fin (k + 2) → E) :
    ContDiff ℝ 3 (residual b a v) :=
  ((selfSum_contDiff v).sub (publicQuadratic_contDiff m k)).sub (forcingSum_contDiff b a v)

theorem sumResidual_contDiff (v : Fin m → Fin (k + 2) → E) :
    ContDiff ℝ 3 (sumResidual (Y := Y) v) := by
  have he : sumResidual (Y := Y) v = fun Z => selfSum v Z - publicQuadratic m k Z := by
    funext Z
    simp [sumResidual, LatchChain.residual, selfSum, block, publicQuadratic, Finset.sum_sub_distrib]
  rw [he]
  exact (selfSum_contDiff v).sub (publicQuadratic_contDiff m k)

end GradientHessian.Inner
