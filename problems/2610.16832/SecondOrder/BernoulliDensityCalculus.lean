import SecondOrder.BernoulliSecondScore
import SecondOrder.ProductSecondDerivative

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

def binaryMass (p : ℝ) (w : Bool) : ℝ := if w then p else 1-p

theorem binaryMass_mul_score {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (w : Bool) :
    binaryMass p w * binaryScore p w = if w then 1 else -1 := by
  cases w <;> simp [binaryMass, binaryScore, hp0.ne', (sub_pos.mpr hp1).ne']

def bernoulliDensity (p : ι → ℝ) (w : ι → Bool) : ℝ := ∏ i, binaryMass (p i) (w i)

theorem bernoulliDensity_eq_toReal (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (w : ι → Bool) :
    bernoulliDensity p w = (bernoulliProduct p hp0 hp1 w).toReal := by
  simp only [bernoulliDensity, bernoulliProduct, finitePiPMF_toReal]
  apply Finset.prod_congr rfl
  intro i _
  cases w i <;> simp [binaryMass, hp0 i, sub_nonneg.mpr (hp1 i)]

theorem secondBilinear_const_sub {f : E → ℝ} (_hf : ContDiff ℝ 2 f) (r : ℝ) (x u v : E) :
    secondBilinear (fun y => r-f y) x u v = -secondBilinear f x u v := by
  have he : fderiv ℝ (fun y => r-f y) = fun y => -fderiv ℝ f y :=
    funext (fun y => fderiv_const_sub r)
  rw [secondBilinear, he, fderiv_neg]
  simp [secondBilinear]

theorem binaryMass_normalized_jets (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (x u v : E) (hp0 : 0 < f x) (hp1 : f x < 1) (w : Bool) :
    ContDiff ℝ 2 (fun y => binaryMass (f y) w) ∧
    fderiv ℝ (fun y => binaryMass (f y) w) x u =
      binaryMass (f x) w * (fderiv ℝ f x u * binaryScore (f x) w) ∧
    secondBilinear (fun y => binaryMass (f y) w) x u v =
      binaryMass (f x) w * (secondBilinear f x u v * binaryScore (f x) w) := by
  have hm := binaryMass_mul_score hp0 hp1 w
  cases w
  · simp only [binaryMass, Bool.false_eq_true, if_false] at hm ⊢
    refine ⟨contDiff_const.sub hf, ?_, ?_⟩
    · rw [fderiv_const_sub 1]
      simp only [ContinuousLinearMap.neg_apply]
      rw [mul_left_comm (1-f x), hm]
      ring
    · rw [secondBilinear_const_sub hf]
      rw [mul_left_comm (1-f x), hm]
      ring
  · simp only [binaryMass, if_true] at hm ⊢
    refine ⟨hf, ?_, ?_⟩ <;> rw [mul_left_comm (f x), hm, mul_one]

/-- The product score is the normalized actual derivative of the mass polynomial. -/
theorem bernoulliDensity_derivatives (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 2 (p i))
    (x u v : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1) (w : ι → Bool) :
    fderiv ℝ (fun y => bernoulliDensity (fun i => p i y) w) x u =
      bernoulliDensity (fun i => p i x) w *
        bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x u) w ∧
    secondBilinear (fun y => bernoulliDensity (fun i => p i y) w) x u v =
      bernoulliDensity (fun i => p i x) w *
        bernoulliSecondScore (fun i => p i x) (fun i => fderiv ℝ (p i) x u)
          (fun i => fderiv ℝ (p i) x v) (fun i => secondBilinear (p i) x u v) w := by
  have hj (i : ι) := binaryMass_normalized_jets (p i) (hp i) x u v (hp0 i) (hp1 i) (w i)
  have hk (i : ι) := binaryMass_normalized_jets (p i) (hp i) x v u (hp0 i) (hp1 i) (w i)
  have hh := product_normalized_jets Finset.univ (fun i y => binaryMass (p i y) (w i))
    (fun i _ => (hj i).1) x u v
    (fun i => fderiv ℝ (p i) x u * binaryScore (p i x) (w i))
    (fun i => fderiv ℝ (p i) x v * binaryScore (p i x) (w i))
    (fun i => secondBilinear (p i) x u v * binaryScore (p i x) (w i))
    (fun i _ => (hj i).2.1) (fun i _ => (hk i).2.1) (fun i _ => (hj i).2.2)
  refine ⟨hh.1, ?_⟩
  unfold bernoulliDensity
  rw [hh.2.2]
  unfold bernoulliSecondScore bernoulliScoreSum bernoulliScoreDiagonal
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end SecondOrder
