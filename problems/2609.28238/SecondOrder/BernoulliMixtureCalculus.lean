import SecondOrder.BernoulliDensityCalculus

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem secondBilinear_sum {α : Type*} [Fintype α] (f : α → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x u v : E) :
    secondBilinear (fun y => ∑ i, f i y) x u v = ∑ i, secondBilinear (f i) x u v := by
  have he : fderiv ℝ (fun y => ∑ i, f i y) = fun y => ∑ i, fderiv ℝ (f i) y :=
    funext (fun y => fderiv_sum (fun i _ => (hf i).differentiable (by norm_num) y))
  rw [secondBilinear, he, fderiv_sum]
  · simp only [ContinuousLinearMap.sum_apply, secondBilinear]
  · intro i _
    exact ((hf i).fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)).differentiable (by norm_num) x

theorem contDiff_bernoulliDensity (p : ι → E → ℝ) {k : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ k (p i)) (w : ι → Bool) :
    ContDiff ℝ k (fun y => bernoulliDensity (fun i => p i y) w) := by
  apply contDiff_prod
  intro i _
  cases w i
  · exact contDiff_const.sub (hp i)
  · exact hp i

/-- A finite Bernoulli mixture as a polynomial in the gates. It remains defined
at boundary gate values, even though interior score formulas divide by gates. -/
def bernoulliMixture (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ) (x : E) : ℝ :=
  ∑ w, bernoulliDensity (fun i => p i x) w * V w x

theorem contDiff_bernoulliMixture (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    {k : WithTop ℕ∞} (hp : ∀ i, ContDiff ℝ k (p i)) (hV : ∀ w, ContDiff ℝ k (V w)) :
    ContDiff ℝ k (bernoulliMixture p V) :=
  ContDiff.sum (fun w _ => (contDiff_bernoulliDensity p hp w).mul (hV w))

theorem bernoulliMixture_fderiv (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x u : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1) :
    fderiv ℝ (bernoulliMixture p V) x u =
      pmfMean (bernoulliProduct (fun i => p i x) (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun w => fderiv ℝ (V w) x u + V w x *
          bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x u) w) := by
  unfold bernoulliMixture
  rw [fderiv_sum (fun w _ => ((contDiff_bernoulliDensity p hp w).mul (hV w)).differentiable (by norm_num) x)]
  simp only [ContinuousLinearMap.sum_apply, pmfMean, smul_eq_mul,
    ← bernoulliDensity_eq_toReal]
  apply Finset.sum_congr rfl
  intro w _
  rw [fderiv_mul ((contDiff_bernoulliDensity p hp w).differentiable (by norm_num) x)
    ((hV w).differentiable (by norm_num) x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [(bernoulliDensity_derivatives p hp x u u hp0 hp1 w).1]
  ring

theorem bernoulliMixture_secondBilinear (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x u v : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1) :
    secondBilinear (bernoulliMixture p V) x u v =
      pmfMean (bernoulliProduct (fun i => p i x) (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun w => secondBilinear (V w) x u v +
          fderiv ℝ (V w) x u * bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x v) w +
          fderiv ℝ (V w) x v * bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x u) w +
          V w x * bernoulliSecondScore (fun i => p i x) (fun i => fderiv ℝ (p i) x u)
            (fun i => fderiv ℝ (p i) x v) (fun i => secondBilinear (p i) x u v) w) := by
  unfold bernoulliMixture
  rw [secondBilinear_sum _ (fun w => (contDiff_bernoulliDensity p hp w).mul (hV w))]
  simp only [pmfMean, smul_eq_mul, ← bernoulliDensity_eq_toReal]
  apply Finset.sum_congr rfl
  intro w _
  rw [secondBilinear_mul (contDiff_bernoulliDensity p hp w) (hV w),
    (bernoulliDensity_derivatives p hp x u v hp0 hp1 w).1,
    (bernoulliDensity_derivatives p hp x v u hp0 hp1 w).1,
    (bernoulliDensity_derivatives p hp x u v hp0 hp1 w).2]
  ring

end
end SecondOrder
