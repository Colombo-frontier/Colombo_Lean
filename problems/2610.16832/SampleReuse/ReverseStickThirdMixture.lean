import SampleReuse.ReverseStickThirdDensity

/-! The third derivative of the actual finite Bernoulli mixture. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem thirdTrilinear_sum (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (x u v w : E) :
    thirdTrilinear (fun y => ∑ i, f i y) x u v w = ∑ i, thirdTrilinear (f i) x u v w := by
  simp only [thirdTrilinear_eq_iterated]
  rw [iteratedFDeriv_sum (u := Finset.univ) (fun i _ => hf i)]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply]

/-- Differentiating the scalar mixture gives the eight expected score terms.
All derivative expressions are genuine Fréchet derivatives, with arbitrary
full-space payload functions, as required by reverse stick localization. -/
theorem bernoulliMixture_third
    (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 3 (p i)) (hV : ∀ ω, ContDiff ℝ 3 (V ω))
    (x u v w : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1) :
    let P := bernoulliProduct (fun i => p i x) (fun i => (hp0 i).le) (fun i => (hp1 i).le)
    let S := fun z => bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x z)
    let K := fun z z' => bernoulliSecondScore (fun i => p i x)
      (fun i => fderiv ℝ (p i) x z) (fun i => fderiv ℝ (p i) x z')
      (fun i => secondBilinear (p i) x z z')
    let H := bernoulliThirdScore (fun i => p i x)
      (fun i => fderiv ℝ (p i) x u) (fun i => fderiv ℝ (p i) x v)
      (fun i => fderiv ℝ (p i) x w)
      (fun i => secondBilinear (p i) x u v) (fun i => secondBilinear (p i) x u w)
      (fun i => secondBilinear (p i) x v w) (fun i => thirdTrilinear (p i) x u v w)
    thirdTrilinear (bernoulliMixture p V) x u v w =
      pmfMean P (fun ω =>
        thirdTrilinear (V ω) x u v w + V ω x * H ω +
        secondBilinear (V ω) x v w * S u ω +
        secondBilinear (V ω) x u w * S v ω +
        secondBilinear (V ω) x u v * S w ω +
        fderiv ℝ (V ω) x u * K v w ω +
        fderiv ℝ (V ω) x v * K u w ω +
        fderiv ℝ (V ω) x w * K u v ω) := by
  dsimp only
  have hp2 (i : ι) := (hp i).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  unfold bernoulliMixture
  rw [thirdTrilinear_sum _ (fun ω => (contDiff_bernoulliDensity p hp ω).mul (hV ω))]
  simp only [pmfMean, smul_eq_mul, ← bernoulliDensity_eq_toReal]
  apply Finset.sum_congr rfl
  intro ω _
  rw [thirdTrilinear_mul _ _ (contDiff_bernoulliDensity p hp ω) (hV ω),
    bernoulliDensity_third p hp x u v w hp0 hp1 ω,
    (bernoulliDensity_derivatives p hp2 x u v hp0 hp1 ω).1,
    (bernoulliDensity_derivatives p hp2 x v w hp0 hp1 ω).1,
    (bernoulliDensity_derivatives p hp2 x w u hp0 hp1 ω).1,
    (bernoulliDensity_derivatives p hp2 x u v hp0 hp1 ω).2,
    (bernoulliDensity_derivatives p hp2 x u w hp0 hp1 ω).2,
    (bernoulliDensity_derivatives p hp2 x v w hp0 hp1 ω).2]
  ring

end
end SampleReuse
