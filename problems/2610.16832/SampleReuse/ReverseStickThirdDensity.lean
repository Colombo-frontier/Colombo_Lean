import SampleReuse.ReverseStickThirdProduct
import SecondOrder.BernoulliMixtureCalculus

/-! The third Bernoulli score is the actual normalized derivative of its mass. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem thirdTrilinear_const_sub (f : E → ℝ) (r : ℝ) (x u v w : E) :
    thirdTrilinear (fun y => r - f y) x u v w = -thirdTrilinear f x u v w := by
  have h1 : fderiv ℝ (fun y => r - f y) = fun y => -fderiv ℝ f y :=
    funext (fun y => fderiv_const_sub r)
  have h2 : fderiv ℝ (fun y => -fderiv ℝ f y) =
      fun y => -fderiv ℝ (fderiv ℝ f) y := funext (fun y => fderiv_neg)
  rw [thirdTrilinear, h1, h2]
  have h3 : fderiv ℝ (fun y => -fderiv ℝ (fderiv ℝ f) y) x =
      -fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x :=
    fderiv_neg (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ f)) (x := x)
  rw [h3]
  simp only [ContinuousLinearMap.neg_apply, thirdTrilinear]

theorem binaryMass_normalized_third (f : E → ℝ) (hf : ContDiff ℝ 3 f)
    (x u v w : E) (hp0 : 0 < f x) (hp1 : f x < 1) (b : Bool) :
    ContDiff ℝ 3 (fun y => binaryMass (f y) b) ∧
      thirdTrilinear (fun y => binaryMass (f y) b) x u v w =
        binaryMass (f x) b * (thirdTrilinear f x u v w * binaryScore (f x) b) := by
  have hm := binaryMass_mul_score hp0 hp1 b
  cases b
  · simp only [binaryMass, Bool.false_eq_true, if_false] at hm ⊢
    refine ⟨contDiff_const.sub hf, ?_⟩
    rw [thirdTrilinear_const_sub, mul_left_comm (1 - f x), hm]
    ring
  · simp only [binaryMass, if_true] at hm ⊢
    refine ⟨hf, ?_⟩
    rw [mul_left_comm (f x), hm, mul_one]

def bernoulliThirdScore (p a b c ab ac bc abc : ι → ℝ) (ω : ι → Bool) : ℝ :=
  normalizedThirdScore Finset.univ
    (fun i => a i * binaryScore (p i) (ω i))
    (fun i => b i * binaryScore (p i) (ω i))
    (fun i => c i * binaryScore (p i) (ω i))
    (fun i => ab i * binaryScore (p i) (ω i))
    (fun i => ac i * binaryScore (p i) (ω i))
    (fun i => bc i * binaryScore (p i) (ω i))
    (fun i => abc i * binaryScore (p i) (ω i))

/-- Exact third derivative of the product Bernoulli density, with all
repeated-index corrections present. -/
theorem bernoulliDensity_third (p : ι → E → ℝ) (hp : ∀ i, ContDiff ℝ 3 (p i))
    (x u v w : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1)
    (ω : ι → Bool) :
    thirdTrilinear (fun y => bernoulliDensity (fun i => p i y) ω) x u v w =
      bernoulliDensity (fun i => p i x) ω *
        bernoulliThirdScore (fun i => p i x)
          (fun i => fderiv ℝ (p i) x u)
          (fun i => fderiv ℝ (p i) x v)
          (fun i => fderiv ℝ (p i) x w)
          (fun i => secondBilinear (p i) x u v)
          (fun i => secondBilinear (p i) x u w)
          (fun i => secondBilinear (p i) x v w)
          (fun i => thirdTrilinear (p i) x u v w) ω := by
  have hp2 (i : ι) := (hp i).of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)
  have huv (i : ι) := binaryMass_normalized_jets (p i) (hp2 i) x u v (hp0 i) (hp1 i) (ω i)
  have huw (i : ι) := binaryMass_normalized_jets (p i) (hp2 i) x u w (hp0 i) (hp1 i) (ω i)
  have hvw (i : ι) := binaryMass_normalized_jets (p i) (hp2 i) x v w (hp0 i) (hp1 i) (ω i)
  have ht (i : ι) := binaryMass_normalized_third (p i) (hp i) x u v w (hp0 i) (hp1 i) (ω i)
  exact product_normalized_third Finset.univ (fun i y => binaryMass (p i y) (ω i))
    (fun i _ => (ht i).1) x u v w
    (fun i => fderiv ℝ (p i) x u * binaryScore (p i x) (ω i))
    (fun i => fderiv ℝ (p i) x v * binaryScore (p i x) (ω i))
    (fun i => fderiv ℝ (p i) x w * binaryScore (p i x) (ω i))
    (fun i => secondBilinear (p i) x u v * binaryScore (p i x) (ω i))
    (fun i => secondBilinear (p i) x u w * binaryScore (p i x) (ω i))
    (fun i => secondBilinear (p i) x v w * binaryScore (p i x) (ω i))
    (fun i => thirdTrilinear (p i) x u v w * binaryScore (p i x) (ω i))
    (fun i _ => (huv i).2.1) (fun i _ => (hvw i).2.1)
    (fun i _ => (binaryMass_normalized_jets (p i) (hp2 i) x w u (hp0 i) (hp1 i) (ω i)).2.1)
    (fun i _ => (huv i).2.2) (fun i _ => (huw i).2.2)
    (fun i _ => (hvw i).2.2) (fun i _ => (ht i).2)

end
end SampleReuse
