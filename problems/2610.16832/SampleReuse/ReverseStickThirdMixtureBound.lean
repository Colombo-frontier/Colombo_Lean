import SampleReuse.ReverseStickThirdMixture
import SecondOrder.BernoulliMixtureOperatorBounds

/-! Third derivative operator bound for the actual scalar Bernoulli mixture. -/

open SecondOrder
open scoped BigOperators Classical
namespace SampleReuse
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem thirdTrilinear_abs_le {f : E → ℝ} (x u v w : E) :
    |thirdTrilinear f x u v w| ≤ ‖iteratedFDeriv ℝ 3 f x‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  have hh := (iteratedFDeriv ℝ 3 f x).le_opNorm ![u, v, w]
  simpa only [thirdTrilinear_eq_iterated, Fin.prod_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val, Matrix.head_cons,
    Matrix.tail_cons, Real.norm_eq_abs, mul_assoc] using hh

theorem third_opNorm_le_of_trilinear_bound {f : E → ℝ} {x : E} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ u v w, |thirdTrilinear f x u v w| ≤ C * ‖u‖ * ‖v‖ * ‖w‖) :
    ‖iteratedFDeriv ℝ 3 f x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro z
  have hz : ![z 0, z 1, z 2] = z := by ext i; fin_cases i <;> rfl
  have hh := hbound (z 0) (z 1) (z 2)
  simpa only [thirdTrilinear_eq_iterated, hz, Fin.prod_univ_three,
    Real.norm_eq_abs, mul_assoc] using hh

/-- Score first-moment estimates convert directly into an operator estimate
for the third derivative of the same sampled scalar mixture. -/
theorem bernoulliMixture_third_operator_bound
    (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 3 (p i)) (hV : ∀ ω, ContDiff ℝ 3 (V ω))
    (x : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1)
    (v₀ v₁ v₂ v₃ ell κ₂ κ₃ : ℝ)
    (hv₀ : 0 ≤ v₀) (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hell : 0 ≤ ell) (hκ₂ : 0 ≤ κ₂) (hκ₃ : 0 ≤ κ₃)
    (hval : ∀ ω, |V ω x| ≤ v₀)
    (hder : ∀ ω, ‖fderiv ℝ (V ω) x‖ ≤ v₁)
    (hsecond : ∀ ω, ‖fderiv ℝ (fderiv ℝ (V ω)) x‖ ≤ v₂)
    (hthird : ∀ ω, ‖iteratedFDeriv ℝ 3 (V ω) x‖ ≤ v₃)
    (hS : ∀ u, pmfMean (bernoulliProduct (fun i => p i x)
        (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun ω => |bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x u) ω|) ≤ ell * ‖u‖)
    (hK : ∀ u v, pmfMean (bernoulliProduct (fun i => p i x)
        (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun ω => |bernoulliSecondScore (fun i => p i x)
          (fun i => fderiv ℝ (p i) x u) (fun i => fderiv ℝ (p i) x v)
          (fun i => secondBilinear (p i) x u v) ω|) ≤ κ₂ * ‖u‖ * ‖v‖)
    (hH : ∀ u v w, pmfMean (bernoulliProduct (fun i => p i x)
        (fun i => (hp0 i).le) (fun i => (hp1 i).le))
        (fun ω => |bernoulliThirdScore (fun i => p i x)
          (fun i => fderiv ℝ (p i) x u) (fun i => fderiv ℝ (p i) x v)
          (fun i => fderiv ℝ (p i) x w)
          (fun i => secondBilinear (p i) x u v) (fun i => secondBilinear (p i) x u w)
          (fun i => secondBilinear (p i) x v w) (fun i => thirdTrilinear (p i) x u v w) ω|) ≤
          κ₃ * ‖u‖ * ‖v‖ * ‖w‖) :
    ‖iteratedFDeriv ℝ 3 (bernoulliMixture p V) x‖ ≤
      v₃ + v₀ * κ₃ + 3 * v₂ * ell + 3 * v₁ * κ₂ := by
  apply third_opNorm_le_of_trilinear_bound (by positivity)
  intro u v w
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
  have hd (ω : ι → Bool) (z : E) : |fderiv ℝ (V ω) x z| ≤ v₁ * ‖z‖ :=
    ((fderiv ℝ (V ω) x).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hder ω) (norm_nonneg z))
  have hd2 (ω : ι → Bool) (z z' : E) : |secondBilinear (V ω) x z z'| ≤ v₂ * ‖z‖ * ‖z'‖ :=
    (secondBilinear_abs_le x z z').trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsecond ω) (norm_nonneg z))
        (norm_nonneg z'))
  have hd3 (ω : ι → Bool) : |thirdTrilinear (V ω) x u v w| ≤ v₃ * ‖u‖ * ‖v‖ * ‖w‖ :=
    (thirdTrilinear_abs_le x u v w).trans (by gcongr; exact hthird ω)
  have h0 := pmfMean_le_const P _ hd3
  have hh := (pmfMean_abs_mul_le_of_bound P (fun ω => V ω x) H v₀ hval).trans
    (mul_le_mul_of_nonneg_left (hH u v w) hv₀)
  have hs (z z' z'' : E) := (pmfMean_abs_mul_le_of_bound P
    (fun ω => secondBilinear (V ω) x z z') (S z'') (v₂ * ‖z‖ * ‖z'‖)
      (fun ω => hd2 ω z z')).trans
      (mul_le_mul_of_nonneg_left (hS z'') (by positivity))
  have hk (z z' z'' : E) := (pmfMean_abs_mul_le_of_bound P
    (fun ω => fderiv ℝ (V ω) x z) (K z' z'') (v₁ * ‖z‖) (fun ω => hd ω z)).trans
      (mul_le_mul_of_nonneg_left (hK z' z'') (by positivity))
  have htri (ω : ι → Bool) :
      |thirdTrilinear (V ω) x u v w + V ω x * H ω +
        secondBilinear (V ω) x v w * S u ω + secondBilinear (V ω) x u w * S v ω +
        secondBilinear (V ω) x u v * S w ω + fderiv ℝ (V ω) x u * K v w ω +
        fderiv ℝ (V ω) x v * K u w ω + fderiv ℝ (V ω) x w * K u v ω| ≤
      |thirdTrilinear (V ω) x u v w| + |V ω x * H ω| +
        |secondBilinear (V ω) x v w * S u ω| + |secondBilinear (V ω) x u w * S v ω| +
        |secondBilinear (V ω) x u v * S w ω| + |fderiv ℝ (V ω) x u * K v w ω| +
        |fderiv ℝ (V ω) x v * K u w ω| + |fderiv ℝ (V ω) x w * K u v ω| := by
    repeat' apply (abs_add _ _).trans (add_le_add_right _ _)
    exact le_refl _
  rw [bernoulliMixture_third p V hp hV x u v w hp0 hp1]
  have ht := (abs_pmfMean_le P _).trans (pmfMean_mono P htri)
  simp only [pmfMean_add] at ht ⊢
  have htotal := ht.trans (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add (add_le_add (add_le_add h0 hh) (hs v w u)) (hs u w v)) (hs u v w))
      (hk u v w)) (hk v u w)) (hk w u v))
  convert htotal using 1
  ring

end
end SampleReuse
