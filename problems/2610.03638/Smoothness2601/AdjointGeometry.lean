import Smoothness2601.Population
import Smoothness2601.AdjointContraction

/-! The adjoint target and contraction are derived from the actual Population. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Smoothness2601.AdjointGeometry

def radius (b : Budgets) : ℝ := b.L₀/b.μ
def ballRadius (b : Budgets) : ℝ := max 1 (radius b)
def stepsize (b : Budgets) : ℝ := 1/(2*b.L₁)
def rate (b : Budgets) : ℝ := 1-stepsize b*b.μ/2
def biasTerm (b : Budgets) (a : ℝ) : ℝ := 3*stepsize b*a ^ 2/b.μ
def noiseTerm (b : Budgets) (W : ℝ) : ℝ := stepsize b ^ 2*b.σ ^ 2*(1+W ^ 2)

theorem radius_nonneg (b : Budgets) : 0 ≤ radius b := div_nonneg b.L₀_pos.le b.μ_pos.le
theorem ballRadius_one (b : Budgets) : 1 ≤ ballRadius b := le_max_left _ _
theorem ballRadius_nonneg (b : Budgets) : 0 ≤ ballRadius b := le_trans zero_le_one (ballRadius_one b)
theorem stepsize_pos (b : Budgets) : 0 < stepsize b := by
  have := b.L₁_pos
  dsimp [stepsize]
  positivity
theorem rate_range (b : Budgets) (hμL : b.μ ≤ b.L₁) : 0 < rate b ∧ rate b < 1 :=
  (AdjointContraction.chosen_stepsize_range b.μ_pos hμL).2.2

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [FiniteDimensional ℝ Y] {b : Budgets}
  (P : Population (X := X) (Y := Y) b)

def target (p : X × Y) : Y := P.primitive.inverseAt p.1 p.2 (P.primitive.fy p.1 p.2)

theorem target_equation (p : X × Y) : P.gyy p.1 p.2 (target P p) = P.primitive.fy p.1 p.2 :=
  P.primitive.inverseAt_right _ _ _

theorem target_norm (p : X × Y) : ‖target P p‖ ≤ radius b :=
  (AdjointContraction.solution_norm_le (P.gyy p.1 p.2).toLinearMap b.μ_pos
    (P.primitive.hessian_coercive _ _) _ _ (target_equation P p)).trans
    (div_le_div_of_nonneg_right (P.primitive.upper_bound _ _) b.μ_pos.le)

theorem target_in_ball (p : X × Y) : ‖target P p‖ ≤ ballRadius b :=
  (target_norm P p).trans (le_max_right _ _)

omit [FiniteDimensional ℝ Y] in
theorem upper (p : X × Y) (v : Y) : ⟪P.gyy p.1 p.2 v,v⟫ ≤ b.L₁*‖v‖ ^ 2 := by
  have hnorm : ‖P.gyy p.1 p.2‖ ≤ b.L₁ :=
    (P.has_gyy _ _).le_of_lip' b.L₁_pos.le
      (Filter.Eventually.of_forall (fun z => P.primitive.gy_lipschitz_y p.1 z p.2))
  have hv := ((P.gyy p.1 p.2).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  calc
    _ ≤ ‖P.gyy p.1 p.2 v‖*‖v‖ := real_inner_le_norm _ _
    _ ≤ (b.L₁*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right hv (norm_nonneg _)
    _ = _ := by ring

theorem clipped_drift (hμL : b.μ ≤ b.L₁) {a : ℝ} (ha : 0 ≤ a)
    (p : X × Y) (v m : Y)
    (hbias : ‖m-P.gyy p.1 p.2 (Bilevel.Clipping.clip (ballRadius b) v)‖ ≤ a) :
    ‖Bilevel.Clipping.clip (ballRadius b) v-stepsize b • (m-P.primitive.fy p.1 p.2)-target P p‖ ^ 2 ≤
      rate b*‖v-target P p‖ ^ 2+biasTerm b a := by
  have hs := AdjointContraction.chosen_stepsize_range b.μ_pos hμL
  have hd := AdjointContraction.deterministic_drift (P.gyy p.1 p.2).toLinearMap
    (P.primitive.hessian_symmetric _ _) b.μ_pos hμL hs.1.le ha hs.2.1
    (P.primitive.hessian_coercive _ _) (upper P p) (P.primitive.fy p.1 p.2)
    (Bilevel.Clipping.clip (ballRadius b) v) (target P p)
    (m-P.gyy p.1 p.2 (Bilevel.Clipping.clip (ballRadius b) v)) (target_equation P p) hbias
  have he : P.gyy p.1 p.2 (Bilevel.Clipping.clip (ballRadius b) v)-P.primitive.fy p.1 p.2+
      (m-P.gyy p.1 p.2 (Bilevel.Clipping.clip (ballRadius b) v)) = m-P.primitive.fy p.1 p.2 := by abel
  change ‖Bilevel.Clipping.clip (ballRadius b) v - stepsize b •
    (P.gyy p.1 p.2 (Bilevel.Clipping.clip (ballRadius b) v)-P.primitive.fy p.1 p.2+
      (m-P.gyy p.1 p.2 (Bilevel.Clipping.clip (ballRadius b) v))) - target P p‖ ^ 2 ≤
    rate b*‖Bilevel.Clipping.clip (ballRadius b) v-target P p‖ ^ 2+biasTerm b a at hd
  rw [he] at hd
  have hclip := Bilevel.Clipping.squared_error_nonincreasing (ballRadius b)
    (ballRadius_nonneg b) v (target P p) (target_in_ball P p)
  exact hd.trans (add_le_add_right (mul_le_mul_of_nonneg_left hclip (rate_range b hμL).1.le) _)

end Smoothness2601.AdjointGeometry
