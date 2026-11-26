import Bilevel.PartialLegendreQuadraticBudget

/-! A numerical slack below L for every actual quadratic coupled block.
The estimate is uniform in all block dimensions and leaves room for the
small partial-Legendre Hessian perturbation. -/
noncomputable section
namespace Bilevel.PartialLegendre
open PrimitiveGeometry

variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem normalQuadraticOperator_norm_bound {m L : ℝ} (hm : 0≤m) (hL : 0≤L)
    (hmL : m≤3*L/4) :
    ‖(normalQuadraticOperator m (L/4) : FullNormalVariables X U V →L[ℝ] FullNormalVariables X U V)‖≤7*L/8 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  have he : ‖normalQuadraticOperator m (L/4) q‖^2=
      (L/4)^2*‖q.snd.fst‖^2+‖m • q.snd.fst-(L/4) • q.fst.snd‖^2+
        m^2*‖q.snd.snd‖^2 := by
    rw [normalQuadraticOperator_apply,norm_sq,norm_sq,norm_sq]
    change (‖(0:X)‖^2+‖(-(L/4)) • q.snd.fst‖^2)+
      (‖m • q.snd.fst-(L/4) • q.fst.snd‖^2+‖m • q.snd.snd‖^2)= _
    simp only [norm_zero,zero_pow (by decide : 2≠0),zero_add,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,neg_sq]
    ring
  have hu : ‖m • q.snd.fst-(L/4) • q.fst.snd‖≤
      L*((3/4)*‖q.snd.fst‖+(1/4)*‖q.fst.snd‖) := by
    have ht := norm_sub_le (m • q.snd.fst) ((L/4) • q.fst.snd)
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg hm,abs_of_nonneg (by positivity : 0≤L/4)] at ht
    have hb := mul_le_mul_of_nonneg_right hmL (norm_nonneg q.snd.fst)
    nlinarith
  have hus := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hu
  have hm2 : m^2≤(3*L/4)^2 := (sq_le_sq₀ hm (by positivity)).mpr hmL
  have hrs := mul_le_mul_of_nonneg_right hm2 (sq_nonneg ‖q.snd.snd‖)
  have hq : ‖q‖^2=(‖q.fst.fst‖^2+‖q.fst.snd‖^2)+
      (‖q.snd.fst‖^2+‖q.snd.snd‖^2) := by rw [norm_sq,norm_sq,norm_sq]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖normalQuadraticOperator m (L/4) q‖^2 ≤
        L^2*((1/16)*‖q.snd.fst‖^2+
          ((3/4)*‖q.snd.fst‖+(1/4)*‖q.fst.snd‖)^2+(9/16)*‖q.snd.snd‖^2) := by
      rw [he]
      nlinarith only [hus,hrs]
    _ ≤ L^2*((49/64)*(‖q.fst.snd‖^2+‖q.snd.fst‖^2+‖q.snd.snd‖^2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
      nlinarith [sq_nonneg (‖q.snd.fst‖-2*‖q.fst.snd‖),
        sq_nonneg ‖q.fst.snd‖,sq_nonneg ‖q.snd.fst‖,sq_nonneg ‖q.snd.snd‖]
    _ ≤ ((7*L/8)*‖q‖)^2 := by
      rw [mul_pow,hq]
      nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg ‖q.fst.fst‖)]

end Bilevel.PartialLegendre
