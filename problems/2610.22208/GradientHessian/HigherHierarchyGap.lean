import GradientHessian.HigherHierarchyValues
import GradientHessian.HigherHierarchyZero

/-! The actual root infimum gap, from the literal scalar at zero and its
global positive-baseline energy bound. Constants are independent of depth. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open Set

def gapConstant (K : ℝ) : ℝ := energyConstant K + Inner.innerConstant

theorem gapConstant_pos {K : ℝ} (hK : 0≤K) : 0<gapConstant K :=
  add_pos (energyConstant_pos hK) Inner.innerConstant_pos

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [∀ t, CompleteSpace (H t)]

theorem scalar_bddBelow {K : ℝ} (hK : 16≤K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) : BddBelow (range (scalar K t d)) := by
  refine ⟨-energy m K t-Inner.innerConstant*(m+1:ℝ), ?_⟩
  rintro _ ⟨Z,rfl⟩
  exact scalar_lower hK t d hd Z

theorem scalar_gap_energy {K : ℝ} (hK : 16≤K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) :
    scalar K t d 0 - sInf (range (scalar K t d)) ≤ energy m K t + Inner.innerConstant*(m+1:ℝ) := by
  have hlow : -energy m K t-Inner.innerConstant*(m+1:ℝ) ≤ sInf (range (scalar K t d)) :=
    le_csInf (range_nonempty _) (by rintro _ ⟨Z,rfl⟩; exact scalar_lower hK t d hd Z)
  rw [scalar_zero hK t d hd]
  nlinarith [sq_nonneg InverseGate.H₀]

theorem scalar_gap {K : ℝ} (hK : 16≤K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) :
    scalar K t d 0 - sInf (range (scalar K t d)) ≤ gapConstant K * 8^t * (m+1) := by
  have he := energy_le m (K := K) (by linarith) t
  have hi : Inner.innerConstant*(m+1:ℝ) ≤ Inner.innerConstant*8^t*(m+1:ℝ) := by
    have hp : (1:ℝ)≤8^t := one_le_pow₀ (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hp Inner.innerConstant_pos.le
    have hz := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ)≤m+1)
    simpa only [mul_one] using hz
  have h := scalar_gap_energy hK t d hd
  unfold gapConstant
  nlinarith

theorem scalar_gap_source_height {K : ℝ} (hK : 16≤K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) :
    scalar K t d 0 - sInf (range (scalar K t d)) ≤ gapConstant K * 8^(t+1) * (m+1) := by
  have h := scalar_gap hK t d hd
  have hp : (8:ℝ)^t ≤ 8^(t+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (gapConstant_pos (by linarith : 0≤K)).le) (by positivity))

end GradientHessian.HigherHierarchy
