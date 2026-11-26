import HeavyTail.IndependentBernoulliLaw
import HeavyTail.IndependentScalarMoments
import HeavyTail.MaskedMomentTools

/-! Exact strong and weak `p`-moment bounds for simultaneous independent
coordinate revelations (the original oracle of the manuscript, not the
alternative one-coordinate sampler used elsewhere). -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal InnerProductSpace
namespace HeavyTail.IndependentBernoulli
noncomputable section

def reply {k : ℕ} (α : ℝ) (g : HardSpace k) (b : Fin k → Bool) : HardSpace k :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => erasureReply (1 - α) (g j) (b j))

@[simp] theorem reply_apply {k : ℕ} (α : ℝ) (g : HardSpace k) (b : Fin k → Bool)
    (j : Fin k) : reply α g b j = erasureReply (1 - α) (g j) (b j) := rfl

theorem reply_unbiased {k : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (g : HardSpace k) : (∫ b, reply α g b ∂maskLaw k α hα.le) = g := by
  apply PiLp.ext
  intro j
  change (EuclideanSpace.proj j) (∫ b, reply α g b ∂maskLaw k α hα.le) = g j
  rw [← ContinuousLinearMap.integral_comp_comm _ Integrable.of_finite]
  exact coordinate_unbiased hα hα1 (g j) j

private theorem sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ r ≤ ∑ i ∈ s, (f i) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hr.ne']
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    exact (Real.rpow_add_le_add_rpow (hf i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)) hr.le hr1).trans
      (add_le_add_left (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) _)

theorem norm_rpow_le_coordinates {k : ℕ} {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (z : HardSpace k) : ‖z‖ ^ p ≤ ∑ j : Fin k, |z j| ^ p := by
  have h := sum_rpow_le Finset.univ (fun j : Fin k => (z j) ^ 2)
    (by linarith : 0 < p / 2) (by linarith : p / 2 ≤ 1) (fun j _ => sq_nonneg _)
  rw [← hardSpace_norm_sq, gaussianLower_square_rpow, abs_of_nonneg (norm_nonneg z)] at h
  simpa only [gaussianLower_square_rpow] using h

theorem reply_coordinate_moment {k : ℕ} {α p a : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (g : HardSpace k)
    (hg : ∀ j, |g j| ≤ a / Real.sqrt k) (j : Fin k) :
    (∫ b, |(reply α g b - g) j| ^ p ∂maskLaw k α hα.le) ≤
      2 * (a / Real.sqrt k) ^ p * α ^ (1 - p) := by
  apply (coordinate_moment hα hα1 hp (g j) j).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hg j) (by linarith))
      (by norm_num)) (by positivity)

theorem reply_strong_ratio {k : ℕ} {α p a : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a) (g : HardSpace k)
    (hg : ∀ j, |g j| ≤ a / Real.sqrt k) :
    (∫ b, ‖reply α g b - g‖ ^ p ∂maskLaw k α hα.le) ≤
      2 * (k : ℝ) * (a / Real.sqrt k) ^ p * α ^ (1 - p) := by
  calc
    _ ≤ ∫ b, ∑ j : Fin k, |(reply α g b - g) j| ^ p ∂maskLaw k α hα.le :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun b => norm_rpow_le_coordinates (by linarith) hp2 _)
    _ = ∑ j : Fin k, ∫ b, |(reply α g b - g) j| ^ p ∂maskLaw k α hα.le :=
      integral_finset_sum _ (fun j _ => Integrable.of_finite)
    _ ≤ ∑ _j : Fin k, 2 * (a / Real.sqrt k) ^ p * α ^ (1 - p) :=
      Finset.sum_le_sum fun j _ => reply_coordinate_moment hα hα1 hp ha g hg j
    _ = _ := by simp; ring

theorem reply_weak_ratio {k : ℕ} (hk : 0 < k) {α p a : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a)
    (g : HardSpace k) (hg : ∀ j, |g j| ≤ a / Real.sqrt k)
    (w : HardSpace k) (hw : ‖w‖ = 1) :
    (∫ b, |⟪w, reply α g b - g⟫_ℝ| ^ p ∂maskLaw k α hα.le) ≤
      (2 : ℝ) ^ p * (2 * (a / Real.sqrt k) ^ p * α ^ (1 - p)) *
        ((k : ℝ) * (1 / Real.sqrt k) ^ p) := by
  let U : Fin k → (Fin k → Bool) → ℝ :=
    fun j b => w j * (erasureReply (1 - α) (g j) (b j) - g j)
  have hU : ∀ j, Measurable (U j) := fun _ => Measurable.of_discrete
  have hInd : iIndepFun U (maskLaw k α hα.le) := by
    exact (maskLaw_independent α hα.le).comp
      (fun j b => w j * (erasureReply (1 - α) (g j) b - g j))
      (fun _ => Measurable.of_discrete)
  have hmean : ∀ j, (∫ b, U j b ∂maskLaw k α hα.le) = 0 := by
    intro j
    dsimp [U]
    rw [integral_const_mul, coordinate_centered hα hα1.le, mul_zero]
  have hmoment : ∀ j, (∫ b, |U j b| ^ p ∂maskLaw k α hα.le) ≤
      |w j| ^ p * (2 * (a / Real.sqrt k) ^ p * α ^ (1 - p)) := by
    intro j
    simp only [U, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (reply_coordinate_moment hα hα1 hp ha g hg j)
      (by positivity)
  have hind := IndependentMoments.independent_centered_sum_moment_of_rpow hp hp2 hU hInd
    Finset.univ (fun _ _ => Integrable.of_finite) (fun j _ => hmean j)
  have hid (b : Fin k → Bool) : ⟪w, reply α g b - g⟫_ℝ = ∑ j : Fin k, U j b := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, U, PiLp.sub_apply, reply_apply]
    congr 1
    ext j
    ring
  simp_rw [hid]
  apply hind.trans
  calc
    _ ≤ (2 : ℝ) ^ p * ∑ j : Fin k,
        |w j| ^ p * (2 * (a / Real.sqrt k) ^ p * α ^ (1 - p)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hmoment j) (by positivity)
    _ = (2 : ℝ) ^ p * (2 * (a / Real.sqrt k) ^ p * α ^ (1 - p)) *
        ∑ j : Fin k, |w j| ^ p := by rw [← Finset.sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (MaskedLower.coordinate_lp_sum_bound hk (by linarith) hp2 w hw) (by positivity)

theorem sqrt_div_rpow {k : ℕ} (hk : 0 < k) {a : ℝ} (ha : 0 ≤ a) (p : ℝ) :
    (a / Real.sqrt k) ^ p = a ^ p * (k : ℝ) ^ (-p / 2) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [Real.div_rpow ha (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hkR.le]
  rw [div_eq_mul_inv, ← Real.rpow_neg hkR.le]
  congr 2
  ring

/-- The printed coordinate estimate, including the exact power of `k`. -/
theorem reply_coordinate_source_moment {k : ℕ} (hk : 0 < k) {α p a : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (ha : 0 ≤ a)
    (g : HardSpace k) (hg : ∀ j, |g j| ≤ a / Real.sqrt k) (j : Fin k) :
    (∫ b, |(reply α g b - g) j| ^ p ∂maskLaw k α hα.le) ≤
      2 * a ^ p * (k : ℝ) ^ (-p / 2) * α ^ (1 - p) := by
  simpa only [sqrt_div_rpow hk ha, mul_assoc] using reply_coordinate_moment hα hα1 hp ha g hg j

/-- Both source estimates, under the actual independent Bernoulli law. -/
theorem reply_source_moments {k : ℕ} (hk : 0 < k) {α p a : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a)
    (g : HardSpace k) (hg : ∀ j, |g j| ≤ a / Real.sqrt k) :
    (∫ b, ‖reply α g b - g‖ ^ p ∂maskLaw k α hα.le) ≤
      2 * a ^ p * (k : ℝ) ^ (1 - p / 2) * α ^ (1 - p) ∧
    ∀ w : HardSpace k, ‖w‖ = 1 →
    (∫ b, |⟪w, reply α g b - g⟫_ℝ| ^ p ∂maskLaw k α hα.le) ≤
      (2 : ℝ) ^ (p + 1) * a ^ p * (k : ℝ) ^ (1 - p) * α ^ (1 - p) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : (k : ℝ) ^ (1 - p / 2) = (k : ℝ) * (k : ℝ) ^ (-p / 2) := by
    rw [show 1 - p / 2 = 1 + (-p / 2) by ring, Real.rpow_add hkR, Real.rpow_one]
  have hwk : (k : ℝ) ^ (1 - p) =
      (k : ℝ) * ((k : ℝ) ^ (-p / 2) * (k : ℝ) ^ (-p / 2)) := by
    rw [← Real.rpow_add hkR, show -p / 2 + -p / 2 = -p by ring,
      show 1 - p = 1 + -p by ring, Real.rpow_add hkR, Real.rpow_one]
  constructor
  · have h := reply_strong_ratio hα hα1 hp hp2 ha g hg
    rw [sqrt_div_rpow hk ha] at h
    rw [hs]
    convert h using 1 <;> ring
  · intro w hw
    have h := reply_weak_ratio hk hα hα1 hp hp2 ha g hg w hw
    rw [sqrt_div_rpow hk ha, sqrt_div_rpow hk (by norm_num : (0 : ℝ) ≤ 1),
      Real.one_rpow] at h
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, hwk]
    convert h using 1 <;> ring

end
end HeavyTail.IndependentBernoulli
