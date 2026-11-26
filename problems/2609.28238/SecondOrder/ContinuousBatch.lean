import SecondOrder.ProductMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter
open scoped InnerProductSpace

namespace SecondOrder
noncomputable section

/-- A finite sequence of fresh draws, represented by iterated products. -/
def Draws (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => Draws Ω n × Ω

instance drawsMeasurableSpace {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    MeasurableSpace (Draws Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ n ih => exact @Prod.instMeasurableSpace _ _ ih inferInstance

def drawsLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    (n : ℕ) → Measure (Draws Ω n)
  | 0 => Measure.dirac PUnit.unit
  | n+1 => (drawsLaw μ n).prod μ

instance drawsLaw_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) : IsProbabilityMeasure (drawsLaw μ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsProbabilityMeasure ((drawsLaw μ n).prod μ))

def drawsSum {Ω E : Type*} [AddZeroClass E] (X : Ω → E) : (n : ℕ) → Draws Ω n → E
  | 0, _ => 0
  | n+1, w => drawsSum X n w.1+X w.2

def drawsMean {Ω E : Type*} [AddZeroClass E] [SMul ℝ E]
    (X : Ω → E) (n : ℕ) (w : Draws Ω n) : E := (n : ℝ)⁻¹ • drawsSum X n w

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E}

theorem drawsSum_integrable (hX : Integrable X μ) (n : ℕ) :
    Integrable (drawsSum X n) (drawsLaw μ n) := by
  induction n with
  | zero => exact integrable_const _
  | succ n ih => exact (integrable_product_fst ih).add (integrable_product_snd hX)

theorem drawsSum_integral (hX : Integrable X μ) (n : ℕ) :
    (∫ w, drawsSum X n w ∂drawsLaw μ n) = (n : ℝ) • (∫ z, X z ∂μ) := by
  induction n with
  | zero => simp [drawsSum]
  | succ n ih =>
    rw [show (drawsLaw μ (n+1)) = (drawsLaw μ n).prod μ from rfl]
    change (∫ w, drawsSum X n w.1+X w.2 ∂(drawsLaw μ n).prod μ) = _
    rw [integral_product_sum (drawsSum_integrable hX n) hX, ih]
    simp [Nat.cast_add, add_smul]

theorem drawsSum_sq_integrable (hX : Integrable X μ)
    (hX2 : Integrable (fun z => ‖X z‖^2) μ) (n : ℕ) :
    Integrable (fun w => ‖drawsSum X n w‖^2) (drawsLaw μ n) := by
  induction n with
  | zero => simpa only [drawsSum, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (integrable_const (μ := drawsLaw μ 0) (0 : ℝ))
  | succ n ih =>
    exact integrable_product_sum_sq (drawsSum_integrable hX n) hX ih hX2

theorem drawsSum_second_moment (hX : Integrable X μ)
    (hX2 : Integrable (fun z => ‖X z‖^2) μ) (hX0 : (∫ z, X z ∂μ) = 0) (n : ℕ) :
    (∫ w, ‖drawsSum X n w‖^2 ∂drawsLaw μ n) = (n : ℝ)*(∫ z, ‖X z‖^2 ∂μ) := by
  induction n with
  | zero => simp [drawsSum]
  | succ n ih =>
    rw [show (drawsLaw μ (n+1)) = (drawsLaw μ n).prod μ from rfl]
    change (∫ w, ‖drawsSum X n w.1+X w.2‖^2 ∂(drawsLaw μ n).prod μ) = _
    rw [integral_product_sum_sq (drawsSum_integrable hX n) hX
      (drawsSum_sq_integrable hX hX2 n) hX2 hX0, ih]
    push_cast
    ring

theorem drawsSum_center (a : E) (n : ℕ) (w : Draws Ω n) :
    drawsSum (fun z => X z-a) n w = drawsSum X n w-(n : ℝ)•a := by
  induction n with
  | zero => simp [drawsSum]
  | succ n ih =>
    simp only [drawsSum, ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

theorem drawsMean_center (a : E) {n : ℕ} (hn : 0 < n) (w : Draws Ω n) :
    drawsMean (fun z => X z-a) n w = drawsMean X n w-a := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [drawsMean, drawsSum_center, smul_sub, smul_smul, hn0]

theorem drawsMean_unbiased (hX : Integrable X μ) {n : ℕ} (hn : 0 < n) :
    (∫ w, drawsMean X n w ∂drawsLaw μ n) = ∫ z, X z ∂μ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [drawsMean]
  rw [integral_smul, drawsSum_integral hX]
  simp [smul_smul, hn0]

theorem drawsMean_variance (hX : Integrable X μ) {a : E}
    (he : Integrable (fun z => ‖X z-a‖^2) μ) (hm : (∫ z, X z ∂μ) = a)
    {n : ℕ} (hn : 0 < n) :
    (∫ w, ‖drawsMean X n w-a‖^2 ∂drawsLaw μ n) =
      (∫ z, ‖X z-a‖^2 ∂μ)/(n : ℝ) := by
  have hE : Integrable (fun z => X z-a) μ := hX.sub (integrable_const _)
  have hE0 : (∫ z, X z-a ∂μ) = 0 := by rw [integral_sub hX (integrable_const _),hm]; simp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp_rw [← drawsMean_center a hn, drawsMean, norm_smul, Real.norm_eq_abs, mul_pow]
  rw [integral_const_mul, drawsSum_second_moment hE he hE0]
  rw [sq_abs]
  field_simp
  ring

theorem drawsMean_error_integrable (hX : Integrable X μ) {a : E}
    (he : Integrable (fun z => ‖X z-a‖^2) μ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun w => ‖drawsMean X n w-a‖^2) (drawsLaw μ n) := by
  have hs := drawsSum_sq_integrable (hX.sub (integrable_const a)) he n
  simp_rw [← drawsMean_center a hn, drawsMean, norm_smul, Real.norm_eq_abs, mul_pow]
  exact hs.const_mul _

/-- Chebyshev's bound without any finite-support assumption on the samples. -/
theorem drawsMean_failure_probability (hX : Integrable X μ) {a : E}
    (he : Integrable (fun z => ‖X z-a‖^2) μ) (hm : (∫ z, X z ∂μ) = a)
    {n : ℕ} (hn : 0 < n) {r V : ℝ} (hr : 0 < r)
    (hV : (∫ z, ‖X z-a‖^2 ∂μ) ≤ V) :
    drawsLaw μ n {w | r ≤ ‖drawsMean X n w-a‖} ≤ ENNReal.ofReal (V/((n : ℝ)*r^2)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsq : 0 < r^2 := sq_pos_of_pos hr
  have hb := ((drawsMean_error_integrable hX he hn).div_const (r^2)).measure_le_integral
    (Eventually.of_forall (fun w => div_nonneg (sq_nonneg _) hsq.le))
    (s := {w | r ≤ ‖drawsMean X n w-a‖}) (fun w hw => by
      apply (le_div_iff₀ hsq).mpr
      simpa only [one_mul] using pow_le_pow_left₀ hr.le hw 2)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div, drawsMean_variance hX he hm hn]
  calc
    _ ≤ (V/(n : ℝ))/r^2 := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hV hnR.le) hsq.le
    _ = _ := by rw [div_div]

end
end SecondOrder
