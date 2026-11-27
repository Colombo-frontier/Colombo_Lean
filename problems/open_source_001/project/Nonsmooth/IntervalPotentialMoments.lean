import Nonsmooth.TiltedMomentCalculus

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem intervalDensityLaw_memLp_two {a b : ℝ} (hab : a ≤ b)
    (w : ℝ → ℝ) (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hZ : 0 < ∫ x in a..b, w x) : MemLp (fun x : ℝ => x) 2 (intervalDensityLaw w a b) := by
  let Q := intervalDensityMeasure w a b
  have hid : AEStronglyMeasurable (fun x : ℝ => x) Q := measurable_id.aestronglyMeasurable
  have hbase : MemLp (fun x : ℝ => x) 2 Q := by
    apply (memLp_two_iff_integrable_sq hid).mpr
    change Integrable (fun x : ℝ => x ^ 2)
      ((volume.restrict (Icc a b)).withDensity (fun x => ENNReal.ofReal (w x)))
    rw [integrable_withDensity_iff hw.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hw0 _)]
    exact ((continuous_id.pow 2).mul hw).continuousOn.integrableOn_Icc
  have hm : Q univ ≠ 0 := by
    dsimp only [Q]
    rw [intervalDensityMeasure_mass hab w hw hw0]
    exact (ENNReal.ofReal_pos.mpr hZ).ne'
  simpa only [intervalDensityLaw, ProbabilityTheory.cond, Measure.restrict_univ] using
    hbase.smul_measure (ENNReal.inv_ne_top.mpr hm)

def intervalPotentialMoment (U : ℝ → ℝ) (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  densityMoment (volume.restrict (Icc a b)) U n t

def intervalPotentialMean (U : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  intervalPotentialMoment U a b 1 t / intervalPotentialMoment U a b 0 t

theorem intervalPotentialMoment_integral (U : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (n : ℕ) (t : ℝ) :
    intervalPotentialMoment U a b n t = ∫ x in a..b, x ^ n * Real.exp (t * x - U x) := by
  rw [intervalPotentialMoment, densityMoment, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

theorem intervalPotentialMoment_hasDerivAt (U : ℝ → ℝ) (hU : Continuous U)
    (a b : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (intervalPotentialMoment U a b n) (intervalPotentialMoment U a b (n + 1) t) t := by
  apply densityMoment_hasDerivAt
  intro r m
  have hc : Continuous (fun x : ℝ => x ^ m * Real.exp (r * x - U x)) := by fun_prop
  exact hc.continuousOn.integrableOn_Icc

theorem intervalPotentialMoment_zero_pos (U : ℝ → ℝ) (hU : Continuous U)
    {a b : ℝ} (hab : a < b) (t : ℝ) : 0 < intervalPotentialMoment U a b 0 t := by
  rw [intervalPotentialMoment_integral U hab.le]
  simp only [pow_zero, one_mul]
  have hc : Continuous (fun x : ℝ => Real.exp (t * x - U x)) := by fun_prop
  exact intervalIntegral.integral_pos hab hc.continuousOn (fun x _ => (Real.exp_pos _).le)
    ⟨a, ⟨le_rfl, hab.le⟩, Real.exp_pos _⟩

theorem intervalPotentialMean_eq_integral (U : ℝ → ℝ) (hU : Continuous U)
    {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    intervalPotentialMean U a b t =
      ∫ x : ℝ, x ∂intervalDensityLaw (fun x => Real.exp (t * x - U x)) a b := by
  have hc : Continuous (fun x : ℝ => Real.exp (t * x - U x)) := by fun_prop
  rw [intervalDensityLaw_integral hab _ hc (fun x => (Real.exp_pos _).le)]
  simp only [intervalPotentialMean, intervalPotentialMoment_integral U hab, pow_one, pow_zero, one_mul]

theorem intervalPotentialVariance_eq (U : ℝ → ℝ) (hU : Continuous U)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    variance (fun x : ℝ => x) (intervalDensityLaw (fun x => Real.exp (t * x - U x)) a b) =
      intervalPotentialMoment U a b 2 t / intervalPotentialMoment U a b 0 t -
        (intervalPotentialMean U a b t) ^ 2 := by
  have hc : Continuous (fun x : ℝ => Real.exp (t * x - U x)) := by fun_prop
  have hc0 : ∀ x, 0 ≤ Real.exp (t * x - U x) := fun x => (Real.exp_pos _).le
  have hZ : 0 < ∫ x in a..b, Real.exp (t * x - U x) := by
    have h := intervalPotentialMoment_zero_pos U hU hab t
    simpa only [intervalPotentialMoment_integral U hab.le, pow_zero, one_mul] using h
  letI := intervalDensityLaw_probability hab.le _ hc hc0 hZ
  have hLp := intervalDensityLaw_memLp_two hab.le _ hc hc0 hZ
  rw [variance_eq_sub hLp, ← intervalPotentialMean_eq_integral U hU hab.le t]
  change (∫ x : ℝ, x ^ 2 ∂intervalDensityLaw (fun x => Real.exp (t * x - U x)) a b) -
    (intervalPotentialMean U a b t) ^ 2 = _
  rw [intervalDensityLaw_integral hab.le _ hc hc0]
  simp only [intervalPotentialMoment_integral U hab.le, pow_zero, one_mul]

end
end Nonsmooth
