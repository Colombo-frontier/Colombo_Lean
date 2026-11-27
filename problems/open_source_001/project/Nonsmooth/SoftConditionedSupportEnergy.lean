import Nonsmooth.SoftVectorConcentration
import Nonsmooth.SoftProjectionRank
import Nonsmooth.SupportProjectionRankCriterion

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- A logarithmic actual posterior mean increment for independent hard
event-conditioned rows that have regular positive soft approximations.
All limiting and posterior identities are proved; existence and regularity
of the approximations remain explicit analytic data. -/
theorem soft_conditioned_support_log_energy {n : ℕ}
    (μ : Fin (n + 1) → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (hLp : ∀ i, MemLp (fun z : E => z) 2 (μ i))
    (hExp : ∀ i (v : E), Integrable (fun z : E => Real.exp ⟪v, z⟫_ℝ) (μ i))
    {u : E} (hu : ‖u‖ = 1) (hd : 2 ≤ Module.finrank ℝ E)
    (hatom : ∀ i y, μ i {z : E | ⟪z, u⟫_ℝ = y} = 0)
    (w : Fin (n + 1) → ℕ → E → ℝ) (hw : ∀ i m, Measurable (w i m))
    (hb : ∀ i m z, 0 ≤ w i m z ∧ w i m z ≤ 1)
    (hp : ∀ i m, ∀ᵐ z ∂μ i, 0 < w i m z)
    (A : Fin (n + 1) → Set E) (hA : ∀ i, MeasurableSet (A i)) (hpos : ∀ i, μ i (A i) ≠ 0)
    (hlim : ∀ i, ∀ᵐ z ∂μ i, Tendsto (fun m => w i m z) atTop (𝓝 ((A i).indicator (fun _ => (1 : ℝ)) z)))
    (H : ∀ i m (v : E), ‖v‖ = 1 → ⟪u, v⟫_ℝ = 0 →
      RegularProjectionImage (weightedDensityLaw (μ i) (w i m)) u v) :
    letI (i : Fin (n + 1)) : IsProbabilityMeasure (μ i)[|A i] := cond_isProbabilityMeasure (hpos i)
    (∫ h, ‖posteriorAggregateShift (Measure.pi (fun i => (μ i)[|A i])) (supportSingleObservation u) h‖ ^ 2
      ∂(Measure.pi (fun i => (μ i)[|A i])).map (supportSingleObservation u)) ≤
        512 * Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) := by
  let ν := fun i => (μ i)[|A i]
  letI (i : Fin (n + 1)) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hpos i)
  have hi := fun i => (hLp i).integrable (by norm_num)
  have hνLp (i : Fin (n + 1)) : MemLp (fun z : E => z) 2 (ν i) :=
    ((hLp i).mono_measure Measure.restrict_le_self).smul_measure (ENNReal.inv_ne_top.mpr (hpos i))
  have hνatom (i : Fin (n + 1)) (y : ℝ) : ν i {z : E | ⟪z, u⟫_ℝ = y} = 0 :=
    cond_absolutelyContinuous (hatom i y)
  have hνrank (i : Fin (n + 1)) := soft_projection_rank_bound (μ i) (hi i) hu hd (hatom i)
    (w i) (hw i) (hb i) (hp i) (A i) (hA i) (hpos i) (hlim i) (H i)
  have hνmgf (i : Fin (n + 1)) (v : E) := soft_conditioned_vector_concentration (μ i) (hi i) hu hd
    (w i) (hw i) (hb i) (hp i) (A i) (hA i) (hpos i) (hlim i) (H i) v (hExp i v)
  have hνbound (i : Fin (n + 1)) (v : E) :
      (∫ z, Real.exp ⟪v, z - ∫ a : E, a ∂ν i⟫_ℝ ∂ν i) ≤ Real.exp (4 * ‖v‖ ^ 2 / 2) := by
    convert (hνmgf i v).2 using 1
    congr 1
    ring
  have hs := support_aggregate_shift_of_projection_rank ν u hνatom hνLp
    (by norm_num : (0 : ℝ) < 4) (by norm_num : (0 : ℝ) < 72)
    (fun i v => (hνmgf i v).1) hνbound hνrank
  apply hs.trans
  have hk : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  have hk0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hlog : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogk : 0 ≤ Real.log (((n + 1 : ℕ) : ℝ)) := Real.log_nonneg hk
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hk0.ne',
    Real.log_mul (Real.exp_ne_zero _) hk0.ne', Real.log_exp]
  nlinarith

end
end Nonsmooth
