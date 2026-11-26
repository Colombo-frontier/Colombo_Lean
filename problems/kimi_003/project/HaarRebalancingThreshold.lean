import HaarRebalancingCutoff
import HaarRebalancingUnion
import RebalancingArithmetic

/-!
The actual spherical rebalancing bound U3. Constants are explicit absolute
functions of a fixed Gaussian tail integral. Every probability input is proved
from the secant family's natural measurable/odd/Lipschitz/moment properties.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.SphereConcentration
open scoped ENNReal NNReal

namespace Task006.HaarRebalancing
noncomputable section

/-- An absolute cutoff coefficient, determined by the proved averaged moment. -/
def rebalancingK0 : ℝ := (2 * thirdHalfMomentConstant) ^ (2 / 3 : ℝ)

def rebalancingB : ℝ := 512 * (1 + rebalancingK0)

def rebalancingC2 : ℝ := rebalancingB ^ (3 / 2 : ℝ)

/-- The full U3 directional-moment tail, with explicit c0=s0=1 and absolute
C2. The actual Phi and h are the integrated secant functions, not placeholders. -/
theorem directionalMoment_rebalancing {d : ℕ} {Sample Ω : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Ω]
    {σ : Measure Sample} {ν : Measure Ω} [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v ν) (hvmeas : Measurable v)
    (hd : 0 < d) (D : Sample → EuclideanSpace ℝ (Fin d) → ℝ) (G : Sample → ℝ≥0)
    (hjoint : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => D p.1 p.2))
    (hG : Measurable G)
    (hlip : ∀ z, LipschitzOnWith (G z) (D z) (sphere (0 : _) 1))
    (hodd : ∀ z q, D z (-q) = -D z q)
    (hbound : ∀ z q, ‖q‖ = 1 → |D z q| ≤ G z)
    (hmG : Integrable (fun z => (G z : ℝ) ^ (3 / 2 : ℝ)) σ)
    {L : ℝ} (hL : 0 < L)
    (hbudget : (∫ z, (G z : ℝ) ^ (3 / 2 : ℝ) ∂σ) ≤ L ^ (3 / 2 : ℝ))
    {s : ℝ} (hs : 1 ≤ s) :
    ν.real {ω | rebalancingC2 * L ^ (3 / 2 : ℝ) * (s / (d : ℝ)) ^ (3 / 4 : ℝ) ≤
      directionalMoment σ D (v ω)} ≤ Real.exp (-s) := by
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hC : 0 ≤ thirdHalfMomentConstant := le_trans (by norm_num) thirdHalfMomentConstant_ge_one
  have hCpos : 0 < thirdHalfMomentConstant := lt_of_lt_of_le (by norm_num) thirdHalfMomentConstant_ge_one
  let M : ℝ := thirdHalfMomentConstant * L ^ (3 / 2 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ)
  let m : ℝ := rebalancingK0 * L / Real.sqrt (d : ℝ)
  let t : ℝ := (rebalancingB / 2) * L * Real.sqrt (s / (d : ℝ))
  have hM : 0 < M := div_pos (mul_pos hCpos (Real.rpow_pos_of_pos hL _))
    (Real.rpow_pos_of_pos hdreal _)
  have hmeas := (directionalMoment_measurable (σ := σ) hjoint).2
  have hrootlip := directionalRootMoment_lipschitz D G hjoint hG hlip hbound hmG hL.le hbudget
  have havg := directionalRootMoment_average hv hvmeas hd D G hjoint hlip hodd hbound hmG hbudget
  have hhalf := lower_half_of_threeHalves_bound
    (fun ω => directionalRootMoment_nonneg σ D (v ω)) havg.1 hM havg.2
  dsimp only [M] at hhalf
  rw [thirdHalf_markov_cutoff hC hL hdreal] at hhalf
  change (1 / 2 : ℝ) ≤ ν.real {ω | directionalRootMoment σ D (v ω) ≤ m} at hhalf
  have hc := Task006.RebalancingArithmetic.constants_valid
    thirdHalfMomentConstant (d : ℝ) L s hC hdreal hL hs
  change 0 < rebalancingB ∧ 0 < rebalancingC2 ∧ m ≤ t ∧
    Real.exp 128 * Real.exp (-((d : ℝ) * t ^ 2) / (128 * L ^ 2)) ≤ Real.exp (-s) ∧
    (rebalancingC2 * L ^ (3 / 2 : ℝ) * (s / (d : ℝ)) ^ (3 / 4 : ℝ)) ^ (2 / 3 : ℝ) =
      rebalancingB * L * Real.sqrt (s / (d : ℝ)) at hc
  have ht : 0 < t := by
    dsimp only [t]
    exact mul_pos (mul_pos (div_pos hc.1 (by norm_num)) hL)
      (Real.sqrt_pos.2 (div_pos (by linarith) hdreal))
  have htail := sphere_lower_half_concentration hv hd hmeas (Real.toNNReal_pos.mpr hL)
    hrootlip hhalf ht
  simp only [Real.coe_toNNReal L hL.le] at htail
  have hthreshold : 0 ≤ rebalancingC2 * L ^ (3 / 2 : ℝ) *
      (s / (d : ℝ)) ^ (3 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg hc.2.1.le (Real.rpow_nonneg hL.le _))
      (Real.rpow_nonneg (div_nonneg (by linarith) hdreal.le) _)
  have hcompare : m + t ≤ rebalancingB * L * Real.sqrt (s / (d : ℝ)) := by
    calc
      m + t ≤ t + t := by linarith [hc.2.2.1]
      _ = rebalancingB * L * Real.sqrt (s / (d : ℝ)) := by dsimp only [t]; ring
  have hsubset : {ω | rebalancingC2 * L ^ (3 / 2 : ℝ) *
      (s / (d : ℝ)) ^ (3 / 4 : ℝ) ≤ directionalMoment σ D (v ω)} ⊆
      {ω | m + t ≤ directionalRootMoment σ D (v ω)} := by
    intro ω hω
    have hr := (directionalMoment_ge_iff_root_ge σ D (v ω) hthreshold).1 hω
    rw [hc.2.2.2.2] at hr
    exact hcompare.trans hr
  exact (measureReal_mono hsubset).trans (htail.trans (by
    simpa only [neg_mul] using hc.2.2.2.1))

/-- A single fresh Haar basis has bad probability at most d*exp(-s). This
uses all actual column laws but no independence between columns. -/
theorem haar_basis_rebalancing {d : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    {σ : Measure Sample} [IsProbabilityMeasure σ]
    (hd : 0 < d) (D : Sample → EuclideanSpace ℝ (Fin d) → ℝ) (G : Sample → ℝ≥0)
    (hjoint : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => D p.1 p.2))
    (hG : Measurable G)
    (hlip : ∀ z, LipschitzOnWith (G z) (D z) (sphere (0 : _) 1))
    (hodd : ∀ z q, D z (-q) = -D z q)
    (hbound : ∀ z q, ‖q‖ = 1 → |D z q| ≤ G z)
    (hmG : Integrable (fun z => (G z : ℝ) ^ (3 / 2 : ℝ)) σ)
    {L : ℝ} (hL : 0 < L)
    (hbudget : (∫ z, (G z : ℝ) ^ (3 / 2 : ℝ) ∂σ) ≤ L ^ (3 / 2 : ℝ))
    {s : ℝ} (hs : 1 ≤ s) :
    (orthogonalHaarProbability d).real {Q | ∃ i : Fin d,
      rebalancingC2 * L ^ (3 / 2 : ℝ) * (s / (d : ℝ)) ^ (3 / 4 : ℝ) ≤
        directionalMoment σ D (column Q i)} ≤ (d : ℝ) * Real.exp (-s) := by
  apply basis_bad_probability_le {q | rebalancingC2 * L ^ (3 / 2 : ℝ) *
    (s / (d : ℝ)) ^ (3 / 4 : ℝ) ≤ directionalMoment σ D q}
  intro i
  exact directionalMoment_rebalancing (column_isUniform i) (measurable_column i) hd
    D G hjoint hG hlip hodd hbound hmG hL hbudget hs

end
end Task006.HaarRebalancing
