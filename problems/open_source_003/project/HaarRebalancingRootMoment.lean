import HaarRebalancingAverage
import SphereConcentration

/-!
The actual Phi and h of the manuscript, with proved measurability, nonnegativity,
root-moment identity, Lipschitz regularity and averaged third-halves moment.
-/

open Set MeasureTheory ProbabilityTheory Real Metric
open Task006.SphereConcentration
open scoped ENNReal NNReal

namespace Task006.HaarRebalancing
noncomputable section

/-- The sample third-halves moment of the actual directional secant family. -/
def directionalMoment {Sample E : Type*} [MeasurableSpace Sample]
    (σ : Measure Sample) (D : Sample → E → ℝ) (q : E) : ℝ :=
  ∫ z, |D z q| ^ (3 / 2 : ℝ) ∂σ

/-- Its actual L^(3/2) root, the function h in the manuscript. -/
def directionalRootMoment {Sample E : Type*} [MeasurableSpace Sample]
    (σ : Measure Sample) (D : Sample → E → ℝ) (q : E) : ℝ :=
  directionalMoment σ D q ^ (2 / 3 : ℝ)

theorem directionalMoment_nonneg {Sample E : Type*} [MeasurableSpace Sample]
    (σ : Measure Sample) (D : Sample → E → ℝ) (q : E) :
    0 ≤ directionalMoment σ D q :=
  integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)

theorem directionalRootMoment_nonneg {Sample E : Type*} [MeasurableSpace Sample]
    (σ : Measure Sample) (D : Sample → E → ℝ) (q : E) :
    0 ≤ directionalRootMoment σ D q :=
  Real.rpow_nonneg (directionalMoment_nonneg σ D q) _

theorem directionalRootMoment_rpow {Sample E : Type*} [MeasurableSpace Sample]
    (σ : Measure Sample) (D : Sample → E → ℝ) (q : E) :
    directionalRootMoment σ D q ^ (3 / 2 : ℝ) = directionalMoment σ D q := by
  unfold directionalRootMoment
  rw [← Real.rpow_mul (directionalMoment_nonneg σ D q)]
  norm_num

/-- Parameter integration gives genuine measurable functions Phi and h. -/
theorem directionalMoment_measurable {d : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    {σ : Measure Sample} [SFinite σ]
    {D : Sample → EuclideanSpace ℝ (Fin d) → ℝ}
    (hjoint : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => D p.1 p.2)) :
    Measurable (directionalMoment σ D) ∧ Measurable (directionalRootMoment σ D) := by
  have hp : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) =>
      |D p.1 p.2| ^ (3 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).measurable.comp hjoint.abs
  have hΦ : Measurable (directionalMoment σ D) :=
    hp.stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨hΦ, ?_⟩
  exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).measurable.comp hΦ

/-- Minkowski proves that the actual h is L-Lipschitz on the unit sphere,
using only the actual G moment budget and legal directional pathwise bounds. -/
theorem directionalRootMoment_lipschitz {d : ℕ} {Sample : Type*} [MeasurableSpace Sample]
    {σ : Measure Sample} [IsProbabilityMeasure σ]
    (D : Sample → EuclideanSpace ℝ (Fin d) → ℝ) (G : Sample → ℝ≥0)
    (hjoint : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => D p.1 p.2))
    (hG : Measurable G)
    (hlip : ∀ z, LipschitzOnWith (G z) (D z) (sphere (0 : _) 1))
    (hbound : ∀ z q, ‖q‖ = 1 → |D z q| ≤ G z)
    (hmG : Integrable (fun z => (G z : ℝ) ^ (3 / 2 : ℝ)) σ)
    {L : ℝ} (hL : 0 ≤ L)
    (hbudget : (∫ z, (G z : ℝ) ^ (3 / 2 : ℝ) ∂σ) ≤ L ^ (3 / 2 : ℝ)) :
    LipschitzOnWith (Real.toNNReal L) (directionalRootMoment σ D) (sphere (0 : _) 1) := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin d)) 1
  let Ds : S → Sample → ℝ := fun q z => D z q
  let Greal : Sample → ℝ := fun z => G z
  have hGreal : Measurable Greal := measurable_subtype_coe.comp hG
  have hm : Integrable (fun z => |Greal z| ^ (3 / 2 : ℝ)) σ := by
    simpa only [Greal, abs_of_nonneg (NNReal.coe_nonneg _)] using hmG
  have hbudget' : (∫ z, |Greal z| ^ (3 / 2 : ℝ) ∂σ) ≤ L ^ (3 / 2 : ℝ) := by
    simpa only [Greal, abs_of_nonneg (NNReal.coe_nonneg _)] using hbudget
  have hDs (q : S) : AEStronglyMeasurable (Ds q) σ :=
    (hjoint.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hdom (q : S) (z : Sample) : |Ds q z| ≤ Greal z :=
    hbound z q (by simpa only [S, mem_sphere_zero_iff_norm] using q.property)
  have hpath (q q' : S) (z : Sample) : |Ds q z - Ds q' z| ≤ Greal z * dist q q' := by
    have h := (hlip z).dist_le_mul (q : EuclideanSpace ℝ (Fin d)) q.property
      (q' : EuclideanSpace ℝ (Fin d)) q'.property
    simpa only [Ds, Greal, Subtype.dist_eq, Real.dist_eq] using h
  have h := threeHalves_rootMoment_lipschitz Ds Greal hL hGreal.aestronglyMeasurable
    hm hbudget' hDs hdom hpath
  apply LipschitzOnWith.of_dist_le_mul
  intro q hq q' hq'
  have hqq := h ⟨q, hq⟩ ⟨q', hq'⟩
  simpa only [Ds, Greal, directionalRootMoment, directionalMoment,
    Subtype.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL] using hqq

/-- The actual h has the averaged r-th moment needed for the Markov step,
with no assumed concentration or moment conclusion. -/
theorem directionalRootMoment_average {d : ℕ} {Sample Ω : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Ω]
    {σ : Measure Sample} {ν : Measure Ω} [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]
    {v : Ω → EuclideanSpace ℝ (Fin d)} (hv : UniformSphereLaw v ν) (hvmeas : Measurable v)
    (hd : 0 < d) (D : Sample → EuclideanSpace ℝ (Fin d) → ℝ) (G : Sample → ℝ≥0)
    (hjoint : Measurable (fun p : Sample × EuclideanSpace ℝ (Fin d) => D p.1 p.2))
    (hlip : ∀ z, LipschitzOnWith (G z) (D z) (sphere (0 : _) 1))
    (hodd : ∀ z q, D z (-q) = -D z q)
    (hbound : ∀ z q, ‖q‖ = 1 → |D z q| ≤ G z)
    (hmG : Integrable (fun z => (G z : ℝ) ^ (3 / 2 : ℝ)) σ)
    {L : ℝ} (hbudget : (∫ z, (G z : ℝ) ^ (3 / 2 : ℝ) ∂σ) ≤ L ^ (3 / 2 : ℝ)) :
    Integrable (fun ω => directionalRootMoment σ D (v ω) ^ (3 / 2 : ℝ)) ν ∧
      (∫ ω, directionalRootMoment σ D (v ω) ^ (3 / 2 : ℝ) ∂ν) ≤
        thirdHalfMomentConstant * L ^ (3 / 2 : ℝ) / (d : ℝ) ^ (3 / 4 : ℝ) := by
  have hD (z : Sample) : Measurable (D z) :=
    hjoint.comp (measurable_const.prodMk measurable_id)
  have hpair : Measurable (fun p : Sample × Ω => D p.1 (v p.2)) :=
    hjoint.comp (measurable_fst.prodMk (hvmeas.comp measurable_snd))
  have h := average_odd_threeHalves_moment hv hvmeas hd D G hD hpair hlip hodd hbound hmG hbudget
  have heq : (fun ω => directionalRootMoment σ D (v ω) ^ (3 / 2 : ℝ)) =ᵐ[ν]
      (fun ω => directionalMoment σ D (v ω)) :=
    Filter.Eventually.of_forall (fun ω => directionalRootMoment_rpow σ D (v ω))
  refine ⟨h.1.integral_prod_right.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact h.2

end
end Task006.HaarRebalancing
