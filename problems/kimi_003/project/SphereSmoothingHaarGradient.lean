import SphereSmoothingRiesz
import SphereSurfaceLaw
open MeasureTheory MeasureTheory.Measure Set Metric Function Filter
open Task006.HaarRebalancing
open scoped NNReal Topology
namespace Task006.SphereSmoothing
noncomputable section

/-- Exact original sphere-gradient formula for actual uniform-ball smoothing,
with the same Haar-column marginal used elsewhere in the paper. -/
theorem ballSmoothGradient_eq_haar {d : ℕ} (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {ρ : ℝ} (hρ : 0 < ρ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    Task006.Full.ballSmoothGradient f ρ x =
      ((d:ℝ)/ρ) • ∫ Q : OrthogonalGroup d,
        f (x+ρ • column Q j) • column Q j ∂orthogonalHaarProbability d := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have hg : Measurable (fun u : EuclideanSpace ℝ (Fin d) => f (x+ρ • u) • u) :=
    (hf.continuous.comp (continuous_const.add (continuous_id.const_smul ρ))).measurable.smul measurable_id
  have hs := surface_integral_eq_haar (fun u : EuclideanSpace ℝ (Fin d) => f (x+ρ • u) • u) hg j
  rw [ballSmoothGradient_eq_surface hd hf hρ x,hs,smul_smul,smul_smul]
  have hV : 0 < (volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : _) zero_lt_one).ne' measure_ball_lt_top.ne
  have hball : (volume : Measure (EuclideanSpace ℝ (Fin d))).real (closedBall 0 ρ) =
      ρ^d*(volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1) := by
    simpa using
      addHaar_real_closedBall (volume : Measure (EuclideanSpace ℝ (Fin d))) (0 : _) hρ.le
  rw [hball,surface_ball_coefficient hd hρ hV]

end
end Task006.SphereSmoothing
namespace Task006.Full.SampleInstance
open Task006.SphereSmoothing
variable {d : ℕ} {L R : ℝ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ] (I : SampleInstance d L R Ω μ)

/-- The exact manuscript population-gradient identity in the original local
sample-instance model. The auxiliary extension agrees at every legal point. -/
theorem smoothedGradient_eq_haar (hL : 0 ≤ L) (hR : 0 ≤ R) (hd : 0 < d)
    {ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {x : Space d} (hx : ‖x‖ ≤ R) (j : Fin d) :
    I.smoothedGradient hL hR ρ x = ((d:ℝ)/ρ) • ∫ Q : OrthogonalGroup d,
      I.objective (x+ρ • column Q j) • column Q j ∂orthogonalHaarProbability d := by
  unfold smoothedGradient
  rw [ballSmoothGradient_eq_haar hd (I.objectiveExtension_lipschitz hL hR) hρ x j]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro Q
  have hq : ‖column Q j‖ ≤ 1 := ((orthonormal_column Q).norm_eq_one j).le
  dsimp only
  rw [← I.objectiveExtension_eq hL hR (ballTranslate_mem_queryDomain hρ.le hρR hx hq)]

end Task006.Full.SampleInstance
