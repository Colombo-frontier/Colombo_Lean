import HardFamilyBayesEvent
import AdaptiveSphereGlobalEnergy

open MeasureTheory

namespace Task006.HardFamilyBayes

open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereGlobal
open Task006.PosteriorCenter Task006.StoppedEnergy

noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

theorem large_dimension_bayes_risk_gt (alg : OracleAlgorithm d N S) (j : Fin d)
    (L R A eps : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hA : 16 ≤ A) (heps : 0 < eps)
    (hscale : (16*L/A)*R = 16*eps) (hd : 8 ≤ d) (hlegal : LegalOriginal alg R)
    (σ : Measure S) [IsProbabilityMeasure σ]
    (hbudget : (4096/A^3)*(N : ℝ) ≤ (d : ℝ)/32) :
    eps < (∫ w, originalGap alg j R (16*L/A) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) := by
  classical
  let k := Task006LowerAudit.rankThreshold d
  have hkb := Task006LowerAudit.rank_threshold_bounds d hd
  have hkd : k ≤ d := by dsimp only [k]; omega
  have hk : 0 < k := by dsimp only [k]; omega
  have hdk : d ≤ 8*k := hkb.2.1
  have h4k : 4*(k : ℝ) ≤ (d : ℝ) := by exact_mod_cast hkb.2.2
  have hm : 0 ≤ 16*L/A := by positivity
  have ha := goodRankEvent_half_mass alg L R A hL hA hlegal σ k hkd hk hdk j hbudget
  have hevent : MeasurableSet (goodRankEvent alg k hkd j) :=
    (jointObservation_measurable alg k hkd N j).comap_le _
      (goodRankEvent_measurable_past alg k hkd j)
  have he : (∫ w, (goodRankEvent alg k hkd j).indicator
      (fun w => ‖jointCenter alg k hkd N j w‖^2) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) ≤ 1/3 := by
    rw [integral_indicator hevent]
    exact (joint_event_center_energy_le_ratio alg k hkd j
      (σ.prod (iidHandleLaw (law L A hA))) _).trans
        (Task006LowerAudit.harmonic_energy_ratio_bound d k (Nat.cast_nonneg _) h4k).2.le
  have hn : 0 ≤ ∫ w, (goodRankEvent alg k hkd j).indicator
      (fun w => ‖jointCenter alg k hkd N j w‖) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d) := by
    apply integral_nonneg
    intro w
    exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) w
  have hCS := event_center_cauchy_schwarz alg k hkd j (σ.prod (iidHandleLaw (law L A hA)))
  have hrisk := originalGap_risk_lower alg k hkd j R (16*L/A) hR hm hlegal
    (σ.prod (iidHandleLaw (law L A hA)))
  rw [hscale] at hrisk
  exact Task006.LowerRisk.large_dimension_risk_from_event_moments eps _ _ _ _
    heps ha hn he hCS hrisk

theorem center_zero_on_zero_rank_event (alg : OracleAlgorithm d N S) (h1d : 1 ≤ d)
    (j : Fin d) (w : Exogenous S × OrthogonalGroup d)
    (hw : w ∈ goodRankEvent alg 1 h1d j) : jointCenter alg 1 h1d N j w = 0 := by
  have hr : (jointFrame alg 1 h1d N j w).1.val = 0 := by
    change (jointFrame alg 1 h1d N j w).1.val < 1 at hw
    omega
  rw [jointCenter_eq_projected alg 1 h1d N le_rfl j w,projectedCenter_eq_sum]
  simp only [hr,Nat.not_lt_zero,Finset.filter_false,Finset.sum_empty]

theorem small_dimension_bayes_risk_gt (alg : OracleAlgorithm d N S) (j : Fin d)
    (L R A eps : ℝ) (hL : 0 < L) (hR : 0 ≤ R) (hA : 16 ≤ A) (heps : 0 < eps)
    (hscale : (16*L/A)*R = 16*eps) (h1d : 1 ≤ d) (hd7 : d ≤ 7) (hlegal : LegalOriginal alg R)
    (σ : Measure S) [IsProbabilityMeasure σ]
    (hbudget : (4096/A^3)*(N : ℝ) ≤ (d : ℝ)/32) :
    eps < (∫ w, originalGap alg j R (16*L/A) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) := by
  classical
  have hm : 0 ≤ 16*L/A := by positivity
  have ha := goodRankEvent_small_mass alg L R A hL hA hlegal σ h1d hd7 j hbudget
  have hz : (fun w : Exogenous S × OrthogonalGroup d =>
      (goodRankEvent alg 1 h1d j).indicator (fun w => ‖jointCenter alg 1 h1d N j w‖) w) =
        fun _ => (0 : ℝ) := by
    funext w
    by_cases hw : w ∈ goodRankEvent alg 1 h1d j
    · rw [Set.indicator_of_mem hw,center_zero_on_zero_rank_event alg h1d j w hw,norm_zero]
    · exact Set.indicator_of_notMem hw _
  have hrisk := originalGap_risk_lower alg 1 h1d j R (16*L/A) hR hm hlegal
    (σ.prod (iidHandleLaw (law L A hA)))
  rw [hz,integral_zero,sub_zero,hscale] at hrisk
  exact Task006LowerAudit.conditional_small_dimension_risk_reduction eps _ _ heps ha hrisk

end
end Task006.HardFamilyBayes
