import ModelFull
import UpperSmoothing
import HaarRebalancing

open MeasureTheory

namespace Task006.Full

abbrev UnitBallPoint (d : ℕ) := Metric.closedBall (0 : Space d) 1

noncomputable def unitBallProbability (d : ℕ) : Measure (UnitBallPoint d) :=
  (unitBallLaw d).comap Subtype.val

lemma unitBallLaw_full_mass (d : ℕ) :
    unitBallLaw d (Metric.closedBall (0 : Space d) 1) = 1 := by
  apply (mem_ae_iff_prob_eq_one measurableSet_closedBall).mp
  change ∀ᵐ u ∂unitBallLaw d, u ∈ Metric.closedBall (0 : Space d) 1
  simpa only [Metric.mem_closedBall, dist_zero_right] using unitBallLaw_norm_le d

instance unitBallProbability_probability (d : ℕ) :
    IsProbabilityMeasure (unitBallProbability d) where
  measure_univ := by
    let emb := MeasurableEmbedding.subtype_coe
      (measurableSet_closedBall : MeasurableSet (Metric.closedBall (0 : Space d) 1))
    rw [unitBallProbability, emb.comap_apply, Set.image_univ, Subtype.range_coe]
    exact unitBallLaw_full_mass d

lemma unitBallProbability_map (d : ℕ) :
    (unitBallProbability d).map (Subtype.val : UnitBallPoint d → Space d) = unitBallLaw d := by
  rw [unitBallProbability, map_comap_subtype_coe measurableSet_closedBall]
  apply Measure.restrict_eq_self_of_ae_mem
  simpa only [Metric.mem_closedBall, dist_zero_right] using unitBallLaw_norm_le d

abbrev UpperBlockSeed (d : ℕ) :=
  Task006.HaarRebalancing.OrthogonalGroup d × (Fin d → UnitBallPoint d)

abbrev UpperSeed (d T : ℕ) := Fin T → UpperBlockSeed d

noncomputable def upperBlockSeedLaw (d : ℕ) : Measure (UpperBlockSeed d) :=
  (Task006.HaarRebalancing.orthogonalHaarProbability d).prod
    (Measure.pi (fun _ : Fin d => unitBallProbability d))

instance upperBlockSeedLaw_probability (d : ℕ) :
    IsProbabilityMeasure (upperBlockSeedLaw d) := by
  unfold upperBlockSeedLaw
  infer_instance

noncomputable def upperSeedLaw (d T : ℕ) : Measure (UpperSeed d T) :=
  Measure.pi (fun _ : Fin T => upperBlockSeedLaw d)

instance upperSeedLaw_probability (d T : ℕ) : IsProbabilityMeasure (upperSeedLaw d T) := by
  unfold upperSeedLaw
  infer_instance

lemma upper_seed_smoothing_legal (d T : ℕ) (seed : UpperSeed d T) (t : Fin T) (i : Fin d) :
    ‖((seed t).2 i).val‖ ≤ 1 := by
  simpa only [Metric.mem_closedBall, dist_zero_right] using ((seed t).2 i).property

lemma upperSeedLaw_eval (d T : ℕ) (t : Fin T) :
    (upperSeedLaw d T).map (fun seed => seed t) = upperBlockSeedLaw d := by
  exact (measurePreserving_eval (fun _ : Fin T => upperBlockSeedLaw d) t).map_eq

lemma upperBlockSeedLaw_basis (d : ℕ) :
    (upperBlockSeedLaw d).map Prod.fst =
      Task006.HaarRebalancing.orthogonalHaarProbability d := by
  simp [upperBlockSeedLaw]

end Task006.Full
