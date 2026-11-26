import NCBall.ChordAverages
import NCBall.FiniteChoice

/-! # An actual two-point estimator with dimension-linear second moment

Draw a point uniformly in the ball and an independent uniform coordinate.
The estimator uses the two endpoints of that coordinate chord. The sample
function is the same at both endpoints. This provides an alternative to
the antipodal spherical estimator in the source paper.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped NNReal ENNReal BigOperators
namespace NCBall

def chordSeedLaw (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) : Measure (CoordSpace (n + 1) × Fin (n + 1)) :=
  (ballLaw volume ρ hρ).prod (uniformIndex (n + 1) (Nat.succ_pos n))

instance chordSeedLaw_probability (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    IsProbabilityMeasure (chordSeedLaw n ρ hρ) := by
  unfold chordSeedLaw
  infer_instance

def chordEstimate {n : ℕ} (f : CoordSpace (n + 1) → ℝ) (ρ : ℝ)
    (x : CoordSpace (n + 1)) (w : CoordSpace (n + 1) × Fin (n + 1)) : CoordSpace (n + 1) :=
  ((n + 1 : ℝ) * chordSlope f x w.2 ρ (chordSide w.2 w.1)) • EuclideanSpace.single w.2 (1 : ℝ)

theorem chordSlope_joint_measurable {n : ℕ} {f : CoordSpace (n + 1) → ℝ} (hf : Continuous f)
    (i : Fin (n + 1)) (ρ : ℝ) :
    Measurable (fun p : CoordSpace (n + 1) × (Fin n → ℝ) => chordSlope f p.1 i ρ p.2) := by
  have hh := (chordHalfLength_continuous (n := n) ρ).measurable.comp
    (measurable_snd : Measurable (Prod.snd : CoordSpace (n + 1) × (Fin n → ℝ) → (Fin n → ℝ)))
  have hp := (chordInsert_joint_measurable i).comp (hh.prodMk measurable_snd)
  have hm := (chordInsert_joint_measurable i).comp (hh.neg.prodMk measurable_snd)
  exact ((hf.measurable.comp (measurable_fst.add hp)).sub
    (hf.measurable.comp (measurable_fst.add hm))).div (measurable_const.mul hh)

theorem chordEstimate_joint_measurable {n : ℕ} {f : CoordSpace (n + 1) → ℝ}
    (hf : Continuous f) (ρ : ℝ) :
    Measurable (fun p : CoordSpace (n + 1) × (CoordSpace (n + 1) × Fin (n + 1)) =>
      chordEstimate f ρ p.1 p.2) := by
  have hm : Measurable (fun p : (CoordSpace (n + 1) × CoordSpace (n + 1)) × Fin (n + 1) =>
      chordEstimate f ρ p.1.1 (p.1.2, p.2)) := by
    apply measurable_from_prod_countable
    intro i
    change Measurable (fun p : CoordSpace (n + 1) × CoordSpace (n + 1) =>
      ((n + 1 : ℝ) * chordSlope f p.1 i ρ (chordSide i p.2)) • EuclideanSpace.single i (1 : ℝ))
    have hside : Measurable (fun p : CoordSpace (n + 1) × CoordSpace (n + 1) =>
        (p.1, chordSide i p.2)) :=
      measurable_fst.prodMk ((chordSide_measurable i).comp measurable_snd)
    have hq := (chordSlope_joint_measurable hf i ρ).comp hside
    dsimp only [Function.comp_def] at hq
    exact (measurable_const.mul hq).smul measurable_const
  have ht : Measurable (fun p : CoordSpace (n + 1) × (CoordSpace (n + 1) × Fin (n + 1)) =>
      ((p.1, p.2.1), p.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hfinal := hm.comp ht
  simpa only [Function.comp_def, Prod.mk.eta] using hfinal

theorem chordEstimate_norm_sq {n : ℕ} (f : CoordSpace (n + 1) → ℝ) (ρ : ℝ)
    (x : CoordSpace (n + 1)) (w : CoordSpace (n + 1) × Fin (n + 1)) :
    ‖chordEstimate f ρ x w‖ ^ 2 = (n + 1 : ℝ) ^ 2 * (chordSlope f x w.2 ρ (chordSide w.2 w.1)) ^ 2 := by
  simp [chordEstimate, norm_smul, EuclideanSpace.norm_single, Real.norm_eq_abs, mul_pow, sq_abs]

theorem chordEstimate_norm_le {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (ρ : ℝ) (x : CoordSpace (n + 1))
    (w : CoordSpace (n + 1) × Fin (n + 1)) : ‖chordEstimate f ρ x w‖ ≤ (n + 1 : ℝ) * L := by
  have hq := chordSlope_abs_le hf x w.2 ρ (chordSide w.2 w.1)
  simpa [chordEstimate, norm_smul, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ))] using
    mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ (n + 1 : ℝ))

theorem chordEstimate_memLp {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) (x : CoordSpace (n + 1)) :
    MemLp (chordEstimate f ρ x) 2 (chordSeedLaw n ρ hρ) :=
  MemLp.of_bound (((chordEstimate_joint_measurable hf.continuous ρ).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ((n + 1 : ℝ) * L)
    (Eventually.of_forall (chordEstimate_norm_le hf ρ x))

theorem chordEstimate_mean {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) (x : CoordSpace (n + 1)) :
    (∫ w, chordEstimate f ρ x w ∂chordSeedLaw n ρ hρ) = gradient (ballAverage volume ρ hρ f) x := by
  have hi := (chordEstimate_memLp hf hρ x).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [chordSeedLaw, integral_prod_symm _ hi, uniformIndex_integral]
  simp_rw [chordEstimate, integral_smul_const, integral_const_mul, chordSlope_mean hf x _ hρ]
  ext j
  have he : (∑ i : Fin (n + 1), ((n + 1 : ℝ) * gradient (ballAverage volume ρ hρ f) x i) •
      EuclideanSpace.single i (1 : ℝ)) j = ∑ i : Fin (n + 1),
      (((n + 1 : ℝ) * gradient (ballAverage volume ρ hρ f) x i) • EuclideanSpace.single i (1 : ℝ)) j :=
    by
      simpa only [PiLp.proj_apply] using map_sum
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) j)
        (fun i : Fin (n + 1) => ((n + 1 : ℝ) * gradient (ballAverage volume ρ hρ f) x i) •
          EuclideanSpace.single i (1 : ℝ)) Finset.univ
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp [PiLp.smul_apply, he, EuclideanSpace.single_apply, smul_eq_mul, hn]

theorem chordEstimate_second_moment {n : ℕ} {f : CoordSpace (n + 1) → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) {ρ : ℝ} (hρ : 0 < ρ) (x : CoordSpace (n + 1)) :
    (∫ w, ‖chordEstimate f ρ x w‖ ^ 2 ∂chordSeedLaw n ρ hρ) ≤ (n + 1 : ℝ) * (L : ℝ) ^ 2 := by
  have hi := (chordEstimate_memLp hf hρ x).norm.integrable_sq
  have hg (i : Fin (n + 1)) : MemLp (fun z => gradient f (x + z) i) 2 (ballLaw volume ρ hρ) :=
    MemLp.of_bound (coordinate_gradient_measurable f x i).aestronglyMeasurable (L : ℝ)
      (Eventually.of_forall (fun z => coordinate_gradient_norm_le hf i (x + z)))
  have hgn : MemLp (fun z => gradient f (x + z)) 2 (ballLaw volume ρ hρ) :=
    MemLp.of_bound ((measurable_gradient f).comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (L : ℝ) (Eventually.of_forall (fun z => norm_gradient_le_of_lipschitz hf (x + z)))
  have hsum : (∑ i : Fin (n + 1), ∫ z, (gradient f (x + z) i) ^ 2 ∂ballLaw volume ρ hρ) =
      ∫ z, ‖gradient f (x + z)‖ ^ 2 ∂ballLaw volume ρ hρ := by
    rw [← integral_finset_sum _ (fun i _ => (hg i).integrable_sq)]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  have hb : (∫ z, ‖gradient f (x + z)‖ ^ 2 ∂ballLaw volume ρ hρ) ≤ (L : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ _, (L : ℝ) ^ 2 ∂ballLaw (volume : Measure (CoordSpace (n + 1))) ρ hρ :=
        integral_mono_ae hgn.norm.integrable_sq (integrable_const _) (Eventually.of_forall (fun z =>
          pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitz hf (x + z)) 2))
      _ = _ := by simp
  rw [chordSeedLaw, integral_prod_symm _ hi, uniformIndex_integral]
  simp_rw [chordEstimate_norm_sq, integral_const_mul, smul_eq_mul]
  calc
    _ = (n + 1 : ℝ) * ∑ i : Fin (n + 1),
        ∫ z, (chordSlope f x i ρ (chordSide i z)) ^ 2 ∂ballLaw volume ρ hρ := by
      rw [← Finset.mul_sum]
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    _ ≤ (n + 1 : ℝ) * ∑ i : Fin (n + 1),
        ∫ z, (gradient f (x + z) i) ^ 2 ∂ballLaw volume ρ hρ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => chordSlope_second_moment hf x i hρ)) (by positivity)
    _ ≤ _ := by rw [hsum]; exact mul_le_mul_of_nonneg_left hb (by positivity)

end NCBall
