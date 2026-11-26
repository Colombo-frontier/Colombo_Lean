import Nonsmooth.GaussianConcentration

open MeasureTheory ProbabilityTheory Metric Filter Function
open scoped Topology InnerProductSpace ENNReal
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem euclideanGaussian_truncation_complement_sharp :
    (euclideanGaussianLaw E).real (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)))ᶜ ≤
      2 / (9 * (Module.finrank ℝ E : ℝ)) := by
  let d := Module.finrank ℝ E
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr Module.finrank_pos
  have hi : Integrable (fun z : E => (‖z‖ ^ 2 - (d : ℝ)) ^ 2) (euclideanGaussianLaw E) :=
    (euclideanGaussian_norm_square_memLp.sub (memLp_const (d : ℝ))).integrable_sq
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := euclideanGaussianLaw E)
    (f := fun z : E => (‖z‖ ^ 2 - (d : ℝ)) ^ 2) (Eventually.of_forall (fun z => sq_nonneg _)) hi
    ((3 * (d : ℝ)) ^ 2)
  rw [euclideanGaussian_norm_centered_square] at hm
  have hs : (euclideanGaussianLaw E).real (closedBall (0 : E) (2 * Real.sqrt d))ᶜ ≤
      (euclideanGaussianLaw E).real {z : E | (3 * (d : ℝ)) ^ 2 ≤ (‖z‖ ^ 2 - (d : ℝ)) ^ 2} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro z hz
    have hz' : 2 * Real.sqrt (d : ℝ) < ‖z‖ := by
      simpa only [Set.mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz
    have hnorm : 4 * (d : ℝ) < ‖z‖ ^ 2 := by
      nlinarith [Real.sq_sqrt hd.le, Real.sqrt_nonneg (d : ℝ), norm_nonneg z]
    change (3 * (d : ℝ)) ^ 2 ≤ (‖z‖ ^ 2 - (d : ℝ)) ^ 2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (3 * (d : ℝ)))
  apply (le_div_iff₀ (by positivity : 0 < 9 * (d : ℝ))).mpr
  nlinarith

theorem gaussian_rows_truncation_complement (k : ℕ) :
    (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      (Set.univ.pi (fun _ : Fin k => closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))))ᶜ ≤
        2 * (k : ℝ) / (9 * (Module.finrank ℝ E : ℝ)) := by
  classical
  let B := closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))
  let P := Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)
  have he : (Set.univ.pi (fun _ : Fin k => B))ᶜ = ⋃ i : Fin k, {z : Fin k → E | z i ∈ Bᶜ} := by
    ext z
    simp
  have hb (i : Fin k) : P.real {z : Fin k → E | z i ∈ Bᶜ} ≤
      2 / (9 * (Module.finrank ℝ E : ℝ)) := by
    have hp := finite_product_coordinate (euclideanGaussianLaw E) i
    have hm := map_measureReal_apply (μ := P) hp.measurable
      (show MeasurableSet Bᶜ from measurableSet_closedBall.compl)
    rw [hp.map_eq] at hm
    calc
      _ = (euclideanGaussianLaw E).real Bᶜ := hm.symm
      _ ≤ _ := euclideanGaussian_truncation_complement_sharp
  change P.real (Set.univ.pi (fun _ : Fin k => B))ᶜ ≤ _
  rw [he]
  have h := (measureReal_iUnion_fintype_le (μ := P) (fun i : Fin k => {z : Fin k → E | z i ∈ Bᶜ})).trans
    (Finset.sum_le_sum (fun i _ => hb i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1 <;> first | rfl | ring

theorem gaussian_rows_truncation_probability {k : ℕ}
    (hk : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 16) :
    15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      (Set.univ.pi (fun _ : Fin k => closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E)))) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hb := gaussian_rows_truncation_complement (E := E) k
  have hb' : (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      (Set.univ.pi (fun _ : Fin k => closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))))ᶜ ≤ 1 / 16 := by
    exact hb.trans ((div_le_iff₀ (by positivity : 0 < 9 * (Module.finrank ℝ E : ℝ))).mpr (by linarith))
  have hs := measureReal_add_measureReal_compl (μ := Measure.pi (fun _ : Fin k => euclideanGaussianLaw E))
    (MeasurableSet.univ_pi (fun _ : Fin k => show MeasurableSet
      (closedBall (0 : E) (2 * Real.sqrt (Module.finrank ℝ E))) from measurableSet_closedBall))
  rw [probReal_univ] at hs
  linarith

end
end Nonsmooth
