import NCBall.FiniteMaximum

/-! # Independent rooms: maximum norm moment and probability of the good event -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace NCBall

theorem iidProduct_eval_map {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (j : ι) :
    Measure.map (fun x : ι → E => x j) (Measure.pi (fun _ => μ)) = μ := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply j) hs]
  change Measure.pi (fun _ : ι => μ) (Function.eval j ⁻¹' s) = μ s
  rw [← Set.univ_pi_update_univ, Measure.pi_pi]
  simp [Function.update_apply, apply_ite]

def gaussianRooms (n M : ℕ) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi (fun _ => isotropicGaussian n)

instance (n M : ℕ) : IsProbabilityMeasure (gaussianRooms n M) := by
  unfold gaussianRooms
  letI : ∀ _j : Fin M, IsProbabilityMeasure (isotropicGaussian n) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

def maximumNormSq {n M : ℕ} (z : Fin M → Fin n → ℝ) : ℝ :=
  nonnegativeMaximum Finset.univ (fun j => coordinateNormSq (z j))

theorem maximumNormSq_continuous (n M : ℕ) : Continuous (@maximumNormSq n M) := by
  apply nonnegativeMaximum_continuous
  intro j hj
  unfold coordinateNormSq
  fun_prop

theorem gaussianRooms_exp_integrable {n M : ℕ} (hn : 0 < n) (j : Fin M) :
    Integrable (fun z => Real.exp ((n : ℝ) / 4 * coordinateNormSq (z j))) (gaussianRooms n M) := by
  have hf : Integrable (fun x => Real.exp ((n : ℝ) / 4 * coordinateNormSq x))
      (Measure.map (fun z : Fin M → Fin n → ℝ => z j) (gaussianRooms n M)) := by
    rw [gaussianRooms, iidProduct_eval_map]
    exact isotropicGaussian_exp_integrable hn
  exact hf.comp_measurable (measurable_pi_apply j)

theorem gaussianRooms_exp_integral {n M : ℕ} (j : Fin M) :
    (∫ z, Real.exp ((n : ℝ) / 4 * coordinateNormSq (z j)) ∂gaussianRooms n M) =
      ∫ x, Real.exp ((n : ℝ) / 4 * coordinateNormSq x) ∂isotropicGaussian n := by
  have hm : Continuous (fun x : Fin n → ℝ => Real.exp ((n : ℝ) / 4 * coordinateNormSq x)) := by
    unfold coordinateNormSq
    fun_prop
  have h := integral_map (μ := gaussianRooms n M)
    (φ := fun z : Fin M → Fin n → ℝ => z j)
    (f := fun x : Fin n → ℝ => Real.exp ((n : ℝ) / 4 * coordinateNormSq x))
    (measurable_pi_apply j).aemeasurable hm.aestronglyMeasurable
  rw [gaussianRooms, iidProduct_eval_map] at h
  exact h.symm

theorem gaussianRooms_maximum_integrable {n M : ℕ} (hn : 0 < n) :
    Integrable (@maximumNormSq n M) (gaussianRooms n M) := by
  exact (nonnegativeMaximum_integral_bound (gaussianRooms n M) Finset.univ
    (fun j z => coordinateNormSq (z j)) (by positivity : 0 < (n : ℝ) / 4)
    (by norm_num : (0 : ℝ) ≤ 4) (maximumNormSq_continuous n M).aestronglyMeasurable
    (fun j _ => gaussianRooms_exp_integrable hn j)).1

/-- Explicit version of (7.2); independence of rooms is encoded by the product law. -/
theorem gaussianRooms_maximum_expectation {n M : ℕ} (hn : 0 < n)
    (hsize : (M : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ 1) :
    (∫ z, maximumNormSq z ∂gaussianRooms n M) ≤ 8 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := (nonnegativeMaximum_integral_bound (gaussianRooms n M) Finset.univ
    (fun j z => coordinateNormSq (z j)) (by positivity : 0 < (n : ℝ) / 4)
    (by norm_num : (0 : ℝ) ≤ 4) (maximumNormSq_continuous n M).aestronglyMeasurable
    (fun j _ => gaussianRooms_exp_integrable hn j)).2
  have hs : (∑ j : Fin M, ∫ z, Real.exp ((n : ℝ) / 4 * coordinateNormSq (z j))
      ∂gaussianRooms n M) ≤ (M : ℝ) * Real.exp ((n : ℝ) / 2) := by
    calc
      _ ≤ ∑ _j : Fin M, Real.exp ((n : ℝ) / 2) := Finset.sum_le_sum (fun j _ => by
        rw [gaussianRooms_exp_integral]
        exact isotropicGaussian_exp_bound hn)
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ ((n : ℝ) / 4)⁻¹ * Real.exp (-(n : ℝ) / 4 * 4))
  have heq : ((n : ℝ) / 4)⁻¹ * Real.exp (-(n : ℝ) / 4 * 4) *
      ((M : ℝ) * Real.exp ((n : ℝ) / 2)) =
      (4 / n) * ((M : ℝ) * Real.exp (-(n : ℝ) / 2)) := by
    have he : Real.exp (-(n : ℝ) / 4 * 4) * Real.exp ((n : ℝ) / 2) =
        Real.exp (-(n : ℝ) / 2) := by rw [← Real.exp_add]; congr 1; ring
    calc
      _ = (4 / n) * (M : ℝ) *
          (Real.exp (-(n : ℝ) / 4 * 4) * Real.exp ((n : ℝ) / 2)) := by ring
      _ = _ := by rw [he]; ring
  rw [heq] at hm
  have hfour : 4 / (n : ℝ) ≤ 4 := (div_le_iff₀ (by positivity)).2 (by linarith)
  have hlast := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 4 / (n : ℝ))
  change (∫ z, maximumNormSq z ∂gaussianRooms n M) ≤ _ at hb
  simp only [neg_div] at hm hlast
  linarith

theorem gaussianRooms_bad_probability {n M : ℕ} (hn : 0 < n) :
    (gaussianRooms n M).real {z | ∃ j, 4 < coordinateNormSq (z j)} ≤
      (M : ℝ) * Real.exp (-(n : ℝ) / 2) := by
  have htail (j : Fin M) :
      (gaussianRooms n M).real {z | 4 < coordinateNormSq (z j)} ≤ Real.exp (-(n : ℝ) / 2) := by
    have hm : MeasurableSet {x : Fin n → ℝ | 4 < coordinateNormSq x} := by
      apply measurableSet_lt measurable_const
      unfold coordinateNormSq
      fun_prop
    have he : (gaussianRooms n M) {z | 4 < coordinateNormSq (z j)} =
        isotropicGaussian n {x | 4 < coordinateNormSq x} := by
      rw [← iidProduct_eval_map (isotropicGaussian n) j,
        Measure.map_apply (measurable_pi_apply j) hm]
      rfl
    simpa only [measureReal_def, he] using isotropicGaussian_norm_tail hn
  have heq : {z : Fin M → Fin n → ℝ | ∃ j, 4 < coordinateNormSq (z j)} =
      ⋃ j, {z | 4 < coordinateNormSq (z j)} := by ext z; simp
  rw [heq]
  calc
    _ ≤ ∑ j, (gaussianRooms n M).real {z | 4 < coordinateNormSq (z j)} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin M, Real.exp (-(n : ℝ) / 2) := Finset.sum_le_sum (fun j _ => htail j)
    _ = _ := by simp

theorem gaussianRooms_good_probability {n M : ℕ} (hn : 0 < n)
    (hsize : (M : ℝ) * Real.exp (-(n : ℝ) / 2) ≤ 1 / 8) :
    7 / 8 ≤ (gaussianRooms n M).real {z | ∀ j, coordinateNormSq (z j) ≤ 4} := by
  have hm : MeasurableSet {z : Fin M → Fin n → ℝ | ∃ j, 4 < coordinateNormSq (z j)} := by
    simp only [setOf_exists]
    apply MeasurableSet.iUnion
    intro j
    apply measurableSet_lt measurable_const
    unfold coordinateNormSq
    fun_prop
  have heq : {z : Fin M → Fin n → ℝ | ∀ j, coordinateNormSq (z j) ≤ 4} =
      {z | ∃ j, 4 < coordinateNormSq (z j)}ᶜ := by ext z; simp
  rw [heq, measureReal_compl hm]
  have hb := gaussianRooms_bad_probability (M := M) hn
  have hu : (gaussianRooms n M).real univ = 1 := measureReal_univ_eq_one
  rw [hu]
  linarith

end NCBall
