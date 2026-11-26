import SampleReuse.OracleBatchConfidence

/-! Root packets use one call per sample. The program and its confidence
bound concern actual derivatives of the common scalar loss on an iid tape. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def gradientRootProgram {H d b : ℕ} (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) (Point d) :=
  OracleProgram.batch b (fun i => (true, handles i, x))
    (fun ys => (b : ℝ)⁻¹ • ∑ i : Fin b, (ys i).1)

def hessianRootProgram {H d b : ℕ} (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) (Point d →L[ℝ] Point d) :=
  OracleProgram.batch b (fun i => (false, handles i, x))
    (fun ys => (b : ℝ)⁻¹ • ∑ i : Fin b, (ys i).2)

theorem gradientRootProgram_exact_calls {H d b : ℕ}
    (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram.UsesExactly b (gradientRootProgram handles x) :=
  OracleProgram.batch_usesExactly _ _ _

theorem hessianRootProgram_exact_calls {H d b : ℕ}
    (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram.UsesExactly b (hessianRootProgram handles x) :=
  OracleProgram.batch_usesExactly _ _ _

theorem gradientRootProgram_run {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (gradientRootProgram handles x) b =
        .done (batchMeanTape (fun z => gradient (F z) x) handles tape) := by
  rw [gradientRootProgram, persistentBatch_run]
  rfl

theorem hessianRootProgram_run {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x : Point d) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (hessianRootProgram handles x) b =
        .done (batchMeanTape (fun z => hessian (F z) x) handles tape) := by
  rw [hessianRootProgram, persistentBatch_run]
  rfl

theorem gradientRootProgram_compiled_output {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x : Point d) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (gradientRootProgram handles x)
    alg.output b (persistentRun alg.toQueryPolicy F tape b) =
      batchMeanTape (fun z => gradient (F z) x) handles tape := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ b = _
  rw [OracleProgram.algorithm_output, gradientRootProgram_run]
  rfl

theorem hessianRootProgram_compiled_output {Ω : Type*} {H d b : ℕ}
    (q₀ : PersistentQuery H d) (F : Ω → Point d → ℝ) (tape : SampleTape H Ω)
    (handles : Fin b → Fin H) (x : Point d) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (hessianRootProgram handles x)
    alg.output b (persistentRun alg.toQueryPolicy F tape b) =
      batchMeanTape (fun z => hessian (F z) x) handles tape := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ b = _
  rw [OracleProgram.algorithm_output, hessianRootProgram_run]
  rfl

theorem gradientRootProgram_measurableFamily {H d b : ℕ}
    (q₀ : PersistentQuery H d) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun w : (Fin b → Fin H) × Point d => gradientRootProgram w.1 w.2) := by
  apply OracleProgram.batch_measurable
  · intro i
    exact measurable_const.prodMk
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  · fun_prop

theorem hessianRootProgram_measurableFamily {H d b : ℕ}
    (q₀ : PersistentQuery H d) :
    OracleProgram.MeasurableFamily q₀ 0
      (fun w : (Fin b → Fin H) × Point d => hessianRootProgram w.1 w.2) := by
  apply OracleProgram.batch_measurable
  · intro i
    exact measurable_const.prodMk
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
  · fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {H d b : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Parameters}
    {f : Point d → ℝ} {F : Ω → Point d → ℝ} {x₀ : Point d}

theorem Admissible.hessian_root_confidence (h : Admissible μ P f F x₀)
    (x : Point d) (handles : Fin b → Fin H) (hinj : Function.Injective handles)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 8 * (matrixMomentOrder (d + 1) δ : ℝ) * P.hessianNoise^2 ≤ (b : ℝ) * η^2) :
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖batchMeanTape (fun z => hessian (F z) x) handles tape - hessian f x‖} ≤ δ := by
  let A := fun z => hessian (F z) x - hessian f x
  have hA : Measurable A :=
    (h.hessian_measurable.comp (measurable_id.prodMk measurable_const)).sub measurable_const
  have hAi : Integrable A μ := (h.hessian_integrable x).sub (integrable_const _)
  have hX : ∀ i : Fin b, Measurable (fun tape : SampleTape H Ω => A (tape (handles i))) :=
    fun i => hA.comp (measurable_pi_apply (handles i))
  have hbound : ∀ i : Fin b, ∀ᵐ tape ∂sampleTapeLaw H μ, ‖A (tape (handles i))‖ ≤ P.hessianNoise := by
    intro i
    have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)),
        ‖A z‖ ≤ P.hessianNoise := by
      rw [sampleTapeLaw_marginal]
      exact h.noise_bound.mono (fun _ hz => (hz x).2)
    exact ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  have hzero : ∀ i : Fin b,
      (∫ tape : SampleTape H Ω, A (tape (handles i)) ∂sampleTapeLaw H μ) = 0 := by
    intro i
    rw [sampleTape_integral μ A hAi (handles i)]
    simp [A, integral_sub (h.hessian_integrable x) (integrable_const (hessian f x)),
      h.hessian_unbiased x]
  have hsym : ∀ i : Fin b, ∀ᵐ tape ∂sampleTapeLaw H μ,
      (A (tape (handles i))).toLinearMap.IsSymmetric := by
    intro i
    have hmapped : ∀ᵐ z ∂(sampleTapeLaw H μ).map (fun tape => tape (handles i)),
        (A z).toLinearMap.IsSymmetric := by
      rw [sampleTapeLaw_marginal]
      filter_upwards [h.sample_regularity] with z hz
      exact (hessian_isSymmetric hz.1 x).sub (hessian_isSymmetric h.population_smooth x)
    exact ae_of_ae_map (measurable_pi_apply (handles i)).aemeasurable hmapped
  have hsize' : 8 * (matrixMomentOrder (Module.finrank ℝ (Point d) + 1) δ : ℝ) *
      P.hessianNoise^2 ≤ (b : ℝ) * η^2 := by
    simpa only [Point, finrank_euclideanSpace_fin] using hsize
  have hc := independent_operator_average_confidence
    (fun i (tape : SampleTape H Ω) => A (tape (handles i))) hX P.hessianNoise_pos.le
    hη hδ hb hbound (sampleTapeLaw_sample_independent μ handles hinj A hA) hzero hsym hsize'
  have he (tape : SampleTape H Ω) :
      batchMeanTape (fun z => hessian (F z) x) handles tape - hessian f x =
        batchMeanTape A handles tape := batchMeanTape_centered _ _ _ _ hb
  simp_rw [he]
  exact hc

theorem Admissible.hessianRootProgram_confidence (h : Admissible μ P f F x₀)
    (q₀ : PersistentQuery H d) (x : Point d) (handles : Fin b → Fin H)
    (hinj : Function.Injective handles) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (hb : 0 < b)
    (hsize : 8 * (matrixMomentOrder (d + 1) δ : ℝ) * P.hessianNoise^2 ≤ (b : ℝ) * η^2) :
    let alg := OracleProgram.algorithm q₀ (0, 0) 0 (hessianRootProgram handles x)
    (sampleTapeLaw H μ).real {tape |
      η ≤ ‖alg.output b (persistentRun alg.toQueryPolicy F tape b) - hessian f x‖} ≤ δ := by
  dsimp only
  simp_rw [hessianRootProgram_compiled_output]
  exact h.hessian_root_confidence x handles hinj hη hδ hb hsize

end
end SampleReuse
