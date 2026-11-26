import SampleReuse.OraclePersistent
import SecondOrder.OracleProgram
import SecondOrder.SampledResponseKernel
import SecondOrder.MeasurableOracleProgram

/-! Literal two-call programs for a same-handle derivative difference, and
their fresh-sample kernels. Kernel equalities below concern fixed endpoints;
adaptive freshness still requires the execution/history bridge. -/

open MeasureTheory ProbabilityTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def gradientChordProgram {H d : ℕ} (r : Fin H) (x y : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) (Point d) :=
  .request (true, r, x) (fun gx =>
    .request (true, r, y) (fun gy => .done (gx.1 - gy.1)))

def hessianChordProgram {H d : ℕ} (r : Fin H) (x y : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) (Point d →L[ℝ] Point d) :=
  .request (false, r, x) (fun hx =>
    .request (false, r, y) (fun hy => .done (hx.2 - hy.2)))

theorem gradientChordProgram_two_calls {H d : ℕ} (r : Fin H) (x y : Point d) :
    OracleProgram.UsesAtMost 2 (gradientChordProgram r x y) ∧
      ¬ OracleProgram.UsesAtMost 1 (gradientChordProgram r x y) := by
  simp [gradientChordProgram, OracleProgram.UsesAtMost]

theorem hessianChordProgram_two_calls {H d : ℕ} (r : Fin H) (x y : Point d) :
    OracleProgram.UsesAtMost 2 (hessianChordProgram r x y) ∧
      ¬ OracleProgram.UsesAtMost 1 (hessianChordProgram r x y) := by
  simp [hessianChordProgram, OracleProgram.UsesAtMost]

theorem gradientChordProgram_run {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x y : Point d) :
    OracleProgram.run (true, r, x) (fun q tape => persistentReply F tape q) (fun _ => tape)
      (gradientChordProgram r x y) 2 =
        .done (gradient (F (tape r)) x - gradient (F (tape r)) y) := rfl

theorem hessianChordProgram_run {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x y : Point d) :
    OracleProgram.run (false, r, x) (fun q tape => persistentReply F tape q) (fun _ => tape)
      (hessianChordProgram r x y) 2 =
        .done (hessian (F (tape r)) x - hessian (F (tape r)) y) := rfl

theorem persistentRun_eq_queryPolicyRun {Ω S : Type*} {H d : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (n : ℕ) :
    persistentRun P F tape n = queryPolicyRun P (fun q tape => persistentReply F tape q)
      (fun _ => tape) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [persistentRun, queryPolicyRun, ih]

theorem gradientChordProgram_compiled_output {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x y : Point d) :
    let P := OracleProgram.algorithm (true, r, x) (0, 0) 0 (gradientChordProgram r x y)
    P.output 2 (persistentRun P.toQueryPolicy F tape 2) =
      gradient (F (tape r)) x - gradient (F (tape r)) y := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ 2 = _
  rw [OracleProgram.algorithm_output, gradientChordProgram_run]
  rfl

theorem hessianChordProgram_compiled_output {Ω : Type*} {H d : ℕ}
    (F : Ω → Point d → ℝ) (tape : SampleTape H Ω) (r : Fin H) (x y : Point d) :
    let P := OracleProgram.algorithm (false, r, x) (0, 0) 0 (hessianChordProgram r x y)
    P.output 2 (persistentRun P.toQueryPolicy F tape 2) =
      hessian (F (tape r)) x - hessian (F (tape r)) y := by
  dsimp only
  rw [persistentRun_eq_queryPolicyRun]
  change oracleAlgorithmOutput _ _ _ 2 = _
  rw [OracleProgram.algorithm_output, hessianChordProgram_run]
  rfl

def gradientChordSample {Ω : Type*} {d : ℕ} (F : Ω → Point d → ℝ)
    (xy : Point d × Point d) (z : Ω) : Point d := gradient (F z) xy.1 - gradient (F z) xy.2

def hessianChordSample {Ω : Type*} {d : ℕ} (F : Ω → Point d → ℝ)
    (xy : Point d × Point d) (z : Ω) : Point d →L[ℝ] Point d :=
  hessian (F z) xy.1 - hessian (F z) xy.2

theorem gradientChordSample_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2)) :
    Measurable (fun w : (Point d × Point d) × Ω => gradientChordSample F w.1 w.2) :=
  (hg.comp (measurable_snd.prodMk measurable_fst.fst)).sub
    (hg.comp (measurable_snd.prodMk measurable_fst.snd))

theorem hessianChordSample_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (F : Ω → Point d → ℝ)
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2)) :
    Measurable (fun w : (Point d × Point d) × Ω => hessianChordSample F w.1 w.2) :=
  (hH.comp (measurable_snd.prodMk measurable_fst.fst)).sub
    (hH.comp (measurable_snd.prodMk measurable_fst.snd))

def gradientChordKernel {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2)) :
    Kernel (Point d × Point d) (Point d) :=
  sampledResponseKernel μ (gradientChordSample F) (gradientChordSample_measurable F hg)

def hessianChordKernel {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Point d → ℝ)
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2)) :
    Kernel (Point d × Point d) (Point d →L[ℝ] Point d) :=
  sampledResponseKernel μ (hessianChordSample F) (hessianChordSample_measurable F hH)

instance gradientChordKernel_markov {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2)) :
    IsMarkovKernel (gradientChordKernel μ F hg) := by
  unfold gradientChordKernel
  infer_instance

instance hessianChordKernel_markov {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Point d → ℝ)
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2)) :
    IsMarkovKernel (hessianChordKernel μ F hH) := by
  unfold hessianChordKernel
  infer_instance

theorem gradientChordKernel_tape_law {Ω : Type*} [MeasurableSpace Ω] {H d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Point d → ℝ)
    (hg : Measurable (fun w : Ω × Point d => gradient (F w.1) w.2))
    (r : Fin H) (xy : Point d × Point d) :
    (sampleTapeLaw H μ).map (fun tape => gradientChordSample F xy (tape r)) =
      gradientChordKernel μ F hg xy := by
  have hm : Measurable (gradientChordSample F xy) := (gradientChordSample_measurable F hg).comp
    (measurable_const.prodMk (measurable_id : Measurable (fun z : Ω => z)))
  calc
    _ = ((sampleTapeLaw H μ).map (fun tape => tape r)).map (gradientChordSample F xy) := by
      exact (Measure.map_map hm (measurable_pi_apply r)).symm
    _ = μ.map (gradientChordSample F xy) := by rw [sampleTapeLaw_marginal]
    _ = _ := rfl

theorem hessianChordKernel_tape_law {Ω : Type*} [MeasurableSpace Ω] {H d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → Point d → ℝ)
    (hH : Measurable (fun w : Ω × Point d => hessian (F w.1) w.2))
    (r : Fin H) (xy : Point d × Point d) :
    (sampleTapeLaw H μ).map (fun tape => hessianChordSample F xy (tape r)) =
      hessianChordKernel μ F hH xy := by
  have hm : Measurable (hessianChordSample F xy) :=
    (hH.comp (measurable_id.prodMk (measurable_const (a := xy.1)))).sub
      (hH.comp (measurable_id.prodMk (measurable_const (a := xy.2))))
  calc
    _ = ((sampleTapeLaw H μ).map (fun tape => tape r)).map (hessianChordSample F xy) := by
      exact (Measure.map_map hm (measurable_pi_apply r)).symm
    _ = μ.map (hessianChordSample F xy) := by rw [sampleTapeLaw_marginal]
    _ = _ := rfl

theorem gradientChordProgram_measurable {H d : ℕ} (q₀ : PersistentQuery H d) :
    OracleProgram.MeasurableFamily q₀ 0 (fun w : Fin H × (Point d × Point d) =>
      gradientChordProgram w.1 w.2.1 w.2.2) := by
  unfold gradientChordProgram
  refine OracleProgram.measurableFamily_request q₀ 0 _ _ ?_ ?_
  · exact measurable_const.prodMk (measurable_fst.prodMk measurable_snd.fst)
  · refine OracleProgram.measurableFamily_request q₀ 0 _ _ ?_ ?_
    · exact measurable_const.prodMk (measurable_fst.fst.prodMk measurable_fst.snd.snd)
    · exact OracleProgram.measurableFamily_done q₀ 0 _
        (measurable_fst.snd.fst.sub measurable_snd.fst)

theorem hessianChordProgram_measurable {H d : ℕ} (q₀ : PersistentQuery H d) :
    OracleProgram.MeasurableFamily q₀ 0 (fun w : Fin H × (Point d × Point d) =>
      hessianChordProgram w.1 w.2.1 w.2.2) := by
  unfold hessianChordProgram
  refine OracleProgram.measurableFamily_request q₀ 0 _ _ ?_ ?_
  · exact measurable_const.prodMk (measurable_fst.prodMk measurable_snd.fst)
  · refine OracleProgram.measurableFamily_request q₀ 0 _ _ ?_ ?_
    · exact measurable_const.prodMk (measurable_fst.fst.prodMk measurable_fst.snd.snd)
    · exact OracleProgram.measurableFamily_done q₀ 0 _
        (measurable_fst.snd.snd.sub measurable_snd.snd)

theorem gradientChordProgram_compiled_measurable {H d : ℕ} (q₀ : PersistentQuery H d) :
    MeasurableOracleAlgorithmFamily (fun w : Fin H × (Point d × Point d) =>
      OracleProgram.algorithm q₀ (0, 0) 0 (gradientChordProgram w.1 w.2.1 w.2.2)) :=
  OracleProgram.algorithm_measurable (0, 0) (gradientChordProgram_measurable q₀)

theorem hessianChordProgram_compiled_measurable {H d : ℕ} (q₀ : PersistentQuery H d) :
    MeasurableOracleAlgorithmFamily (fun w : Fin H × (Point d × Point d) =>
      OracleProgram.algorithm q₀ (0, 0) 0 (hessianChordProgram w.1 w.2.1 w.2.2)) :=
  OracleProgram.algorithm_measurable (0, 0) (hessianChordProgram_measurable q₀)

end
end SampleReuse
