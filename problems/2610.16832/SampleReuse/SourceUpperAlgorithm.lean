import SampleReuse.CurvatureFirstCapSuccess
import SampleReuse.CurvatureFirstCostCalibration
import SampleReuse.OracleProgramStopping
import SampleReuse.OptimizerOutputFallback

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def sourceGradientQueryCap (P : Parameters) (d : ℕ) (ε γ : ℝ) : ℕ :=
  ⌈48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*sourceGradientBudget P ε γ⌉₊

def sourceHessianQueryCap (P : Parameters) (d : ℕ) (ε γ : ℝ) : ℕ :=
  ⌈48*sourceUpperConstant*(sourceLogScale d (sourceIterationCap P ε γ))^4*sourceHessianBudget P ε γ⌉₊

def sourceGradientRootBatch (P : Parameters) (d : ℕ) (ε γ : ℝ) : ℕ :=
  batchSize (sourceConfidenceScale d (sourceIterationCap P ε γ) ε) (P.gradientNoise^2)

def sourceHessianRootBatch (P : Parameters) (d : ℕ) (ε γ : ℝ) : ℕ :=
  batchSize (sourceConfidenceScale d (sourceIterationCap P ε γ) γ) (P.hessianNoise^2)

theorem sourceGradientRootBatch_pos (P : Parameters) (d : ℕ) (ε γ : ℝ) :
    0<sourceGradientRootBatch P d ε γ := batchSize_pos _ _

theorem sourceHessianRootBatch_pos (P : Parameters) (d : ℕ) (ε γ : ℝ) :
    0<sourceHessianRootBatch P d ε γ := batchSize_pos _ _

abbrev sourceHandleCount (P : Parameters) (d : ℕ) (ε γ : ℝ) :=
  (sourceIterationCap P ε γ+1)*sourceGradientRootBatch P d ε γ+
    (sourceIterationCap P ε γ+1)*sourceHessianRootBatch P d ε γ

def sourceUpperDefaultQuery (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d) :
    PersistentQuery (sourceHandleCount P d ε γ) d :=
  (true,⟨0,by have hg := sourceGradientRootBatch_pos P d ε γ; unfold sourceHandleCount; positivity⟩,x₀)

/-- This program depends only on the problem parameters, initial point and
private signs. It cannot inspect the population function, loss or sample tape. -/
def sourceUpperProgram (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) :
    OracleProgram (PersistentQuery (sourceHandleCount P d ε γ) d) (PersistentReply d) (Option (Point d)) :=
  cappedCurvatureFirstProgram (sourceGradientRootBatch_pos P d ε γ) (sourceHessianRootBatch_pos P d ε γ)
    P ε γ (sourceConfidenceScale d (sourceIterationCap P ε γ) ε)
    (sourceConfidenceScale d (sourceIterationCap P ε γ) γ) (extendFiniteSigns bits)
    (sourceIterationCap P ε γ) 0 (optimizerInitial x₀)
    (sourceGradientQueryCap P d ε γ) (sourceHessianQueryCap P d ε γ)

theorem sourceUpperProgram_usesAtMost (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) :
    OracleProgram.UsesAtMost (sourceGradientQueryCap P d ε γ+sourceHessianQueryCap P d ε γ)
      (sourceUpperProgram P d ε γ x₀ bits) :=
  cappedCurvatureFirstProgram_usesAtMost _ _ _ _ _ _ _ _ _ _ _ _ _

theorem sourceUpperProgram_measurableFamily (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d) :
    OracleProgram.MeasurableFamily (sourceUpperDefaultQuery P d ε γ x₀) none
      (sourceUpperProgram P d ε γ x₀) := by
  exact (cappedCurvatureFirstProgram_measurableFamily (sourceGradientRootBatch_pos P d ε γ)
    (sourceHessianRootBatch_pos P d ε γ) P ε γ (sourceConfidenceScale d (sourceIterationCap P ε γ) ε)
    (sourceConfidenceScale d (sourceIterationCap P ε γ) γ) (sourceUpperDefaultQuery P d ε γ x₀)
    (sourceIterationCap P ε γ) 0 (sourceGradientQueryCap P d ε γ) (sourceHessianQueryCap P d ε γ)).comp
      (fun bits => (extendFiniteSigns bits,optimizerInitial x₀))
      ((extendFiniteSigns_measurable _).prodMk measurable_const)

def sourceUpperStop {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) : ℕ :=
  OracleProgramStopping.firstStop (sourceUpperDefaultQuery P d ε γ x₀)
    (fun q tape => persistentReply F tape q) (fun _ => tape) (sourceUpperProgram P d ε γ x₀ bits)
    (sourceGradientQueryCap P d ε γ+sourceHessianQueryCap P d ε γ)
    (sourceUpperProgram_usesAtMost P d ε γ x₀ bits)

/-- Return a point at actual termination. A budget abort or exhausted outer
horizon returns the initial point; no oracle query is needed for this fallback. -/
def sourceUpperOutput {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) : Point d :=
  (OracleProgram.output none (OracleProgram.run (sourceUpperDefaultQuery P d ε γ x₀)
    (fun q tape => persistentReply F tape q) (fun _ => tape) (sourceUpperProgram P d ε γ x₀ bits)
    (sourceUpperStop P d ε γ x₀ F tape bits))).getD x₀

def sourceUpperQueryCounts {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) : ℕ×ℕ :=
  OracleProgramStopping.literalPrefixCounts Prod.fst (sourceUpperDefaultQuery P d ε γ x₀)
    (fun q tape => persistentReply F tape q) (fun _ => tape) (sourceUpperProgram P d ε γ x₀ bits)
    (sourceUpperStop P d ε γ x₀ F tape bits)

theorem sourceUpperStop_le {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) :
    sourceUpperStop P d ε γ x₀ F tape bits≤sourceGradientQueryCap P d ε γ+sourceHessianQueryCap P d ε γ :=
  OracleProgramStopping.firstStop_le _ _ _ _ _ _

theorem sourceUpperQueryCounts_le {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) :
    (sourceUpperQueryCounts P d ε γ x₀ F tape bits).1≤sourceGradientQueryCap P d ε γ ∧
      (sourceUpperQueryCounts P d ε γ x₀ F tape bits).2≤sourceHessianQueryCap P d ε γ :=
  OracleProgramStopping.capped_literal_counts _ _ _ _ _ _ _ _

theorem sourceUpperQueryCounts_total {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) :
    (sourceUpperQueryCounts P d ε γ x₀ F tape bits).1+(sourceUpperQueryCounts P d ε γ x₀ F tape bits).2 =
      sourceUpperStop P d ε γ x₀ F tape bits :=
  OracleProgramStopping.literalPrefixCounts_total _ _ _ _ _ _

theorem sourceUpperOutput_eq_padded {Ω : Type} (P : Parameters) (d : ℕ) (ε γ : ℝ) (x₀ : Point d)
    (F : Ω→Point d→ℝ) (tape : SampleTape (sourceHandleCount P d ε γ) Ω)
    (bits : Fin (sourceIterationCap P ε γ)→Bool) :
    sourceUpperOutput P d ε γ x₀ F tape bits =
      (cappedCurvatureFirstOutput (sourceGradientRootBatch_pos P d ε γ) (sourceHessianRootBatch_pos P d ε γ)
        P ε γ (sourceConfidenceScale d (sourceIterationCap P ε γ) ε)
        (sourceConfidenceScale d (sourceIterationCap P ε γ) γ) F (sourceUpperDefaultQuery P d ε γ x₀) x₀
        (sourceGradientQueryCap P d ε γ) (sourceHessianQueryCap P d ε γ) tape bits).getD x₀ := by
  unfold sourceUpperOutput sourceUpperStop
  rw [OracleProgramStopping.firstStop_output_eq]
  unfold cappedCurvatureFirstOutput
  rw [cappedCurvatureFirstAlgorithm_output]
  rfl

end
end SampleReuse
