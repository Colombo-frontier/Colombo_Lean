import SecondOrder.OracleProgramBudgetLaw

open MeasureTheory

namespace SecondOrder
noncomputable section

variable {Ω Q Y O : Type}

def drawsPrepend : (n : ℕ) → Ω → Draws Ω n → Draws Ω (n+1)
  | 0, z, _ => (PUnit.unit,z)
  | n+1, z, w => (drawsPrepend n z w.1,w.2)

theorem drawsPrepend_measurePreserving [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun w : Ω × Draws Ω n => drawsPrepend n w.1 w.2)
      (μ.prod (drawsLaw μ n)) (drawsLaw μ (n+1)) := by
  induction n with
  | zero =>
    convert Measure.measurePreserving_swap (μ := μ) (ν := drawsLaw μ 0) using 1
  | succ n ih =>
    exact (ih.prod (MeasurePreserving.id μ)).comp
      ((measurePreserving_prodAssoc μ (drawsLaw μ n) μ).symm MeasurableEquiv.prodAssoc)

/-- Expose the first fresh sample of a sequential execution. -/
theorem OracleProgram.runDraws_prepend (q₀ : Q) (reply : Q → Ω → Y)
    (p : OracleProgram Q Y O) (n : ℕ) (z : Ω) (w : Draws Ω n) :
    runDraws q₀ reply p (n+1) (drawsPrepend n z w)=
      runDraws q₀ reply (advance p (reply (query q₀ p) z)) n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun pp : OracleProgram Q Y O => advance pp (reply (query q₀ pp) w.2)) (ih w.1)

end
end SecondOrder
