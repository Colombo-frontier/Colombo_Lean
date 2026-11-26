import SampleReuse.SourceMainLower

open SecondOrder MeasureTheory
open scoped ENNReal

namespace SampleReuse
noncomputable section

/-- An operational minimax statement: every common measurable solver has an
actual finite scalar-loss instance with this expected query cost. The order
is `for every algorithm, there exists an instance`. -/
def SourceUniformSolverLower (M : Parameters) (d : ℕ) (ε γ rate : ℝ) : Prop :=
  ∀ (H S Ξ : Type) [MeasurableSpace S] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → PersistentStoppingAlgorithm (Bool × Point d) H (PersistentReply d) (Point d) S),
    MeasurableStoppingFamily P → SeparateOperationallyMeasurable P →
    SolvesSeparateFiniteInstances (M := M) μ P ε γ →
    ∃ I : FiniteScalarInstance M d, ENNReal.ofReal rate ≤ separateFiniteInstanceCost μ P I

/-- The lower half of matching total complexity, for independently chosen
tolerances, with a fully explicit logarithmic loss and dimension envelope. -/
theorem source_lower_logarithmic (M : Parameters) :
    ∃ c Cd ε₀ γ₀ : ℝ, 0<c ∧ 0<Cd ∧ 0<ε₀ ∧ 0<γ₀ ∧ ε₀≤1 ∧ γ₀≤1 ∧
      ∀ ε γ : ℝ, 0<ε → ε≤ε₀ → 0<γ → γ<γ₀ →
      ∃ dstar : ℕ,
        (dstar:ℝ) ≤ Cd*(1+M.gap*(slowBlockSize M ε:ℝ)^(3/4:ℝ)/ε+
          Real.log (2/γ)/γ^4+1/γ^3) ∧
      ∀ d : ℕ, dstar≤d → SourceUniformSolverLower M d ε γ
        (c*(1/ε^3+1/γ^3)/(1+Real.log (1/ε))) := by
  obtain ⟨c,Cd,ε₀,γ₀,hc,hCd,hε₀,hγ₀,hmain⟩ := source_main_lower_separate M
  let k := min (M.gap*slowModelScale M^2) 1/(2*slowLogConstant M)
  have hk : 0<k := sourceLowerEnvelope_log_coefficient_pos M
  refine ⟨c*k,Cd,min ε₀ 1,min γ₀ 1,mul_pos hc hk,hCd,
    lt_min hε₀ (by norm_num),lt_min hγ₀ (by norm_num),min_le_right _ _,min_le_right _ _,?_⟩
  intro ε γ hε he hγ hg
  obtain ⟨dstar,hdstar,hmain⟩ := hmain ε γ hε (he.trans (min_le_left _ _)) hγ
    (hg.trans_le (min_le_left _ _))
  refine ⟨dstar,hdstar,?_⟩
  intro d hd H S Ξ _ _ μ _ P hmeas hop hsolve
  obtain ⟨I,hI⟩ := hmain d hd H S Ξ μ P hmeas hop hsolve
  refine ⟨I,?_⟩
  apply (ENNReal.ofReal_le_ofReal (show c*k*(1/ε^3+1/γ^3)/(1+Real.log (1/ε)) ≤
    c*sourceLowerEnvelope M ε γ from ?_)).trans hI
  have hl := mul_le_mul_of_nonneg_left
    (sourceLowerEnvelope_log_rate M hε (he.trans (min_le_right _ _)) hγ) hc.le
  convert hl using 1
  dsimp [k]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end SampleReuse
