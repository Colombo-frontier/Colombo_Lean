import GradientHessian.NalenOrdinaryPolicy
import GradientHessian.NalenOrdinaryParameters

/-! Source upper bound (ii) for an actual measurable ordinary-only
algorithm, with zero rich calls and explicit dimension-dependent cost. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Nalen Model
open scoped ENNReal

def dimensionAlgorithm (d : ℕ) (T : ℝ) (hq : 1≤ordinaryAveraging d) : Algorithm d :=
  ordinaryAlgorithm d (stepRadius_pos hq).le (stepSize d (ordinaryAveraging d))
    d (ordinaryAveraging d) (ordinaryHorizon T d)

theorem dimensionAlgorithm_guarantees {d : ℕ} {T : ℝ} (hT : 1≤T) (hd : 1≤d) :
    (dimensionAlgorithm d T (ordinary_parameters hT hd).1).Guarantees T (ordinaryQueryCap T d) 0 := by
  obtain ⟨hq,hK,hdq,hTK,hN,hG⟩ := ordinary_parameters hT hd
  exact ordinaryAlgorithm_guarantees hd hq hK hdq (by rfl) hTK

theorem source_ordinary_upper {d : ℕ} {T : ℝ} (hT : 1≤T) (hd : 1≤d) :
    ∃ (A : Algorithm d) (G : ℕ), A.Guarantees T G 0 ∧
      (G:ℝ)≤4096*((d:ℝ)+T*(d:ℝ)^((1:ℝ)/3)) :=
  ⟨dimensionAlgorithm d T (ordinary_parameters hT hd).1,ordinaryQueryCap T d,
    dimensionAlgorithm_guarantees hT hd,(ordinary_parameters hT hd).2.2.2.2.2⟩

theorem source_ordinary_complexity_upper {d : ℕ} {T : ℝ} (hT : 1≤T) (hd : 1≤d) :
    complexity 0 d T≤ENNReal.ofReal (4096*((d:ℝ)+T*(d:ℝ)^((1:ℝ)/3))) := by
  obtain ⟨A,G,hA,hG⟩ := source_ordinary_upper hT hd
  exact (complexity_le A hA).trans
    (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hG)

end GradientHessian.NalenPolicy
