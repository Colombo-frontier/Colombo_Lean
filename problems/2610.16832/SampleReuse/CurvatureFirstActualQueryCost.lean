import SampleReuse.CurvatureFirstGradientCostCoupling
import SampleReuse.CurvatureFirstHessianCostCoupling

open SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

theorem actual_hessian_queries_le_cost {Ω : Type*} {d T Bg BH M : ℕ}
    (hBg : 0<Bg) (hBH : 0<BH) (P : Parameters) (ε γ scaleG scaleH : ℝ)
    (f : Point d → ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (x₀ : Point d) (w : Fin M→Bool)
    (depth : ℕ) (hd : M<2^depth) (hcap : BH=batchSize scaleH (P.hessianNoise^2))
    (hv : curvatureFirstFiniteValid hBg hBH P ε γ scaleG scaleH f F tape M 0 (optimizerInitial x₀) w) :
    (curvatureFirstDerivativeCounts hBg hBH P ε γ scaleG scaleH F tape
      (extendFiniteSigns w) M 0 (optimizerInitial x₀)).2 ≤
      stoppedHessianCost hBg hBH P ε γ scaleG scaleH f F tape x₀ depth w := by
  have he := curvatureStoppedQueryCounts_eq_actual_of_valid hBg hBH P ε γ scaleG scaleH f F tape
    (extendFiniteSigns w) M 0 (optimizerInitial x₀) w (by intro i; simp only [Nat.zero_add,extendFiniteSigns,dif_pos i.isLt]) hv
  rw [← he]
  exact curvatureStoppedQueryCounts_hessian_le_tree hBg hBH P ε γ scaleG scaleH f F tape x₀ w depth hd hcap

end
end SampleReuse
