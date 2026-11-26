import ExactHistoryCost254

noncomputable section
namespace Paper254

/-- The exact oracle may return any feasible minimizer. Positive definite
metrics make this result unique, so it equals the semantic projection. -/
theorem exact_metric_minimizer_unique {d : ℕ} {D : ℝ} (W : Domain d D)
    (A : Precision d) (hA : A.PosDef) (a : Coordinates d) (u : W.carrier)
    (hmin : ∀ v : W.carrier,matrixQuadratic A (u.val-WithLp.toLp 2 a)≤
      matrixQuadratic A (v.val-WithLp.toLp 2 a)) :
    u=metricProject W (precisionFactor hA) (WithLp.toLp 2 a) := by
  let Q:=precisionFactor hA
  let m:=metricProject W Q (WithLp.toLp 2 a)
  have hgap : ‖Q (u.val-WithLp.toLp 2 a)‖^2≤‖Q (m.val-WithLp.toLp 2 a)‖^2+0 := by
    simpa only [Q,precisionFactor_norm,add_zero] using hmin m
  have hd:=metricProject_objective_gap W Q (WithLp.toLp 2 a) u 0 hgap
  have hn : ‖Q (u.val-m.val)‖=0 := by
    change ‖Q (u.val-m.val)‖^2≤0 at hd
    nlinarith [norm_nonneg (Q (u.val-m.val))]
  have hz : Q (u.val-m.val)=0 := norm_eq_zero.mp hn
  have he : u.val-m.val=0 := Q.injective (hz.trans (map_zero Q).symm)
  exact Subtype.ext (sub_eq_zero.mp he)

structure ExactProjectionMinimizerPrimitive {d : ℕ} {D : ℝ} (W : Domain d D) where
  run : (A : Precision d)→A.PosDef→Coordinates d→W.carrier×ℕ
  minimizes : ∀ A hA a (v : W.carrier),matrixQuadratic A ((run A hA a).1.val-WithLp.toLp 2 a)≤
    matrixQuadratic A (v.val-WithLp.toLp 2 a)
  bound : ℕ
  cost : ∀ A hA a,(run A hA a).2≤bound

def ExactProjectionMinimizerPrimitive.toExact {d : ℕ} {D : ℝ} {W : Domain d D}
    (oracle : ExactProjectionMinimizerPrimitive W) : ExactProjectionPrimitive W where
  run A hA a:=((oracle.run A hA a).1.val,(oracle.run A hA a).2)
  value A hA a:=congrArg (fun u : W.carrier=>(u.val : Coordinates d))
    (exact_metric_minimizer_unique W A hA a (oracle.run A hA a).1 (oracle.minimizes A hA a))
  bound:=oracle.bound
  cost:=oracle.cost

end Paper254
#print axioms Paper254.exact_metric_minimizer_unique
