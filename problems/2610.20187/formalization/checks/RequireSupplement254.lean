import Paper254

open MeasureTheory ProbabilityTheory InformationTheory
open scoped NNReal ENNReal

example : Paper254.AnytimeUpperStatement := Paper254.main_anytime_upper

example (a lam : ℝ) (v : ℝ≥0) (ha : |2*lam*a| ≤ 1/4) :
    (∫ x,Real.exp (-lam*x-lam^2*x^2) ∂gaussianReal a v) ≤
      Real.exp (-lam*a-lam^2*a^2) := Paper254.gaussian_integral_mixgap a lam v ha

example (u m : ℝ) (q c : ℝ≥0) (hq : q ≠ 0) (hc : c ≠ 0) :
    klDiv (gaussianReal u q) (gaussianReal m c)=
      ENNReal.ofReal (Paper254.coordinateKL q c (u-m)) := Paper254.gaussian_kl_formula u m q c hq hc

example (y B : ℝ) (hB : 0 < B) :
    ConcaveOn ℝ (Set.Icc (y-B) (y+B))
      (fun z => Real.exp (-(1/B^2)*(1/2*(z-y)^2))) := Paper254.bounded_square_expConcave y B hB

example (B : ℝ) : ConcaveOn ℝ (Set.Icc (-B) B)
    (fun x => Real.exp (-Real.exp (-B)*Paper254.logisticLoss x)) := Paper254.logistic_expConcave B

example {d : ℕ} (W : Set (Paper254.Space d)) (hW : Convex ℝ W)
    (L : Paper254.Space d →L[ℝ] ℝ) (hL : ∀ w ∈ W,0 < L w) :
    Paper254.ExpConcaveOn 1 W (fun w => -Real.log (L w)) := Paper254.portfolio_expConcave W hW L hL

#print axioms Paper254.main_anytime_upper
#print axioms Paper254.gaussian_integral_mixgap
#print axioms Paper254.gaussian_kl_formula
#print axioms Paper254.bounded_square_expConcave
#print axioms Paper254.logistic_expConcave
#print axioms Paper254.portfolio_expConcave
#print axioms Paper254.square_prediction_gradient
#print axioms Paper254.logistic_prediction_gradient
#print axioms Paper254.portfolio_prediction_gradient
