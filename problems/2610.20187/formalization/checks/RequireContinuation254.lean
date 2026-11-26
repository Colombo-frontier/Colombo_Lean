import Paper254

open Paper254 MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators NNReal

example : AnytimeClippedStatement := main_anytime_clipped

example {d : ℕ} (P : PrecisionGaussian d) : IsGaussian P.gaussianMeasure := P.measure_isGaussian

example {d : ℕ} (P : PrecisionGaussian d) (u : Coordinates d) (q : ℝ≥0) (hq : q ≠ 0) :
    klDiv (Measure.pi (fun i => gaussianReal (u i) q)) P.gaussianMeasure=
      ENNReal.ofReal (P.potential q u) := P.standard_gaussian_kl u q hq

example {d : ℕ} {S : Set (Space d)} (hS : Convex ℝ S) (ho : IsOpen S)
    (f : Space d → ℝ) (F : Space d → Space d →L[ℝ] ℝ)
    (H : Space d → Space d →L[ℝ] Space d →L[ℝ] ℝ) (η : ℝ) (hη : 0 < η)
    (hf : ∀ x ∈ S,HasFDerivAt f (F x) x) (hF : ∀ x ∈ S,HasFDerivAt F (H x) x) :
    ExpConcaveOn η S f ↔ ∀ x ∈ S,∀ v,η*(F x v)^2 ≤ H x v v :=
  expConcave_iff_hessian hS ho f F H η hη hf hF

example (x : ℚ) (p : ℕ) (hx : |(x:ℝ)| ≤ 1/2) :
    |Real.exp (x:ℝ)-(rationalExp x p:ℝ)| ≤ ((2:ℝ)^p)⁻¹/4 := rationalExp_error x p hx

example {n : ℕ} (p : ℕ) (w z : Fin n → ℚ)
    (hw : ∀ j,0 ≤ w j) (hsum : ∑ j,w j=1) (hz : ∀ j,|(z j:ℝ)| ≤ 1/2) :
    let v := (rationalPrior w hw hsum).exponential (-1) (fun j => (z j:ℝ))
    (∑ j,rationalSoftmax p w z j)=1 ∧ ∀ j,
      v.weight j/(1+3*n*((2:ℝ)^p)⁻¹) ≤ (rationalSoftmax p w z j:ℝ) ∧
      ((2:ℝ)^p)⁻¹/(1+3*n*((2:ℝ)^p)⁻¹) ≤ (rationalSoftmax p w z j:ℝ) :=
  rationalSoftmax_spec p w z hw hsum hz

#print axioms Paper254.main_anytime_clipped
#print axioms Paper254.expConcave_iff_hessian
#print axioms Paper254.expConcave_of_uniform_hessian
#print axioms Paper254.PrecisionGaussian.standard_gaussian_kl
#print axioms Paper254.certifiedSqrt_error
#print axioms Paper254.certifiedSqrt_encoding_bound
#print axioms Paper254.rationalExp_error
#print axioms Paper254.rationalSoftmax_spec
#print axioms Paper254.rationalUpperMass_encoding_bound
#print axioms Paper254.rational_covariance_interval
#print axioms Paper254.PrecisionGaussian.measure_isGaussian
#print axioms Paper254.gaussian_affine_quadratic_integral
#eval rationalExp (1/2) 4
#eval rationalSoftmax 4 (fun _ : Fin 2 => 1/2) (fun j => if j.val=0 then 1/2 else -1/2) 0
