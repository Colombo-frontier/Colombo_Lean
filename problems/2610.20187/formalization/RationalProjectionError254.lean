import RationalFloorError254

noncomputable section
namespace Paper254

/-- The oracle is evaluated at the actual rounded metric and centre. Its
input perturbations and objective tolerance imply an error to the exact
Gaussian projected mean. -/
theorem rationalHistoryStep_mean_error {d : ℕ} {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (q : ℝ) (hq : 0<q)
    (hmetric : (realMatrix (rationalProjectionMetric cfg S lam g)).PosDef)
    (M R e l : ℝ) (hM : 0≤M) (hR : 0≤R) (he : 0≤e) (hl : 0<l)
    (hB : ∀ i j,|realMatrix (rationalProjectionMetric cfg S lam g) i j|≤M)
    (hAB : ∀ i j,|((S.gaussian hS).historyUpdate W (lam:ℝ) q hlam hq
      (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))).precision i j-
      realMatrix (rationalProjectionMetric cfg S lam g) i j|≤e)
    (hA : ∀ x : Space d,l*‖x‖^2≤matrixQuadratic
      ((S.gaussian hS).historyUpdate W (lam:ℝ) q hlam hq (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))).precision x)
    (hcenter : ∀ v : W.carrier,∀ i,
      |v.val i-(rationalTiltMean S lam g w i:ℝ)|+((2:ℝ)^cfg.storagePrecision)⁻¹≤R) :
    ∀ i,|(rationalHistoryStep oracle cfg S lam g w).mean i-
      ((S.gaussian hS).historyUpdate W (lam:ℝ) q hlam hq (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))).mean i|≤
      Real.sqrt ((((2:ℝ)^cfg.projectionPrecision)⁻¹+
        2*(d:ℝ)^2*(e*R^2+2*M*R*((2:ℝ)^cfg.storagePrecision)⁻¹))/l) := by
  let F := ((S.gaussian hS).tilt (lam:ℝ) (2*(lam:ℝ)) hlam (by positivity)
    (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))).floorCovariance q hq
  let a : Space d := WithLp.toLp 2 F.mean
  let b : Space d := WithLp.toLp 2 (fun j=>
    (rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w) j:ℝ))
  let B := realMatrix (rationalProjectionMetric cfg S lam g)
  let m : W.carrier := ⟨WithLp.toLp 2 (fun j=>((rationalHistoryStep oracle cfg S lam g w).mean j:ℝ)),
    rationalHistoryStep_feasible W oracle hspec cfg S lam g w hmetric⟩
  have ha : ∀ i,a i=(rationalTiltMean S lam g w i:ℝ) := by
    intro i
    exact congrFun (rationalTiltGaussian_mean S hS lam hlam g w) i
  have hab : ∀ i,|a i-b i|≤((2:ℝ)^cfg.storagePrecision)⁻¹ := by
    intro i
    rw [ha i,abs_sub_comm]
    exact rationalVectorRound_error cfg.storagePrecision (rationalTiltMean S lam g w) i
  have hwa : ∀ v : W.carrier,∀ i,|v.val i-a i|≤R := by
    intro v i
    rw [ha i]
    have hh := hcenter v i
    linarith [show 0≤((2:ℝ)^cfg.storagePrecision)⁻¹ by positivity]
  have hwb : ∀ v : W.carrier,∀ i,|v.val i-b i|≤R := by
    intro v i
    have hh := abs_sub_le (v.val i) (a i) (b i)
    have hb := hab i
    have hc := hcenter v i
    rw [←ha i] at hc
    linarith
  have ho : ∀ v : W.carrier,matrixQuadratic B (m.val-b)≤
      matrixQuadratic B (v.val-b)+((2:ℝ)^cfg.projectionPrecision)⁻¹ :=
    (hspec (rationalProjectionMetric cfg S lam g)
      (rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w))
      cfg.projectionPrecision hmetric).2
  have hg := rounded_projection_input_gap W F.precision B F.positive a b m
    M R e (((2:ℝ)^cfg.storagePrecision)⁻¹) (((2:ℝ)^cfg.projectionPrecision)⁻¹)
    hM hR he (by positivity) hB hAB hwa hwb hab ho
  have hm := projected_mean_coordinate_error W F.precision F.positive a m l
    ((((2:ℝ)^cfg.projectionPrecision)⁻¹)+
      2*(d:ℝ)^2*(e*R^2+2*M*R*((2:ℝ)^cfg.storagePrecision)⁻¹)) hl (by positivity) hA hg
  exact hm

end Paper254
#print axioms Paper254.rationalHistoryStep_mean_error
