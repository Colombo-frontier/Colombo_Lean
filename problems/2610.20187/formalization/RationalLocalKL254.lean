import RationalProjectionError254
import NumericalHistoryStep254

noncomputable section
namespace Paper254

theorem PrecisionGaussian.bounds_from_covariance {d : ℕ} (P : PrecisionGaussian d)
    (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hL : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic P.precision⁻¹ x)
    (hU : ∀ x : Space d,matrixQuadratic P.precision⁻¹ x≤hi*‖x‖^2) :
    (∀ x : Space d,(1/hi)*‖x‖^2≤matrixQuadratic P.precision x ∧
      matrixQuadratic P.precision x≤(1/lo)*‖x‖^2) ∧
    (1/hi)^d≤P.precision.det ∧ (∀ i j,|P.precision i j|≤(d:ℝ)^2/lo) := by
  have hh := precision_bounds_from_covariance P.precision⁻¹ P.positive.inv lo hi hlo hhi hL hU
  rwa [Matrix.nonsing_inv_nonsing_inv P.precision (isUnit_iff_ne_zero.mpr P.positive.det_pos.ne')] at hh

def historyCovError (d : ℕ) (cfg : RationalHistoryParameters) (h : ℝ) : ℝ :=
  ((2:ℝ)^cfg.storagePrecision)⁻¹+((2:ℝ)^cfg.accuracy)⁻¹+
    (d:ℝ)^2*(cfg.smoothing:ℝ)+(d:ℝ)^2*h

def historyPrecisionError (d : ℕ) (lo : ℝ) (cfg : RationalHistoryParameters) (h : ℝ) : ℝ :=
  ((d:ℝ)^3/lo)^2*d*historyCovError d cfg h

def historyMeanError (d : ℕ) (lo hi R : ℝ) (cfg : RationalHistoryParameters) (h : ℝ) : ℝ :=
  Real.sqrt ((((2:ℝ)^cfg.projectionPrecision)⁻¹+2*(d:ℝ)^2*
    ((historyPrecisionError d lo cfg h+((2:ℝ)^cfg.storagePrecision)⁻¹)*R^2+
      2*((d:ℝ)^2/lo+((2:ℝ)^cfg.storagePrecision)⁻¹)*R*((2:ℝ)^cfg.storagePrecision)⁻¹))/(1/hi))

/-- All matrix, determinant and mean-error hypotheses are derived from the
actual update. Only geometric bounds and the projection-oracle specification
are supplied, not a KL or regret conclusion. -/
theorem rationalHistoryStep_local_KL {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (hD : 0≤D) (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hlohi : lo≤hi)
    (hguard : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (h R : ℝ) (hh : 0≤h) (hR : 0≤R)
    (hl : |(cfg.lowerThreshold:ℝ)-lo|≤h) (hu : |(cfg.upperThreshold:ℝ)-hi|≤h)
    (hcenter : ∀ v : W.carrier,∀ i,
      |v.val i-(rationalTiltMean S lam g w i:ℝ)|+((2:ℝ)^cfg.storagePrecision)⁻¹≤R) :
    let hs := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi hguard S hS lam g w
    let N := (rationalHistoryStep oracle cfg S lam g w).gaussian hs.covariance_pos
    let E := (S.gaussian hS.covariance_pos).historyUpdate W (lam:ℝ) lo hlam hlo
      (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))
    ∀ u : W.carrier,|E.potential lo u.val-N.potential lo u.val|≤
      numericalKLError d lo D (max 1 ((d:ℝ)^2/lo)) ((1/hi)^d)
        (historyPrecisionError d lo cfg h) (historyMeanError d lo hi R cfg h) := by
  let hs := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi hguard S hS lam g w
  let N := (rationalHistoryStep oracle cfg S lam g w).gaussian hs.covariance_pos
  let P := (S.gaussian hS.covariance_pos).tilt (lam:ℝ) (2*(lam:ℝ)) hlam (by positivity)
    (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))
  let E := (P.floorCovariance lo hlo).projectMean W
  let C := (P.floorCovariance lo hlo).precision⁻¹
  let V := realMatrix (rationalNextCovariance cfg S lam g)
  let B := realMatrix (rationalProjectionMetric cfg S lam g)
  let rho : ℝ := ((2:ℝ)^cfg.storagePrecision)⁻¹
  let e := historyPrecisionError d lo cfg h
  have hsmooth := hguard.smoothing_pos
  have he0 : 0≤e := by dsimp [e,historyPrecisionError,historyCovError]; positivity
  have hP := rationalTiltGaussian_precision S hS.covariance_pos lam hlam g w
  have hbound : ∀ x : Space d,matrixQuadratic P.precision⁻¹ x≤hi*‖x‖^2 := by
    have hx := rationalTiltCovariance_upper S hS.covariance_pos lo hi hlo hhi
      hS.covariance_lower hS.covariance_upper lam g
    rw [realMatrix_inverse,←Matrix.nonsing_inv_eq_ringInverse,←hP] at hx
    exact hx
  have hc := P.floor_covariance_interval lo hi hlo hlohi hbound
  have hC : C.PosDef := (P.floorCovariance lo hlo).positive.inv
  have hV : V.PosDef := hs.covariance_pos
  have hcov := rationalNextCovariance_exact_floor_error hd W S lo hi hlo hhi hlohi hS
    cfg hguard lam g P hP h hh hl hu
  have hpre := rationalFloor_precision_error C V hC hV lo hi (historyCovError d cfg h)
    hlo hhi (by dsimp [historyCovError]; positivity) (fun x=>(hc x).1) (fun x=>(hc x).2)
    hs.covariance_lower hs.covariance_upper hcov
  have hdouble : C⁻¹=E.precision :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (P.floorCovariance lo hlo).positive.det_pos.ne')
  have hprec : ∀ i j,|E.precision i j-N.precision i j|≤e := by
    intro i j
    rw [abs_sub_comm]
    change |V⁻¹ i j-E.precision i j|≤e
    rw [←hdouble]
    exact hpre i j
  have hEB := E.bounds_from_covariance lo hi hlo hhi (fun x=>(hc x).1) (fun x=>(hc x).2)
  have hNB := precision_bounds_from_covariance V hV lo hi hlo hhi hs.covariance_lower hs.covariance_upper
  have hr : ∀ i j,|B i j-N.precision i j|≤rho := by
    intro i j
    have hx := roundRationalMatrix_entry cfg.storagePrecision
      (rationalMatrixInverse (rationalNextCovariance cfg S lam g)) i j
    have hiEq := congrArg (fun A : Precision d=>A i j)
      (realMatrix_inverse (rationalNextCovariance cfg S lam g))
    rw [←Matrix.nonsing_inv_eq_ringInverse] at hiEq
    change (rationalMatrixInverse (rationalNextCovariance cfg S lam g) i j:ℝ)=N.precision i j at hiEq
    rw [hiEq] at hx
    exact hx
  have hB : ∀ i j,|B i j|≤(d:ℝ)^2/lo+rho := by
    intro i j
    have ht := abs_sub_le (B i j) (N.precision i j) 0
    simp only [sub_zero] at ht
    exact ht.trans (by simpa only [add_comm] using add_le_add (hr i j) (hNB.2.2 i j))
  have hAB : ∀ i j,|E.precision i j-B i j|≤e+rho := by
    intro i j
    have ht := abs_sub_le (E.precision i j) (N.precision i j) (B i j)
    have hx := hr i j
    rw [abs_sub_comm] at hx
    linarith [hprec i j]
  have hmetric : B.PosDef := rationalMetricRound_posDef _ hV lo hi hlo hhi
    hs.covariance_lower hs.covariance_upper cfg.storagePrecision hguard.metric
  have hm := rationalHistoryStep_mean_error W oracle hspec cfg S hS.covariance_pos lam hlam g w lo hlo
    hmetric ((d:ℝ)^2/lo+rho) R (e+rho) (1/hi) (by dsimp [rho]; positivity) hR
    (by dsimp [rho]; positivity) (by positivity) hB hAB (fun x=>(hEB.1 x).1) hcenter
  change ∀ u : W.carrier,|E.potential lo u.val-N.potential lo u.val|≤_
  intro u
  exact feasible_potential_perturbation W hD E N
    (PrecisionGaussian.projectMean_feasible _ W) hs.feasible lo (max 1 ((d:ℝ)^2/lo)) e
    (historyMeanError d lo hi R cfg h) ((1/hi)^d) hlo (le_max_left _ _) he0 (Real.sqrt_nonneg _)
    (by positivity) hEB.2.1 hNB.2.1
    (fun i j=>(hEB.2.2 i j).trans (le_max_right _ _))
    (fun i j=>(hNB.2.2 i j).trans (le_max_right _ _)) hprec
    (fun i=>by rw [abs_sub_comm]; exact hm i) u

end Paper254
#print axioms Paper254.rationalHistoryStep_local_KL
