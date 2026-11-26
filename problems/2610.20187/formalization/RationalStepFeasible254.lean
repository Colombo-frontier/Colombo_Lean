import RationalMetric254

noncomputable section
open scoped Matrix.Norms.Operator
namespace Paper254

theorem rationalTiltPrecision_posDef {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lam : ℚ) (g : Fin d→ℚ) :
    (realMatrix (rationalTiltPrecision S lam g)).PosDef := by
  rw [rationalTiltPrecision_cast,← Matrix.nonsing_inv_eq_ringInverse]
  exact rankOnePrecision_posDef hS.inv _ (by nlinarith [sq_nonneg (lam:ℝ)]) _

theorem rationalHistoryStep_feasible_of_guards {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lam : ℚ) (g w : Fin d→ℚ)
    (U : Matrix.unitaryGroup (Fin d) ℝ) (c : Coordinates d)
    (hC : realMatrix (rationalMatrixInverse (rationalTiltPrecision S lam g))=rotatedPrecision U c)
    (hdim : (d:ℝ)≤(2:ℝ)^cfg.dimensionLog) (he : 0<(cfg.smoothing:ℝ))
    (hsmall : ((2:ℝ)^cfg.spectralLog)⁻¹≤(cfg.smoothing:ℝ))
    (hcl : ∀ j,|c j-(cfg.lowerThreshold:ℝ)|+(cfg.smoothing:ℝ)≤(2:ℝ)^cfg.spectralLog)
    (hcu : ∀ j,|c j-(cfg.upperThreshold:ℝ)|+(cfg.smoothing:ℝ)≤(2:ℝ)^cfg.spectralLog)
    (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hlu : (cfg.lowerThreshold:ℝ)≤(cfg.upperThreshold:ℝ))
    (hmarginL : lo+d*(((2:ℝ)^cfg.accuracy)⁻¹+(d:ℝ)^2*(cfg.smoothing:ℝ)+
      ((2:ℝ)^cfg.storagePrecision)⁻¹)≤(cfg.lowerThreshold:ℝ))
    (hmarginU : (cfg.upperThreshold:ℝ)≤hi-d*(((2:ℝ)^cfg.accuracy)⁻¹+
      (d:ℝ)^2*(cfg.smoothing:ℝ)+((2:ℝ)^cfg.storagePrecision)⁻¹))
    (hmetric : (d:ℝ)*((2:ℝ)^cfg.storagePrecision)⁻¹≤1/(2*hi)) :
    (realMatrix (rationalNextCovariance cfg S lam g)).PosDef ∧
    (∀ x : Space d,lo*‖x‖^2≤matrixQuadratic (realMatrix (rationalNextCovariance cfg S lam g)) x ∧
      matrixQuadratic (realMatrix (rationalNextCovariance cfg S lam g)) x≤hi*‖x‖^2) ∧
    WithLp.toLp 2 (fun j=>((rationalHistoryStep oracle cfg S lam g w).mean j:ℝ))∈W.carrier := by
  have hs := rationalTiltPrecision_posDef S hS lam g
  have hsym := rationalMatrixInverse_symmetric (rationalTiltPrecision S lam g) hs
  have hb := rationalSpectralClip_interval hd cfg.dimensionLog cfg.spectralLog cfg.accuracy
    cfg.storagePrecision hdim cfg.smoothing cfg.lowerThreshold cfg.upperThreshold he
    (rationalMatrixInverse (rationalTiltPrecision S lam g)) U c hC hsmall hcl hcu
    lo hi hlu hmarginL hmarginU
  change ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic (realMatrix (rationalNextCovariance cfg S lam g)) x ∧
    matrixQuadratic (realMatrix (rationalNextCovariance cfg S lam g)) x≤hi*‖x‖^2 at hb
  have hpos : (realMatrix (rationalNextCovariance cfg S lam g)).PosDef := by
    apply symmetric_quadratic_lower_posDef _ lo hlo _ (fun x=>(hb x).1)
    intro i j
    exact congrArg (fun z : ℚ=>(z:ℝ))
      (rationalSpectralClip_symmetric cfg.dimensionLog cfg.spectralLog cfg.accuracy cfg.storagePrecision
        cfg.smoothing cfg.lowerThreshold cfg.upperThreshold
        (rationalMatrixInverse (rationalTiltPrecision S lam g)) hsym i j)
  refine ⟨hpos,hb,?_⟩
  apply rationalHistoryStep_feasible W oracle hspec cfg S lam g w
  exact rationalMetricRound_posDef _ hpos lo hi hlo hhi (fun x=>(hb x).1) (fun x=>(hb x).2)
    cfg.storagePrecision hmetric

end Paper254
#print axioms Paper254.rationalHistoryStep_feasible_of_guards
