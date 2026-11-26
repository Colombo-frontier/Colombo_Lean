import EfficientSpectralClip254
import RationalHistoryRun254

open Matrix
namespace Paper254

/-- Shared inverse, tilted covariance, and rounded covariance are computed
once and stored before the next operation consumes them. -/
def efficientHistoryStep {d : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d)
    (lam : ℚ) (g w : Fin d→ℚ) : RationalHistoryData d :=
  let P := rationalMatrixOfRows (efficientGeneralInverseRows S.covariance)
  let Q := rationalMatrixOfRows (rationalMatrixRows (P+(2*lam^2) • Matrix.vecMulVec g g))
  let V := rationalMatrixOfRows (efficientGeneralInverseRows Q)
  let C := rationalMatrixOfRows (rationalMatrixRows (roundRationalMatrix cfg.storagePrecision
    (efficientSpectralClip cfg.dimensionLog cfg.spectralLog cfg.accuracy cfg.smoothing
      cfg.lowerThreshold cfg.upperThreshold V)))
  let B := rationalMatrixOfRows (rationalMatrixRows (roundRationalMatrix cfg.storagePrecision
    (rationalMatrixOfRows (efficientGeneralInverseRows C))))
  let a := Vector.ofFn (rationalVectorRound cfg.storagePrecision
    (V *ᵥ (P *ᵥ S.mean-lam • g+(2*lam^2*(g ⬝ᵥ w)) • g)))
  ⟨oracle B (fun j=>a.get j) cfg.projectionPrecision,C⟩

/-- The optimized executable step has exactly the same rational state as
the semantic step on every state satisfying the proved invariant. -/
theorem efficientHistoryStep_eq {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hguard : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (g w : Fin d→ℚ) :
    efficientHistoryStep oracle cfg S lam g w=rationalHistoryStep oracle cfg S lam g w := by
  have hP : efficientGeneralInverse S.covariance=rationalMatrixInverse S.covariance := by
    rw [efficientGeneralInverse_correct _ (realMatrix_unit_reflect _ hS.covariance_pos.isUnit),
      rationalMatrixInverse_eq_inv]
  have hQ : efficientGeneralInverse (rationalTiltPrecision S lam g)=
      rationalMatrixInverse (rationalTiltPrecision S lam g) := by
    rw [efficientGeneralInverse_correct _ (realMatrix_unit_reflect _
      (rationalTiltPrecision_posDef S hS.covariance_pos lam g).isUnit),rationalMatrixInverse_eq_inv]
  obtain ⟨U,c,hC,hc⟩ := rationalTiltCovariance_spectrum S hS.covariance_pos lo hi hlo hhi
    hS.covariance_lower hS.covariance_upper lam g
  have hclip := efficientSpectralClip_eq hd cfg.dimensionLog cfg.spectralLog cfg.accuracy
    hguard.dimension cfg.smoothing cfg.lowerThreshold cfg.upperThreshold hguard.smoothing_pos
    (rationalMatrixInverse (rationalTiltPrecision S lam g)) U c hC hguard.smoothing_lower
    (fun j=>hguard.lower_spectral (c j) (hc j).1.le (hc j).2)
    (fun j=>hguard.upper_spectral (c j) (hc j).1.le (hc j).2)
  have hnext := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi hguard S hS lam g w
  have hB : efficientGeneralInverse (rationalNextCovariance cfg S lam g)=
      rationalMatrixInverse (rationalNextCovariance cfg S lam g) := by
    have hpos : (realMatrix (rationalNextCovariance cfg S lam g)).PosDef := hnext.covariance_pos
    rw [efficientGeneralInverse_correct _ (realMatrix_unit_reflect _ hpos.isUnit),
      rationalMatrixInverse_eq_inv]
  unfold efficientGeneralInverse at hP hQ hB
  unfold rationalTiltPrecision at hQ
  unfold rationalNextCovariance at hB
  simp only [efficientHistoryStep,matrix_of_cached_rows,hP,hQ]
  change _ = rationalHistoryStep oracle cfg S lam g w
  rw [←rationalTiltPrecision]
  rw [hclip,hB]
  simp [Vector.get,rationalHistoryStep,rationalProjectionMetric,rationalTiltMean,rationalNextCovariance]

end Paper254
#print axioms Paper254.efficientHistoryStep_eq
