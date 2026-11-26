import RationalSpectralClip254
import ProjectionInputError254

open scoped BigOperators Matrix.Norms.Operator
open Matrix
namespace Paper254

structure RationalHistoryData (d : ℕ) where
  mean : Fin d→ℚ
  covariance : Matrix (Fin d) (Fin d) ℚ

def rationalVectorRound {d : ℕ} (p : ℕ) (v : Fin d→ℚ) : Fin d→ℚ :=
  fun j=>dyadicCeil p (v j)

def rationalTiltPrecision {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :=
  rationalMatrixInverse S.covariance+(2*lam^2) • Matrix.vecMulVec g g

def rationalTiltMean {d : ℕ} (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :=
  rationalMatrixInverse (rationalTiltPrecision S lam g) *ᵥ
    (rationalMatrixInverse S.covariance *ᵥ S.mean-lam • g+(2*lam^2*(g ⬝ᵥ w)) • g)

structure RationalHistoryParameters where
  dimensionLog : ℕ
  spectralLog : ℕ
  accuracy : ℕ
  storagePrecision : ℕ
  projectionPrecision : ℕ
  smoothing : ℚ
  lowerThreshold : ℚ
  upperThreshold : ℚ

abbrev RationalProjectionProcedure (d : ℕ) :=
  Matrix (Fin d) (Fin d) ℚ → (Fin d→ℚ) → ℕ → (Fin d→ℚ)

/-- The exact oracle interface in the manuscript: feasibility and a
quadratic objective gap at the supplied rational inputs. -/
def RationalProjectionSpec {d : ℕ} {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) : Prop :=
  ∀ B a p,(realMatrix B).PosDef →
    WithLp.toLp 2 (fun j=>(oracle B a p j:ℝ))∈W.carrier ∧
    ∀ v : W.carrier,
      matrixQuadratic (realMatrix B) (fun j=>(oracle B a p j:ℝ)-(a j:ℝ))≤
      matrixQuadratic (realMatrix B) (fun j=>v.val j-(a j:ℝ))+((2:ℝ)^p)⁻¹

def rationalNextCovariance {d : ℕ} (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :=
  roundRationalMatrix cfg.storagePrecision
    (rationalSpectralClip cfg.dimensionLog cfg.spectralLog cfg.accuracy cfg.smoothing
      cfg.lowerThreshold cfg.upperThreshold
      (rationalMatrixInverse (rationalTiltPrecision S lam g)))

def rationalProjectionMetric {d : ℕ} (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g : Fin d→ℚ) :=
  roundRationalMatrix cfg.storagePrecision (rationalMatrixInverse (rationalNextCovariance cfg S lam g))

def rationalHistoryStep {d : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d)
    (lam : ℚ) (g w : Fin d→ℚ) : RationalHistoryData d :=
  let C := rationalNextCovariance cfg S lam g
  let B := rationalProjectionMetric cfg S lam g
  let a := rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w)
  ⟨oracle B a cfg.projectionPrecision,C⟩

theorem rationalVectorRound_error {d : ℕ} (p : ℕ) (a : Fin d→ℚ) (j : Fin d) :
    |(rationalVectorRound p a j:ℝ)-(a j:ℝ)|≤((2:ℝ)^p)⁻¹ := by
  have hh := dyadicCeil_real_bounds p (a j)
  change |(dyadicCeil p (a j):ℝ)-(a j:ℝ)|≤_
  rw [abs_of_nonneg (sub_nonneg.mpr hh.1)]
  linarith [hh.2]

theorem rationalHistoryStep_feasible {d : ℕ} {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ)
    (hmetric : (realMatrix (rationalProjectionMetric cfg S lam g)).PosDef) :
    WithLp.toLp 2 (fun j=>((rationalHistoryStep oracle cfg S lam g w).mean j:ℝ))∈W.carrier :=
  (hspec _ _ _ hmetric).1

theorem rationalHistoryStep_covariance_encoding {d : ℕ}
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) (i j : Fin d) :
    ∃ z : ℤ,(rationalHistoryStep oracle cfg S lam g w).covariance i j=
      (z:ℚ)/(2:ℚ)^cfg.storagePrecision := ⟨_,rfl⟩

theorem rationalProjection_inputs_encoding {d : ℕ} (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :
    (∀ i j,∃ z : ℤ,rationalProjectionMetric cfg S lam g i j=(z:ℚ)/(2:ℚ)^cfg.storagePrecision) ∧
    (∀ j,∃ z : ℤ,rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w) j=
      (z:ℚ)/(2:ℚ)^cfg.storagePrecision) := by
  constructor
  · intro i j
    exact ⟨_,rfl⟩
  · intro j
    exact ⟨_,rfl⟩

theorem rationalTiltPrecision_cast {d : ℕ} (S : RationalHistoryData d) (lam : ℚ)
    (g : Fin d→ℚ) :
    realMatrix (rationalTiltPrecision S lam g)=
      rankOnePrecision (Ring.inverse (realMatrix S.covariance))
        ((lam:ℝ)*(2*(lam:ℝ))) (fun j=>(g j:ℝ)) := by
  rw [← realMatrix_inverse]
  ext i j
  change ((rationalMatrixInverse S.covariance i j+(2*lam^2)*(g i*g j):ℚ):ℝ)=
    (rationalMatrixInverse S.covariance i j:ℝ)+((lam:ℝ)*(2*(lam:ℝ)))*((g i:ℝ)*(g j:ℝ))
  push_cast
  ring

end Paper254
#print axioms Paper254.rationalHistoryStep_feasible
#print axioms Paper254.rationalTiltPrecision_cast
