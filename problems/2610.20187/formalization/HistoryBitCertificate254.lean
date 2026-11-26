import NumericalWorkHeight254
import CanonicalMatrixHeight254

noncomputable section
open Matrix
namespace Paper254

def historyOracleMeanBits (d L0 c k v : ℕ) (cfg : RationalHistoryParameters) :=
  c*(d+L0+(6*v+4+cfg.storagePrecision+1)+cfg.projectionPrecision+1)^k

def historyWorkHeight (d b v L0 c k : ℕ) (cfg : RationalHistoryParameters) :=
  b+tiltDataHeight d b+inverseWorkHeight d b+inverseWorkHeight d (tiltPrecisionHeight d b)+
    spectralWorkHeight d cfg.dimensionLog cfg.spectralLog cfg.accuracy (tiltedCovarianceHeight d b) b+
    inverseWorkHeight d (3*v+cfg.storagePrecision)+(3*v+cfg.storagePrecision)+
    (3*v+1+cfg.storagePrecision)+(6*v+4+cfg.storagePrecision)+
    (d+1)*historyOracleMeanBits d L0 c k v cfg+
    cfg.storagePrecision+cfg.projectionPrecision+
    matrixSqrtPrecision cfg.dimensionLog cfg.spectralLog cfg.accuracy+
    matrixSqrtIterations cfg.dimensionLog cfg.spectralLog cfg.accuracy+cfg.spectralLog+10

/-- The certificate follows every call in countedHistoryStep, including
all nested Newton and Schur calls, and its actual projection result. -/
def HistoryWorkHeights {d : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d) (lam : ℚ)
    (g w : Fin d→ℚ) (b : ℕ) : Prop :=
  HistoryInputHeight cfg S lam g w b ∧
  InverseWorkHeights S.covariance b ∧ TiltIntermediateHeights S lam g w b ∧
  InverseWorkHeights (rationalTiltPrecision S lam g) b ∧
  SpectralWorkHeights cfg.dimensionLog cfg.spectralLog cfg.accuracy cfg.smoothing
    cfg.lowerThreshold cfg.upperThreshold (rationalMatrixInverse (rationalTiltPrecision S lam g)) b ∧
  MatrixHeight (rationalNextCovariance cfg S lam g) b ∧
  InverseWorkHeights (rationalNextCovariance cfg S lam g) b ∧
  MatrixHeight (rationalProjectionMetric cfg S lam g) b ∧
  MatrixHeight (rationalColumn (rationalVectorRound cfg.storagePrecision (rationalTiltMean S lam g w))) b ∧
  MatrixHeight (rationalColumn (rationalHistoryStep oracle cfg S lam g w).mean) b

theorem actual_history_work_heights {d b : ℕ} (hd : 0<d) {D : ℝ}
    (W : Domain d D) (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (L0 c k : ℕ) (henc : ProjectionEncodingSpec oracle L0 c k)
    (cfg : RationalHistoryParameters) (lo hi G : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hG : 0≤G)
    (guards : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hinput : HistoryInputHeight cfg S lam g w b)
    (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4)
    (w0 : W.carrier) (v : ℕ) (hw0 : ∀ i,|w0.val i|≤(2:ℝ)^v)
    (hdim : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : hi≤(2:ℝ)^v)
    (hLi : lo⁻¹≤(2:ℝ)^v) (hGb : G≤(2:ℝ)^v) (hlb : (lam:ℝ)≤(2:ℝ)^v) :
    HistoryWorkHeights oracle cfg S lam g w (historyWorkHeight d b v L0 c k cfg) := by
  have htilt := history_tilt_heights cfg S lam g w hS.covariance_pos hinput
  have hfirst := inverse_work_heights S.covariance
    (realMatrix_unit_reflect _ hS.covariance_pos.isUnit) hinput.covariance
  have hsecond := inverse_work_heights (rationalTiltPrecision S lam g)
    (realMatrix_unit_reflect _ (rationalTiltPrecision_posDef S hS.covariance_pos lam g).isUnit) htilt.1
  obtain ⟨U,e,hC,he⟩ := rationalTiltCovariance_spectrum S hS.covariance_pos lo hi hlo hhi
    hS.covariance_lower hS.covariance_upper lam g
  have hclip := spectral_work_heights hd cfg.dimensionLog cfg.spectralLog cfg.accuracy
    guards.dimension cfg.smoothing cfg.lowerThreshold cfg.upperThreshold guards.smoothing_pos
    hinput.smoothing hinput.lower hinput.upper _ htilt.2.1 U e hC guards.smoothing_lower
    (fun j=>guards.lower_spectral (e j) (he j).1.le (he j).2)
    (fun j=>guards.upper_spectral (e j) (he j).1.le (he j).2)
  have hnext := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi guards S hS lam g w
  have hreset := rationalHistoryStep_input_heights hd W oracle hspec cfg lo hi G hlo hhi hG guards
    S hS lam hlam g w hg hsmall w0 v hw0 hdim hD hH hLi hGb hlb
  have hthird := inverse_work_heights (rationalNextCovariance cfg S lam g)
    (realMatrix_unit_reflect _ hnext.covariance_pos.isUnit) hreset.1
  have hstored := rationalHistoryStep_stored_bits hd W oracle hspec L0 c k henc cfg lo hi G
    hlo hhi hG guards S hS lam hlam g w hg hsmall w0 v hw0 hdim hD hH hLi hGb hlb
  have hmean : MatrixHeight (rationalColumn (rationalHistoryStep oracle cfg S lam g w).mean)
      ((d+1)*historyOracleMeanBits d L0 c k v cfg) := by
    have hh := canonical_matrix_height (rationalColumn (rationalHistoryStep oracle cfg S lam g w).mean)
      (fun i _=>hstored.2 i)
    simpa only [Nat.mul_one] using hh
  refine ⟨hinput.mono ?_,hfirst.mono ?_,htilt.2.2.mono ?_,hsecond.mono ?_,hclip.mono ?_,
    hreset.1.mono ?_,hthird.mono ?_,hreset.2.1.mono ?_,hreset.2.2.mono ?_,hmean.mono ?_⟩
  all_goals dsimp [historyWorkHeight]; omega

/-- Uniform upper charges for rational arithmetic and dyadic rounding on
inputs of at most b bits. The polynomial primitive bound is the explicit
standard arithmetic-cost interface; projection is charged separately. -/
structure PolynomialArithmeticCharge where
  cost : ℕ→ℕ
  coefficient : ℕ
  degree : ℕ
  bound : ∀ b,cost b≤coefficient*(b+1)^degree

def chargedHistoryStep {d : ℕ} (model : PolynomialArithmeticCharge) (workBits projectionCost : ℕ)
    (oracle : RationalProjectionProcedure d) (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) : RationalHistoryData d×ℕ :=
  let run := countedHistoryStep 1 0 oracle cfg S lam g w
  (run.1,run.2*model.cost workBits+projectionCost)

/-- Space for the partial dot-product accumulators as well as the stored
matrix values and rounding precision integers. -/
def historyPrimitiveBits (d H : ℕ) := 4*H+d+10

theorem matrix_partial_work_bits {m k : Type*} {n d H : ℕ}
    {A : Matrix m (Fin n) ℚ} {B : Matrix (Fin n) k ℚ}
    (hA : MatrixHeight A H) (hB : MatrixHeight B H) (hnd : n≤d)
    (P : Fin n→Prop) [DecidablePred P] (i : m) (j : k) :
    (∑ t : Fin n,if P t then A i t*B t j else 0).num.natAbs.size≤historyPrimitiveBits d H ∧
    (∑ t : Fin n,if P t then A i t*B t j else 0).den.size≤historyPrimitiveBits d H := by
  have hh := matrix_mul_partial_bits hA hB P i j
  constructor <;> dsimp [historyPrimitiveBits] <;> omega

theorem chargedHistoryStep_bound {d : ℕ} (hd : 0<d) (model : PolynomialArithmeticCharge)
    (workBits projectionCost : ℕ) (oracle : RationalProjectionProcedure d)
    (cfg : RationalHistoryParameters) (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) :
    (chargedHistoryStep model workBits projectionCost oracle cfg S lam g w).2≤
      historyStepCostBound d 1 0 cfg*model.coefficient*(workBits+1)^model.degree+projectionCost := by
  have hc := countedHistoryStep_cost hd 1 0 oracle cfg S lam g w
  have hb := model.bound workBits
  have hm := Nat.mul_le_mul hc hb
  simpa only [chargedHistoryStep,Nat.mul_assoc] using Nat.add_le_add_right hm projectionCost

/-- Joint certificate for one actual program, its actual intermediate
data, and its polynomial bit charge under the stated primitive/oracle model. -/
theorem chargedHistoryStep_certificate {d b : ℕ} (hd : 0<d) {D : ℝ}
    (W : Domain d D) (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (L0 c k : ℕ) (henc : ProjectionEncodingSpec oracle L0 c k)
    (model : PolynomialArithmeticCharge) (projectionCost : ℕ)
    (cfg : RationalHistoryParameters) (lo hi G : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hG : 0≤G)
    (guards : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hinput : HistoryInputHeight cfg S lam g w b)
    (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4)
    (w0 : W.carrier) (v : ℕ) (hw0 : ∀ i,|w0.val i|≤(2:ℝ)^v)
    (hdim : (d:ℝ)≤(2:ℝ)^v) (hD : D≤(2:ℝ)^v) (hH : hi≤(2:ℝ)^v)
    (hLi : lo⁻¹≤(2:ℝ)^v) (hGb : G≤(2:ℝ)^v) (hlb : (lam:ℝ)≤(2:ℝ)^v) :
    let H := historyWorkHeight d b v L0 c k cfg
    let run := chargedHistoryStep model (historyPrimitiveBits d H) projectionCost oracle cfg S lam g w
    run.1=rationalHistoryStep oracle cfg S lam g w ∧
    HistoryWorkHeights oracle cfg S lam g w H ∧
    run.2≤historyStepCostBound d 1 0 cfg*model.coefficient*
      (historyPrimitiveBits d H+1)^model.degree+projectionCost := by
  refine ⟨?_,?_,?_⟩
  · exact countedHistoryStep_value hd W 1 0 oracle hspec cfg lo hi hlo hhi guards S hS lam g w
  · exact actual_history_work_heights hd W oracle hspec L0 c k henc cfg lo hi G hlo hhi hG
      guards S hS lam hlam g w hinput hg hsmall w0 v hw0 hdim hD hH hLi hGb hlb
  · exact chargedHistoryStep_bound hd model _ projectionCost oracle cfg S lam g w

end Paper254
#print axioms Paper254.actual_history_work_heights
#print axioms Paper254.chargedHistoryStep_bound
#print axioms Paper254.chargedHistoryStep_certificate
