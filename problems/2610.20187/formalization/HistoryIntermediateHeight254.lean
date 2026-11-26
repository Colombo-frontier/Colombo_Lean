import RationalEncodingReset254
import EfficientHistoryCost254
import EfficientInverseCertificate254

noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Operator
namespace Paper254

theorem MatrixHeight.smul {m n : Type*} {b c : ℕ} {x : ℚ} {A : Matrix m n ℚ}
    (hx : RationalHeight x b) (hA : MatrixHeight A c) : MatrixHeight (x • A) (b+c) := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hx
  obtain ⟨W,r,hr0,hrb,hW,hs⟩ := hA
  refine ⟨fun i j=>Z 0 0*W i j,q*r,mul_ne_zero hq hr0,?_,?_,?_⟩
  · rw [abs_mul,pow_add]
    exact mul_le_mul hqb hrb (abs_nonneg _) (by positivity)
  · intro i j
    rw [abs_mul,pow_add]
    exact mul_le_mul (hZ 0 0) (hW i j) (abs_nonneg _) (by positivity)
  · intro i j
    change x*A i j=_
    dsimp only at hr
    rw [hr 0 0,hs]
    push_cast
    exact div_mul_div_comm _ _ _ _

theorem MatrixHeight.identity (d : ℕ) : MatrixHeight (1:Matrix (Fin d) (Fin d) ℚ) 0 := by
  refine ⟨1,1,by norm_num,by norm_num,?_,?_⟩
  · intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num

theorem rational_half_height : RationalHeight (1/2:ℚ) 1 := by
  refine ⟨fun _ _=>1,2,by norm_num,by norm_num,by intros; norm_num,?_⟩
  intros
  norm_num

structure HistoryInputHeight {d : ℕ} (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ) (b : ℕ) : Prop where
  covariance : MatrixHeight S.covariance b
  mean : MatrixHeight (rationalColumn S.mean) b
  learningRate : RationalHeight lam b
  gradient : MatrixHeight (rationalColumn g) b
  prediction : MatrixHeight (rationalColumn w) b
  smoothing : RationalHeight cfg.smoothing b
  lower : RationalHeight cfg.lowerThreshold b
  upper : RationalHeight cfg.upperThreshold b

theorem HistoryInputHeight.mono {d b c : ℕ} {cfg : RationalHistoryParameters}
    {S : RationalHistoryData d} {lam : ℚ} {g w : Fin d→ℚ}
    (h : HistoryInputHeight cfg S lam g w b) (hbc : b≤c) :
    HistoryInputHeight cfg S lam g w c :=
  ⟨h.covariance.mono hbc,h.mean.mono hbc,h.learningRate.mono hbc,h.gradient.mono hbc,
    h.prediction.mono hbc,h.smoothing.mono hbc,h.lower.mono hbc,h.upper.mono hbc⟩

def tiltPrecisionHeight (d b : ℕ) := inverseHeight d b+4*b+6
def tiltedCovarianceHeight (d b : ℕ) := inverseHeight d (tiltPrecisionHeight d b)
def tiltDataHeight (d b : ℕ) :=
  inverseHeight d b+tiltedCovarianceHeight d b+16*b+8*d+32

/-- All operands and results of the actual shared tilt and raw mean kernels. -/
def TiltIntermediateHeights {d : ℕ} (S : RationalHistoryData d) (lam : ℚ)
    (g w : Fin d→ℚ) (b : ℕ) : Prop :=
  let P := rationalMatrixInverse S.covariance
  let Q := rationalTiltPrecision S lam g
  let V := rationalMatrixInverse Q
  MatrixHeight P b ∧ RationalHeight (2*lam^2) b ∧
  MatrixHeight (Matrix.vecMulVec g g) b ∧
  MatrixHeight ((2*lam^2) • Matrix.vecMulVec g g) b ∧ MatrixHeight Q b ∧ MatrixHeight V b ∧
  MatrixHeight (P*rationalColumn S.mean) b ∧ MatrixHeight (lam • rationalColumn g) b ∧
  MatrixHeight (P*rationalColumn S.mean-lam • rationalColumn g) b ∧
  RationalHeight (g ⬝ᵥ w) b ∧ RationalHeight (2*lam^2*(g ⬝ᵥ w)) b ∧
  MatrixHeight ((2*lam^2*(g ⬝ᵥ w)) • rationalColumn g) b ∧
  MatrixHeight (P*rationalColumn S.mean-lam • rationalColumn g+
    (2*lam^2*(g ⬝ᵥ w)) • rationalColumn g) b ∧
  MatrixHeight (rationalColumn (rationalTiltMean S lam g w)) b

theorem TiltIntermediateHeights.mono {d b c : ℕ} {S : RationalHistoryData d}
    {lam : ℚ} {g w : Fin d→ℚ} (h : TiltIntermediateHeights S lam g w b) (hbc : b≤c) :
    TiltIntermediateHeights S lam g w c := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
  exact ⟨h1.mono hbc,h2.mono hbc,h3.mono hbc,h4.mono hbc,h5.mono hbc,h6.mono hbc,
    h7.mono hbc,h8.mono hbc,h9.mono hbc,h10.mono hbc,h11.mono hbc,h12.mono hbc,
    h13.mono hbc,h14.mono hbc⟩

theorem history_tilt_heights {d b : ℕ} (cfg : RationalHistoryParameters)
    (S : RationalHistoryData d) (lam : ℚ) (g w : Fin d→ℚ)
    (hS : (realMatrix S.covariance).PosDef) (hinput : HistoryInputHeight cfg S lam g w b) :
    MatrixHeight (rationalTiltPrecision S lam g) (tiltPrecisionHeight d b) ∧
    MatrixHeight (rationalMatrixInverse (rationalTiltPrecision S lam g)) (tiltedCovarianceHeight d b) ∧
    TiltIntermediateHeights S lam g w (tiltDataHeight d b) := by
  have hp : MatrixHeight (rationalMatrixInverse S.covariance) (inverseHeight d b) := by
    rw [rationalMatrixInverse_eq_inv]
    exact hinput.covariance.inv (realMatrix_unit_reflect _ hS.isUnit)
  have htwo : RationalHeight (2:ℚ) 1 := by
    simpa using RationalHeight.of_int 2 1 (by norm_num)
  have hs : RationalHeight (2*lam^2) (2*b+4) := by
    convert htwo.mul (hinput.learningRate.pow 2) using 1 <;> ring
  have hr : MatrixHeight (Matrix.vecMulVec g g) (2*b+1) := by
    rw [←rationalColumn_outer]
    simpa only [two_mul] using hinput.gradient.mul hinput.gradient.transpose
  have hscaled := MatrixHeight.smul hs hr
  have hq : MatrixHeight (rationalTiltPrecision S lam g) (tiltPrecisionHeight d b) := by
    exact (hp.add hscaled).mono (by dsimp [tiltPrecisionHeight]; omega)
  have hv : MatrixHeight (rationalMatrixInverse (rationalTiltPrecision S lam g))
      (tiltedCovarianceHeight d b) := by
    rw [rationalMatrixInverse_eq_inv]
    exact hq.inv (realMatrix_unit_reflect _ (rationalTiltPrecision_posDef S hS lam g).isUnit)
  have hbase := hp.mul hinput.mean
  have hlinear := MatrixHeight.smul hinput.learningRate hinput.gradient
  have hsub := hbase.sub hlinear
  have hdot : RationalHeight (g ⬝ᵥ w) (2*b+d) := by
    have he : (rationalColumn g)ᵀ*rationalColumn w=(fun _ _ : Fin 1=>g ⬝ᵥ w) := by ext i j; rfl
    have hh := hinput.gradient.transpose.mul hinput.prediction
    rw [he] at hh
    simpa only [two_mul] using hh
  have hscalar := hs.mul hdot
  have hcorr := MatrixHeight.smul hscalar hinput.gradient
  have hrhs := hsub.add hcorr
  have hmean : MatrixHeight (rationalColumn (rationalTiltMean S lam g w))
      (tiltedCovarianceHeight d b+(inverseHeight d b+b+d+(b+b)+1+
        (2*b+4+(2*b+d)+1+b)+1)+d) := by
    have hh := hv.mul hrhs
    convert hh using 1
  refine ⟨hq,hv,?_⟩
  dsimp only [TiltIntermediateHeights]
  refine ⟨hp.mono ?_,hs.mono ?_,hr.mono ?_,hscaled.mono ?_,hq.mono ?_,hv.mono ?_,
    hbase.mono ?_,hlinear.mono ?_,hsub.mono ?_,hdot.mono ?_,hscalar.mono ?_,hcorr.mono ?_,
    hrhs.mono ?_,hmean.mono ?_⟩
  all_goals dsimp only [tiltDataHeight,tiltPrecisionHeight]; omega

end Paper254
#print axioms Paper254.history_tilt_heights
