import RationalHistoryInit254
import GaussianHistory254
import GaussianFloorClip254

open scoped BigOperators
open Matrix
namespace Paper254

noncomputable def RationalHistoryData.gaussian {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) : PrecisionGaussian d :=
  ⟨fun j=>(S.mean j:ℝ),(realMatrix S.covariance)⁻¹,hS.inv⟩

theorem realMatrix_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) (v : Fin d→ℚ) :
    (fun j=>((A *ᵥ v) j:ℝ))=realMatrix A *ᵥ (fun j=>(v j:ℝ)) := by
  ext i
  simp [Matrix.mulVec,dotProduct,realMatrix]

theorem rationalTiltGaussian_precision {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) :
    ((S.gaussian hS).tilt (lam:ℝ) (2*(lam:ℝ)) hlam (by positivity)
      (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))).precision=
      realMatrix (rationalTiltPrecision S lam g) := by
  rw [rationalTiltPrecision_cast,←Matrix.nonsing_inv_eq_ringInverse]
  rfl

theorem rationalTiltGaussian_mean {d : ℕ} (S : RationalHistoryData d)
    (hS : (realMatrix S.covariance).PosDef) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) :
    ((S.gaussian hS).tilt (lam:ℝ) (2*(lam:ℝ)) hlam (by positivity)
      (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ))).mean=
      (fun j=>(rationalTiltMean S lam g w j:ℝ)) := by
  have hb : (fun j=>((rationalMatrixInverse S.covariance *ᵥ S.mean-lam • g+
      (2*lam^2*(g ⬝ᵥ w)) • g) j:ℝ))=
      (S.gaussian hS).precision *ᵥ (S.gaussian hS).mean-
        (lam:ℝ) • (fun j=>(g j:ℝ))+
        ((lam:ℝ)*(2*(lam:ℝ))*((fun j=>(g j:ℝ)) ⬝ᵥ (fun j=>(w j:ℝ)))) • (fun j=>(g j:ℝ)) := by
    have hm := realMatrix_mulVec (rationalMatrixInverse S.covariance) S.mean
    rw [realMatrix_inverse,←Matrix.nonsing_inv_eq_ringInverse] at hm
    ext i
    have hi := congrFun hm i
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Rat.cast_add,Rat.cast_sub,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,dotProduct,Rat.cast_sum]
    change _=(((realMatrix S.covariance)⁻¹) *ᵥ (fun j=>(S.mean j:ℝ))) i-_
      +((lam:ℝ)*(2*(lam:ℝ))*(∑ j,(g j:ℝ)*(w j:ℝ)))*(g i:ℝ)
    rw [hi]
    ring
  unfold rationalTiltMean
  rw [realMatrix_mulVec,hb,realMatrix_inverse,←Matrix.nonsing_inv_eq_ringInverse,
    ←rationalTiltGaussian_precision S hS lam hlam g w]
  rfl

end Paper254
#print axioms Paper254.rationalTiltGaussian_mean
