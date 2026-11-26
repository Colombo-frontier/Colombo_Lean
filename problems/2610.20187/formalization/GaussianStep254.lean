import GaussianTilt254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

def coordinateSurrogate {d : ℕ} (γ : ℝ) (g w x : Coordinates d) : ℝ :=
  g ⬝ᵥ (x-w)+γ/2*(g ⬝ᵥ (x-w))^2

def smoothedCoordinateSurrogate {d : ℕ} (γ q : ℝ) (g w u : Coordinates d) : ℝ :=
  coordinateSurrogate γ g w u+γ*q*(g ⬝ᵥ g)/2

theorem gaussian_step_scalar_identity (lam v a z q gg Q C : ℝ)
    (hden : 1+2*lam^2*v ≠ 0) :
    let k := lam*(1+2*lam*a)/(1+2*lam^2*v)
    (C+Q)/2-
      (C+q*(2*lam^2)*gg-Real.log (1+2*lam^2*v)+
        (Q+2*k*z+k^2*v+(2*lam^2)*(z+k*v)^2))/2-
      lam*((a+lam*a^2)-((a+z)+lam*(a+z)^2+lam*q*gg)) =
      Real.log (1+2*lam^2*v)/2-
        (2*lam^2*v)*(1+2*lam*a)^2/(4*(1+2*lam^2*v)) := by
  dsimp only
  field_simp
  <;> ring

theorem PrecisionGaussian.raw_step_identity {d : ℕ} (P : PrecisionGaussian d)
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q) (g w u : Coordinates d) :
    P.potential q u-(P.tilt lam (2*lam) hlam (by positivity) g w).potential q u-
      lam*(coordinateSurrogate (2*lam) g w P.mean-
        smoothedCoordinateSurrogate (2*lam) q g w u) =
      Real.log (1+2*lam^2*matrixQuadratic P.precision⁻¹ g)/2-
        (2*lam^2*matrixQuadratic P.precision⁻¹ g)*(1+2*lam*(g ⬝ᵥ (P.mean-w)))^2/
          (4*(1+2*lam^2*matrixQuadratic P.precision⁻¹ g)) := by
  let v := matrixQuadratic P.precision⁻¹ g
  let a := g ⬝ᵥ (P.mean-w)
  let z := g ⬝ᵥ (u-P.mean)
  let k := lam*(1+2*lam*a)/(1+2*lam^2*v)
  have ht : lam*(2*lam) = 2*lam^2 := by ring
  have hu : g ⬝ᵥ (u-w) = a+z := by
    dsimp [a, z]
    rw [← dotProduct_add]
    congr 1
    abel
  have hm : u-(P.tilt lam (2*lam) hlam (by positivity) g w).mean =
      (u-P.mean)+k • (P.precision⁻¹ *ᵥ g) := by
    rw [P.tilt_mean, ht]
    dsimp [k, a, v]
    abel
  unfold PrecisionGaussian.potential
  rw [hm]
  change (_+_)/2-
    (precisionCovariancePart q (rankOnePrecision P.precision (lam*(2*lam)) g)+
      matrixQuadratic (rankOnePrecision P.precision (lam*(2*lam)) g)
        ((u-P.mean)+k • (P.precision⁻¹ *ᵥ g)))/2-_ = _
  rw [ht, precisionCovariancePart_rankOne P.positive q (2*lam^2) hq (by positivity),
    tilt_quadratic_expansion P.positive]
  simp only [smoothedCoordinateSurrogate, coordinateSurrogate, hu]
  have hv : 0 ≤ v := matrixQuadratic_nonneg P.positive.inv g
  have hden : 1+2*lam^2*v ≠ 0 := by positivity
  convert gaussian_step_scalar_identity lam v a z q (g ⬝ᵥ g)
    (matrixQuadratic P.precision (u-P.mean))
    (precisionCovariancePart q P.precision) hden using 1 <;> dsimp [k, v, a, z] <;> ring

theorem PrecisionGaussian.raw_one_step {d : ℕ} (P : PrecisionGaussian d)
    (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q) (g w u : Coordinates d)
    (hbounded : |2*lam*(g ⬝ᵥ (P.mean-w))| ≤ 1/4) :
    lam*(coordinateSurrogate (2*lam) g w P.mean-
        smoothedCoordinateSurrogate (2*lam) q g w u) ≤
      P.potential q u-(P.tilt lam (2*lam) hlam (by positivity) g w).potential q u := by
  have hi := P.raw_step_identity lam q hlam hq g w u
  have hg := gaussian_gap_formula_nonpos
    (2*lam^2*matrixQuadratic P.precision⁻¹ g) (2*lam*(g ⬝ᵥ (P.mean-w)))
    (mul_nonneg (by positivity) (matrixQuadratic_nonneg P.positive.inv g)) hbounded
  linarith

end Paper254
#print axioms Paper254.PrecisionGaussian.raw_one_step
