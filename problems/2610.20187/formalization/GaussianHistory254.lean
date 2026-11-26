import GaussianNorm254
import GaussianStep254

noncomputable section
open scoped Matrix BigOperators
open Matrix
namespace Paper254

def PrecisionGaussian.historyUpdate {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q)
    (g w : Coordinates d) : PrecisionGaussian d :=
  (((P.tilt lam (2*lam) hlam (by positivity) g w).floorCovariance q hq).projectMean W)

theorem PrecisionGaussian.historyUpdate_feasible {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q) (g w : Coordinates d) :
    WithLp.toLp 2 (P.historyUpdate W lam q hlam hq g w).mean ∈ W.carrier :=
  PrecisionGaussian.projectMean_feasible _ W

theorem PrecisionGaussian.history_one_step {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q)
    (g w : Coordinates d) (u : W.carrier)
    (hbounded : |2*lam*(g ⬝ᵥ (P.mean-w))| ≤ 1/4) :
    lam*(coordinateSurrogate (2*lam) g w P.mean-
      smoothedCoordinateSurrogate (2*lam) q g w u.val) ≤
        P.potential q u.val-(P.historyUpdate W lam q hlam hq g w).potential q u.val := by
  have hraw := P.raw_one_step lam q hlam hq g w u.val hbounded
  have hfloor := (P.tilt lam (2*lam) hlam (by positivity) g w).floor_potential_decreases q hq u.val
  have hproj := PrecisionGaussian.project_potential_decreases
    ((P.tilt lam (2*lam) hlam (by positivity) g w).floorCovariance q hq) W q u
  change _ ≤ _-(((P.tilt lam (2*lam) hlam (by positivity) g w).floorCovariance q hq).projectMean W).potential q u.val
  linarith

theorem PrecisionGaussian.potential_movement {d : ℕ} (P : PrecisionGaussian d)
    (q : ℝ) (hq : 0 < q) (u v : Space d) :
    Real.sqrt (P.potential q v) ≤ Real.sqrt (P.potential q u)+
      (‖(precisionFactor P.positive).toContinuousLinearMap‖/Real.sqrt 2)*‖v-u‖ := by
  let Q := (precisionFactor P.positive).toContinuousLinearMap
  let c := precisionCovariancePart q P.precision
  have hc : 0 ≤ c := precisionCovariancePart_nonneg q hq P.positive
  have hh := quadratic_potential_movement Q (WithLp.toLp 2 P.mean) u v c hc
  have hdiv := div_le_div_of_nonneg_right hh (Real.sqrt_nonneg 2)
  have he (x : Space d) : Real.sqrt (P.potential q x) =
      Real.sqrt (c+‖Q (x-WithLp.toLp 2 P.mean)‖^2)/Real.sqrt 2 := by
    rw [← Real.sqrt_div (add_nonneg hc (sq_nonneg _))]
    congr 1
    change (_+_)/2 = (c+‖precisionFactor P.positive (x-WithLp.toLp 2 P.mean)‖^2)/2
    rw [precisionFactor_norm]
    rfl
  rw [he v, he u]
  convert hdiv using 1 <;> ring

theorem PrecisionGaussian.history_movement {d : ℕ} {D : ℝ} (P : PrecisionGaussian d)
    (W : Domain d D) (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q)
    (g w : Coordinates d) (u v : Space d) :
    Real.sqrt ((P.historyUpdate W lam q hlam hq g w).potential q v) ≤
      Real.sqrt ((P.historyUpdate W lam q hlam hq g w).potential q u)+
        ‖v-u‖/(Real.sqrt 2*Real.sqrt q) := by
  let R := P.tilt lam (2*lam) hlam (by positivity) g w
  let N := P.historyUpdate W lam q hlam hq g w
  have hb : ‖(precisionFactor N.positive).toContinuousLinearMap‖ ≤ 1/Real.sqrt q := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    exact R.floor_factor_bound q hq x
  have hh := N.potential_movement q hq u v
  have hr := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hb (Real.sqrt_nonneg 2)) (norm_nonneg (v-u))
  have he : ((1/Real.sqrt q)/Real.sqrt 2)*‖v-u‖ = ‖v-u‖/(Real.sqrt 2*Real.sqrt q) := by ring
  rw [he] at hr
  exact le_trans hh (add_le_add_left hr _)

end Paper254
#print axioms Paper254.PrecisionGaussian.history_one_step
#print axioms Paper254.PrecisionGaussian.history_movement
