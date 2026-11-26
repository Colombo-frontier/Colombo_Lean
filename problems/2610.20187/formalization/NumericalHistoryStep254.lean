import GaussianPerturbation254
import GaussianHistory254

noncomputable section
namespace Paper254

def numericalKLError (d : ℕ) (q D M l e t : ℝ) : ℝ :=
  (q*d*e+(Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*e*M^d/l+
    (d:ℝ)^2*(e*D^2+2*M*D*t))/2

theorem feasible_potential_perturbation {d : ℕ} {D : ℝ} (W : Domain d D)
    (hD : 0≤D) (P Q : PrecisionGaussian d)
    (hp : WithLp.toLp 2 P.mean∈W.carrier) (hqmean : WithLp.toLp 2 Q.mean∈W.carrier)
    (q M e t l : ℝ) (hq : 0<q) (hM : 1≤M) (he : 0≤e) (ht : 0≤t) (hl : 0<l)
    (hdetP : l≤P.precision.det) (hdetQ : l≤Q.precision.det)
    (hP : ∀ i j,|P.precision i j|≤M) (hQ : ∀ i j,|Q.precision i j|≤M)
    (hPQ : ∀ i j,|P.precision i j-Q.precision i j|≤e)
    (hm : ∀ i,|P.mean i-Q.mean i|≤t) (u : W.carrier) :
    |P.potential q u.val-Q.potential q u.val|≤numericalKLError d q D M l e t := by
  apply precision_potential_perturbation P Q q hq u.val M D e t l hM hD he ht hl
    hdetP hdetQ hP hQ hPQ _ _ hm
  · intro i
    exact (PiLp.norm_apply_le (u.val-WithLp.toLp 2 P.mean) i).trans
      (W.diameter u.val u.property _ hp)
  · intro i
    exact (PiLp.norm_apply_le (u.val-WithLp.toLp 2 Q.mean) i).trans
      (W.diameter u.val u.property _ hqmean)

/-- The implemented successor is compared with the exact update from the
same implemented input state. There is no error propagation from a
separate ideal trajectory. -/
theorem history_one_step_entry_error {d : ℕ} {D : ℝ} (W : Domain d D) (hD : 0≤D)
    (P N : PrecisionGaussian d) (hN : WithLp.toLp 2 N.mean∈W.carrier)
    (lam q : ℝ) (hlam : 0≤lam) (hq : 0<q) (g w : Coordinates d)
    (hbounded : |2*lam*(g ⬝ᵥ (P.mean-w))|≤1/4)
    (M e t l : ℝ) (hM : 1≤M) (he : 0≤e) (ht : 0≤t) (hl : 0<l)
    (hdetE : l≤(P.historyUpdate W lam q hlam hq g w).precision.det)
    (hdetN : l≤N.precision.det)
    (hE : ∀ i j,|(P.historyUpdate W lam q hlam hq g w).precision i j|≤M)
    (hNB : ∀ i j,|N.precision i j|≤M)
    (hprec : ∀ i j,|(P.historyUpdate W lam q hlam hq g w).precision i j-N.precision i j|≤e)
    (hmean : ∀ i,|(P.historyUpdate W lam q hlam hq g w).mean i-N.mean i|≤t)
    (u : W.carrier) :
    lam*(coordinateSurrogate (2*lam) g w P.mean-smoothedCoordinateSurrogate (2*lam) q g w u.val)≤
      P.potential q u.val-N.potential q u.val+numericalKLError d q D M l e t := by
  have hx := P.history_one_step W lam q hlam hq g w u hbounded
  have hn := feasible_potential_perturbation W hD
    (P.historyUpdate W lam q hlam hq g w) N
    (P.historyUpdate_feasible W lam q hlam hq g w) hN q M e t l hq hM he ht hl
    hdetE hdetN hE hNB hprec hmean u
  have hb := abs_le.mp hn
  linarith [hb.1]

/-- The movement inequality holds at every feasible rounded covariance,
using its certified spectral bound directly. -/
theorem rounded_history_movement {d : ℕ} (N : PrecisionGaussian d) (q : ℝ) (hq : 0<q)
    (hcap : ∀ x : Space d,matrixQuadratic N.precision x≤(1/q)*‖x‖^2)
    (u v : Space d) :
    Real.sqrt (N.potential q v)≤Real.sqrt (N.potential q u)+‖v-u‖/(Real.sqrt 2*Real.sqrt q) := by
  have hfac : ∀ x : Space d,‖precisionFactor N.positive x‖≤(1/Real.sqrt q)*‖x‖ := by
    intro x
    have hh := hcap x
    rw [← precisionFactor_norm N.positive] at hh
    have he : ((1/Real.sqrt q)*‖x‖)^2=(1/q)*‖x‖^2 := by
      rw [mul_pow,div_pow,one_pow,Real.sq_sqrt hq.le]
    have hp : 0≤(1/Real.sqrt q)*‖x‖ := by positivity
    nlinarith [norm_nonneg (precisionFactor N.positive x)]
  have hb : ‖(precisionFactor N.positive).toContinuousLinearMap‖≤1/Real.sqrt q :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hfac
  have hh := N.potential_movement q hq u v
  have hr := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hb (Real.sqrt_nonneg 2)) (norm_nonneg (v-u))
  have he : ((1/Real.sqrt q)/Real.sqrt 2)*‖v-u‖=‖v-u‖/(Real.sqrt 2*Real.sqrt q) := by ring
  rw [he] at hr
  exact hh.trans (add_le_add_left hr _)

end Paper254
#print axioms Paper254.history_one_step_entry_error
#print axioms Paper254.rounded_history_movement
