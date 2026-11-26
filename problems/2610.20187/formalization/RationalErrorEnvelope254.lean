import ExplicitErrorBudget254

noncomputable section
namespace Paper254

def precisionErrorCoefficient (d : ℕ) (lo : ℝ) : ℝ :=
  ((d:ℝ)^3/lo)^2*d*(2+2*(d:ℝ)^2)

def meanErrorCoefficient (d : ℕ) (lo hi R : ℝ) : ℝ :=
  hi*(1+2*(d:ℝ)^2*((precisionErrorCoefficient d lo+1)*R^2+
    2*((d:ℝ)^2/lo+1)*R))

def localLinearCoefficient (d : ℕ) (D lo hi : ℝ) : ℝ :=
  (lo*d+(Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*(max 1 ((d:ℝ)^2/lo))^d/((1/hi)^d)+
    (d:ℝ)^2*D^2)*precisionErrorCoefficient d lo/2

def localRootCoefficient (d : ℕ) (D lo : ℝ) : ℝ :=
  (d:ℝ)^2*(max 1 ((d:ℝ)^2/lo))*D

theorem history_error_linear_envelope (d a b r : ℕ) (lo hi : ℚ) :
    historyPrecisionError d (lo:ℝ) (uniformHistoryParameters a b r r lo hi)
      (((2:ℝ)^(r+2))⁻¹)≤precisionErrorCoefficient d (lo:ℝ)*((2:ℝ)^r)⁻¹ := by
  have hn : ((2:ℝ)^(3*a+b+r+6))⁻¹≤((2:ℝ)^r)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hm : ((2:ℝ)^(r+2))⁻¹≤((2:ℝ)^r)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hc : historyCovError d (uniformHistoryParameters a b r r lo hi)
      (((2:ℝ)^(r+2))⁻¹)≤(2+2*(d:ℝ)^2)*((2:ℝ)^r)⁻¹ := by
    dsimp [historyCovError,uniformHistoryParameters]
    push_cast
    have hdn := mul_le_mul_of_nonneg_left hn (sq_nonneg (d:ℝ))
    have hdm := mul_le_mul_of_nonneg_left hm (sq_nonneg (d:ℝ))
    nlinarith
  unfold historyPrecisionError precisionErrorCoefficient
  calc
    _ ≤ ((d:ℝ)^3/(lo:ℝ))^2*d*((2+2*(d:ℝ)^2)*((2:ℝ)^r)⁻¹) := by gcongr
    _ = _ := by ring

theorem history_mean_root_envelope (d a b r : ℕ) (lo hi : ℚ)
    (hlo : 0<(lo:ℝ)) (hhi : 0≤(hi:ℝ)) (R : ℝ) (hR : 0≤R) :
    historyMeanError d (lo:ℝ) (hi:ℝ) R (uniformHistoryParameters a b r r lo hi)
      (((2:ℝ)^(r+2))⁻¹)≤
      Real.sqrt (meanErrorCoefficient d (lo:ℝ) (hi:ℝ) R*((2:ℝ)^r)⁻¹) := by
  let x : ℝ := ((2:ℝ)^r)⁻¹
  let rho : ℝ := ((2:ℝ)^(3*a+b+r+6))⁻¹
  have hx : 0≤x := by dsimp [x]; positivity
  have hx1 : x≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hrho : 0≤rho := by dsimp [rho]; positivity
  have hrhox : rho≤x := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hrho1 := hrhox.trans hx1
  have he := history_error_linear_envelope d a b r lo hi
  have he0 : 0≤precisionErrorCoefficient d (lo:ℝ) := by
    dsimp [precisionErrorCoefficient]; positivity
  unfold historyMeanError
  apply Real.sqrt_le_sqrt
  change (x+2*(d:ℝ)^2*((historyPrecisionError d (lo:ℝ)
    (uniformHistoryParameters a b r r lo hi) (((2:ℝ)^(r+2))⁻¹)+rho)*R^2+
    2*((d:ℝ)^2/(lo:ℝ)+rho)*R*rho))/(1/(hi:ℝ))≤_
  have hfirst := mul_le_mul_of_nonneg_right (add_le_add he hrhox) (sq_nonneg R)
  have hsecond : 2*((d:ℝ)^2/(lo:ℝ)+rho)*R*rho≤
      2*((d:ℝ)^2/(lo:ℝ)+1)*R*x := by gcongr
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (show 0≤2*(d:ℝ)^2 by positivity)
  have htotal := mul_le_mul_of_nonneg_left (add_le_add_left hsum x) hhi
  dsimp [meanErrorCoefficient]
  simp only [one_div,div_inv_eq_mul]
  convert htotal using 1 <;> dsimp [x] <;> ring

theorem actual_history_error_envelope (d a b r : ℕ) (D G lam : ℝ) (lo hi : ℚ)
    (hD : 0≤D) (hG : 0≤G) (hlam : 0≤lam) (hlo : 0<(lo:ℝ)) (hhi : 0<(hi:ℝ)) :
    actualHistoryLocalError d D (lo:ℝ) (hi:ℝ) G lam
      (uniformHistoryParameters a b r r lo hi) (((2:ℝ)^(r+2))⁻¹)≤
    localLinearCoefficient d D (lo:ℝ) (hi:ℝ)*((2:ℝ)^r)⁻¹+
      localRootCoefficient d D (lo:ℝ)*Real.sqrt
        (meanErrorCoefficient d (lo:ℝ) (hi:ℝ) (uniformHistoryRadius d D (hi:ℝ) G lam)*((2:ℝ)^r)⁻¹) := by
  have he := history_error_linear_envelope d a b r lo hi
  have ht := history_mean_root_envelope d a b r lo hi hlo hhi.le
    (uniformHistoryRadius d D (hi:ℝ) G lam) (by dsimp [uniformHistoryRadius]; positivity)
  unfold actualHistoryLocalError numericalKLError
  calc
    _ ≤ ((lo:ℝ)*d*(precisionErrorCoefficient d (lo:ℝ)*((2:ℝ)^r)⁻¹)+
      (Fintype.card (Equiv.Perm (Fin d)):ℝ)*d*(precisionErrorCoefficient d (lo:ℝ)*((2:ℝ)^r)⁻¹)*
        (max 1 ((d:ℝ)^2/(lo:ℝ)))^d/((1/(hi:ℝ))^d)+
      (d:ℝ)^2*((precisionErrorCoefficient d (lo:ℝ)*((2:ℝ)^r)⁻¹)*D^2+
        2*(max 1 ((d:ℝ)^2/(lo:ℝ)))*D*Real.sqrt
          (meanErrorCoefficient d (lo:ℝ) (hi:ℝ) (uniformHistoryRadius d D (hi:ℝ) G lam)*((2:ℝ)^r)⁻¹)))/2 := by
      gcongr
    _ = _ := by dsimp [localLinearCoefficient,localRootCoefficient]; ring

end Paper254
#print axioms Paper254.actual_history_error_envelope
