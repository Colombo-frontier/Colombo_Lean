import RationalSparseNormalized254
import RationalScaleGrid254
import StandardMasterPrecision254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T (scaleCount T) D G eta W)

theorem masterBudget_log (hT : 0 < T) (hp : C.masterError≤1) :
    C.masterBudget*(C.lam : ℝ)≤2*logFactor T := by
  have he : C.masterBudget*(C.lam : ℝ)=
      Real.log ((T : ℝ)/standardBirthMass T (scaleCount T) C.master_precision) := by
    unfold masterBudget
    field_simp [ne_of_gt C.lam_pos]
  rw [he]
  exact standardMaster_normalized_log_budget T C.master_precision hT hp

/-- Clipped scale guarantee for the same rational learner at every comparator
path.  The logarithmic grid omits covariance equality at the upper floor. -/
theorem loss_clipped (hT : 2 ≤ T) (f : ℕ → Loss d)
    (hf : ∀ t < T, ExpConcaveOn eta W.carrier (f t))
    (hder : ∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val)
    (hgrid : ∀ k, C.lo k=rationalCappedVariance C.hi k.val)
    (hp : C.masterError≤1) (delta : ℝ)
    (hloc : ∀ k, C.localError k≤(C.lam : ℝ)*delta/(2*T))
    (hmast : C.masterError≤(C.lam : ℝ)*delta/(2*T))
    (u : ℕ → W.carrier) (tau : ℝ) (hlo : D/T≤tau) (hhi : tau≤D) :
    C.cumulativeRegret f u≤2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
      Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*
        intervalCharge (C.movementLength u) 0 (T-1)+curvature D G eta*G^2*T*tau^2)+delta := by
  have hT0 : 0<T := by omega
  obtain ⟨k,hklo,hkhi⟩ := cappedDyadicScale_approx D C.diameter_pos T hT tau hlo hhi
  have hr := cappedDyadicScale_range D C.diameter_pos T hT k
  have hs : (C.lo k : ℝ)=(cappedDyadicScale D k.val)^2 := by
    rw [hgrid k]
    exact rationalCappedVariance_cast D C.diameter_pos C.hi C.hi_eq k.val
  have hh := C.loss_normalized_scale hT0 f hf hder u k (cappedDyadicScale D k.val)
    hr.1 (by linarith [hr.2.2,C.diameter_pos]) hs (C.masterBudget_log hT0 hp) delta (hloc k) hmast
  let gamma := curvature D G eta
  let Lambda := logFactor T
  let tauk := cappedDyadicScale D k.val
  let P := intervalCharge (C.movementLength u) 0 (T-1)
  have hgamma : 0<gamma := Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos
  have htau : 0<tau := (div_pos C.diameter_pos (by exact_mod_cast hT0)).trans_le hlo
  have htauk : 0<tauk := hr.2.1
  have hP : 0≤P := intervalCharge_nonneg _ (fun _ => norm_nonneg _) _ _
  have hm := div_le_div_of_nonneg_left (by positivity : 0≤Real.sqrt (d+1 : ℝ)*Lambda^2)
    (mul_pos hgamma (by positivity : 0<tau/2)) (mul_le_mul_of_nonneg_left hklo hgamma.le)
  have hmp := mul_le_mul_of_nonneg_right hm hP
  have hme : Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*(tau/2))*P=
      2*(Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau)*P) := by ring
  rw [hme] at hmp
  have hsq : tauk^2≤4*tau^2 := by nlinarith
  have hsm := mul_le_mul_of_nonneg_left hsq (by positivity : 0≤gamma*G^2*T/2)
  have hs0 : 0≤(d+1 : ℝ)*Lambda^2/gamma := by positivity
  have hm0 : 0≤Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau)*P := by positivity
  have hsm0 : 0≤gamma*G^2*T*tau^2 := by positivity
  change C.cumulativeRegret f u≤24*(d+1 : ℝ)*Lambda^2/gamma+
    1024*(Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tauk))*P+gamma*G^2*T*tauk^2/2+delta at hh
  change C.cumulativeRegret f u≤2048*((d+1 : ℝ)*Lambda^2/gamma+
    Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau)*P+gamma*G^2*T*tau^2)+delta
  change Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tauk)*P≤_ at hmp
  ring_nf at hh hmp hsm hs0 hm0 hsm0 ⊢
  nlinarith

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.loss_clipped
