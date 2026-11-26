import RationalSparseRegret254
import NormalizedGrid254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem loss_normalized_scale (hT : 0 < T) (f : ℕ → Loss d)
    (hf : ∀ t < T, ExpConcaveOn eta W.carrier (f t))
    (hder : ∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val)
    (u : ℕ → W.carrier) (k : Fin (K+1)) (tau : ℝ)
    (hlo : D/T ≤ tau) (hhi : tau ≤ D) (hscale : (C.lo k : ℝ)=tau^2)
    (hmaster : C.masterBudget*(C.lam : ℝ)≤2*logFactor T)
    (delta : ℝ) (hloc : C.localError k≤(C.lam : ℝ)*delta/(2*T))
    (hmast : C.masterError≤(C.lam : ℝ)*delta/(2*T)) :
    C.cumulativeRegret f u ≤ 24*(d+1 : ℝ)*logFactor T^2/curvature D G eta+
      1024*(Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau))*
        intervalCharge (C.movementLength u) 0 (T-1)+
      curvature D G eta*G^2*T*tau^2/2+delta := by
  let gamma := curvature D G eta
  let Lambda := logFactor T
  let L := scaleCount T+1
  let a := C.masterBudget
  let B := birthBudget d D (tau^2)
  let H := restartThreshold L a B (gamma/2)
  let V := variationThreshold L a B (gamma/2) (tau^2)
  have hgamma : 0 < gamma := Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos
  have hlam : (C.lam : ℝ)=gamma/2 := by linarith [C.lam_eq]
  have htau : 0 < tau := (div_pos C.diameter_pos (by exact_mod_cast hT)).trans_le hlo
  have hLambda : 0 ≤ Lambda := (by norm_num : (0 : ℝ)≤1).trans (logFactor_ge_one T hT)
  have hL : (0 : ℝ)<L := by dsimp [L]; positivity
  have ha : 0 ≤ a := C.masterBudget_nonneg hT
  have hB : 0 < B := birthBudget_positive d D _ C.diameter_pos (sq_pos_of_pos htau)
  have hLmax : (L : ℝ)≤2*Lambda := by
    simpa only [L,Nat.cast_add,Nat.cast_one] using scaleDepth_log_bound T hT
  have haMax : a*(gamma/2)≤2*Lambda := by simpa only [hlam] using hmaster
  have hBmax : B≤(d+1 : ℝ)*Lambda := birthBudget_log_bound d T hT D tau C.diameter_pos hlo hhi
  have hs := restart_static_normalization a B gamma L Lambda (d+1 : ℝ) ha hB.le hgamma hL.le hLambda
    (by linarith [Nat.cast_nonneg d (α := ℝ)]) hLmax haMax hBmax
  have hm := restart_movement_normalization a B gamma L Lambda (d+1 : ℝ) tau ha hB hgamma hL hLambda
    (by linarith [Nat.cast_nonneg d (α := ℝ)]) htau hLmax haMax hBmax
  have hP : 0 ≤ intervalCharge (C.movementLength u) 0 (T-1) :=
    intervalCharge_nonneg _ (fun _ => norm_nonneg _) _ _
  have hp := mul_le_mul_of_nonneg_right hm hP
  have hpow : T<2^L := Nat.lt_pow_succ_log_self (by norm_num) T
  have hh := C.loss_fixed_scale_budget hT f hf hder u k L (by dsimp [L]; omega) hpow delta hloc hmast
  rw [hscale,hlam] at hh
  change C.cumulativeRegret f u≤(H/64)*(1+intervalCharge (C.movementLength u) 0 (T-1)/V)+
    gamma*G^2*T*tau^2/2+delta at hh
  have he : (H/64)*(1+intervalCharge (C.movementLength u) 0 (T-1)/V)=
      H/64+((H/64)/V)*intervalCharge (C.movementLength u) 0 (T-1) := by ring
  rw [he] at hh
  change H/64≤_ at hs
  change ((H/64)/V)*intervalCharge (C.movementLength u) 0 (T-1)≤_ at hp
  have hp' : ((H/64)/V)*intervalCharge (C.movementLength u) 0 (T-1)≤
      1024*(Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau))*intervalCharge (C.movementLength u) 0 (T-1) := by
    convert hp using 1 <;> ring
  change C.cumulativeRegret f u≤24*(d+1 : ℝ)*Lambda^2/gamma+
    1024*(Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau))*intervalCharge (C.movementLength u) 0 (T-1)+
      gamma*G^2*T*tau^2/2+delta
  linarith

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.loss_normalized_scale
