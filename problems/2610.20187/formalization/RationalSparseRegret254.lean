import RationalSparseGlobal254

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def playedPoint (t : ℕ) : W.carrier :=
  ⟨WithLp.toLp 2 (fun j => (C.prediction t j : ℝ)),C.prediction_feasible t⟩

def cumulativeRegret (f : ℕ → Loss d) (u : ℕ → W.carrier) : ℝ :=
  intervalCharge (fun t => f t (C.playedPoint t).val-f t (u t).val) 0 T

theorem loss_step (f : Loss d) (hf : ExpConcaveOn eta W.carrier f)
    (u : W.carrier) (k : Fin (K+1)) (t : ℕ)
    (hder : HasGradientWithinAt f (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val) :
    f (C.playedPoint t).val-f u.val ≤ C.regretCharge (fun _ => u) k t+
      curvature D G eta*G^2*(C.lo k : ℝ)/2 := by
  let g : Space d := WithLp.toLp 2 (fun j => (C.gradient t j : ℝ))
  let w := C.playedPoint t
  have hs := surrogate_domination W C.diameter_pos C.gradient_pos C.curvature_pos hf
    hder (C.gradient_bound t) w.property u.property
  have he : C.regretCharge (fun _ => u) k t=
      -rankOneSurrogate (curvature D G eta) g w.val u.val-
        curvature D G eta*(C.lo k : ℝ)*((g : Coordinates d) ⬝ᵥ (g : Coordinates d))/2 := by
    unfold regretCharge smoothedLoss smoothedCoordinateSurrogate
    rw [C.lam_eq]
    change coordinateSurrogate (curvature D G eta) g w.val w.val-
      (coordinateSurrogate (curvature D G eta) g w.val u.val+
        curvature D G eta*(C.lo k : ℝ)*((g : Coordinates d) ⬝ᵥ (g : Coordinates d))/2)=_
    rw [coordinate_surrogate_eq,coordinate_surrogate_eq]
    simp [rankOneSurrogate]
    ring
  have hquad : (g : Coordinates d) ⬝ᵥ (g : Coordinates d)=‖g‖^2 := by
    rw [coordinate_inner,real_inner_self_eq_norm_sq]
  have hgnorm : ‖g‖≤G := C.gradient_bound t
  have hg2 : ‖g‖^2≤G^2 := by nlinarith [norm_nonneg g]
  have hsm := mul_le_mul_of_nonneg_left hg2
    (mul_nonneg (Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos).le
      (C.lo_pos k).le)
  rw [he,hquad]
  change f w.val-f u.val≤-rankOneSurrogate (curvature D G eta) g w.val u.val at hs
  nlinarith

/-- True-loss dynamic regret for the implemented rational trajectory.
The gradient hypothesis identifies the supplied rational query with the
observed loss derivative; no regret property is an input. -/
theorem loss_fixed_scale (hT : 0 < T) (f : ℕ → Loss d)
    (hf : ∀ t < T, ExpConcaveOn eta W.carrier (f t))
    (hder : ∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val)
    (u : ℕ → W.carrier) (k : Fin (K+1)) (L : ℕ) (hL : 1 ≤ L) (hpow : T < 2^L) :
    C.cumulativeRegret f u ≤
      restartThreshold L C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lam : ℝ)/64*
        (1+intervalCharge (C.movementLength u) 0 (T-1)/
          variationThreshold L C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lam : ℝ) (C.lo k : ℝ))+
        curvature D G eta*G^2*T*(C.lo k : ℝ)/2+
        T*(C.localError k+C.masterError)/(C.lam : ℝ) := by
  have hb := C.fixed_scale hT u k L hL hpow
  have hp := Finset.sum_le_sum (s := Finset.range T) (fun t ht =>
    C.loss_step (f t) (hf t (Finset.mem_range.mp ht)) (u t) k t (hder t (Finset.mem_range.mp ht)))
  have he : ∀ t, C.regretCharge (fun _ => u t) k t=C.regretCharge u k t := fun _ => rfl
  simp only [he,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hp
  change C.cumulativeRegret f u≤_
  have hsum : C.cumulativeRegret f u ≤ intervalCharge (C.regretCharge u k) 0 T+
      curvature D G eta*G^2*T*(C.lo k : ℝ)/2 := by
    simp only [cumulativeRegret,intervalCharge,Nat.zero_add]
    convert hp using 1 <;> ring
  linarith

theorem loss_fixed_scale_budget (hT : 0 < T) (f : ℕ → Loss d)
    (hf : ∀ t < T, ExpConcaveOn eta W.carrier (f t))
    (hder : ∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
      W.carrier (C.playedPoint t).val)
    (u : ℕ → W.carrier) (k : Fin (K+1)) (L : ℕ) (hL : 1 ≤ L) (hpow : T < 2^L)
    (delta : ℝ) (hloc : C.localError k≤(C.lam : ℝ)*delta/(2*T))
    (hmast : C.masterError≤(C.lam : ℝ)*delta/(2*T)) :
    C.cumulativeRegret f u ≤
      restartThreshold L C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lam : ℝ)/64*
        (1+intervalCharge (C.movementLength u) 0 (T-1)/
          variationThreshold L C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lam : ℝ) (C.lo k : ℝ))+
        curvature D G eta*G^2*T*(C.lo k : ℝ)/2+delta := by
  have hh := C.loss_fixed_scale hT f hf hder u k L hL hpow
  have hnum : T*(C.localError k+C.masterError)/(C.lam : ℝ)≤delta := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hloc hmast) (Nat.cast_nonneg T (α := ℝ))
    have he : (T : ℝ)*((C.lam : ℝ)*delta/(2*T)+(C.lam : ℝ)*delta/(2*T))=(C.lam : ℝ)*delta := by
      field_simp
      ring
    rw [he] at h
    exact (div_le_iff₀ C.lam_pos).mpr (by simpa [mul_comm] using h)
  linarith

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.loss_fixed_scale
#print axioms Paper254.RationalSparseConstruction.loss_fixed_scale_budget
