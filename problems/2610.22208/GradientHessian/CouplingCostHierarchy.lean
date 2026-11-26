import GradientHessian.CouplingCost

/-! The incoming-coupling lemma on the literal hierarchy, including the
height-one child-port scale and all higher localized child ports. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open ScaledJets CouplingCost
universe u

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

theorem outgoing_scaledJets {K : ℝ} (hK : 0 < K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) : Bound (outgoing K t d) profileConstant (childScale m t) := by
  cases t with
  | zero =>
    refine ⟨profileConstant_pos.le, outgoing_contDiff hK 0 d, ?_⟩
    intro n hn Z
    exact (FirstHeight.sourceOutgoing_derivative_bound d (hd.outer_unit _ _) Z hn).trans
      (div_le_div_of_nonneg_right profileConstant_bounds.2.2
        (pow_nonneg (childScale_pos m 0).le n))
  | succ t => exact nodePort_scaledJets (width_pos m t) (centers K d) (Fin.last 7)

theorem outgoing_derivative_bound {K : ℝ} (hK : 0 < K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) {n : ℕ} (hn : n ≤ 3) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ n (outgoing K t d) Z‖ ≤ profileConstant / childScale m t ^ n :=
  (outgoing_scaledJets hK t d hd).norm_le n hn Z

variable [∀ t, CompleteSpace (H t)]

def incomingCouplingTerm (K : ℝ) (t : ℕ) (d : Data Y E H m (t+1)) (i : Fin 8) :
    Space Y E H m (t+1) → ℝ :=
  CouplingCost.term (radius m K t) (width m t) (centers K d)
    (fun j => outgoing K t (d.children j)) i

def incomingCoupling (K : ℝ) (t : ℕ) (d : Data Y E H m (t+1)) :
    Space Y E H m (t+1) → ℝ :=
  CouplingCost.coupling (radius m K t) (width m t) (centers K d)
    (fun j => outgoing K t (d.children j))

theorem incomingCouplingTerm_scaledJets {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m (t+1)) (hd : Valid Y E H m (t+1) d) (i : Fin 8) :
    Bound (incomingCouplingTerm K t d i) (termConstant*radius m K t) (childScale m t) := by
  have hK0 : 0 < K := by linarith
  exact term_scaledJets (width_pos m t) (childScale_pos m t) (scale_separation m hK t)
    (childScale_comparable m t).2 (centers K d) (centers_norm hK0.le d hd) _
    (fun j => outgoing_scaledJets hK0 t (d.children j) (hd.1 j)) i

theorem incomingCoupling_scaledJets {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m (t+1)) (hd : Valid Y E H m (t+1) d) :
    Bound (incomingCoupling K t d) (couplingConstant*radius m K t) (childScale m t) := by
  have hK0 : 0 < K := by linarith
  exact coupling_scaledJets (width_pos m t) (childScale_pos m t) (scale_separation m hK t)
    (childScale_comparable m t).2 (centers K d) (centers_norm hK0.le d hd) _
    (fun j => outgoing_scaledJets hK0 t (d.children j) (hd.1 j))

theorem incomingCoupling_derivative_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m (t+1)) (hd : Valid Y E H m (t+1) d)
    {n : ℕ} (hn : n ≤ 3) (Z : Space Y E H m (t+1)) :
    ‖iteratedFDeriv ℝ n (incomingCoupling K t d) Z‖ ≤
      couplingConstant * radius m K t / childScale m t ^ n :=
  (incomingCoupling_scaledJets hK t d hd).norm_le n hn Z

theorem incomingCoupling_first_source_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m (t+1)) (hd : Valid Y E H m (t+1) d) (Z : Space Y E H m (t+1)) :
    ‖iteratedFDeriv ℝ 1 (incomingCoupling K t d) Z‖ ≤
      couplingConstant * (1 + radius m K t / childScale m t) := by
  have h := incomingCoupling_derivative_bound hK t d hd (n := 1) (by norm_num) Z
  simp only [pow_one] at h
  have hC := couplingConstant_pos
  nlinarith [show couplingConstant * radius m K t / childScale m t =
    couplingConstant * (radius m K t / childScale m t) by ring]

theorem incomingCoupling_higher_source_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m (t+1)) (hd : Valid Y E H m (t+1) d)
    {n : ℕ} (_hn1 : 2 ≤ n) (hn3 : n ≤ 3) (Z : Space Y E H m (t+1)) :
    ‖iteratedFDeriv ℝ n (incomingCoupling K t d) Z‖ ≤
      couplingConstant * ((width m t)^(1-(n:ℤ)) + (childScale m t)^(1-(n:ℤ)) +
        radius m K t / childScale m t ^ n) := by
  have h := incomingCoupling_derivative_bound hK t d hd hn3 Z
  have hw := zpow_nonneg (width_pos m t).le (1-(n:ℤ))
  have hb := zpow_nonneg (childScale_pos m t).le (1-(n:ℤ))
  have hC := couplingConstant_pos
  have hmul := mul_nonneg hC.le (add_nonneg hw hb)
  convert h.trans (le_add_of_nonneg_left hmul) using 1; ring

omit [CompleteSpace Y] in
theorem nodePerturbation_source_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m (t+1)) {n : ℕ} (hn : n ≤ 3) (Z : Space Y E H m (t+1)) :
    ‖iteratedFDeriv ℝ n (nodePerturbation (radius m K t) (width m t) (centers K d)) Z‖ ≤
      (8*profileConstant) * (width m t)^(1-(n:ℤ)) := by
  have hw := width_pos m t
  have hs := scale_separation m hK t
  have h := (nodePerturbation_scaledJets (F := Space Y E H m t) hw
    (by linarith : width m t ≤ radius m K t) (centers K d)).norm_le n hn Z
  rw [zpow_sub₀ hw.ne', zpow_one, zpow_natCast, ← mul_div_assoc]
  exact h

end GradientHessian.HigherHierarchy
