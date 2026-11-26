import GradientHessian.HigherHierarchyRegularityMajorants

/-! Uniform bounds for the actual recursive residual. The proof derives
every step from the literal node; no derivative-recurrence hypothesis occurs. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open CouplingCost
universe u

def jetMajorant (K : ℝ) (m t : ℕ) : ℕ → ℝ
  | 0 => residualValueBound m K t
  | 1 => firstMajorant K m t
  | 2 => secondMajorant K m t
  | 3 => thirdMajorant K t
  | _ => 0

theorem jetMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (m t n : ℕ) (hn : n ≤ 3) :
    0 ≤ jetMajorant K m t n := by
  interval_cases n
  · exact add_nonneg (energy_pos m hK t).le (mul_nonneg Leaf.leafJetConstant_pos.le (by positivity))
  · exact firstMajorant_nonneg hK m t
  · exact secondMajorant_nonneg hK m t
  · exact thirdMajorant_nonneg hK t

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)] [∀ t, CompleteSpace (H t)]

theorem residual_value_jet_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ)
    (d : Data Y E H m t) (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 0 (residual K t d) Z‖ ≤ residualValueBound m K t := by
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
  have h := residual_global_bounds hK t d hd Z
  have hJ := jetMajorant_nonneg (by linarith : 0 ≤ K) m t 0 (by norm_num)
  exact abs_le.mpr ⟨by dsimp [residualValueBound]; linarith, h.2.trans hJ⟩

theorem residual_jet_majorant {K : ℝ} (hK : 16 ≤ K) :
    ∀ t (d : Data Y E H m t), Valid Y E H m t d →
      ∀ n, n ≤ 3 → ∀ Z, ‖iteratedFDeriv ℝ n (residual K t d) Z‖ ≤ jetMajorant K m t n := by
  have hK0 : 0 < K := by linarith
  have hF := FirstHeight.firstDerivativeConstant_pos.le
  have hA := (amplitudeConstant_pos hK0.le).le
  have hC := crossConstant_pos.le
  have hC1 := (firstConstant_pos hK0.le).le
  have hC2 := (secondConstant_pos hK0.le).le
  have hbase1 : FirstHeight.firstDerivativeConstant ≤ firstConstant K := by unfold firstConstant; linarith
  have hbase2 : FirstHeight.firstDerivativeConstant ≤ secondConstant K := by
    unfold secondConstant
    have h := mul_nonneg hC (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC1)
    linarith
  have hbase3 : FirstHeight.firstDerivativeConstant ≤ thirdConstant K := by
    unfold thirdConstant
    have h := mul_nonneg hC (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 18) hC2)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC1))
    linarith
  intro t
  induction t with
  | zero =>
    intro d hd n hn Z
    by_cases hn0 : n = 0
    · subst n; exact residual_value_jet_bound hK 0 d hd Z
    have hn1 : 1 ≤ n := by omega
    have hs := FirstHeight.sourceResidual_derivative_bound d hd Z (by omega : 1 ≤ n) hn
    interval_cases n
    · norm_num [jetMajorant, firstMajorant] at ⊢
      norm_num only [Nat.reduceSub] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right hbase1 (sq_nonneg _))
    · norm_num [jetMajorant, secondMajorant] at ⊢
      norm_num only [Nat.reduceSub, pow_one] at hs
      exact hs.trans (mul_le_mul_of_nonneg_right hbase2 (by positivity))
    · norm_num only [Nat.sub_self, pow_zero, mul_one] at hs
      simpa only [jetMajorant, thirdMajorant, Finset.range_zero, Finset.sum_empty, add_zero] using hs.trans hbase3
  | succ t ih =>
    intro d hd n hn Z
    by_cases hn0 : n = 0
    · subst n; exact residual_value_jet_bound hK (t+1) d hd Z
    have hn1 : 1 ≤ n := by omega
    let f : Fin 8 → Space Y E H m t → ℝ := fun i => residual K t (d.children i)
    have hf (i : Fin 8) : ContDiff ℝ 3 (f i) := residual_contDiff hK0 t (d.children i)
    have hAn := jetMajorant_nonneg hK0.le m t
    have hD (i : Fin 8) (j : ℕ) (hj : j ≤ 3) (x : Space Y E H m t) :
        ‖iteratedFDeriv ℝ j (f i) x‖ ≤ jetMajorant K m t j := ih (d.children i) (hd.1 i) j hj x
    have hnew (j : ℕ) (hj : j ≤ 3) :
        ‖iteratedFDeriv ℝ j (residual K (t+1) d) Z‖ ≤
          ‖iteratedFDeriv ℝ j (selectedChildren (width m t) (centers K d) f) Z‖ +
          (offsetConstant*spacing m K t + 27*couplingConstant*radius m K t +
            8*profileConstant*width m t)/width m t^j := by
      exact nodeResidual_derivative_bound (spacing_pos m hK0.le t).le
        (width_pos m t) (childScale_pos m t) (scale_separation m hK t)
        (childScale_comparable m t).2 (by linarith [(childScale_comparable m t).1])
        (baseline K t) (fun i => scalar K t (d.children i)) (fun i => outgoing K t (d.children i))
        (baseline_contDiff hK0 t) (fun i => scalar_contDiff hK0 t (d.children i))
        (fun i => outgoing_scaledJets hK0 t (d.children i) (hd.1 i))
        (centers K d) (centers_norm hK0.le d hd) Z hj
    interval_cases n
    · have hs := selectedChildren_first_bound (width_pos m t) (centers K d) f hf
        (jetMajorant K m t) hAn hD Z
      have hr : ‖iteratedFDeriv ℝ 1 (residual K (t+1) d) Z‖ ≤
          firstMajorant K m t + newAmplitude m K t/width m t := by
        apply ((hnew 1 (by norm_num)).trans (add_le_add_right hs _)).trans_eq
        simp only [jetMajorant, newAmplitude, pow_one]
        ring
      exact hr.trans ((add_le_add_left (first_increment_covers hK0.le m t) _).trans_eq
        (firstMajorant_succ K m t).symm)
    · have hs := selectedChildren_second_bound (width_pos m t) (centers K d) f hf
        (jetMajorant K m t) hAn hD Z
      have hr := (hnew 2 (by norm_num)).trans (add_le_add_right hs _)
      have hex : (secondMajorant K m t + 16*weightConstant*firstMajorant K m t/width m t +
          8*weightConstant*residualValueBound m K t/width m t^2) +
          (offsetConstant*spacing m K t + 27*couplingConstant*radius m K t +
            8*profileConstant*width m t)/width m t^2 =
          secondMajorant K m t + 16*weightConstant*firstMajorant K m t/width m t +
            newAmplitude m K t/width m t^2 := by unfold newAmplitude; ring
      simp only [jetMajorant] at hr
      rw [hex] at hr
      have hcross : 16*weightConstant*firstMajorant K m t/width m t ≤
          crossConstant*firstMajorant K m t/width m t := by
        apply div_le_div_of_nonneg_right _ (width_pos m t).le
        apply mul_le_mul_of_nonneg_right _ (firstMajorant_nonneg hK0.le m t)
        unfold crossConstant
        linarith [weightConstant_pos]
      have hi := second_increment_covers hK0.le m t
      change _ ≤ secondMajorant K m (t+1)
      rw [secondMajorant_succ]
      linarith
    · have hs := selectedChildren_third_bound (width_pos m t) (centers K d) f hf
        (jetMajorant K m t) hAn hD Z
      have hr := (hnew 3 (by norm_num)).trans (add_le_add_right hs _)
      have hi := third_increment_covers hK0.le m t
      change _ ≤ thirdMajorant K (t+1)
      rw [thirdMajorant_succ]
      have heq : (thirdMajorant K t + 24*weightConstant*secondMajorant K m t/width m t +
          24*weightConstant*firstMajorant K m t/width m t^2 +
          8*weightConstant*residualValueBound m K t/width m t^3) +
          (offsetConstant*spacing m K t + 27*couplingConstant*radius m K t +
            8*profileConstant*width m t)/width m t^3 =
          thirdMajorant K t + (crossConstant*secondMajorant K m t/width m t +
            crossConstant*firstMajorant K m t/width m t^2 + newAmplitude m K t/width m t^3) := by
        unfold crossConstant newAmplitude
        ring
      simp only [jetMajorant] at hr
      rw [heq] at hr
      exact hr.trans (add_le_add_left hi _)

theorem residual_first_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 1 (residual K t d) Z‖ ≤
      4*firstConstant K*((m+1:ℝ)^2+(8/3)^t) :=
  (residual_jet_majorant hK t d hd 1 (by norm_num) Z).trans
    (firstMajorant_bound (by linarith) m t)

theorem residual_second_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 2 (residual K t d) Z‖ ≤ 18*secondConstant K*(m+1) :=
  (residual_jet_majorant hK t d hd 2 (by norm_num) Z).trans
    (secondMajorant_bound (by linarith) m t)

theorem residual_third_bound {K : ℝ} (hK : 16 ≤ K) (t : ℕ) (d : Data Y E H m t)
    (hd : Valid Y E H m t d) (Z : Space Y E H m t) :
    ‖iteratedFDeriv ℝ 3 (residual K t d) Z‖ ≤ 9*thirdConstant K :=
  (residual_jet_majorant hK t d hd 3 (by norm_num) Z).trans
    (thirdMajorant_bound (by linarith) t)

end GradientHessian.HigherHierarchy
