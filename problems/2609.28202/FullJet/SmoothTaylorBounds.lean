import FullJet.LineTaylor
import FullJet.ModelStepBounds

open scoped BigOperators ContDiff

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ℕ}

theorem lineTaylor_eq_jetTaylor (f : E → ℝ) (p : ℕ) (x h : E) :
    lineTaylor f p x h = f x + jetTaylor (fullJet p f x) h := by
  rw [lineTaylor, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    iteratedFDeriv_zero_apply, one_smul]
  rfl

theorem actual_jetTaylor_value_remainder {f : E → ℝ}
    (hf : ContDiff ℝ p f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖)
    (x h : E) : ‖f (x + h) - f x - jetTaylor (fullJet p f x) h‖ ≤ L * ‖h‖ ^ (p + 1) := by
  have hb := lineTaylor_remainder hf L hL hlip x h
  rwa [lineTaylor_eq_jetTaylor, ← sub_sub] at hb

theorem iteratedFDeriv_fderiv_sub_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (k : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ k (fderiv ℝ f) x - iteratedFDeriv ℝ k (fderiv ℝ f) y‖ =
      ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  exact ((continuousMultilinearCurryRightEquiv' ℝ k E F).symm.dist_map
    (iteratedFDeriv ℝ k (fderiv ℝ f) x) (iteratedFDeriv ℝ k (fderiv ℝ f) y)).symm

/-- The gradient is approximated directly in its operator norm. This does
not require choosing coordinates or a basis of the ambient space. -/
theorem actual_gradientTaylor_remainder {f : E → ℝ} {k : ℕ}
    (hf : ContDiff ℝ (k + 1) f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ ≤ L * ‖x - y‖)
    (x h : E) : ‖fderiv ℝ f (x + h) - lineTaylor (fderiv ℝ f) k x h‖ ≤ L * ‖h‖ ^ (k + 1) := by
  apply lineTaylor_remainder (hf.fderiv_right (m := k) (by simp)) L hL
  intro a b
  rw [iteratedFDeriv_fderiv_sub_norm]
  exact hlip a b

theorem average_contDiff {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i)) :
    ContDiff ℝ p (average f) := by
  exact contDiff_const.mul (ContDiff.sum fun i _ => hf i)

theorem average_iteratedFDeriv {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i))
    (r : ℕ) (hr : r ≤ p) (x : E) :
    iteratedFDeriv ℝ r (average f) x = (n : ℝ)⁻¹ • ∑ i, iteratedFDeriv ℝ r (f i) x := by
  have hs : ∀ i, ContDiff ℝ r (f i) := fun i => (hf i).of_le (by exact_mod_cast hr)
  change iteratedFDeriv ℝ r (fun y => (n : ℝ)⁻¹ • (∑ i, f i y)) x = _
  rw [iteratedFDeriv_const_smul_apply' (ContDiff.sum (fun i _ => hs i)).contDiffAt,
    iteratedFDeriv_sum (fun i _ => hs i)]
  simp only [Finset.sum_apply]

theorem average_fullJet {f : Fin n → E → ℝ} (hf : ∀ i, ContDiff ℝ p (f i)) (x : E) :
    fullJet p (average f) x = (n : ℝ)⁻¹ • ∑ i, fullJet p (f i) x := by
  funext r
  simpa only [fullJet, Pi.smul_apply, Finset.sum_apply] using
    average_iteratedFDeriv hf r.val (Nat.le_of_lt_succ r.isLt) x

theorem average_derivative_lipschitz {f : Fin n → E → ℝ} (hn : 0 < n)
    (hf : ∀ i, ContDiff ℝ p (f i)) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ i x y, ‖iteratedFDeriv ℝ p (f i) x - iteratedFDeriv ℝ p (f i) y‖ ≤ L * ‖x - y‖)
    (x y : E) : ‖iteratedFDeriv ℝ p (average f) x - iteratedFDeriv ℝ p (average f) y‖ ≤ L * ‖x - y‖ := by
  rw [average_iteratedFDeriv hf p le_rfl, average_iteratedFDeriv hf p le_rfl,
    ← smul_sub, ← Finset.sum_sub_distrib]
  have hnorm := norm_smul (n : ℝ)⁻¹
    (∑ i, (iteratedFDeriv ℝ p (f i) x - iteratedFDeriv ℝ p (f i) y))
  rw [hnorm, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, L * ‖x - y‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hlip i x y)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

theorem Admissible.value_remainder {Δ L : ℝ} {f : Fin n → E → ℝ}
    (hf : Admissible p n Δ L f) (hL : 0 ≤ L) (x h : E) :
    ‖average f (x + h) - average f x - jetTaylor (fullJet p (average f) x) h‖ ≤
      L * ‖h‖ ^ (p + 1) :=
  actual_jetTaylor_value_remainder (average_contDiff hf.smooth) L hL
    (average_derivative_lipschitz hf.n_pos hf.smooth L hL hf.derivative_lipschitz) x h

theorem Admissible.model_step_descent [FiniteDimensional ℝ E]
    {Δ L : ℝ} {f : Fin n → E → ℝ} (hf : Admissible p n Δ L f) (hL : 0 ≤ L)
    (x : E) (J : JetPacket p E) (M r : ℝ) (hr : 0 ≤ r) :
    average f (x + regularizedJetStep J M r hr) ≤ average f x -
      (M / ((p + 1).factorial : ℝ) - L) * ‖regularizedJetStep J M r hr‖ ^ (p + 1) +
        jetValueError (fullJet p (average f) x) J r := by
  apply regularizedJetStep_descent (average f) x J (fullJet p (average f) x) M r L hr
  exact (le_abs_self _).trans (hf.value_remainder hL x _)

end FullJet
