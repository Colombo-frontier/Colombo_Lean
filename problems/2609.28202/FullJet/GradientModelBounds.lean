import FullJet.FiniteJetSymmetry

open scoped BigOperators ContDiff

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ℕ}

theorem actual_tensor_diagonal_fderiv {f : E → ℝ} {m : ℕ}
    (hf : ContDiff ℝ (m + 1) f) (x h : E) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ (m + 1) f x (fun _ => y)) h =
      (m + 1 : ℝ) • iteratedFDeriv ℝ m (fderiv ℝ f) x (fun _ => h) := by
  rw [tensor_diagonal_fderiv]
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  change (∑ i : Fin (m + 1), iteratedFDeriv ℝ (m + 1) f x (Function.update (fun _ => h) i v)) = _
  simp only [iteratedFDeriv_single_slot hf x h v, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- The derivative of the actual scalar Taylor polynomial is exactly the
Taylor polynomial of the true gradient, under only finite C^p smoothness. -/
theorem actual_jetTaylor_fderiv {f : E → ℝ} {k : ℕ}
    (hf : ContDiff ℝ (k + 1) f) (x h : E) :
    fderiv ℝ (jetTaylor (fullJet (k + 1) f x)) h = lineTaylor (fderiv ℝ f) k x h := by
  rw [jetTaylor_fderiv]
  unfold lineTaylor
  apply Finset.sum_congr rfl
  intro j _
  change ((j.val + 1).factorial : ℝ)⁻¹ •
    fderiv ℝ (fun y => iteratedFDeriv ℝ (j.val + 1) f x (fun _ => y)) h = _
  have hj : ContDiff ℝ (j.val + 1) f := hf.of_le (by exact_mod_cast j.isLt)
  rw [actual_tensor_diagonal_fderiv hj, smul_smul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem actual_jetTaylor_gradient_remainder {f : E → ℝ}
    (hp : 0 < p) (hf : ContDiff ℝ p f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖iteratedFDeriv ℝ p f x - iteratedFDeriv ℝ p f y‖ ≤ L * ‖x - y‖)
    (x h : E) : ‖fderiv ℝ f (x + h) - fderiv ℝ (jetTaylor (fullJet p f x)) h‖ ≤ L * ‖h‖ ^ p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [actual_jetTaylor_fderiv hf]
  exact actual_gradientTaylor_remainder hf L hL hlip x h

theorem Admissible.gradient_remainder {Δ L : ℝ} {f : Fin n → E → ℝ}
    (hf : Admissible p n Δ L f) (hp : 0 < p) (hL : 0 ≤ L) (x h : E) :
    ‖fderiv ℝ (average f) (x + h) - fderiv ℝ (jetTaylor (fullJet p (average f) x)) h‖ ≤ L * ‖h‖ ^ p :=
  actual_jetTaylor_gradient_remainder hp (average_contDiff hf.smooth) L hL
    (average_derivative_lipschitz hf.n_pos hf.smooth L hL hf.derivative_lipschitz) x h

theorem Admissible.model_step_stationarity [FiniteDimensional ℝ E]
    {Δ L : ℝ} {f : Fin n → E → ℝ} (hf : Admissible p n Δ L f) (hp : 0 < p) (hL : 0 ≤ L)
    (x : E) (J : JetPacket p E) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hinterior : ‖regularizedJetStep J M r hr‖ < r) :
    ‖fderiv ℝ (average f) (x + regularizedJetStep J M r hr)‖ ≤
      (L + M / (p.factorial : ℝ)) * r ^ p + jetGradientError (fullJet p (average f) x) J r := by
  have hb := hf.gradient_remainder hp hL x (regularizedJetStep J M r hr)
  have hb' : ‖fderiv ℝ (average f) (x + regularizedJetStep J M r hr) -
      fderiv ℝ (jetTaylor (fullJet p (average f) x)) (regularizedJetStep J M r hr)‖ ≤ L * r ^ p := by
    apply hb.trans
    gcongr
  have hc := regularizedJetStep_stationarity hp (average f) x J (fullJet p (average f) x)
    M r (L * r ^ p) hM hr hinterior hb'
  exact hc.trans_eq (by ring)

end FullJet
