import FullJet.TaylorPerturbation

open scoped BigOperators

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

noncomputable def jetValueError (J K : JetPacket p E) (r : ℝ) : ℝ :=
  ∑ j : Fin p, ((j.val + 1).factorial : ℝ)⁻¹ * ‖J j.succ - K j.succ‖ * r ^ (j.val + 1)

noncomputable def jetGradientError (J K : JetPacket p E) (r : ℝ) : ℝ :=
  ∑ j : Fin p, (j.val.factorial : ℝ)⁻¹ * ‖J j.succ - K j.succ‖ * r ^ j.val

theorem jetValueError_bound (J K : JetPacket p E) (h : E) (r : ℝ) (hh : ‖h‖ ≤ r) :
    ‖jetTaylor J h - jetTaylor K h‖ ≤ jetValueError J K r := by
  apply (jetTaylor_perturbation J K h).trans
  apply Finset.sum_le_sum
  intro j _
  gcongr

theorem jetGradientError_bound (J K : JetPacket p E) (h : E) (r : ℝ) (hh : ‖h‖ ≤ r) :
    ‖fderiv ℝ (jetTaylor J) h - fderiv ℝ (jetTaylor K) h‖ ≤ jetGradientError J K r := by
  apply (jetTaylor_fderiv_perturbation J K h).trans
  apply Finset.sum_le_sum
  intro j _
  gcongr

theorem norm_regularization_fderiv (hp : 0 < p) (M : ℝ) (hM : 0 ≤ M) (h : E) :
    ‖(M / ((p + 1).factorial : ℝ)) • fderiv ℝ (fun y : E => ‖y‖ ^ (p + 1)) h‖ =
      M / (p.factorial : ℝ) * ‖h‖ ^ p := by
  have hs := norm_smul (M / ((p + 1).factorial : ℝ))
    (fderiv ℝ (fun y : E => ‖y‖ ^ (p + 1)) h)
  rw [hs, Real.norm_of_nonneg (by positivity), normPower_fderiv_norm hp,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem regularizedJetStep_polynomial_gradient [FiniteDimensional ℝ E]
    (hp : 0 < p) (J : JetPacket p E) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hinterior : ‖regularizedJetStep J M r hr‖ < r) :
    ‖fderiv ℝ (jetTaylor J) (regularizedJetStep J M r hr)‖ ≤ M / (p.factorial : ℝ) * r ^ p := by
  have hz := regularizedJetStep_fderiv_zero J M r hr hinterior
  rw [regularizedJetModel_fderiv hp] at hz
  have heq := eq_neg_of_add_eq_zero_left hz
  rw [heq, norm_neg, norm_regularization_fderiv hp M hM]
  gcongr

/-- At an interior step, a bound on the true Taylor gradient remainder and
the actual packet error gives a stationarity certificate. -/
theorem regularizedJetStep_stationarity [FiniteDimensional ℝ E]
    (hp : 0 < p) (f : E → ℝ) (x : E) (J K : JetPacket p E)
    (M r R : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hinterior : ‖regularizedJetStep J M r hr‖ < r)
    (hremainder : ‖fderiv ℝ f (x + regularizedJetStep J M r hr) -
      fderiv ℝ (jetTaylor K) (regularizedJetStep J M r hr)‖ ≤ R) :
    ‖fderiv ℝ f (x + regularizedJetStep J M r hr)‖ ≤
      R + jetGradientError K J r + M / (p.factorial : ℝ) * r ^ p := by
  let h := regularizedJetStep J M r hr
  have hb := jetGradientError_bound K J h r (regularizedJetStep_spec J M r hr).1
  have hc := regularizedJetStep_polynomial_gradient hp J M r hM hr hinterior
  calc
    _ ≤ ‖fderiv ℝ f (x + h) - fderiv ℝ (jetTaylor K) h‖ +
      ‖fderiv ℝ (jetTaylor K) h - fderiv ℝ (jetTaylor J) h‖ +
      ‖fderiv ℝ (jetTaylor J) h‖ := by
        calc
          _ = ‖(fderiv ℝ f (x + h) - fderiv ℝ (jetTaylor K) h) +
            (fderiv ℝ (jetTaylor K) h - fderiv ℝ (jetTaylor J) h) +
            fderiv ℝ (jetTaylor J) h‖ := by congr 1; abel
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ _ := add_le_add (add_le_add hremainder hb) hc

/-- Model minimality turns the true Taylor value remainder and tensor errors
into a quantitative decrease of the actual objective. -/
theorem regularizedJetStep_descent [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : E) (J K : JetPacket p E) (M r R : ℝ) (hr : 0 ≤ r)
    (hremainder : f (x + regularizedJetStep J M r hr) - f x -
      jetTaylor K (regularizedJetStep J M r hr) ≤ R * ‖regularizedJetStep J M r hr‖ ^ (p + 1)) :
    f (x + regularizedJetStep J M r hr) ≤ f x -
      (M / ((p + 1).factorial : ℝ) - R) * ‖regularizedJetStep J M r hr‖ ^ (p + 1) +
        jetValueError K J r := by
  have hmin := regularizedJetStep_value_nonpos J M r hr
  have he := jetValueError_bound K J (regularizedJetStep J M r hr) r
    (regularizedJetStep_spec J M r hr).1
  have he' := (le_abs_self (jetTaylor K (regularizedJetStep J M r hr) -
    jetTaylor J (regularizedJetStep J M r hr))).trans he
  unfold regularizedJetModel at hmin
  nlinarith only [hmin, he', hremainder]

theorem regularizedJetStep_boundary_descent [FiniteDimensional ℝ E]
    (f : E → ℝ) (x : E) (J K : JetPacket p E) (M r R : ℝ) (hr : 0 ≤ r)
    (hboundary : ‖regularizedJetStep J M r hr‖ = r)
    (hR : R ≤ M / (2 * ((p + 1).factorial : ℝ)))
    (herr : jetValueError K J r ≤ M / (4 * ((p + 1).factorial : ℝ)) * r ^ (p + 1))
    (hremainder : f (x + regularizedJetStep J M r hr) - f x -
      jetTaylor K (regularizedJetStep J M r hr) ≤ R * ‖regularizedJetStep J M r hr‖ ^ (p + 1)) :
    f (x + regularizedJetStep J M r hr) ≤ f x -
      M / (4 * ((p + 1).factorial : ℝ)) * r ^ (p + 1) := by
  have hd := regularizedJetStep_descent f x J K M r R hr hremainder
  rw [hboundary] at hd
  have hR' := mul_le_mul_of_nonneg_right hR (pow_nonneg hr (p + 1))
  have heq : M / ((p + 1).factorial : ℝ) = 4 * (M / (4 * ((p + 1).factorial : ℝ))) := by ring
  have heq' : M / (2 * ((p + 1).factorial : ℝ)) = 2 * (M / (4 * ((p + 1).factorial : ℝ))) := by ring
  rw [heq] at hd
  rw [heq'] at hR'
  nlinarith only [hd, hR', herr]

end FullJet
