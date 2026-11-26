import SecondOrder.IdealBounds

open MeasureTheory Filter

namespace SecondOrder
noncomputable section

variable {Ξ : Type*} [MeasurableSpace Ξ] {η : Measure Ξ} [IsProbabilityMeasure η]

/-- A uniformly bounded conditional mean supplies product integrability.
No finite-support restriction or assumed integrability of the full experiment
is imposed on the external random tape. -/
theorem mixed_sign_mean_bound {M : ℕ} {X : Ξ × (Fin M → Bool) → ℝ}
    (hX : Measurable X) (hn : ∀ z, 0 ≤ X z) {B : ℝ}
    (hb : ∀ x, uniformMean (fun w => X (x,w)) ≤ B) :
    Integrable X (η.prod (signLaw M)) ∧ (∫ z, X z ∂η.prod (signLaw M)) ≤ B := by
  have hnorm (z) : ‖X z‖ = X z := Real.norm_of_nonneg (hn z)
  have hin : Integrable (fun x => ∫ w, ‖X (x,w)‖ ∂signLaw M) η := by
    apply (integrable_const B).mono'
      hX.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (integral_nonneg (fun w => norm_nonneg _))]
    simp_rw [hnorm, integral_signLaw]
    exact hb x
  have hi : Integrable X (η.prod (signLaw M)) :=
    (integrable_prod_iff hX.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall (fun _ => Integrable.of_finite), hin⟩
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ _ : Ξ, B ∂η := integral_mono_ae hi.integral_prod_left (integrable_const B)
      (Eventually.of_forall (fun x => by simpa only [integral_signLaw] using hb x))
    _ = B := by simp

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealMixture_total_moves (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : Ξ → IdealPolicy d)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x))
    (M : ℕ)
    (hm : Measurable (fun w : Ξ × (Fin M → Bool) =>
      let z := idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2
      ((z.gradientMoves+z.curvatureMoves : ℕ) : ℝ))) :
    let X := fun w : Ξ × (Fin M → Bool) =>
      let z := idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2
      ((z.gradientMoves+z.curvatureMoves : ℕ) : ℝ)
    Integrable X (η.prod (signLaw M)) ∧
      (∫ w, X w ∂η.prod (signLaw M)) ≤ idealMoveBudget P ν τ γ :=
  mixed_sign_mean_bound hm (fun _ => Nat.cast_nonneg _)
    (fun x => h.idealRun_total_moves hτ hγ (policy x) (hv x) M)

theorem CommonLoss.idealMixture_energy (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : Ξ → IdealPolicy d)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x))
    (M : ℕ)
    (hmg : Measurable (fun w : Ξ × (Fin M → Bool) =>
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).gradientEnergy))
    (hmc : Measurable (fun w : Ξ × (Fin M → Bool) =>
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).curvatureEnergy)) :
    let z := fun w : Ξ × (Fin M → Bool) =>
      idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2
    (Integrable (fun w => (z w).gradientEnergy) (η.prod (signLaw M)) ∧
      (∫ w, (z w).gradientEnergy ∂η.prod (signLaw M)) ≤ P.gap/P.gradientLip) ∧
    (Integrable (fun w => (z w).curvatureEnergy) (η.prod (signLaw M)) ∧
      (∫ w, (z w).curvatureEnergy ∂η.prod (signLaw M)) ≤ 16*P.gap/(3*γ)) := by
  refine ⟨mixed_sign_mean_bound hmg (fun w => (idealRun_energy_nonnegative _ _ _ _ _).1) ?_,
    mixed_sign_mean_bound hmc (fun w => (idealRun_energy_nonnegative _ _ _ _ _).2) ?_⟩
  · intro x
    exact (h.idealRun_statistics hτ hγ (policy x) (hv x) M).2.2.1
  · intro x
    exact (h.idealRun_statistics hτ hγ (policy x) (hv x) M).2.2.2

theorem CommonLoss.idealMixture_physical_cap (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : Ξ → IdealPolicy d)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x))
    {M : ℕ} (hM : 0 < M)
    (hm : Measurable (fun w : Ξ × (Fin M → Bool) =>
      let z := idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2
      ((z.gradientMoves+z.curvatureMoves : ℕ) : ℝ))) :
    (η.prod (signLaw M)) {w |
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2).running = true}
      ≤ ENNReal.ofReal (idealMoveBudget P ν τ γ/(M : ℝ)) := by
  have hi := h.idealMixture_total_moves (η := η) hτ hγ policy hv M hm
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hp := (hi.1.div_const (M : ℝ)).measure_le_integral
    (Eventually.of_forall (fun w => by positivity))
    (s := {w | (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ)
      (policy w.1) M w.2).running = true}) (fun w hw => by
        have hc := idealRun_running_count P.gradientLip (curvatureRadius P.hessianHolder ν γ)
          (policy w.1) M w.2 hw
        dsimp only
        rw [hc, div_self hMr.ne'])
  refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div]
  exact div_le_div_of_nonneg_right hi.2 hMr.le

end
end SecondOrder
