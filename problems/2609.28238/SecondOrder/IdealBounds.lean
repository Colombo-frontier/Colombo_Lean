import SecondOrder.IdealProgress
import SecondOrder.MixedSigns

open MeasureTheory

namespace SecondOrder
noncomputable section

theorem split_weighted_bound {a b u v B : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : a*u+b*v ≤ B) : u ≤ B/a ∧ v ≤ B/b := by
  constructor
  · apply (le_div_iff₀ ha).mpr
    nlinarith [mul_nonneg hb.le hv]
  · apply (le_div_iff₀ hb).mpr
    nlinarith [mul_nonneg ha.le hu]

def idealMoveBudget (P : Parameters) (ν τ γ : ℝ) : ℝ :=
  P.gap/(τ^2/P.gradientLip)+P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2/16)

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {P : Parameters} {ν : ℝ}
  {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- Uniform finite-horizon bounds, with the manuscript's constants made explicit.
This does not yet assert the infinite-horizon monotone-convergence conclusion. -/
theorem CommonLoss.idealRun_statistics (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy)
    (t : ℕ) :
    let z := idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy t
    uniformMean (fun w => (z w).gradientMoves : (Fin t → Bool) → ℝ) ≤ P.gap*P.gradientLip/τ^2 ∧
    uniformMean (fun w => (z w).curvatureMoves : (Fin t → Bool) → ℝ) ≤
      16*P.gap/(3*γ*(curvatureRadius P.hessianHolder ν γ)^2) ∧
    uniformMean (fun w => (z w).gradientEnergy) ≤ P.gap/P.gradientLip ∧
    uniformMean (fun w => (z w).curvatureEnergy) ≤ 16*P.gap/(3*γ) := by
  dsimp only
  have hc := h.idealRun_countWork_bound hτ.le hγ policy hv t
  have he := h.idealRun_energyWork_bound hτ.le hγ policy hv t
  simp only [countWork, uniformMean_add, uniformMean_mul] at hc
  simp only [energyWork, uniformMean_add, uniformMean_mul] at he
  have hL := P.gradientLip_pos
  have hs := curvatureRadius_pos (ν := ν) P.hessianHolder_pos hγ
  have hcn := split_weighted_bound (by positivity) (by positivity)
    (uniformMean_nonneg (fun w => Nat.cast_nonneg _))
    (uniformMean_nonneg (fun w => Nat.cast_nonneg _)) hc
  have hen := split_weighted_bound hL (by positivity)
    (uniformMean_nonneg (fun w => (idealRun_energy_nonnegative _ _ policy t w).1))
    (uniformMean_nonneg (fun w => (idealRun_energy_nonnegative _ _ policy t w).2)) he
  convert And.intro hcn.1 (And.intro hcn.2 hen) using 1 <;> field_simp <;> ring

theorem CommonLoss.idealRun_total_moves (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy)
    (t : ℕ) :
    uniformMean (fun w =>
      let z := idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy t w
      ((z.gradientMoves+z.curvatureMoves : ℕ) : ℝ)) ≤ idealMoveBudget P ν τ γ := by
  have hc := h.idealRun_countWork_bound hτ.le hγ policy hv t
  simp only [countWork, uniformMean_add, uniformMean_mul] at hc
  have hL := P.gradientLip_pos
  have hs := curvatureRadius_pos (ν := ν) P.hessianHolder_pos hγ
  have hn := split_weighted_bound (by positivity) (by positivity)
    (uniformMean_nonneg (fun w => Nat.cast_nonneg _))
    (uniformMean_nonneg (fun w => Nat.cast_nonneg _)) hc
  simpa only [Nat.cast_add, uniformMean_add, idealMoveBudget] using add_le_add hn.1 hn.2

/-- The physical-cap failure estimate uses actual running states and actual
counts, not a separately assumed stopping-time or count bound. -/
theorem CommonLoss.idealRun_physical_cap (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy)
    {M : ℕ} (hM : 0 < M) :
    signLaw M {w | (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w).running = true}
      ≤ ENNReal.ofReal (idealMoveBudget P ν τ γ/(M : ℝ)) := by
  let z := idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M
  let X : (Fin M → Bool) → ℝ := fun w => ((z w).gradientMoves+(z w).curvatureMoves : ℕ)
  have hX : Integrable X (signLaw M) := Integrable.of_finite
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hp := (hX.div_const (M : ℝ)).measure_le_integral
    (Filter.Eventually.of_forall (fun w => by dsimp [X]; positivity))
    (s := {w | (z w).running = true}) (fun w hw => by
      have hc := idealRun_running_count P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w hw
      dsimp [X, z]
      rw [hc, div_self hMr.ne'])
  refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [integral_div, integral_signLaw]
  exact div_le_div_of_nonneg_right (h.idealRun_total_moves hτ hγ policy hv M) hMr.le

end
end SecondOrder
