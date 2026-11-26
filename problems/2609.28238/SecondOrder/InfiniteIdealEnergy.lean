import SecondOrder.InfiniteSigns
import SecondOrder.PhysicalPrefix

open MeasureTheory Filter
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- The cumulative quantities whose uniform finite-time bounds imply
infinite-horizon bounds. -/
inductive IdealStatistic
  | gradientMoves | curvatureMoves | gradientEnergy | curvatureEnergy | totalMoves
  deriving DecidableEq

def IdealStatistic.value (a : IdealStatistic) {d : ℕ} (z : IdealState d) : ℝ :=
  match a with
  | .gradientMoves => z.gradientMoves
  | .curvatureMoves => z.curvatureMoves
  | .gradientEnergy => z.gradientEnergy
  | .curvatureEnergy => z.curvatureEnergy
  | .totalMoves => stateMoves z

def IdealStatistic.bound (a : IdealStatistic) (P : Parameters) (ν τ γ : ℝ) : ℝ :=
  match a with
  | .gradientMoves => P.gap * P.gradientLip / τ^2
  | .curvatureMoves => 16 * P.gap / (3 * γ * (curvatureRadius P.hessianHolder ν γ)^2)
  | .gradientEnergy => P.gap / P.gradientLip
  | .curvatureEnergy => 16 * P.gap / (3 * γ)
  | .totalMoves => idealMoveBudget P ν τ γ

theorem IdealStatistic.measurable_value (a : IdealStatistic) {d : ℕ} :
    Measurable (a.value (d := d)) := by
  have hz := state_measurable_fields.mp (measurable_id (α := IdealState d))
  cases a with
  | gradientMoves => exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hz.2.2.1
  | curvatureMoves => exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hz.2.2.2.1
  | gradientEnergy => exact hz.2.2.2.2.1
  | curvatureEnergy => exact hz.2.2.2.2.2
  | totalMoves =>
    exact (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (hz.2.2.1.add hz.2.2.2.1)

theorem IdealStatistic.step_mono (a : IdealStatistic) {d : ℕ} (L s : ℝ)
    (z : IdealState d) (move : IdealMove d) (b : Bool) :
    a.value z ≤ a.value (idealStep L s z move b) := by
  cases a with
  | gradientEnergy =>
    change z.gradientEnergy ≤ (idealStep L s z move b).gradientEnergy
    rw [idealStep_gradientEnergy]
    exact le_add_of_nonneg_right (sq_nonneg _)
  | curvatureEnergy =>
    change z.curvatureEnergy ≤ (idealStep L s z move b).curvatureEnergy
    rw [idealStep_curvatureEnergy]
    exact le_add_of_nonneg_right (sq_nonneg _)
  | totalMoves =>
    change (stateMoves z : ℝ) ≤ (stateMoves (idealStep L s z move b) : ℝ)
    exact_mod_cast idealStep_moves_mono L s z move b
  | gradientMoves =>
    cases hr : z.running <;> cases move <;> simp [value, idealStep, hr]
  | curvatureMoves =>
    cases hr : z.running <;> cases move <;> simp [value, idealStep, hr]

theorem IdealStatistic.path_mono (a : IdealStatistic) {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool) :
    Monotone (fun t => a.value (idealPath L s policy w t)) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [idealPath_succ]
  exact a.step_mono L s _ _ _

theorem IdealStatistic.run_nonnegative (a : IdealStatistic) {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (M : ℕ) (w : Fin M → Bool) :
    0 ≤ a.value (idealRun L s policy M w) := by
  have hn := idealRun_energy_nonnegative L s policy M w
  cases a with
  | gradientMoves => exact Nat.cast_nonneg _
  | curvatureMoves => exact Nat.cast_nonneg _
  | gradientEnergy => exact hn.1
  | curvatureEnergy => exact hn.2
  | totalMoves => exact Nat.cast_nonneg _

/-- Total count or total squared path length. Extended nonnegative reals
retain the possibility of an infinite execution until finiteness is proved. -/
def infiniteIdealTotal (a : IdealStatistic) {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool) : ℝ≥0∞ :=
  ⨆ t : ℕ, ENNReal.ofReal (a.value (idealPath L s policy w t))

theorem idealPath_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ}
    (L s : ℝ) {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy) (t : ℕ) :
    Measurable (fun w : Ξ × (ℕ → Bool) => idealPath L s (policy w.1) w.2 t) :=
  (idealRun_measurable L s hm t).comp
    (measurable_fst.prodMk ((infiniteSignPrefix_measurable t).comp measurable_snd))

theorem infiniteIdealTotal_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d : ℕ}
    (a : IdealStatistic) (L s : ℝ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy) :
    Measurable (fun w : Ξ × (ℕ → Bool) => infiniteIdealTotal a L s (policy w.1) w.2) :=
  Measurable.iSup (fun t =>
    (a.measurable_value.comp (idealPath_measurable L s hm t)).ennreal_ofReal)

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

theorem CommonLoss.idealRun_statistic_bound (h : CommonLoss μ P ν F f)
    (a : IdealStatistic) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (policy : IdealPolicy d)
    (hv : ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ policy)
    (M : ℕ) :
    uniformMean (fun w => a.value
      (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy M w)) ≤
        a.bound P ν τ γ := by
  have hb := h.idealRun_statistics hτ hγ policy hv M
  cases a with
  | gradientMoves => exact hb.1
  | curvatureMoves => exact hb.2.1
  | gradientEnergy => exact hb.2.2.1
  | curvatureEnergy => exact hb.2.2.2
  | totalMoves => exact h.idealRun_total_moves hτ hγ policy hv M

/-- Monotone convergence on one probability space proves all four path
energy/count estimates, plus the total-move bound, without assuming halting. -/
theorem CommonLoss.infiniteIdealTotal_bound (h : CommonLoss μ P ν F f)
    (a : IdealStatistic) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x)) :
    (∫⁻ w, infiniteIdealTotal a P.gradientLip (curvatureRadius P.hessianHolder ν γ)
      (policy w.1) w.2 ∂η.prod infiniteSignLaw) ≤ ENNReal.ofReal (a.bound P ν τ γ) := by
  unfold infiniteIdealTotal
  rw [lintegral_iSup (μ := η.prod infiniteSignLaw)
    (f := fun t w => ENNReal.ofReal (a.value
      (idealPath P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 t))) (fun t =>
    (a.measurable_value.comp
      (idealPath_measurable P.gradientLip (curvatureRadius P.hessianHolder ν γ) hm t)).ennreal_ofReal)
    (fun i j hij w => ENNReal.ofReal_le_ofReal (a.path_mono _ _ _ _ hij))]
  apply iSup_le
  intro M
  let X : Ξ × (Fin M → Bool) → ℝ := fun w =>
    a.value (idealRun P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) M w.2)
  have hX : Measurable X := a.measurable_value.comp (idealRun_measurable _ _ hm M)
  have hn : ∀ w, 0 ≤ X w := fun w => a.run_nonnegative _ _ _ _ _
  have hb := mixed_sign_mean_bound (η := η) hX hn
    (fun x => h.idealRun_statistic_bound a hτ hγ (policy x) (hv x) M)
  change (∫⁻ w, ENNReal.ofReal (X (w.1, infiniteSignPrefix M w.2)) ∂η.prod infiniteSignLaw) ≤ _
  rw [(mixedSignPrefix_measurePreserving η M).lintegral_comp hX.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hb.1 (Eventually.of_forall hn)]
  exact ENNReal.ofReal_le_ofReal hb.2

theorem CommonLoss.infiniteIdealTotal_finite_ae (h : CommonLoss μ P ν F f)
    (a : IdealStatistic) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x)) :
    ∀ᵐ w ∂η.prod infiniteSignLaw,
      infiniteIdealTotal a P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 < ∞ :=
  ae_lt_top (infiniteIdealTotal_measurable a _ _ hm)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.infiniteIdealTotal_bound a hτ hγ hm hv))

end
end SecondOrder
