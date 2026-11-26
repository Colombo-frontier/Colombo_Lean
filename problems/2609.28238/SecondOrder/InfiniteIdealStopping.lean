import SecondOrder.InfiniteIdealEnergy
import SecondOrder.HolderCostScaling

open MeasureTheory Filter
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section

/-- The supremum definition is exactly the sum of squared gradient
displacements, even on paths which have not been assumed to halt. -/
theorem infiniteIdealTotal_gradientEnergy_eq_tsum {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool) :
    infiniteIdealTotal .gradientEnergy L s policy w =
      ∑' t : ℕ, ENNReal.ofReal (‖pathDrift L s policy w t‖^2) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  unfold infiniteIdealTotal
  congr 1
  funext M
  change ENNReal.ofReal (idealPath L s policy w M).gradientEnergy = _
  rw [← idealPath_gradientEnergy]
  exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)

theorem infiniteIdealTotal_curvatureEnergy_eq_tsum {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool) :
    infiniteIdealTotal .curvatureEnergy L s policy w =
      ∑' t : ℕ, ENNReal.ofReal (‖pathInnovation L s policy w t‖^2) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  unfold infiniteIdealTotal
  congr 1
  funext M
  change ENNReal.ofReal (idealPath L s policy w M).curvatureEnergy = _
  rw [← idealPath_curvatureEnergy]
  exact ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)

/-- On a stopped path, every infinite total is the corresponding
cumulative statistic at the stopping state. -/
theorem infiniteIdealTotal_eq_of_stopped {d : ℕ} (a : IdealStatistic) (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool) {M : ℕ}
    (hr : (idealPath L s policy w M).running = false) :
    infiniteIdealTotal a L s policy w = ENNReal.ofReal (a.value (idealPath L s policy w M)) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply ENNReal.ofReal_le_ofReal
    rcases le_total t M with ht | ht
    · exact a.path_mono L s policy w ht
    · rw [idealPath_stopped_frozen L s policy w ht hr]
  · exact le_iSup (fun t => ENNReal.ofReal (a.value (idealPath L s policy w t))) M

theorem infiniteIdealTotal_moves_eq_top_of_never_stopped {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool)
    (hr : ∀ t, (idealPath L s policy w t).running = true) :
    infiniteIdealTotal .totalMoves L s policy w = ∞ := by
  have hc (t : ℕ) : stateMoves (idealPath L s policy w t) = t :=
    idealRun_running_count L s policy t (fun i => w i.val) (hr t)
  simp only [infiniteIdealTotal, IdealStatistic.value, hc, ENNReal.ofReal_natCast]
  exact ENNReal.iSup_natCast

theorem idealPath_stops_of_finite_total_moves {d : ℕ} (L s : ℝ)
    (policy : IdealPolicy d) (w : ℕ → Bool)
    (hf : infiniteIdealTotal .totalMoves L s policy w < ∞) :
    ∃ M, (idealPath L s policy w M).running = false := by
  by_contra hn
  have hr (t : ℕ) : (idealPath L s policy w t).running = true := by
    cases he : (idealPath L s policy w t).running
    · exact False.elim (hn ⟨t, he⟩)
    · rfl
  rw [infiniteIdealTotal_moves_eq_top_of_never_stopped L s policy w hr] at hf
  exact (lt_self_iff_false _).mp hf

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The original infinite-horizon path-energy proposition, with explicit
constants and an arbitrary independent external random tape. -/
theorem CommonLoss.infiniteIdeal_pathenergy (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x)) :
    let total := fun a w => infiniteIdealTotal a P.gradientLip
      (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2
    (∫⁻ w, total .gradientMoves w ∂η.prod infiniteSignLaw) ≤
      ENNReal.ofReal (P.gap * P.gradientLip / τ^2) ∧
    (∫⁻ w, total .curvatureMoves w ∂η.prod infiniteSignLaw) ≤
      ENNReal.ofReal (curvatureCountCoefficient P ν * γ^(-(1+2/ν))) ∧
    (∫⁻ w, total .gradientEnergy w ∂η.prod infiniteSignLaw) ≤
      ENNReal.ofReal (P.gap / P.gradientLip) ∧
    (∫⁻ w, total .curvatureEnergy w ∂η.prod infiniteSignLaw) ≤
      ENNReal.ofReal (16*P.gap/(3*γ)) := by
  refine ⟨h.infiniteIdealTotal_bound .gradientMoves hτ hγ hm hv, ?_,
    h.infiniteIdealTotal_bound .gradientEnergy hτ hγ hm hv,
    h.infiniteIdealTotal_bound .curvatureEnergy hτ hγ hm hv⟩
  have hb := h.infiniteIdealTotal_bound (η := η) .curvatureMoves hτ hγ hm hv
  simpa only [IdealStatistic.bound, curvatureCountScale_eq P ν hγ] using hb

/-- Finite expected move count proves almost-sure halting, with no stopping
assumption in the hypotheses. -/
theorem CommonLoss.infiniteIdeal_stops_ae (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x)) :
    ∀ᵐ w ∂η.prod infiniteSignLaw, ∃ M,
      (idealPath P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 M).running = false := by
  filter_upwards [h.infiniteIdealTotal_finite_ae (η := η) .totalMoves hτ hγ hm hv] with w hw
  exact idealPath_stops_of_finite_total_moves _ _ _ _ hw

/-- Almost every infinite path is eventually a single frozen SOSP. -/
theorem CommonLoss.infiniteIdeal_eventually_sosp_ae (h : CommonLoss μ P ν F f)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ)
    {policy : Ξ → IdealPolicy d} (hm : MeasurableIdealPolicy policy)
    (hv : ∀ x, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy x)) :
    ∀ᵐ w ∂η.prod infiniteSignLaw, ∃ M, ∀ k, M ≤ k →
      let z := idealPath P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2
      z k = z M ∧ (z k).running = false ∧ IsSOSP F (10*τ) γ (z k).point := by
  filter_upwards [h.infiniteIdeal_stops_ae (η := η) hτ hγ hm hv] with w hw
  obtain ⟨M, hr⟩ := hw
  refine ⟨M, fun k hk => ?_⟩
  dsimp only
  have he := idealPath_stopped_frozen P.gradientLip (curvatureRadius P.hessianHolder ν γ)
    (policy w.1) w.2 hk hr
  rw [he]
  exact ⟨rfl, hr, idealRun_stopped_sosp (hv w.1) M (fun i => w.2 i.val) hr⟩

end
end SecondOrder
