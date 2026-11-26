import SecondOrder.EpochPathMeasurability
import SecondOrder.EpochDyadicEnergy

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def idealEpochTreeEnergy {d M : ℕ} (q : ℕ) (Lip s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (L : ℕ) : ℝ :=
  ∑ e : Fin M, ∑ i ∈ completedNodes L (idealEpochLength q Lip s policy w e.val),
    ‖idealEpochPath q Lip s policy w e.val (nodeRight i)-idealEpochPath q Lip s policy w e.val (nodeLeft i)‖^2

theorem idealEpochTreeEnergy_nonneg {d M : ℕ} (q : ℕ) (Lip s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (L : ℕ) : 0 ≤ idealEpochTreeEnergy q Lip s policy w L := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Future-dependent completion selects a subset of padded blocks. The
inequality is pathwise and makes no conditional orthogonality claim. -/
theorem idealEpochTreeEnergy_le {Ξ : Type*} {d M q : ℕ} (hq : 0 < q) (Lip s : ℝ)
    (policy : Ξ → IdealPolicy d) (w : Ξ × (Fin M → Bool)) (L : ℕ) :
    idealEpochTreeEnergy q Lip s (policy w.1) w.2 L ≤
      ∑ e : Fin M, ∑ i : Fin L × Fin M, ‖∑ k ∈ dyadicBlock M i.1.val i.2,
        (idealEpochDrift q Lip s policy (e.val,k.val) w+idealEpochInnovation q Lip s policy (e.val,k.val) w)‖^2 := by
  apply Finset.sum_le_sum
  intro e he
  rw [sum_completedNodes_finite (idealEpochLength_le q Lip s (policy w.1) w.2 e.val)]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hn : nodeRight (paddedNode i) ≤ idealEpochLength q Lip s (policy w.1) w.2 e.val
  · rw [if_pos hn]
    have hh := dyadicBlock_telescopes (idealEpochPath q Lip s (policy w.1) w.2 e.val) i
      (hn.trans (idealEpochLength_le q Lip s (policy w.1) w.2 e.val))
    simp_rw [idealEpochPath_displacement hq] at hh
    rw [hh]
  · rw [if_neg hn]
    exact sq_nonneg _

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- The paper's all-epoch energy bound, now for the actual completed
chords and actual stopped physical lengths of a measurable valid policy. -/
theorem CommonLoss.idealEpochTreeEnergy_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M L : ℕ) :
    let energy := fun w : Ξ × (Fin M → Bool) =>
      idealEpochTreeEnergy q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 L
    Integrable energy (η.prod (signLaw M)) ∧
      (∫ w, energy w ∂η.prod (signLaw M)) ≤
        2*(L : ℝ)*((q : ℝ)*(P.gap/P.gradientLip)+16*P.gap/(3*γ)) := by
  dsimp only
  have ha := h.idealEpochDrift_moments (η := η) hq hτ hγ hm hv M
  have hmi := h.idealEpochInnovation_moments (η := η) hq hτ hγ hm hv M
  have hi : Integrable (fun w : Ξ × (Fin M → Bool) =>
      idealEpochTreeEnergy q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 L)
      (η.prod (signLaw M)) := by
    unfold idealEpochTreeEnergy
    apply integrable_finset_sum
    intro e he
    exact completed_chord_energy_integrable (A := Ξ × (Fin M → Bool)) (E := Point d)
      (η := η.prod (signLaw M)) M L
      (fun w => idealEpochLength q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 e.val)
      (idealEpochLength_measurable hq P.gradientLip (curvatureRadius P.hessianHolder ν γ) hm M e.val)
      (fun w => idealEpochLength_le q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 e.val)
      (fun w => idealEpochPath q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 e.val)
      (fun k => idealEpochDrift q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy (e.val,k.val))
      (fun k => idealEpochInnovation q P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy (e.val,k.val))
      (fun w k => idealEpochPath_displacement hq P.gradientLip (curvatureRadius P.hessianHolder ν γ) policy w e.val k.val)
      (fun k => (ha (e.val,k.val)).1) (fun k => (hmi (e.val,k.val)).1)
      (fun k => (ha (e.val,k.val)).2) (fun k => (hmi (e.val,k.val)).2)
  have hb := h.idealEpoch_dyadic_energy (ξLaw := η) hq hτ hγ hm hv M L
  exact ⟨hi,(integral_mono hi hb.1 (fun w => idealEpochTreeEnergy_le hq _ _ policy w L)).trans hb.2⟩

end
end SecondOrder
