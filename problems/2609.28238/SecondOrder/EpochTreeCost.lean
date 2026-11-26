import SecondOrder.EpochTreeEnergy

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def idealEpochTreeQueries {d M : ℕ} (P : Parameters) (q : ℕ) (Lip s : ℝ) (policy : IdealPolicy d)
    (w : Fin M → Bool) (L : ℕ) (ρ δ : ℝ) : ℕ :=
  ∑ e : Fin M, treeQueryCount P (idealEpochPath q Lip s policy w e.val) L
    (idealEpochLength q Lip s policy w e.val) ρ δ

/-- Each actual created node is charged once. Empty epochs and padded
post-stop times contribute no calls. -/
theorem idealEpochTreeQueries_created {d M : ℕ} (P : Parameters) (q : ℕ) (Lip s : ℝ)
    (policy : IdealPolicy d) (w : Fin M → Bool) (L : ℕ) (ρ δ : ℝ) :
    (∑ e : Fin M, ∑ t ∈ Finset.range (idealEpochLength q Lip s policy w e.val),
      ∑ i ∈ createdNodes L t, localQueryCount
        (chordVariance P (idealEpochPath q Lip s policy w e.val (nodeLeft i))
          (idealEpochPath q Lip s policy w e.val (nodeRight i))) ρ δ) =
      idealEpochTreeQueries P q Lip s policy w L ρ δ := by
  simp only [treeQueryCount_created,idealEpochTreeQueries]

theorem idealEpochTreeQueries_bound {d M : ℕ} (P : Parameters) (q : ℕ) (Lip s : ℝ)
    (policy : IdealPolicy d) (w : Fin M → Bool) (L : ℕ)
    {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (idealEpochTreeQueries P q Lip s policy w L ρ δ : ℝ) ≤
      (chordCostCoefficient P ρ*idealEpochTreeEnergy q Lip s policy w L+
        4*(idealPhysicalLength Lip s policy w : ℝ))*(8*Real.log (1/δ)+2) := by
  simp only [idealEpochTreeQueries,Nat.cast_sum]
  calc
    _ ≤ ∑ e : Fin M,
        (chordCostCoefficient P ρ*(∑ i ∈ completedNodes L (idealEpochLength q Lip s policy w e.val),
          ‖idealEpochPath q Lip s policy w e.val (nodeRight i)-idealEpochPath q Lip s policy w e.val (nodeLeft i)‖^2)+
          4*(idealEpochLength q Lip s policy w e.val : ℝ))*(8*Real.log (1/δ)+2) := by
      apply Finset.sum_le_sum
      intro e he
      exact treeQueryCount_bound P _ L _ hδ hδ1
    _ = _ := by
      rw [← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
        ← Nat.cast_sum,sum_idealEpochLength]
      rfl

theorem idealEpochTreeQueries_measurable {Ξ : Type*} [MeasurableSpace Ξ] {d q : ℕ}
    (P : Parameters) (hq : 0 < q) (Lip s : ℝ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy) (M L : ℕ) (ρ δ : ℝ) :
    Measurable (fun w : Ξ × (Fin M → Bool) => idealEpochTreeQueries P q Lip s (policy w.1) w.2 L ρ δ) := by
  apply Finset.measurable_sum
  intro e he
  exact treeQueryCount_measurable P M L (idealEpochLength_measurable hq Lip s hm M e.val)
    (fun w => idealEpochLength_le q Lip s (policy w.1) w.2 e.val)
    (fun w => idealEpochPath q Lip s (policy w.1) w.2 e.val)
    (idealEpochPath_measurable hq Lip s hm M e.val) ρ δ

def epochTreeBudget (P : Parameters) (ν τ γ ρ δ : ℝ) (q L : ℕ) : ℝ :=
  (chordCostCoefficient P ρ*(2*(L : ℝ)*((q : ℝ)*(P.gap/P.gradientLip)+16*P.gap/(3*γ)))+
    4*idealMoveBudget P ν τ γ)*(8*Real.log (1/δ)+2)

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
  {μ : Measure Ω} {η : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
  {P : Parameters} {ν : ℝ} {F : Point d → ℝ} {f : Ω → Point d → ℝ}

/-- All epoch tree work is integrable and bounded by explicit model and
tolerance parameters. The node-count term uses the true physical move
budget, not the deterministic cap once for every epoch. -/
theorem CommonLoss.idealEpochTreeQueries_integral (h : CommonLoss μ P ν F f)
    {q : ℕ} (hq : 0 < q) {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) {policy : Ξ → IdealPolicy d}
    (hm : MeasurableIdealPolicy policy)
    (hv : ∀ ξ, ValidIdealPolicy F P.gradientLip (curvatureRadius P.hessianHolder ν γ) τ γ (policy ξ))
    (M L : ℕ) {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let cost := fun w : Ξ × (Fin M → Bool) =>
      (idealEpochTreeQueries P q P.gradientLip (curvatureRadius P.hessianHolder ν γ) (policy w.1) w.2 L ρ δ : ℝ)
    Integrable cost (η.prod (signLaw M)) ∧
      (∫ w, cost w ∂η.prod (signLaw M)) ≤ epochTreeBudget P ν τ γ ρ δ q L := by
  dsimp only
  let s := curvatureRadius P.hessianHolder ν γ
  let E := fun w : Ξ × (Fin M → Bool) => idealEpochTreeEnergy q P.gradientLip s (policy w.1) w.2 L
  let T := fun w : Ξ × (Fin M → Bool) => (idealPhysicalLength P.gradientLip s (policy w.1) w.2 : ℝ)
  let C := chordCostCoefficient P ρ
  let D := 8*Real.log (1/δ)+2
  let cost := fun w : Ξ × (Fin M → Bool) =>
    (idealEpochTreeQueries P q P.gradientLip s (policy w.1) w.2 L ρ δ : ℝ)
  have hE := h.idealEpochTreeEnergy_integral (η := η) hq hτ hγ hm hv M L
  have hT := h.idealPhysicalLength_integral (η := η) hτ hγ hm hv M
  have henv : Integrable (fun w => (C*E w+4*T w)*D) (η.prod (signLaw M)) :=
    ((hE.1.const_mul C).add (hT.1.const_mul 4)).mul_const D
  have hb (w) : cost w ≤ (C*E w+4*T w)*D :=
    idealEpochTreeQueries_bound P q P.gradientLip s (policy w.1) w.2 L hδ hδ1
  have hc : Measurable cost := (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (idealEpochTreeQueries_measurable P hq P.gradientLip s hm M L ρ δ)
  have hi : Integrable cost (η.prod (signLaw M)) := by
    apply henv.mono' hc.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hb w
  refine ⟨hi,(integral_mono hi henv hb).trans ?_⟩
  rw [integral_mul_const,integral_add (hE.1.const_mul C) (hT.1.const_mul 4),
    integral_const_mul,integral_const_mul]
  exact mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hE.2 (chordCostCoefficient_nonneg P ρ))
      (mul_le_mul_of_nonneg_left hT.2 (by norm_num))) (chordConfidenceFactor_nonneg hδ hδ1)

end
end SecondOrder
