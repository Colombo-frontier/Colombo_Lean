import SecondOrder.ChordCost
import SecondOrder.BinaryEnergy

open MeasureTheory
open scoped Classical BigOperators

namespace SecondOrder
noncomputable section

def chordCostCoefficient (P : Parameters) (ρ : ℝ) : ℝ :=
  36*(P.hessianNoise^2+P.gradientLip^2)/ρ^2

theorem chordCostCoefficient_nonneg (P : Parameters) (ρ : ℝ) : 0 ≤ chordCostCoefficient P ρ := by
  unfold chordCostCoefficient
  positivity

theorem chordConfidenceFactor_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ 8*Real.log (1/δ)+2 := by
  have hl : 0 ≤ Real.log (1/δ) := Real.log_nonneg ((le_div_iff₀ hδ).mpr (by simpa using hδ1))
  linarith

theorem sum_chord_query_count {ι : Type*} {d : ℕ} (P : Parameters) (s : Finset ι)
    (x y : ι → Point d) {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((∑ i ∈ s, localQueryCount (chordVariance P (x i) (y i)) ρ δ : ℕ) : ℝ) ≤
      (chordCostCoefficient P ρ*(∑ i ∈ s, ‖y i-x i‖^2)+2*(s.card : ℝ))*(8*Real.log (1/δ)+2) := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ i ∈ s, (chordCostCoefficient P ρ*‖y i-x i‖^2+2)*(8*Real.log (1/δ)+2) := by
      apply Finset.sum_le_sum
      intro i hi
      convert chord_query_count P (x i) (y i) (ρ := ρ) hδ hδ1 using 1 <;>
        dsimp [chordCostCoefficient] <;> ring
    _ = _ := by
      simp only [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
      ring

def treeQueryCount {d : ℕ} (P : Parameters) (x : ℕ → Point d) (L n : ℕ) (ρ δ : ℝ) : ℕ :=
  ∑ i ∈ completedNodes L n, localQueryCount (chordVariance P (x (nodeLeft i)) (x (nodeRight i))) ρ δ

/-- Each created node is charged exactly once, at its actual creation time. -/
theorem treeQueryCount_created {d : ℕ} (P : Parameters) (x : ℕ → Point d) (L n : ℕ) (ρ δ : ℝ) :
    (∑ t ∈ Finset.range n, ∑ i ∈ createdNodes L t,
      localQueryCount (chordVariance P (x (nodeLeft i)) (x (nodeRight i))) ρ δ) =
      treeQueryCount P x L n ρ δ := by
  induction n with
  | zero => simp [treeQueryCount, completedNodes_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold treeQueryCount createdNodes
    rw [add_comm]
    exact Finset.sum_sdiff (completedNodes_mono L (Nat.le_succ n))

theorem treeQueryCount_bound {d : ℕ} (P : Parameters) (x : ℕ → Point d) (L n : ℕ)
    {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (treeQueryCount P x L n ρ δ : ℝ) ≤
      (chordCostCoefficient P ρ*(∑ i ∈ completedNodes L n, ‖x (nodeRight i)-x (nodeLeft i)‖^2)+4*(n : ℝ))*
        (8*Real.log (1/δ)+2) := by
  have hc : ((completedNodes L n).card : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast completedNodes_card L n
  refine (sum_chord_query_count P (completedNodes L n) (fun i => x (nodeLeft i))
    (fun i => x (nodeRight i)) hδ hδ1).trans ?_
  apply mul_le_mul_of_nonneg_right _ (chordConfidenceFactor_nonneg hδ hδ1)
  linarith

theorem treeQueryCount_measurable {A : Type*} [MeasurableSpace A] {d : ℕ}
    (P : Parameters) (M L : ℕ) {N : A → ℕ} (hN : Measurable N) (hcap : ∀ w, N w ≤ M)
    (x : A → ℕ → Point d) (hx : ∀ n, Measurable (fun w => x w n)) (ρ δ : ℝ) :
    Measurable (fun w => treeQueryCount P (x w) L (N w) ρ δ) := by
  have he (w : A) := sum_completedNodes_finite (L := L) (hcap w)
    (fun i => localQueryCount (chordVariance P (x w (nodeLeft i)) (x w (nodeRight i))) ρ δ)
  simp_rw [treeQueryCount, he]
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (measurableSet_le measurable_const hN)
    (adaptiveChordCost_measurable P (hx _) (hx _) ρ δ) measurable_const

/-- Integrating the actual finite tree cost needs only integrability of
its squared-chord energy, with the explicit constant node-count charge. -/
theorem treeQueryCount_integral {A : Type*} [MeasurableSpace A] {η : Measure A} [IsProbabilityMeasure η]
    {d : ℕ} (P : Parameters) (M L : ℕ) {N : A → ℕ} (hN : Measurable N) (hcap : ∀ w, N w ≤ M)
    (x : A → ℕ → Point d) (hx : ∀ n, Measurable (fun w => x w n))
    {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hE : Integrable (fun w => ∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2) η) :
    Integrable (fun w => (treeQueryCount P (x w) L (N w) ρ δ : ℝ)) η ∧
    (∫ w, (treeQueryCount P (x w) L (N w) ρ δ : ℝ) ∂η) ≤
      (chordCostCoefficient P ρ*(∫ w, ∑ i ∈ completedNodes L (N w),
        ‖x w (nodeRight i)-x w (nodeLeft i)‖^2 ∂η)+4*(∫ w, (N w : ℝ) ∂η))*(8*Real.log (1/δ)+2) := by
  let energy := fun w => ∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2
  let D := 8*Real.log (1/δ)+2
  have hm : Measurable (fun w => (treeQueryCount P (x w) L (N w) ρ δ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (treeQueryCount_measurable P M L hN hcap x hx ρ δ)
  have hNi : Integrable (fun w => (N w : ℝ)) η := by
    apply (integrable_const (M : ℝ)).mono'
      (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hN).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro w
    change ‖(N w : ℝ)‖ ≤ (M : ℝ)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hcap w
  have he : Integrable (fun w => (chordCostCoefficient P ρ*energy w+4*(N w : ℝ))*D) η :=
    ((hE.const_mul _).add (hNi.const_mul _)).mul_const _
  have hb (w) : (treeQueryCount P (x w) L (N w) ρ δ : ℝ) ≤
      (chordCostCoefficient P ρ*energy w+4*(N w : ℝ))*D :=
    treeQueryCount_bound P (x w) L (N w) hδ hδ1
  have hi : Integrable (fun w => (treeQueryCount P (x w) L (N w) ρ δ : ℝ)) η := by
    apply he.mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro w
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hb w
  refine ⟨hi, (integral_mono hi he hb).trans_eq ?_⟩
  rw [integral_mul_const, integral_add (hE.const_mul _) (hNi.const_mul _), integral_const_mul, integral_const_mul]

end
end SecondOrder
