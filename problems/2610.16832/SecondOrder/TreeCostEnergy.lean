import SecondOrder.TreeQueryCost

open MeasureTheory
open scoped Classical BigOperators InnerProductSpace

namespace SecondOrder
noncomputable section

variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {η : Measure A}

/-- The energy of the actual randomly stopped tree is integrable as a
consequence of the physical increments' second moments. -/
theorem completed_chord_energy_integrable (M L : ℕ) (N : A → ℕ) (hN : Measurable N)
    (hcap : ∀ w, N w ≤ M) (x : A → ℕ → E) (a m : Fin M → A → E)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+m k w)
    (ha : ∀ k, Integrable (a k) η) (hm : ∀ k, Integrable (m k) η)
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) η)
    (hm2 : ∀ k, Integrable (fun w => ‖m k w‖^2) η) :
    Integrable (fun w => ∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2) η := by
  have he (w : A) : (∑ i ∈ completedNodes L (N w), ‖x w (nodeRight i)-x w (nodeLeft i)‖^2) =
      ∑ i : Fin L × Fin M, if nodeRight (paddedNode i) ≤ N w then
        ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2 else 0 := by
    rw [sum_completedNodes_finite (hcap w)]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hh : nodeRight (paddedNode i) ≤ N w
    · rw [if_pos hh, if_pos hh, ← dyadicBlock_telescopes (x w) i (hh.trans (hcap w))]
      simp_rw [hx]
    · rw [if_neg hh, if_neg hh]
  simp_rw [he]
  apply integrable_finset_sum
  intro i hi
  have hh := integrable_norm_sum_sq (dyadicBlock M i.1.val i.2) (fun k w => a k w+m k w)
    (fun k _ => (ha k).add (hm k))
    (fun k _ => integrable_norm_add_sq (ha k) (hm k) (ha2 k) (hm2 k))
  convert hh.indicator (measurableSet_le (measurable_const (a := nodeRight (paddedNode i))) hN) using 1
  ext w
  simp [Set.indicator]

/-- Actual single-epoch HVP query work, obtained by composing exact local
batch costs, actual node creation, and the drift/martingale energy bound.
The martingale energy keeps its coefficient independent of q. -/
theorem completed_tree_query_cost [IsProbabilityMeasure η] {d : ℕ}
    (P : Parameters) (M L q : ℕ) (N : A → ℕ) (hN : Measurable N) (hcap : ∀ w, N w ≤ M)
    (x : A → ℕ → Point d) (hxm : ∀ n, Measurable (fun w => x w n)) (a m : Fin M → A → Point d)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+m k w)
    (ha : ∀ k, Integrable (a k) η) (hm : ∀ k, Integrable (m k) η)
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) η)
    (hm2 : ∀ k, Integrable (fun w => ‖m k w‖^2) η)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪m i w,m j w⟫_ℝ ∂η) = 0)
    {ρ δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Integrable (fun w => (treeQueryCount P (x w) L (N w) ρ δ : ℝ)) η ∧
    (∫ w, (treeQueryCount P (x w) L (N w) ρ δ : ℝ) ∂η) ≤
      (chordCostCoefficient P ρ*(2*(L : ℝ)*
        ((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂η)+(∫ w, ∑ k, ‖m k w‖^2 ∂η)))+4*(∫ w, (N w : ℝ) ∂η))*
          (8*Real.log (1/δ)+2) := by
  have hi := completed_chord_energy_integrable M L N hN hcap x a m hx ha hm ha2 hm2
  have hc := treeQueryCount_integral P M L hN hcap x hxm (ρ := ρ) hδ hδ1 hi
  have he := completed_chord_energy M L q N hN hcap x a m hx ha hm ha2 hm2
    (fun w => by
      convert hs w using 1
      congr 1
      ext k
      simp) ho
  refine ⟨hc.1, hc.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (chordConfidenceFactor_nonneg hδ hδ1)
  exact add_le_add_right (mul_le_mul_of_nonneg_left he (chordCostCoefficient_nonneg P ρ)) _

end
end SecondOrder
