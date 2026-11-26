import MatchingBounds1005.CUPGMonitor

/-! A finite convexity witness with the value bound required by escape. -/
noncomputable section
open scoped InnerProductSpace

namespace MatchingBounds1005.CUPG
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def witnessPoint (f : E → ℝ) (q μ : ℝ) (start : E) (n : ℕ) : E :=
  if f (estimateRun f q μ start n).point ≤ f start then
    descentPoint f q μ (estimateRun f q μ start n).point else start

theorem witnessPoint_value (f : E → ℝ) {q μ L : ℝ}
    (hμ : 0 < μ) (hscale : L * q ^ 2 = μ) (hsm : SmoothUpper f L)
    (start : E) (n : ℕ) : f (witnessPoint f q μ start n) ≤ f start := by
  unfold witnessPoint
  split_ifs with h
  · exact (descent_decrease f hμ hscale hsm _).trans h
  · exact le_rfl

theorem bounded_progress_witness (f : E → ℝ) {q μ L : ℝ}
    (hq : 0 < q) (hqone : q ≤ 1) (hμ : 0 < μ) (hscale : L * q ^ 2 = μ)
    (hsm : SmoothUpper f L) (start : E) (n : ℕ)
    (hpast : ∀ j < n, ProgressPass f q μ L start j)
    (hfail : ¬ ProgressPass f q μ L start n) :
    ∃ j < n, ∃ u : E,
      (u = (estimateRun f q μ start j).point ∨ u = witnessPoint f q μ start n) ∧
      f u ≤ f start ∧ ¬ LocalConvex f μ (query q (estimateRun f q μ start j)) u := by
  have hbad : ∃ j < n, ∃ u : E,
      (u = (estimateRun f q μ start j).point ∨ u = witnessPoint f q μ start n) ∧
      ¬ LocalConvex f μ (query q (estimateRun f q μ start j)) u := by
    by_contra hn
    push_neg at hn
    have hy : ∀ j < n, LocalConvex f μ (query q (estimateRun f q μ start j))
        (estimateRun f q μ start j).point := fun j hj => hn j hj _ (Or.inl rfl)
    have hw := local_accelerated_estimate f hq.le hqone hμ hscale hsm start
      (witnessPoint f q μ start n) n hy (fun j hj => hn j hj _ (Or.inr rfl))
    by_cases hv : f (estimateRun f q μ start n).point ≤ f start
    · rw [witnessPoint, if_pos hv] at hw
      have hgap : 0 ≤ progressGap f μ start (descentPoint f q μ (estimateRun f q μ start n).point) := by
        have hd := descent_decrease f hμ hscale hsm (estimateRun f q μ start n).point
        unfold progressGap
        have hp : 0 ≤ μ / 2 * ‖descentPoint f q μ (estimateRun f q μ start n).point - start‖ ^ 2 := by positivity
        linarith
      have hg := descent_gradient_bound f hμ hscale hsm (estimateRun f q μ start n).point
      have hL : 0 < L := by nlinarith [sq_nonneg q]
      have hm := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2 * L by positivity)
      have he := mul_le_mul_of_nonneg_left (contraction_le_exp hqone n)
        (show 0 ≤ 2 * L * progressGap f μ start
          (descentPoint f q μ (estimateRun f q μ start n).point) by positivity)
      apply hfail
      refine ⟨hv, ?_⟩
      unfold progressGap at he
      change ‖gradient f (estimateRun f q μ start n).point‖ ^ 2 ≤
        2 * L * (f start - f (descentPoint f q μ (estimateRun f q μ start n).point) +
          μ / 2 * ‖descentPoint f q μ (estimateRun f q μ start n).point - start‖ ^ 2) *
            Real.exp (-q * n)
      nlinarith only [hg, hm, he]
    · rw [witnessPoint, if_neg hv] at hw
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, add_zero] at hw
      exact hv (by linarith)
  obtain ⟨j, hj, u, hu, hnc⟩ := hbad
  refine ⟨j, hj, u, hu, ?_, hnc⟩
  rcases hu with rfl | rfl
  · exact (hpast j hj).1
  · exact witnessPoint_value f hμ hscale hsm start n

end MatchingBounds1005.CUPG
