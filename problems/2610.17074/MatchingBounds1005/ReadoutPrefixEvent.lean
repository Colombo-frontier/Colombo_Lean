import MatchingBounds1005.ScheduledHaarPrefix

/-! A closed event for finitely many stopped readouts and the compressed
query/candidate trace. No random-rank projection measurability is assumed. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace MatchingBounds1005.ScheduledPrefix
open ChronologicalProjection
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} {n : ℕ}

def readoutEvent (b : ι → E) (ell : ι → ℕ) (θ : ℝ) : Set (Fin n → E) :=
  {xs | ∀ s, 0 < ell s → ∀ c : Fin n → ℝ,
    |⟪b s, synthesis xs (ell s - 1) c⟫_ℝ| ≤ θ * ‖b s‖ * ‖synthesis xs (ell s - 1) c‖}

theorem isClosed_readoutEvent (b : ι → E) (ell : ι → ℕ) (θ : ℝ) :
    IsClosed (readoutEvent (n := n) b ell θ) := by
  unfold readoutEvent
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_iInter fun c =>
    isClosed_le (continuous_const.inner (continuous_synthesis (ell s - 1) c)).abs
      (continuous_const.mul (continuous_synthesis (ell s - 1) c).norm)

theorem readoutEvent_projection {b : ι → E} {ell : ι → ℕ} {θ : ℝ}
    (hθ : 0 ≤ θ) {xs : Fin n → E} (hx : xs ∈ readoutEvent b ell θ) (s : ι) :
    ‖(prefixSpan (List.ofFn xs) (ell s)).orthogonalProjection (b s)‖ ≤ θ * ‖b s‖ := by
  by_cases hp : 0 < ell s
  · let P := prefixSpan (List.ofFn xs) (ell s)
    have he : ell s - 1 + 1 = ell s := Nat.sub_add_cancel hp
    have hm : (P.orthogonalProjection (b s) : E) ∈ prefixSpan (List.ofFn xs) (ell s - 1 + 1) := by
      rw [he]
      exact (P.orthogonalProjection (b s)).property
    obtain ⟨c, hc⟩ := (mem_prefix_iff_synthesis xs (ell s - 1) _).mp hm
    have hv := hx s hp c
    rw [hc] at hv
    have hi : ⟪b s, (P.orthogonalProjection (b s) : E)⟫_ℝ = ‖P.orthogonalProjection (b s)‖ ^ 2 := by
      rw [← P.inner_orthogonalProjection_eq_of_mem_right (P.orthogonalProjection (b s)) (b s)]
      exact real_inner_self_eq_norm_sq _
    rw [hi, abs_of_nonneg (sq_nonneg _)] at hv
    change ‖P.orthogonalProjection (b s)‖ ^ 2 ≤ θ * ‖b s‖ * ‖P.orthogonalProjection (b s)‖ at hv
    change ‖P.orthogonalProjection (b s)‖ ≤ _
    have hn := norm_nonneg (P.orthogonalProjection (b s))
    have hright : 0 ≤ θ * ‖b s‖ := mul_nonneg hθ (norm_nonneg _)
    by_cases hz : ‖P.orthogonalProjection (b s)‖ = 0
    · simpa only [hz] using hright
    · have hp' : 0 < ‖P.orthogonalProjection (b s)‖ := lt_of_le_of_ne hn (Ne.symm hz)
      nlinarith
  · have he : ell s = 0 := by omega
    rw [he]
    have hz : prefixSpan (List.ofFn xs) 0 = ⊥ := by
      simp only [prefixSpan, List.take_zero]
      convert Submodule.span_empty (R := ℝ) (M := E) using 1
      ext x
      simp
    rw [hz]
    simpa using mul_nonneg hθ (norm_nonneg (b s))

theorem readoutEvent_coordinate {b : ι → E} {ell : ι → ℕ} {θ : ℝ}
    {xs : Fin n → E} (hx : xs ∈ readoutEvent b ell θ) (s : ι) (i : Fin n)
    (hi : i.val < ell s) : |⟪b s, xs i⟫_ℝ| ≤ θ * ‖b s‖ * ‖xs i‖ := by
  have hp : 0 < ell s := Nat.zero_lt_of_lt hi
  have hv := hx s hp (Pi.single i 1)
  have he : synthesis xs (ell s - 1) (Pi.single i 1) = xs i := by
    unfold synthesis
    rw [Finset.sum_eq_single i]
    · simp [maskedPrefix, show i.val ≤ ell s - 1 by omega]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  simpa only [he] using hv

theorem measurableSet_readoutEvent [MeasurableSpace E] [BorelSpace E]
    (b : ι → E) (ell : ι → ℕ) (θ : ℝ) : MeasurableSet (readoutEvent (n := n) b ell θ) :=
  (isClosed_readoutEvent b ell θ).measurableSet

end MatchingBounds1005.ScheduledPrefix
