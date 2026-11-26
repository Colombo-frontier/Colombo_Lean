import SecondOrder.CurvatureTruncation

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

theorem reverseSelectorValue_congr {b c V W : ℕ → ℝ} (n : ℕ)
    (hb : ∀ i<n, b i=c i) (hV : ∀ i≤n, V i=W i) :
    reverseSelectorValue b V n = reverseSelectorValue c W n := by
  induction n with
  | zero => simp [reverseSelectorValue, tailProduct, hV 0 le_rfl]
  | succ n ih =>
    rw [reverseSelectorValue_step, reverseSelectorValue_step, hb n (Nat.lt_succ_self n),
      hV (n+1) le_rfl, ih (fun i hi => hb i (by omega)) (fun i hi => hV i (by omega))]

theorem reverseSelectorValue_truncate (b V : ℕ → ℝ) {k n : ℕ} (hkn : k≤n)
    (hzero : ∀ i, k ≤ i → i<n → b i=0) :
    reverseSelectorValue b V n = reverseSelectorValue b V k := by
  induction n with
  | zero =>
    have hk : k=0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases he : k=n+1
    · rw [he]
    · have hk : k≤n := by omega
      rw [reverseSelectorValue_step, hzero n hk (Nat.lt_succ_self n)]
      simp only [sub_zero, one_mul, zero_mul, add_zero]
      exact ih hk (fun i hi hin => hzero i hi (by omega))

theorem reverseSelectorValue_prefix (b V : ℕ → ℝ) {k n : ℕ} (hkn : k≤n) :
    reverseSelectorValue (fun i => if i<k then b i else 0) V n = reverseSelectorValue b V k := by
  rw [reverseSelectorValue_truncate _ _ hkn (by intro i hi _; simp [Nat.not_lt.mpr hi])]
  exact reverseSelectorValue_congr k (fun i hi => if_pos hi) (fun _ _ => rfl)

theorem sum_range_prefix (a : ℕ → ℝ) {k n : ℕ} (hkn : k≤n) :
    (∑ i ∈ Finset.range n, if i<k then a i else 0) = ∑ i ∈ Finset.range k, a i := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The scalar expression remaining after k gates are retained. -/
def frontierLossValue (b W S : ℕ → ℝ) (k : ℕ) : ℝ :=
  W 0+∑ i ∈ Finset.range k, 2*(b i*W (i+1))+
    reverseSelectorValue b (fun j => curvaturePayloadScale j*(S j-W j)) k

theorem frontierLossValue_zero (b W S : ℕ → ℝ) : frontierLossValue b W S 0=S 0 := by
  simp [frontierLossValue, reverseSelectorValue, tailProduct, curvaturePayloadScale]

/-- The fresh block's population potential cancels exactly against its noise. -/
theorem frontierLossValue_succ (b W S : ℕ → ℝ) (k : ℕ) :
    frontierLossValue b W S (k+1) =
      W 0+(∑ i ∈ Finset.range k, 2*(b i*W (i+1)))+
      (1-b k)*reverseSelectorValue b (fun j => curvaturePayloadScale j*(S j-W j)) k+
      2*b k*S (k+1) := by
  rw [frontierLossValue, Finset.sum_range_succ, reverseSelectorValue_step]
  simp only [curvaturePayloadScale, Nat.add_one_ne_zero, if_false]
  ring

/-- The fresh hidden block is absent: only hidden data strictly before k
and sampled data through k affect this scalar expression. -/
theorem frontierLossValue_congr {b c W W' S S' : ℕ → ℝ} (k : ℕ)
    (hb : ∀ i<k, b i=c i) (hW : ∀ i<k, W i=W' i) (hS : ∀ i≤k, S i=S' i) :
    frontierLossValue b W S k = frontierLossValue c W' S' k := by
  cases k with
  | zero => rw [frontierLossValue_zero, frontierLossValue_zero, hS 0 le_rfl]
  | succ k =>
    rw [frontierLossValue_succ, frontierLossValue_succ, hW 0 (by omega), hb k (by omega),
      hS (k+1) le_rfl]
    have hs : (∑ i ∈ Finset.range k, 2*(b i*W (i+1))) =
        ∑ i ∈ Finset.range k, 2*(c i*W' (i+1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [hb i (by omega), hW (i+1) (by omega)]
    rw [hs, reverseSelectorValue_congr k (fun i hi => hb i (by omega))
      (fun i hi => by rw [hS i (by omega), hW i (by omega)])]

end
end SecondOrder
