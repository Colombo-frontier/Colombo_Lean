import FullJet.RowTransition

open scoped BigOperators

namespace FullJet

theorem balancedCount_history_capacity (n k d : ℕ) (hk : k ≤ n) (m theta : ℝ)
    (hm : 0 ≤ m) (htheta : theta = -1 ∨ theta = 1)
    (hbalance : 2 * (k : ℝ) = n + m * theta)
    (hbudget : 8 * m + 9 * (d : ℝ) ≤ n) : d ≤ k ∧ d ≤ n - k := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hp : (d : ℝ) ≤ k := by
    rcases htheta with rfl | rfl <;> nlinarith
  have hn : (d : ℝ) ≤ n - k := by
    rcases htheta with rfl | rfl <;> nlinarith
  refine ⟨by exact_mod_cast hp, ?_⟩
  rw [← Nat.cast_sub hk] at hn
  exact_mod_cast hn

noncomputable def rowKernel {n D : ℕ} (k : Fin D → ℕ) (hk : ∀ j, k j ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (fallback : Fin D → Bool) (rows : List (Fin D → Bool)) : (Fin D → Bool) → ℝ :=
  historyKernelWeight (vectorColumnLaw Finset.univ k (by simpa using hk))
    (fun S hist j => decide (ask hist ∈ S j)) past fallback rows

theorem rowKernel_fresh {n D : ℕ} (k : Fin D → ℕ) (hk : ∀ j, k j ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (fallback : Fin D → Bool)
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support)
    (hfresh : ask (past ++ rows) ∉ vectorQueriedLabels ask past rows)
    (m : ℝ) (theta : Fin D → ℝ) (hbalance : ∀ j, 2 * (k j : ℝ) = n + m * theta j) :
    rowKernel k hk ask past fallback rows = finiteProductWeight (fun j => bitWeight
      (nextSignProbability n m (vectorHistorySize ask past rows) (vectorHistorySum ask past rows j) (theta j))) := by
  funext b
  unfold rowKernel historyKernelWeight
  rw [historyKernel_vector_active _ _ _ _ _ _ _ hpos]
  exact vectorColumnLaw_next_row_mass_signed k hk ask past rows hpos
    (ask (past ++ rows)) hfresh m theta hbalance b

theorem rowKernel_repeated {n D : ℕ} (k : Fin D → ℕ) (hk : ∀ j, k j ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (fallback : Fin D → Bool)
    (hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support)
    (hrepeat : ask (past ++ rows) ∈ vectorQueriedLabels ask past rows) :
    rowKernel k hk ask past fallback rows = fun b =>
      ((PMF.pure (fun j => decide (ask (past ++ rows) ∈ vectorPositiveLabels ask past rows j))) b).toReal := by
  funext b
  unfold rowKernel historyKernelWeight
  rw [historyKernel_vector_active _ _ _ _ _ _ _ hpos,
    vectorColumnLaw_repeated_row _ _ _ _ _ _ hpos _ hrepeat]

theorem rowKernel_inactive {n D : ℕ} (k : Fin D → ℕ) (hk : ∀ j, k j ≤ n)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (fallback : Fin D → Bool)
    (hpos : ¬ ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support) :
    rowKernel k hk ask past fallback rows = fun b => ((PMF.pure fallback) b).toReal := by
  funext b
  unfold rowKernel historyKernelWeight
  rw [historyKernel_vector_inactive _ _ _ _ _ _ _ hpos]

/-- Full next-row information bound for the actual adaptive fixed-table laws.
Fresh rows, repeated rows, and impossible histories are all included. -/
theorem rowKernel_information {n D : ℕ} (hn : 0 < n)
    (k k' : Fin D → ℕ) (hk : ∀ j, k j ≤ n) (hk' : ∀ j, k' j ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (theta theta' : Fin D → ℝ)
    (htheta : ∀ j, theta j = -1 ∨ theta j = 1)
    (htheta' : ∀ j, theta' j = -1 ∨ theta' j = 1)
    (hbalance : ∀ j, 2 * (k j : ℝ) = n + m * theta j)
    (hbalance' : ∀ j, 2 * (k' j : ℝ) = n + m * theta' j)
    (ask : List (Fin D → Bool) → Fin n) (past rows : List (Fin D → Bool))
    (fallback : Fin D → Bool) (hbudget : 8 * m + 9 * (rows.length : ℝ) ≤ n) :
    (∀ b, rowKernel k hk ask past fallback rows b ≠ 0 →
      rowKernel k' hk' ask past fallback rows b ≠ 0) ∧
    finiteKL (rowKernel k hk ask past fallback rows) (rowKernel k' hk' ask past fallback rows) ≤
      32 * D * (m / n) ^ 2 := by
  have hcap := fun j => balancedCount_history_capacity n (k j) rows.length (hk j)
    m (theta j) hm (htheta j) (hbalance j) hbudget
  have hcap' := fun j => balancedCount_history_capacity n (k' j) rows.length (hk' j)
    m (theta' j) hm (htheta' j) (hbalance' j) hbudget
  have hcommon :
      (∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
        S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support) ↔
      (∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
        S ∈ (vectorColumnLaw Finset.univ k' (by simpa using hk')).support) := by
    constructor
    · exact vectorColumnLaw_history_transfer k k' (by simpa using hk) (by simpa using hk')
        ask past rows (by simpa using fun j => (hcap' j).1) (by simpa using fun j => (hcap' j).2)
    · exact vectorColumnLaw_history_transfer k' k (by simpa using hk') (by simpa using hk)
        ask past rows (by simpa using fun j => (hcap j).1) (by simpa using fun j => (hcap j).2)
  have hc : (0 : ℝ) ≤ 32 * D * (m / n) ^ 2 := by positivity
  by_cases hpos : ∃ S ∈ {S | vectorRowAnswers ask S past rows.length = rows},
      S ∈ (vectorColumnLaw Finset.univ k (by simpa using hk)).support
  · have hpos' := hcommon.mp hpos
    by_cases hrepeat : ask (past ++ rows) ∈ vectorQueriedLabels ask past rows
    · rw [rowKernel_repeated k hk ask past rows fallback hpos hrepeat,
        rowKernel_repeated k' hk' ask past rows fallback hpos' hrepeat]
      exact ⟨fun _ h => h, by simpa only [finiteKL_self] using hc⟩
    · rw [rowKernel_fresh k hk ask past rows fallback hpos hrepeat m theta hbalance,
        rowKernel_fresh k' hk' ask past rows fallback hpos' hrepeat m theta' hbalance']
      have hd : (vectorHistorySize ask past rows : ℝ) ≤ rows.length :=
        by exact_mod_cast vectorQueriedLabels_card_le ask past rows
      have hbudget' : 8 * m + 9 * (vectorHistorySize ask past rows : ℝ) ≤ n := by linarith
      have hb := fun j => nextSignProbability_bounds n m (vectorHistorySize ask past rows)
        (vectorHistorySum ask past rows j) (theta' j) (by exact_mod_cast hn) hm (Nat.cast_nonneg _)
        (vectorHistorySum_bounds ask past rows j) (htheta' j) hbudget'
      refine ⟨?_, nextRow_kl_bound D n m (vectorHistorySize ask past rows)
        (vectorHistorySum ask past rows) theta theta' (by exact_mod_cast hn) hm (Nat.cast_nonneg _)
          (vectorHistorySum_bounds ask past rows) htheta htheta' hbudget'⟩
      intro b hb0
      apply ne_of_gt
      unfold finiteProductWeight
      apply Finset.prod_pos
      intro j hj
      exact bitWeight_pos _ (by linarith [(hb j).1]) (by linarith [(hb j).2]) _
  · have hpos' := hcommon.not.mp hpos
    rw [rowKernel_inactive k hk ask past rows fallback hpos,
      rowKernel_inactive k' hk' ask past rows fallback hpos']
    exact ⟨fun _ h => h, by simpa only [finiteKL_self] using hc⟩

/-- Any adaptive strategy observing at most `q` rows has total pairwise
relative entropy at most `32 q D (m/n)^2` under the two hidden vectors. -/
theorem vectorRowTranscript_kl_le {n D : ℕ} (hn : 0 < n)
    (k k' : Fin D → ℕ) (hk : ∀ j, k j ≤ n) (hk' : ∀ j, k' j ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (theta theta' : Fin D → ℝ)
    (htheta : ∀ j, theta j = -1 ∨ theta j = 1)
    (htheta' : ∀ j, theta' j = -1 ∨ theta' j = 1)
    (hbalance : ∀ j, 2 * (k j : ℝ) = n + m * theta j)
    (hbalance' : ∀ j, 2 * (k' j : ℝ) = n + m * theta' j)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n) :
    finiteKL
      (fun v => (((vectorColumnLaw Finset.univ k (by simpa using hk)).map
        (fun S => runReplies (fun S hist j => decide (ask hist ∈ S j)) S past q)) v).toReal)
      (fun v => (((vectorColumnLaw Finset.univ k' (by simpa using hk')).map
        (fun S => runReplies (fun S hist j => decide (ask hist ∈ S j)) S past q)) v).toReal) ≤
        32 * q * D * (m / n) ^ 2 := by
  let fallback : Fin D → Bool := fun _ => false
  have hstep (rows : List (Fin D → Bool)) (hrows : rows.length < q) :=
    rowKernel_information hn k k' hk hk' m hm theta theta' htheta htheta' hbalance hbalance'
      ask past rows fallback (by
        have hl : (rows.length : ℝ) ≤ q := by exact_mod_cast hrows.le
        linarith)
  have h := runReplies_kl_le
    (vectorColumnLaw Finset.univ k (by simpa using hk))
    (vectorColumnLaw Finset.univ k' (by simpa using hk'))
    (fun S hist j => decide (ask hist ∈ S j)) (fun S hist j => decide (ask hist ∈ S j))
    past fallback q (32 * D * (m / n) ^ 2) (by positivity)
    (fun rows hh => (hstep rows hh).1) (fun rows hh => (hstep rows hh).2)
  convert h using 1 <;> ring

theorem vectorRowTranscript_support {n D : ℕ} (hn : 0 < n)
    (k k' : Fin D → ℕ) (hk : ∀ j, k j ≤ n) (hk' : ∀ j, k' j ≤ n)
    (m : ℝ) (hm : 0 ≤ m) (theta theta' : Fin D → ℝ)
    (htheta : ∀ j, theta j = -1 ∨ theta j = 1)
    (htheta' : ∀ j, theta' j = -1 ∨ theta' j = 1)
    (hbalance : ∀ j, 2 * (k j : ℝ) = n + m * theta j)
    (hbalance' : ∀ j, 2 * (k' j : ℝ) = n + m * theta' j)
    (ask : List (Fin D → Bool) → Fin n) (past : List (Fin D → Bool))
    (q : ℕ) (hbudget : 8 * m + 9 * (q : ℝ) ≤ n) (v : Fin q → Fin D → Bool)
    (hv : (((vectorColumnLaw Finset.univ k (by simpa using hk)).map
      (fun S => runReplies (fun S hist j => decide (ask hist ∈ S j)) S past q)) v).toReal ≠ 0) :
    (((vectorColumnLaw Finset.univ k' (by simpa using hk')).map
      (fun S => runReplies (fun S hist j => decide (ask hist ∈ S j)) S past q)) v).toReal ≠ 0 := by
  apply runReplies_support _ _ _ _ past (fun _ => false) q _ v hv
  intro rows hrows
  exact (rowKernel_information hn k k' hk hk' m hm theta theta' htheta htheta' hbalance hbalance'
    ask past rows (fun _ => false) (by
      have hl : (rows.length : ℝ) ≤ q := by exact_mod_cast hrows.le
      linarith)).1

end FullJet
