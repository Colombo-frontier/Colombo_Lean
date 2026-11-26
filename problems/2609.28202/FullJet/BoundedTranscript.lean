import FullJet.TranscriptLaw

open scoped BigOperators

namespace FullJet

variable {β : Type*} [Fintype β]

theorem finiteKL_self (p : β → ℝ) : finiteKL p p = 0 := by
  classical
  unfold finiteKL
  apply Finset.sum_eq_zero
  intro b hb
  by_cases h : p b = 0 <;> simp [h]

theorem transcriptWeight_congr_of_length (K L : List β → β → ℝ) (budget : ℕ)
    (h : ∀ hist, hist.length < budget → K hist = L hist)
    (past : List β) (q : ℕ) (hq : past.length + q ≤ budget) (v : Fin q → β) :
    transcriptWeight K past q v = transcriptWeight L past q v := by
  induction q generalizing past with
  | zero => rfl
  | succ q ih =>
    rw [transcriptWeight, transcriptWeight, h past (by omega)]
    rw [ih (past ++ [v 0]) (by simp only [List.length_append, List.length_singleton]; omega)]

/-- Information bounds need only hold before the specified finite horizon. -/
theorem transcriptWeight_support_of_length (K L : List β → β → ℝ) (budget : ℕ)
    (h : ∀ hist, hist.length < budget → ∀ b, K hist b ≠ 0 → L hist b ≠ 0)
    (past : List β) (q : ℕ) (hq : past.length + q ≤ budget) (v : Fin q → β)
    (hv : transcriptWeight K past q v ≠ 0) : transcriptWeight L past q v ≠ 0 := by
  induction q generalizing past with
  | zero => simp [transcriptWeight]
  | succ q ih =>
    obtain ⟨hfirst, htail⟩ := mul_ne_zero_iff.mp hv
    apply mul_ne_zero (h past (by omega) (v 0) hfirst)
    exact ih (past ++ [v 0]) (by simp only [List.length_append, List.length_singleton]; omega) _ htail

theorem runReplies_support {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (p : PMF Ω) (p' : PMF Ω') (reply : Ω → List β → β) (reply' : Ω' → List β → β)
    (base : List β) (fallback : β) (q : ℕ)
    (hAC : ∀ hist, hist.length < q → ∀ b,
      historyKernelWeight p reply base fallback hist b ≠ 0 →
        historyKernelWeight p' reply' base fallback hist b ≠ 0)
    (v : Fin q → β) (hv : ((p.map (fun ω => runReplies reply ω base q)) v).toReal ≠ 0) :
    ((p'.map (fun ω => runReplies reply' ω base q)) v).toReal ≠ 0 := by
  rw [runReplies_mass p reply base fallback] at hv
  rw [runReplies_mass p' reply' base fallback]
  exact transcriptWeight_support_of_length _ _ q hAC [] q (by simp) v hv

/-- Information bounds need only hold before the specified finite horizon. -/
theorem transcriptKL_le_bounded (K L : List β → β → ℝ) (fallback : β) (budget : ℕ)
    (hK0 : ∀ past b, 0 ≤ K past b) (hK : ∀ past, ∑ b, K past b = 1)
    (hKL : ∀ past, past.length < budget → ∀ b, K past b ≠ 0 → L past b ≠ 0)
    (c : ℝ) (hc : 0 ≤ c)
    (hstep : ∀ past, past.length < budget → finiteKL (K past) (L past) ≤ c) :
    finiteKL (transcriptWeight K [] budget) (transcriptWeight L [] budget) ≤ budget * c := by
  classical
  let R : β → ℝ := fun b => ((PMF.pure fallback) b).toReal
  let K' : List β → β → ℝ := fun past => if past.length < budget then K past else R
  let L' : List β → β → ℝ := fun past => if past.length < budget then L past else R
  have heqK : transcriptWeight K [] budget = transcriptWeight K' [] budget := by
    funext v
    exact transcriptWeight_congr_of_length K K' budget
      (fun hist hh => by simp [K', hh]) [] budget (by simp) v
  have heqL : transcriptWeight L [] budget = transcriptWeight L' [] budget := by
    funext v
    exact transcriptWeight_congr_of_length L L' budget
      (fun hist hh => by simp [L', hh]) [] budget (by simp) v
  rw [heqK, heqL]
  apply transcriptKL_le K' L'
  · intro past b
    by_cases hh : past.length < budget
    · simpa [K', hh] using hK0 past b
    · simp only [K', if_neg hh, R]
      exact ENNReal.toReal_nonneg
  · intro past
    by_cases hh : past.length < budget
    · simpa [K', hh] using hK past
    · simpa [K', hh, R] using pmf_toReal_sum (PMF.pure fallback)
  · intro past b hb
    by_cases hh : past.length < budget
    · simpa only [L', if_pos hh] using
        hKL past hh b (by simpa [K', hh] using hb)
    · simpa only [K', L', if_neg hh] using hb
  · intro past
    by_cases hh : past.length < budget
    · simpa [K', L', hh] using hstep past hh
    · simpa only [K', L', if_neg hh, finiteKL_self] using hc

/-- The accumulated information estimate now applies to actual adaptive
pushforward distributions of latent samples. -/
theorem runReplies_kl_le {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']
    (p : PMF Ω) (p' : PMF Ω') (reply : Ω → List β → β) (reply' : Ω' → List β → β)
    (base : List β) (fallback : β) (q : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hAC : ∀ hist, hist.length < q → ∀ b,
      historyKernelWeight p reply base fallback hist b ≠ 0 →
        historyKernelWeight p' reply' base fallback hist b ≠ 0)
    (hstep : ∀ hist, hist.length < q →
      finiteKL (historyKernelWeight p reply base fallback hist)
        (historyKernelWeight p' reply' base fallback hist) ≤ c) :
    finiteKL (fun v => ((p.map (fun ω => runReplies reply ω base q)) v).toReal)
      (fun v => ((p'.map (fun ω => runReplies reply' ω base q)) v).toReal) ≤ q * c := by
  simp_rw [runReplies_mass p reply base fallback, runReplies_mass p' reply' base fallback]
  exact transcriptKL_le_bounded _ _ fallback q
    (historyKernelWeight_nonneg p reply base fallback)
    (historyKernelWeight_sum p reply base fallback) hAC c hc hstep

end FullJet
