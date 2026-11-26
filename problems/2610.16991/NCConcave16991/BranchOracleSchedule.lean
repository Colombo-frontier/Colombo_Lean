import NCConcave16991.BranchOracleSupport

/-! # Arbitrary edge-index schedules in simultaneous branch rounds -/

namespace NCConcave16991.BranchOracle.WordProfile
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Each edge may select its own index, using the old lower-layer set. -/
def matrixScheduleStep (p : WordProfile ι) (schedule : ℕ → ι) : WordProfile ι where
  words t := (p.matrixStep (schedule (t - 1))).words t
  deletion := by
    intro t w hw
    change w ∈ p.words (t + 1) ∪ (p.words t).image (Fin.cons (schedule t)) at hw
    rcases Finset.mem_union.mp hw with ho | hn
    · exact p.words_subset_stepWords (schedule (t - 1)) t (p.deletion t w ho)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
      rw [Fin.tail_cons]
      exact p.words_subset_stepWords (schedule (t - 1)) t hv

theorem words_subset_matrixScheduleStep (p : WordProfile ι) (schedule : ℕ → ι) (t : ℕ) :
    p.words t ⊆ (p.matrixScheduleStep schedule).words t := p.words_subset_stepWords (schedule (t - 1)) t

theorem matrixScheduleStep_mass_zero (p : WordProfile ι) (schedule : ℕ → ι) :
    (p.matrixScheduleStep schedule).mass 0 = p.mass 0 := rfl

theorem matrixScheduleStep_mass_step (p : WordProfile ι) (schedule : ℕ → ι) (t : ℕ) :
    (p.matrixScheduleStep schedule).mass (t + 1) ≤ p.mass (t + 1) + p.mass t / (Fintype.card ι : ℝ) :=
  p.matrixStep_mass_step (schedule t) t

inductive ScheduledRun (ρ : ℝ) : ℕ → ℕ → WordProfile ι → Prop
  | initial : ScheduledRun ρ 0 0 root
  | matrix {k r : ℕ} {p : WordProfile ι} (prior : ScheduledRun ρ k r p) (schedule : ℕ → ι) :
      ScheduledRun ρ (k + 1) r (p.matrixScheduleStep schedule)
  | release {k r : ℕ} {p : WordProfile ι} (prior : ScheduledRun ρ k r p) (j : ℕ)
      (eligible : ρ ≤ p.mass j) : ScheduledRun ρ k (r + 1) (p.prefixReset j)

theorem ScheduledRun.accounting {ρ : ℝ} {k r : ℕ} {p : WordProfile ι} (h : ScheduledRun ρ k r p) :
    BranchAccounting.AccountingRun (Fintype.card ι : ℝ) ρ k r p.massProfile := by
  induction h with
  | initial => rw [root_massProfile]; exact BranchAccounting.AccountingRun.initial
  | @matrix k r p h schedule ih =>
    exact BranchAccounting.AccountingRun.matrix ih (p.matrixScheduleStep schedule).massProfile
      (p.matrixScheduleStep_mass_zero schedule).le (p.matrixScheduleStep_mass_step schedule)
  | @release k r p h j hel ih =>
    rw [prefixReset_massProfile]
    exact BranchAccounting.AccountingRun.release ih j hel

theorem ScheduledRun.chronological_bound {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    {k r : ℕ} {p : WordProfile ι} (h : ScheduledRun ρ k r p) (t : ℕ) :
    p.mass t ≤ BranchAccounting.accountingBound (Fintype.card ι : ℝ) ρ k r t := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact BranchAccounting.chronological_bound hn hρ hρone h.accounting t

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem schedule_forward_mem_wordSupport (p : WordProfile ι) (W : Submodule ℝ E) (t : ℕ)
    (schedule : ℕ → ι) (x : FormalLayer (ι := ι) E t) (hx : x ∈ wordSupport t (p.words t) W) :
    (formalBranchFamily E t).branch (schedule t) x ∈
      wordSupport (t + 1) ((p.matrixScheduleStep schedule).words (t + 1)) W :=
  forward_mem_wordSupport p W t (schedule t) x hx

theorem schedule_transpose_mem_wordSupport (p : WordProfile ι) (W : Submodule ℝ E) (t : ℕ)
    (schedule : ℕ → ι) (y : FormalLayer (ι := ι) E (t + 1)) (hy : y ∈ wordSupport (t + 1) (p.words (t + 1)) W) :
    ((formalBranchFamily E t).branch (schedule t)).toContinuousLinearMap.adjoint y ∈
      wordSupport t ((p.matrixScheduleStep schedule).words t) W := by
  exact wordSupport_mono (p.words_subset_matrixScheduleStep schedule t) le_rfl
    (transpose_mem_wordSupport p W t (schedule t) y hy)

end
end NCConcave16991.BranchOracle.WordProfile
