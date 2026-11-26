import NCConcave16991.BranchOracleWords

/-! # Concrete source releases and chronological branch accounting -/

namespace NCConcave16991.BranchOracle.WordProfile
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def prefixReset (p : WordProfile ι) (j : ℕ) : WordProfile ι where
  words t := if t ≤ j then Finset.univ else p.words t
  deletion := by
    intro t w hw
    by_cases ht : t ≤ j
    · simp [ht]
    · have ht' : ¬t + 1 ≤ j := by omega
      simp only [if_neg ht'] at hw
      simp only [if_neg ht]
      exact p.deletion t w hw

theorem prefixReset_mass (p : WordProfile ι) (j t : ℕ) :
    (p.prefixReset j).mass t = if t ≤ j then 1 else p.mass t := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases ht : t ≤ j
  · simp only [mass, prefixReset, if_pos ht, Finset.card_univ]
    have hc : (Fintype.card (Word ι t) : ℝ) = (Fintype.card ι : ℝ) ^ t := by
      norm_cast
      simp [Word]
    rw [hc, div_self (pow_ne_zero _ hn.ne')]
  · simp only [mass, prefixReset, if_neg ht]

private theorem massProfile_ext (p q : BranchAccounting.MassProfile) (h : ∀ t, p t = q t) : p = q := by
  obtain ⟨pm, pn, po, pa⟩ := p
  obtain ⟨qm, qn, qo, qa⟩ := q
  have he : pm = qm := funext h
  cases he
  rfl

theorem root_massProfile : (root (ι := ι)).massProfile = BranchAccounting.rootMass := by
  apply massProfile_ext
  intro t
  change (root (ι := ι)).mass t = if t = 0 then 1 else 0
  by_cases ht : t = 0
  · subst t
    simp [mass, root, Word]
  · simp [mass, root, ht]

theorem prefixReset_massProfile (p : WordProfile ι) (j : ℕ) :
    (p.prefixReset j).massProfile = BranchAccounting.prefixReset p.massProfile j := by
  apply massProfile_ext
  intro t
  exact p.prefixReset_mass j t

/-- A literal chronology of simultaneous selected-index rounds and legal
source releases. Every update uses the old lower-layer word set. -/
inductive Run (ρ : ℝ) : ℕ → ℕ → WordProfile ι → Prop
  | initial : Run ρ 0 0 root
  | matrix {k r : ℕ} {p : WordProfile ι} (prior : Run ρ k r p) (i : ι) :
      Run ρ (k + 1) r (p.matrixStep i)
  | release {k r : ℕ} {p : WordProfile ι} (prior : Run ρ k r p) (j : ℕ)
      (eligible : ρ ≤ p.mass j) : Run ρ k (r + 1) (p.prefixReset j)

/-- The abstract accounting chronology is derived from actual word sets. -/
theorem Run.accounting {ρ : ℝ} {k r : ℕ} {p : WordProfile ι} (h : Run ρ k r p) :
    BranchAccounting.AccountingRun (Fintype.card ι : ℝ) ρ k r p.massProfile := by
  induction h with
  | initial => rw [root_massProfile]; exact BranchAccounting.AccountingRun.initial
  | @matrix k r p h i ih =>
    exact BranchAccounting.AccountingRun.matrix ih (p.matrixStep i).massProfile
      (p.matrixStep_mass_zero i).le (p.matrixStep_mass_step i)
  | @release k r p h j hel ih =>
    rw [prefixReset_massProfile]
    exact BranchAccounting.AccountingRun.release ih j hel

theorem Run.chronological_bound {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    {k r : ℕ} {p : WordProfile ι} (h : Run ρ k r p) (t : ℕ) :
    p.mass t ≤ BranchAccounting.accountingBound (Fintype.card ι : ℝ) ρ k r t := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact BranchAccounting.chronological_bound hn hρ hρone h.accounting t

theorem Run.mass_eq_zero_of_rounds_lt_depth {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    {k r : ℕ} {p : WordProfile ι} (h : Run ρ k r p) (t : ℕ) (hkt : k < t) : p.mass t = 0 := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact BranchAccounting.mass_eq_zero_of_rounds_lt_depth hn hρ hρone h.accounting t hkt

theorem eligible_prefix (p : WordProfile ι) {ρ : ℝ} {j k : ℕ} (hj : ρ ≤ p.mass j) (hkj : k ≤ j) :
    ρ ≤ p.mass k := hj.trans (p.massProfile.antitone hkj)

end
end NCConcave16991.BranchOracle.WordProfile
