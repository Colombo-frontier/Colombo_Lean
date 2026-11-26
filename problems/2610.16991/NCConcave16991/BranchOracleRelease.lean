import NCConcave16991.BranchOracleSchedule

/-! # A terminating eager prefix-release closure of the concrete word process -/

namespace NCConcave16991.BranchOracle.WordProfile
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {M : ℕ}

def ReleaseClosed (ρ : ℝ) (site : Fin M → ℕ) (r : ℕ) (p : WordProfile ι) : Prop :=
  ∀ j : Fin M, r ≤ j.val → p.mass (site j) < ρ

/-- Only the first unreleased site is tested; deletion monotonicity makes
failure of that test close the entire remaining suffix. -/
def closeAux (ρ : ℝ) (site : Fin M → ℕ) : ℕ → ℕ → WordProfile ι → ℕ × WordProfile ι
  | 0, r, p => (r, p)
  | fuel + 1, r, p =>
      if hr : r < M then
        if ρ ≤ p.mass (site ⟨r, hr⟩) then
          closeAux ρ site fuel (r + 1) (p.prefixReset (site ⟨r, hr⟩))
        else (r, p)
      else (r, p)

theorem closeAux_ge (ρ : ℝ) (site : Fin M → ℕ) (fuel r : ℕ) (p : WordProfile ι) :
    r ≤ (closeAux ρ site fuel r p).1 := by
  induction fuel generalizing r p with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [closeAux]
    split_ifs with hr hel
    · exact (Nat.le_succ r).trans (ih (r + 1) _)
    · exact le_rfl
    · exact le_rfl

theorem closeAux_le (ρ : ℝ) (site : Fin M → ℕ) (fuel r : ℕ) (p : WordProfile ι) (hr : r ≤ M) :
    (closeAux ρ site fuel r p).1 ≤ M := by
  induction fuel generalizing r p with
  | zero => exact hr
  | succ fuel ih =>
    simp only [closeAux]
    split_ifs with hlt hel
    · exact ih (r + 1) _ (by omega)
    · exact hr
    · exact hr

theorem closed_of_frontier_ineligible (ρ : ℝ) (site : Fin M → ℕ) (hsite : Monotone site)
    (r : ℕ) (p : WordProfile ι) (hr : r < M) (hel : ¬ρ ≤ p.mass (site ⟨r, hr⟩)) :
    ReleaseClosed ρ site r p := by
  intro j hj
  exact (p.massProfile.antitone (hsite (show (⟨r, hr⟩ : Fin M) ≤ j from hj))).trans_lt (lt_of_not_ge hel)

theorem closeAux_closed (ρ : ℝ) (site : Fin M → ℕ) (hsite : Monotone site)
    (fuel r : ℕ) (p : WordProfile ι) (hbound : M ≤ fuel + r) :
    ReleaseClosed ρ site (closeAux ρ site fuel r p).1 (closeAux ρ site fuel r p).2 := by
  induction fuel generalizing r p with
  | zero =>
    intro j hj
    have hh : j.val < M := j.isLt
    simp only [closeAux] at hj
    omega
  | succ fuel ih =>
    simp only [closeAux]
    split_ifs with hr hel
    · exact ih (r + 1) _ (by omega)
    · exact closed_of_frontier_ineligible ρ site hsite r p hr hel
    · intro j hj
      have hh := j.isLt
      omega

/-- Every reset performed by eager closure is an actual legal source release. -/
theorem closeAux_scheduledRun (ρ : ℝ) (site : Fin M → ℕ) (fuel r k : ℕ) (p : WordProfile ι)
    (h : ScheduledRun ρ k r p) :
    ScheduledRun ρ k (closeAux ρ site fuel r p).1 (closeAux ρ site fuel r p).2 := by
  induction fuel generalizing r p with
  | zero => exact h
  | succ fuel ih =>
    simp only [closeAux]
    split_ifs with hr hel
    · exact ih (r + 1) _ (ScheduledRun.release h (site ⟨r, hr⟩) hel)
    · exact h
    · exact h

def close (ρ : ℝ) (site : Fin M → ℕ) (r : ℕ) (p : WordProfile ι) : ℕ × WordProfile ι :=
  closeAux ρ site M r p

theorem close_closed (ρ : ℝ) (site : Fin M → ℕ) (hsite : Monotone site) (r : ℕ) (p : WordProfile ι) :
    ReleaseClosed ρ site (close ρ site r p).1 (close ρ site r p).2 :=
  closeAux_closed ρ site hsite M r p (by omega)

theorem close_scheduledRun (ρ : ℝ) (site : Fin M → ℕ) (r k : ℕ) (p : WordProfile ι)
    (h : ScheduledRun ρ k r p) : ScheduledRun ρ k (close ρ site r p).1 (close ρ site r p).2 :=
  closeAux_scheduledRun ρ site M r k p h

theorem close_release_bound (ρ : ℝ) (site : Fin M → ℕ) (r : ℕ) (p : WordProfile ι) (hr : r ≤ M) :
    r ≤ (close ρ site r p).1 ∧ (close ρ site r p).1 ≤ M :=
  ⟨closeAux_ge ρ site M r p, closeAux_le ρ site M r p hr⟩

end
end NCConcave16991.BranchOracle.WordProfile
