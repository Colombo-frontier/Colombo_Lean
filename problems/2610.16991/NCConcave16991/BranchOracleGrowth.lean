import NCConcave16991.BranchOracleRelease

/-! # Previously exposed support survives every actual round and closure -/

namespace NCConcave16991.BranchOracle.WordProfile
noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {M : ℕ}

def WordsExtend (p q : WordProfile ι) : Prop := ∀ t, p.words t ⊆ q.words t

theorem WordsExtend.refl (p : WordProfile ι) : WordsExtend p p := fun _ ↦ Finset.Subset.refl _

theorem WordsExtend.trans {p q r : WordProfile ι} (h : WordsExtend p q) (h' : WordsExtend q r) :
    WordsExtend p r := fun t ↦ (h t).trans (h' t)

theorem prefixReset_words_extend (p : WordProfile ι) (j : ℕ) : WordsExtend p (p.prefixReset j) := by
  intro t w hw
  by_cases ht : t ≤ j
  · simp [prefixReset, ht]
  · simpa only [prefixReset, if_neg ht] using hw

theorem matrixScheduleStep_words_extend (p : WordProfile ι) (schedule : ℕ → ι) :
    WordsExtend p (p.matrixScheduleStep schedule) := p.words_subset_matrixScheduleStep schedule

theorem closeAux_words_extend (ρ : ℝ) (site : Fin M → ℕ) (fuel r : ℕ) (p : WordProfile ι) :
    WordsExtend p (closeAux ρ site fuel r p).2 := by
  induction fuel generalizing r p with
  | zero => exact WordsExtend.refl p
  | succ fuel ih =>
    simp only [closeAux]
    split_ifs with hr hel
    · exact (prefixReset_words_extend p _).trans (ih (r + 1) _)
    · exact WordsExtend.refl p
    · exact WordsExtend.refl p

theorem close_words_extend (ρ : ℝ) (site : Fin M → ℕ) (r : ℕ) (p : WordProfile ι) :
    WordsExtend p (close ρ site r p).2 := closeAux_words_extend ρ site M r p

theorem roundClosure_words_extend (ρ : ℝ) (site : Fin M → ℕ) (r : ℕ) (p : WordProfile ι) (schedule : ℕ → ι) :
    WordsExtend p (close ρ site r (p.matrixScheduleStep schedule)).2 :=
  (matrixScheduleStep_words_extend p schedule).trans (close_words_extend ρ site r _)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem WordsExtend.support {p q : WordProfile ι} (h : WordsExtend p q) (W : Submodule ℝ E) (t : ℕ) :
    wordSupport t (p.words t) W ≤ wordSupport t (q.words t) W := wordSupport_mono (h t) le_rfl

end
end NCConcave16991.BranchOracle.WordProfile
