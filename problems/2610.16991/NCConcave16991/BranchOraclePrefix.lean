import NCConcave16991.BranchOracleReferenceInvariants
import NCConcave16991.BranchOracleFlat

/-! # The actual release counter fills exactly the public source prefix -/

namespace NCConcave16991.BranchOracle.WordProfile
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def PrefixFilled (p : WordProfile ι) (s : ℕ) : Prop := ∀ t, t ≤ s → p.words t = Finset.univ

theorem root_prefixFilled : PrefixFilled (root : WordProfile ι) 0 := by
  intro t ht
  have he : t = 0 := by omega
  subst t
  rfl

theorem prefixReset_prefixFilled (p : WordProfile ι) (s : ℕ) : PrefixFilled (p.prefixReset s) s := by
  intro t ht
  simp only [prefixReset, if_pos ht]

theorem PrefixFilled.mono {p q : WordProfile ι} (h : WordsExtend p q) {s : ℕ} (hp : PrefixFilled p s) : PrefixFilled q s := by
  intro t ht
  apply Finset.eq_univ_iff_forall.mpr
  intro w
  apply h t
  rw [hp t ht]
  exact Finset.mem_univ _

theorem closeAux_prefixFilled {M m : ℕ} (ρ : ℝ) (fuel r : ℕ) (p : WordProfile ι)
    (hp : PrefixFilled p (r * (m + 1))) :
    PrefixFilled (closeAux ρ (macroSite (M := M) m) fuel r p).2
      ((closeAux ρ (macroSite (M := M) m) fuel r p).1 * (m + 1)) := by
  induction fuel generalizing r p with
  | zero => exact hp
  | succ fuel ih =>
    simp only [closeAux]
    split_ifs with hr hel
    · apply ih
      have hh := prefixReset_prefixFilled p (macroSite m (⟨r, hr⟩ : Fin M))
      simpa only [macroSite, Nat.succ_mul, Nat.add_mul, one_mul] using hh
    · exact hp
    · exact hp

theorem close_prefixFilled {M m : ℕ} (ρ : ℝ) (r : ℕ) (p : WordProfile ι)
    (hp : PrefixFilled p (r * (m + 1))) :
    PrefixFilled (close ρ (macroSite (M := M) m) r p).2
      ((close ρ (macroSite (M := M) m) r p).1 * (m + 1)) :=
  closeAux_prefixFilled ρ M r p hp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem PrefixFilled.target_mem {p : WordProfile ι} {s t : ℕ} (hp : PrefixFilled p s) (ht : t ≤ s)
    (W : Submodule ℝ E) (e : E) : formalTarget E t e ∈ wordSupport t (p.words t) W := by
  intro w hw
  rw [hp t ht] at hw
  exact (hw (Finset.mem_univ _)).elim

end
end NCConcave16991.BranchOracle.WordProfile

namespace NCConcave16991.BranchOracle.Reference
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n M m : ℕ} [NeZero n] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
variable {D : ℝ} (K : KnownDualDomain (dualDimension (MacroSpaces (ι := Fin n) E M m)) D)
  (Q : ∀ t : ℕ, FormalLayer (ι := Fin n) E t ≃ₗᵢ[ℝ] FormalLayer (ι := Fin n) E t) (e : E)
  (ρ d c μ : ℝ)

theorem step_prefixFilled (s : State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (q : OracleQuery n (primalDimension (MacroSpaces (ι := Fin n) E M m)) K)
    (hp : WordProfile.PrefixFilled s.profile (s.released * (m + 1))) :
    WordProfile.PrefixFilled
      (step (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ s q).profile
      ((step (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ s q).released * (m + 1)) :=
  WordProfile.close_prefixFilled ρ s.released _
    (hp.mono (WordProfile.matrixScheduleStep_words_extend s.profile (fun _ ↦ q.1)))

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy K (n := n) (dx := primalDimension (MacroSpaces (ι := Fin n) E M m)) Ω)

theorem runAux_prefixFilled (seed : Ω) (t : ℕ) (s : State (n := n) (MacroSpaces (ι := Fin n) E M m) K)
    (hp : WordProfile.PrefixFilled s.profile (s.released * (m + 1))) :
    WordProfile.PrefixFilled
      (runAux (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ P seed t s).2.profile
      ((runAux (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ P seed t s).2.released * (m + 1)) := by
  induction t generalizing s with
  | zero => exact hp
  | succ t ih =>
    cases hn : P.next seed s.history with
    | inl x => simpa only [runAux, hn] using hp
    | inr q => simpa only [runAux, hn] using ih _ (step_prefixFilled E K Q e ρ d c μ s q hp)

theorem run_prefixFilled (seed : Ω) (budget : ℕ) :
    WordProfile.PrefixFilled
      (run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ P seed budget).2.profile
      ((run (MacroSpaces (ι := Fin n) E M m) K (macroBranches E Q) (incomingSources E Q e) (terminalSources E Q e)
        ρ (macroSite (M := M) m) d c μ P seed budget).2.released * (m + 1)) := by
  apply runAux_prefixFilled E K Q e ρ d c μ P seed budget
  simpa only [initial, Nat.zero_mul] using (WordProfile.root_prefixFilled (ι := Fin n))

end
end NCConcave16991.BranchOracle.Reference
