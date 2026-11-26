import NCConcave16991.DenseSmoothRevelationEntry

/-! # The first stage entrance is selected from strict-past data -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n)
    (dx := primalDimension E T) Ω)

def FirstEntry (seed : Ω) (A : Table E n T ρ) (j : Fin (T + 1)) (t : ℕ) : Prop :=
  frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) < j.val ∧
  j.val ≤ frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A (t + 1))

theorem exists_firstEntry (seed : Ω) (A : Table E n T ρ) (j : Fin (T + 1))
    (hj : 0 < j.val) (N : ℕ)
    (hN : j.val ≤ frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N)) :
    ∃ t < N, FirstEntry E n T hn ρ hρ P seed A j t := by
  induction N with
  | zero => change j.val ≤ 0 at hN; omega
  | succ N ih =>
      by_cases h : j.val ≤ frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A N)
      · obtain ⟨t,ht,hfirst⟩ := ih h
        exact ⟨t,by omega,hfirst⟩
      · exact ⟨N,by omega,Nat.lt_of_not_ge h,hN⟩

theorem reached_iff_of_prefix (seed : Ω) (A B : Table E n T ρ) (j : Fin (T + 1))
    (hAB : SamePrefix E n T ρ j A B) (t : ℕ) :
    (j.val ≤ frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t)) ↔
      j.val ≤ frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t) := by
  have hh := run_prefix_eq E n T hn ρ hρ P seed j A B hAB t
  have hz (s : State E n T hn ρ hρ) :
      (prefixView E n T hn ρ hρ j s = none) ↔ j.val ≤ frontier E n T hn ρ hρ s := by
    by_cases h : frontier E n T hn ρ hρ s < j.val <;> simp [prefixView,h] <;> omega
  rw [← hz _,← hz _,hh]

theorem run_eq_before_entry (seed : Ω) (A B : Table E n T ρ) (j : Fin (T + 1))
    (hAB : SamePrefix E n T ρ j A B) (t : ℕ)
    (hb : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t) < j.val) :
    runWithTable E n T hn ρ hρ P seed A t = runWithTable E n T hn ρ hρ P seed B t := by
  have ha : frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) < j.val := by
    have hh := reached_iff_of_prefix E n T hn ρ hρ P seed A B j hAB t
    omega
  exact Option.some.inj (by simpa only [prefixView,ha,hb,ite_true] using
    (run_prefix_eq E n T hn ρ hρ P seed j A B hAB t))

theorem firstEntry_details (seed : Ω) (A : Table E n T ρ) (j : Fin (T + 1)) (t : ℕ)
    (ht : FirstEntry E n T hn ρ hρ P seed A j t) :
    frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) + 1 = j.val ∧
    ∃ o : Query E n T hn ρ hρ,
      action E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A t) = .inr o ∧
      completion E n T hn ρ hρ P seed A (runWithTable E n T hn ρ hρ P seed A t) = true := by
  let s := runWithTable E n T hn ρ hρ P seed A t
  change frontier E n T hn ρ hρ s + 1 = j.val ∧
    ∃ o : Query E n T hn ρ hρ, action E n T hn ρ hρ P seed s = .inr o ∧
      completion E n T hn ρ hρ P seed A s = true
  have hf : frontier E n T hn ρ hρ s < j.val := ht.1
  have hnxt : j.val ≤ frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) := ht.2
  have hb : frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) ≤
      frontier E n T hn ρ hρ s + 1 := by
    unfold stepWithTable
    exact (step_frontier_bounds E n T hn ρ hρ P seed s _ _ _ _ _).2
  refine ⟨by omega,?_⟩
  cases ha : action E n T hn ρ hρ P seed s with
  | inl x =>
      have he : frontier E n T hn ρ hρ (stepWithTable E n T hn ρ hρ P seed A s) = frontier E n T hn ρ hρ s := by
        simp only [stepWithTable,step,ha,Sum.elim_inl]
        rfl
      omega
  | inr o =>
      refine ⟨o,rfl,?_⟩
      cases hc : completion E n T hn ρ hρ P seed A s with
      | true => rfl
      | false =>
          rw [stepWithTable_noncompletion E n T hn ρ hρ P seed A s hc,precompletionStep_frontier] at hnxt
          omega

theorem firstEntry_eq_initialization (seed : Ω) (A B : Table E n T ρ)
    (j : Fin (T + 1)) (hAB : SamePrefix E n T ρ j A B) (t : ℕ)
    (ht : FirstEntry E n T hn ρ hρ P seed B j t) :
    ∃ o : Query E n T hn ρ hρ,
      action E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed B t) = .inr o ∧
      frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t) + 1 = j.val ∧
      runWithTable E n T hn ρ hρ P seed A (t + 1) =
        entryStart E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t) o
          (B.row o.1 (stageIndex E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t)))
          (B.direction (stageIndex E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t)))
          (fun i ↦ B.row i (stageIndex E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed B t)))
          (A.row o.1 j) := by
  let s := runWithTable E n T hn ρ hρ P seed B t
  have hf : frontier E n T hn ρ hρ s < j.val := ht.1
  have hv : frontier E n T hn ρ hρ s < T + 1 := hf.trans j.isLt
  obtain ⟨hfj,o,ho,hcB⟩ := firstEntry_details E n T hn ρ hρ P seed B j t ht
  have hs : runWithTable E n T hn ρ hρ P seed A t = s :=
    run_eq_before_entry E n T hn ρ hρ P seed A B j hAB t hf
  have hc : completion E n T hn ρ hρ P seed A s = true :=
    (completion_eq_of_prefix E n T hn ρ hρ P seed j A B hAB s hf).trans hcB
  have hi : (stageIndex E n T hn ρ hρ s).val < j.val := by
    change frontier E n T hn ρ hρ s % (T + 1) < j.val
    rw [Nat.mod_eq_of_lt hv]
    exact hf
  have hnxt : successorIndex E n T hn ρ hρ s = j := by
    apply Fin.ext
    change (frontier E n T hn ρ hρ s + 1) % (T + 1) = j.val
    rw [hfj,Nat.mod_eq_of_lt j.isLt]
  refine ⟨o,ho,hfj,?_⟩
  rw [runWithTable,hs,stepWithTable_eq_entry E n T hn ρ hρ P seed A s o ho hc,
    hnxt,(hAB _ hi).1,(hAB _ hi).2 o.1]
  congr 1
  exact funext (hAB _ hi).2

end
end NCConcave16991.DenseSmooth.Revelation
