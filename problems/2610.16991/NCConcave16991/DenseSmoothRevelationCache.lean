import NCConcave16991.DenseSmoothRevelationAccounting

/-! # Exact released caches and the selected successor initialization row -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

def PastCorrect (A : Table E n T ρ) (s : State E n T hn ρ hρ) : Prop :=
  ∀ j : Fin (T + 1), j.val < frontier E n T hn ρ hρ s →
    (∀ i, s.base.rows j i = A.row i j) ∧ s.base.directions j = A.direction j

theorem paidQuery_control (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (rows : Fin n → E) (init : E) :
    (paidQuery E n T hn ρ hρ s o a complete direction rows init).base.control =
      Machine.appendControl E n T hn ρ hρ s.base.control o
        (referenceReply hn hρ
          (frontier E n T hn ρ hρ (paidQuery E n T hn ρ hρ s o a complete direction rows init))
          (paidQuery E n T hn ρ hρ s o a complete direction rows init).base.directions
          (fun i j ↦ (paidQuery E n T hn ρ hρ s o a complete direction rows init).base.rows j i) o) := by
  cases complete <;> by_cases hf : s.base.progress.1 < T + 1 <;>
    simp only [paidQuery, frontier, hf, ite_true, ite_false, Bool.false_eq_true, frontier, Machine.cachedReply]

theorem paidQuery_pastCorrect (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (hs : PastCorrect E n T hn ρ hρ A s) (o : Query E n T hn ρ hρ) (a init : E) (complete : Bool) :
    PastCorrect E n T hn ρ hρ A (paidQuery E n T hn ρ hρ s o a complete
      (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) init) := by
  by_cases hf : s.base.progress.1 < T + 1
  · have hjval : (stageIndex E n T hn ρ hρ s).val = s.base.progress.1 := Nat.mod_eq_of_lt hf
    cases complete with
    | false =>
        intro j hj
        simp only [paidQuery, frontier, hf, ite_true, Bool.false_eq_true, ite_false, frontier] at hj ⊢
        have hjne : j ≠ stageIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
        change (∀ i, ConeReferenceCache.putRow s.base.rows (stageIndex E n T hn ρ hρ s) o.1 a j i = A.row i j) ∧ _
        rw [ConeReferenceCache.putRow_other_stage _ _ _ _ _ hjne]
        exact hs j hj
    | true =>
        intro j hj
        have hjlt : j.val < frontier E n T hn ρ hρ s + 1 := by
          simpa only [paidQuery, frontier, hf, ite_true, frontier] using hj
        have hrow (i : Fin n) :
            (paidQuery E n T hn ρ hρ s o a true (A.direction (stageIndex E n T hn ρ hρ s))
              (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) init).base.rows j i =
            Function.update (ConeReferenceCache.putRow s.base.rows (stageIndex E n T hn ρ hρ s) o.1 a)
              (stageIndex E n T hn ρ hρ s) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) j i := by
          by_cases hnext : s.base.progress.1 + 1 < T + 1
          · have hnval : (successorIndex E n T hn ρ hρ s).val = frontier E n T hn ρ hρ s + 1 := Nat.mod_eq_of_lt hnext
            have hjne : j ≠ successorIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
            simp only [paidQuery, frontier, hf, ite_true, hnext]
            exact congrFun (ConeReferenceCache.putRow_other_stage _ _ _ _ _ hjne) i
          · simp only [paidQuery, frontier, hf, ite_true, hnext, ite_false]
        have hjold_of_ne (hje : j ≠ stageIndex E n T hn ρ hρ s) :
            j.val < frontier E n T hn ρ hρ s := by
          have hne : j.val ≠ s.base.progress.1 := fun he ↦ hje (Fin.ext (he.trans hjval.symm))
          change j.val < s.base.progress.1
          change j.val < s.base.progress.1 + 1 at hjlt
          omega
        constructor
        · intro i
          rw [hrow i]
          by_cases hje : j = stageIndex E n T hn ρ hρ s
          · subst j; simp only [Function.update_self]
          · rw [Function.update_of_ne hje, ConeReferenceCache.putRow_other_stage _ _ _ _ _ hje]
            exact (hs j (hjold_of_ne hje)).1 i
        · simp only [paidQuery, frontier, hf, ite_true]
          change Function.update s.base.directions (stageIndex E n T hn ρ hρ s)
            (A.direction (stageIndex E n T hn ρ hρ s)) j = A.direction j
          by_cases hje : j = stageIndex E n T hn ρ hρ s
          · subst j; simp only [Function.update_self]
          · rw [Function.update_of_ne hje]
            exact (hs j (hjold_of_ne hje)).2
  · intro j hj
    simp only [paidQuery, frontier, hf, ite_false, frontier] at hj ⊢
    exact hs j hj

theorem paidQuery_selected_row (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (o : Query E n T hn ρ hρ) (complete : Bool) (j : Fin (T + 1))
    (hj : j.val = frontier E n T hn ρ hρ
      (paidQuery E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s)) complete
        (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))
        (A.row o.1 (successorIndex E n T hn ρ hρ s)))) :
    (paidQuery E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s)) complete
      (A.direction (stageIndex E n T hn ρ hρ s)) (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s))
      (A.row o.1 (successorIndex E n T hn ρ hρ s))).base.rows j o.1 = A.row o.1 j := by
  by_cases hf : s.base.progress.1 < T + 1
  · cases complete with
    | false =>
        rw [paidQuery_frontier, if_neg (by simp)] at hj
        have he : j = stageIndex E n T hn ρ hρ s := by
          apply Fin.ext
          exact hj.trans (Nat.mod_eq_of_lt hf).symm
        subst j
        simpa only [paidQuery, frontier, hf, ite_true, Bool.false_eq_true, ite_false] using
          ConeReferenceCache.putRow_same s.base.rows (stageIndex E n T hn ρ hρ s) o.1 (A.row o.1 _)
    | true =>
        rw [paidQuery_frontier, if_pos ⟨hf, rfl⟩] at hj
        have hj' : j.val = frontier E n T hn ρ hρ s + 1 := hj
        have hnext : frontier E n T hn ρ hρ s + 1 < T + 1 := hj' ▸ j.isLt
        have hnext' : s.base.progress.1 + 1 < T + 1 := hnext
        have he : j = successorIndex E n T hn ρ hρ s := Fin.ext (hj'.trans (Nat.mod_eq_of_lt hnext).symm)
        subst j
        simp only [paidQuery, frontier, hf, ite_true, hnext', ConeReferenceCache.putRow_same]
  · rw [paidQuery_frontier, if_neg (by intro h; exact hf h.1)] at hj
    change j.val = s.base.progress.1 at hj
    omega

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

theorem stepWithTable_query (seed : Ω) (A : Table E n T ρ) (s : State E n T hn ρ hρ)
    (o : Query E n T hn ρ hρ) (ha : action E n T hn ρ hρ P seed s = Sum.inr o) :
    stepWithTable E n T hn ρ hρ P seed A s =
      paidQuery E n T hn ρ hρ s o (A.row o.1 (stageIndex E n T hn ρ hρ s))
        (completion E n T hn ρ hρ P seed A s) (A.direction (stageIndex E n T hn ρ hρ s))
        (fun i ↦ A.row i (stageIndex E n T hn ρ hρ s)) (A.row o.1 (successorIndex E n T hn ρ hρ s)) := by
  unfold stepWithTable step request initializationRequest
  rw [ha]
  simp only [Sum.elim_inr]
  by_cases hf : s.base.progress.1 < T + 1
  · simp only [frontier, hf, ite_true, Option.elim_some]
    cases hc : completion E n T hn ρ hρ P seed A s with
    | false => simp only [Bool.false_eq_true, ite_false, Option.elim_none, paidQuery, frontier, hf, ite_true]
    | true =>
        simp only [ite_true]
        by_cases hnext : s.base.progress.1 + 1 < T + 1
        · simp only [hnext, ite_true, Option.elim_some]
        · simp only [frontier, hnext, ite_false, Option.elim_none, paidQuery, hf, ite_true]
  · simp only [frontier, hf, ite_false, Option.elim_none, paidQuery]

theorem run_pastCorrect (seed : Ω) (A : Table E n T ρ) (t : ℕ) :
    PastCorrect E n T hn ρ hρ A (runWithTable E n T hn ρ hρ P seed A t) := by
  induction t with
  | zero => intro j hj; change j.val < 0 at hj; omega
  | succ t ih =>
      rw [runWithTable]
      cases ha : action E n T hn ρ hρ P seed (runWithTable E n T hn ρ hρ P seed A t) with
      | inl x =>
          intro j hj
          have hj' : j.val < frontier E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) := by
            simpa only [stepWithTable, step, ha, Sum.elim_inl, frontier] using hj
          simpa only [stepWithTable, step, ha, Sum.elim_inl, frontier] using ih j hj'
      | inr o =>
          rw [stepWithTable_query E n T hn ρ hρ P seed A _ o ha]
          exact paidQuery_pastCorrect E n T hn ρ hρ A _ ih o _ _ _

end

end NCConcave16991.DenseSmooth.Revelation
