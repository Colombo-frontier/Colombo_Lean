import NCConcave16991.DenseSmoothRevelationAccounting

/-! # Literal assigned-call costs of completed and not-yet-current stages -/

namespace NCConcave16991.DenseSmooth.Revelation

noncomputable section

open Set MeasureTheory

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (n T : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)

theorem paidQuery_assigned_current (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (rows : Fin n → E) (init : E)
    (hf : frontier E n T hn ρ hρ s < T + 1) :
    (paidQuery E n T hn ρ hρ s o a complete direction rows init).assigned (stageIndex E n T hn ρ hρ s) =
      s.assigned (stageIndex E n T hn ρ hρ s) + 1 := by
  rw [paidQuery_assigned, if_pos hf, Function.update_self]

theorem paidQuery_assigned_past (s : State E n T hn ρ hρ) (o : Query E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (rows : Fin n → E) (init : E)
    (j : Fin (T + 1)) (hj : j.val < frontier E n T hn ρ hρ s) :
    (paidQuery E n T hn ρ hρ s o a complete direction rows init).assigned j = s.assigned j := by
  rw [paidQuery_assigned]
  split_ifs with hf
  · have hidx : (stageIndex E n T hn ρ hρ s).val = frontier E n T hn ρ hρ s := Nat.mod_eq_of_lt hf
    have hjne : j ≠ stageIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
    exact Function.update_of_ne hjne _ _
  · rfl

def FutureZero (s : State E n T hn ρ hρ) : Prop :=
  ∀ j : Fin (T + 1), frontier E n T hn ρ hρ s < j.val → s.assigned j = 0

theorem paidQuery_futureZero (s : State E n T hn ρ hρ) (hs : FutureZero E n T hn ρ hρ s)
    (o : Query E n T hn ρ hρ) (a : E) (complete : Bool) (direction : E) (rows : Fin n → E) (init : E) :
    FutureZero E n T hn ρ hρ (paidQuery E n T hn ρ hρ s o a complete direction rows init) := by
  intro j hj
  have hb := (paidQuery_frontier_bounds E n T hn ρ hρ s o a complete direction rows init).1
  have hjold : frontier E n T hn ρ hρ s < j.val := by omega
  rw [paidQuery_assigned]
  split_ifs with hf
  · have hidx : (stageIndex E n T hn ρ hρ s).val = frontier E n T hn ρ hρ s := Nat.mod_eq_of_lt hf
    have hjne : j ≠ stageIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
    rw [Function.update_of_ne hjne]
    exact hs j hjold
  · exact hs j hjold

theorem paidQuery_entry_cost_zero (s : State E n T hn ρ hρ) (hs : FutureZero E n T hn ρ hρ s)
    (o : Query E n T hn ρ hρ) (a direction : E) (rows : Fin n → E) (init : E)
    (hf : frontier E n T hn ρ hρ s + 1 < T + 1) :
    (paidQuery E n T hn ρ hρ s o a true direction rows init).assigned
      (successorIndex E n T hn ρ hρ s) = 0 := by
  have hvalid : frontier E n T hn ρ hρ s < T + 1 := by omega
  have hidx : (stageIndex E n T hn ρ hρ s).val = frontier E n T hn ρ hρ s := Nat.mod_eq_of_lt hvalid
  have hnxt : (successorIndex E n T hn ρ hρ s).val = frontier E n T hn ρ hρ s + 1 := Nat.mod_eq_of_lt hf
  have hne : successorIndex E n T hn ρ hρ s ≠ stageIndex E n T hn ρ hρ s := by intro he; have := congrArg Fin.val he; omega
  rw [paidQuery_assigned, if_pos hvalid, Function.update_of_ne hne]
  exact hs _ (by omega)

variable {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain n T hn ρ hρ) (n := n) (dx := primalDimension E T) Ω)

theorem step_futureZero (seed : Ω) (s : State E n T hn ρ hρ) (hs : FutureZero E n T hn ρ hρ s)
    (a : E) (complete : Bool) (direction : E) (rows : Fin n → E) (init : E) :
    FutureZero E n T hn ρ hρ (step E n T hn ρ hρ P seed s a complete direction rows init) := by
  unfold step
  cases action E n T hn ρ hρ P seed s with
  | inl x => exact hs
  | inr o => exact paidQuery_futureZero E n T hn ρ hρ s hs o a complete direction rows init

theorem run_futureZero (seed : Ω) (A : Table E n T ρ) (t : ℕ) :
    FutureZero E n T hn ρ hρ (runWithTable E n T hn ρ hρ P seed A t) := by
  induction t with
  | zero => intro j hj; rfl
  | succ t ih =>
      rw [runWithTable, stepWithTable]
      exact step_futureZero E n T hn ρ hρ P seed _ ih _ _ _ _ _

theorem step_assigned_past (seed : Ω) (s : State E n T hn ρ hρ)
    (a : E) (complete : Bool) (direction : E) (rows : Fin n → E) (init : E)
    (j : Fin (T + 1)) (hj : j.val < frontier E n T hn ρ hρ s) :
    (step E n T hn ρ hρ P seed s a complete direction rows init).assigned j = s.assigned j := by
  unfold step
  cases action E n T hn ρ hρ P seed s with
  | inl x => rfl
  | inr o => exact paidQuery_assigned_past E n T hn ρ hρ s o a complete direction rows init j hj

end

end NCConcave16991.DenseSmooth.Revelation
