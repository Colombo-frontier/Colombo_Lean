import RationalMaterializedState254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem compactAmbient_invariant (t : ℕ) :
    RationalSparseInvariant W C.allLo (C.hi : ℝ) ((standardRationalSchedule T K).live t)
      ((CompactRationalSparseData.restrict (C.run t) ((standardRationalSchedule T K).live t)).ambient
        (rationalHistoryInitial C.initial_mean C.hi)) := by
  have hw := CompactRationalSparseData.restrict_weightView (C.run t) (C.invariant t).support
  constructor
  · intro e
    by_cases he : e∈(standardRationalSchedule T K).live t
    · simpa [CompactRationalSparseData.ambient,CompactRationalSparseData.restrict,he] using
        (C.invariant t).histories e
    · simpa [CompactRationalSparseData.ambient,CompactRationalSparseData.restrict,he] using
        (C.initial_invariant).histories e
  · change ∀ e,0≤(CompactRationalSparseData.restrict (C.run t) _).weightView e
    rw [hw]
    exact (C.invariant t).nonneg
  · change (∑ e,(CompactRationalSparseData.restrict (C.run t) _).weightView e)=1
    rw [hw]
    exact (C.invariant t).total
  · exact CompactRationalSparseData.weightView_support _

def materializedRun (C : RationalSparseConstruction d T K D G eta W)
    (roundCost projectionCost gradientCost : ℕ) : ℕ → MaterializedRationalSparseData d ((T+1)*(K+1))
  | 0 => MaterializedRationalSparseData.ofCompact
      (CompactRationalSparseData.restrict C.initial ((standardRationalSchedule T K).live 0))
      (rationalHistoryInitial C.initial_mean C.hi)
  | t+1 => (materializedRun C roundCost projectionCost gradientCost t).step
      C.master_precision roundCost projectionCost gradientCost C.oracle C.allCfg
      ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) C.lam
      (rationalHistoryInitial C.initial_mean C.hi) (C.query t)

/-- The executable list transition agrees with the trajectory whose regret
was proved. The list is pruned at every round, so no extinct history is retained. -/
theorem materializedRun_refines (roundCost projectionCost gradientCost t : ℕ) (ht : t≤T) :
    (C.materializedRun roundCost projectionCost gradientCost t).compactView
      ((standardRationalSchedule T K).live t) (rationalHistoryInitial C.initial_mean C.hi)=
        CompactRationalSparseData.restrict (C.run t) ((standardRationalSchedule T K).live t) := by
  induction t with
  | zero => exact MaterializedRationalSparseData.compactView_ofCompact _ _
  | succ t ih =>
    have ih' := ih (by omega)
    have hS : RationalSparseInvariant W C.allLo (C.hi : ℝ) ((standardRationalSchedule T K).live t)
        (((C.materializedRun roundCost projectionCost gradientCost t).compactView
          ((standardRationalSchedule T K).live t) (rationalHistoryInitial C.initial_mean C.hi)).ambient
            (rationalHistoryInitial C.initial_mean C.hi)) := by
      rw [ih']
      exact C.compactAmbient_invariant t
    have hs := MaterializedRationalSparseData.step_compactView C.dimension_pos W
      (C.materializedRun roundCost projectionCost gradientCost t) C.master_precision roundCost projectionCost gradientCost
      C.oracle C.oracle_spec C.allCfg C.allLo (C.hi : ℝ) (fun e => C.lo_pos _) C.hi_pos (fun e => C.guards _)
      ((standardRationalSchedule T K).live t) ((standardRationalSchedule T K).live (t+1))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t) C.lam
      (rationalHistoryInitial C.initial_mean C.hi) (C.query t) hS
    rw [ih'] at hs
    exact hs.trans (C.compact_step_actual t (by omega))

theorem materializedRun_prediction (roundCost projectionCost gradientCost t : ℕ) (ht : t≤T) :
    ((C.materializedRun roundCost projectionCost gradientCost t).compactView
      ((standardRationalSchedule T K).live t) (rationalHistoryInitial C.initial_mean C.hi)).prediction=C.prediction t := by
  rw [C.materializedRun_refines roundCost projectionCost gradientCost t ht]
  exact CompactRationalSparseData.restrict_prediction (C.run t) (C.invariant t).support

theorem materializedRun_history_length (roundCost projectionCost gradientCost t : ℕ) :
    (C.materializedRun roundCost projectionCost gradientCost t).histories.length=
      ((standardRationalSchedule T K).live t).card := by
  cases t with
  | zero => simp [materializedRun,MaterializedRationalSparseData.ofCompact]
  | succ t => exact MaterializedRationalSparseData.step_history_length _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem materializedRun_weights_length (roundCost projectionCost gradientCost t : ℕ) :
    (C.materializedRun roundCost projectionCost gradientCost t).weights.length=
      ((standardRationalSchedule T K).live t).card := by
  cases t with
  | zero => simp [materializedRun,MaterializedRationalSparseData.ofCompact]
  | succ t => exact MaterializedRationalSparseData.step_weights_length _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem materializedRun_storage (roundCost projectionCost gradientCost t : ℕ) :
    (C.materializedRun roundCost projectionCost gradientCost t).histories.length*(d*d+d)+
      (C.materializedRun roundCost projectionCost gradientCost t).weights.length≤
        standardLiveCap T K*(d*d+d+1) := by
  rw [C.materializedRun_history_length,C.materializedRun_weights_length]
  have hh := Nat.mul_le_mul_right (d*d+d+1) (standardRationalSchedule_uniform_card T K t)
  simpa only [Nat.mul_add,Nat.mul_one] using hh

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.materializedRun_refines
#print axioms Paper254.RationalSparseConstruction.materializedRun_prediction
