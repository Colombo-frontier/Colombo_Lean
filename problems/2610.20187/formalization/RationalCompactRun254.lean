import RationalCompactState254
import RationalCompactMaster254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

theorem newborn_history (t : ℕ) (ht : t<T) (e : Fin ((T+1)*(K+1)))
    (hn : e∈(standardRationalSchedule T K).live (t+1))
    (ho : e∉(standardRationalSchedule T K).live t) :
    (C.run (t+1)).histories e=rationalHistoryInitial C.initial_mean C.hi := by
  let key := (numberedExpertEquiv T K).symm e
  have heq : numberedExpertEquiv T K key=e := (numberedExpertEquiv T K).apply_symm_apply e
  have hnext : HistoryActive (t+2) (expertBirth key) := by
    apply (standardRationalSchedule_live (by omega : t+1≤T) key).mp
    simpa only [heq] using hn
  have hnot : ¬expertBirth key≤t+1 := by
    intro hb
    apply ho
    rw [←heq]
    apply (standardRationalSchedule_live (by omega : t≤T) key).mpr
    exact historyActive_prefix hnext hb (by omega)
  apply rationalSparseRun_unborn
  intro j hj he
  have hactive : HistoryActive (j+1) (expertBirth key) := by
    apply (standardRationalSchedule_live (by omega : j≤T) key).mp
    simpa only [heq] using he
  exact hnot (hactive.2.1.trans (by omega))

theorem compact_step_actual (t : ℕ) (ht : t<T) :
    let S := CompactRationalSparseData.restrict (C.run t) ((standardRationalSchedule T K).live t)
    S.step C.oracle C.allCfg C.master_precision C.lam ((standardRationalSchedule T K).live (t+1))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      (rationalHistoryInitial C.initial_mean C.hi) (C.query t S.prediction)=
        CompactRationalSparseData.restrict (C.run (t+1)) ((standardRationalSchedule T K).live (t+1)) := by
  let S := CompactRationalSparseData.restrict (C.run t) ((standardRationalSchedule T K).live t)
  have hp : S.prediction=C.prediction t :=
    CompactRationalSparseData.restrict_prediction (C.run t) (C.invariant t).support
  have hw : S.weightView=(C.run t).weights :=
    CompactRationalSparseData.restrict_weightView (C.run t) (C.invariant t).support
  change S.step _ _ _ _ _ _ _ _ _=_
  apply CompactRationalSparseData.ext
  · intro e
    change (if he : e.val∈(standardRationalSchedule T K).live t then
      rationalHistoryStep C.oracle (C.allCfg e.val) (S.histories ⟨e.val,he⟩) C.lam
        (C.query t S.prediction) S.prediction else rationalHistoryInitial C.initial_mean C.hi)=_
    by_cases he : e.val∈(standardRationalSchedule T K).live t
    · rw [dif_pos he,hp]
      exact (rationalSparseRun_live_update C.oracle C.allCfg C.master_precision C.lam
        (standardRationalSchedule T K) C.initial C.query t e.val he).symm
    · rw [dif_neg he]
      exact (C.newborn_history t ht e.val e.property he).symm
  · intro e
    change rationalMasterUpdate C.master_precision ((standardRationalSchedule T K).live t)
      ((standardRationalSchedule T K).live (t+1)) S.weightView
      (S.exponents C.lam (C.query t S.prediction)) ((standardRationalSchedule T K).prior t)
      ((standardRationalSchedule T K).share t) e.val=_
    rw [hw,hp]
    change rationalMasterUpdate C.master_precision ((standardRationalSchedule T K).live t)
      ((standardRationalSchedule T K).live (t+1)) (C.run t).weights
      (S.exponents C.lam (C.gradient t)) ((standardRationalSchedule T K).prior t)
      ((standardRationalSchedule T K).share t) e.val=
        rationalMasterUpdate C.master_precision ((standardRationalSchedule T K).live t)
          ((standardRationalSchedule T K).live (t+1)) (C.run t).weights
          (rationalSparseExponents C.lam (C.run t) (C.gradient t)) ((standardRationalSchedule T K).prior t)
          ((standardRationalSchedule T K).share t) e.val
    apply congrFun (rationalMasterUpdate_congr_live _ _ _ _ _ _ _ _ (C.invariant t).support ?_) e.val
    intro j hj
    simp only [CompactRationalSparseData.exponents,dif_pos hj,hp,rationalSparseExponents]
    rfl

def compactRun (C : RationalSparseConstruction d T K D G eta W) :
    (t : ℕ) → CompactRationalSparseData d ((T+1)*(K+1)) ((standardRationalSchedule T K).live t)
  | 0 => CompactRationalSparseData.restrict C.initial ((standardRationalSchedule T K).live 0)
  | t+1 => let S := compactRun C t
    S.step C.oracle C.allCfg C.master_precision C.lam ((standardRationalSchedule T K).live (t+1))
      ((standardRationalSchedule T K).prior t) ((standardRationalSchedule T K).share t)
      (rationalHistoryInitial C.initial_mean C.hi) (C.query t S.prediction)

/-- The live-only state has exactly the histories and weights used in the
verified regret trajectory, including birth, deletion, and terminal rounds. -/
theorem compactRun_refines (t : ℕ) (ht : t≤T) :
    C.compactRun t=CompactRationalSparseData.restrict (C.run t) ((standardRationalSchedule T K).live t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [compactRun,ih (by omega)]
    exact C.compact_step_actual t (by omega)

theorem compactRun_prediction (t : ℕ) (ht : t≤T) : (C.compactRun t).prediction=C.prediction t := by
  rw [C.compactRun_refines t ht]
  exact CompactRationalSparseData.restrict_prediction (C.run t) (C.invariant t).support

theorem compactRun_weights (t : ℕ) (ht : t≤T) : (C.compactRun t).weightView=(C.run t).weights := by
  rw [C.compactRun_refines t ht]
  exact CompactRationalSparseData.restrict_weightView (C.run t) (C.invariant t).support

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.compactRun_refines
#print axioms Paper254.RationalSparseConstruction.compactRun_prediction
