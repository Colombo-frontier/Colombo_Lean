import GradientHessian.OracleBranches

/-! Measurable fixed-budget control flow. Idle calls query zero; padding
preserves outputs; conditional procedures choose only from their initial seed. -/

namespace GradientHessian.OracleComposition.Procedure
open MeasureTheory Matrix LowRank
noncomputable section

def idlePolicy (d : ℕ) : (q : ℕ) → {S : Type*} → [MeasurableSpace S] → AmbientOraclePolicy d q S
  | 0, _, _ => PUnit.unit
  | q + 1, _, _ => (⟨fun _ => 0, measurable_const⟩, idlePolicy d q)

variable {d q : ℕ} {S O : Type*} [MeasurableSpace S] [MeasurableSpace O]

/-- Exactly `q` zero queries, followed by a measurable function of the seed. -/
def idle (d q : ℕ) (f : MeasurableStateMap S O) : Procedure d q S O where
  policy := idlePolicy d q
  decode := ⟨fun h => f.1 (oracleHistorySeed d q h),
    f.2.comp (measurable_oracleHistorySeed d q S)⟩

theorem run_idle (d q : ℕ) (f : MeasurableStateMap S O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (idle d q f).run A s = f.1 s := by
  change f.1 (oracleHistorySeed d q (runAmbientOracle d q (idlePolicy d q) A s)) = _
  rw [oracleHistorySeed_runAmbientOracle]

/-- Pad only after the original procedure has finished. -/
def padTo (P : Procedure d q S O) (q' : ℕ) (h : q ≤ q') : Procedure d q' S O :=
  (P.bind (idle d (q'-q) ⟨id, measurable_id⟩)).castBudget (by omega)

theorem run_padTo (P : Procedure d q S O) (q' : ℕ) (h : q ≤ q')
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) : (P.padTo q' h).run A s = P.run A s := by
  simp only [padTo, run_castBudget, run_bind, run_idle, id_eq]

def extendFlag (flag : MeasurableStateMap S Bool) :
    MeasurableStateMap (S × (Fin d → ℝ)) Bool :=
  ⟨fun t => flag.1 t.1, flag.2.comp measurable_fst⟩

def choosePolicy (d : ℕ) : (q : ℕ) → {S : Type*} → [MeasurableSpace S] →
    MeasurableStateMap S Bool → AmbientOraclePolicy d q S → AmbientOraclePolicy d q S →
      AmbientOraclePolicy d q S
  | 0, _, _, _, _, _ => PUnit.unit
  | q + 1, _, _, flag, P, Q =>
      (⟨fun s => if flag.1 s = true then P.1.1 s else Q.1.1 s,
        Measurable.ite (flag.2 (measurableSet_singleton true)) P.1.2 Q.1.2⟩,
        choosePolicy d q (extendFlag flag) P.2 Q.2)

theorem run_choosePolicy (d q : ℕ) {S : Type*} [MeasurableSpace S]
    (flag : MeasurableStateMap S Bool) (P Q : AmbientOraclePolicy d q S)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    runAmbientOracle d q (choosePolicy d q flag P Q) A s =
      if flag.1 s = true then runAmbientOracle d q P A s else runAmbientOracle d q Q A s := by
  induction q generalizing S with
  | zero => simp only [runAmbientOracle, ite_self]
  | succ q ih =>
      simp only [choosePolicy, runAmbientOracle]
      rw [ih]
      by_cases h : flag.1 s = true <;> simp only [extendFlag, h, Bool.false_eq_true, if_true, if_false]

/-- The flag uses the original seed. Actual replies remain available to the
selected branch, and cannot change which branch is selected. -/
def choose (flag : MeasurableStateMap S Bool) (P Q : Procedure d q S O) : Procedure d q S O where
  policy := choosePolicy d q flag P.policy Q.policy
  decode := ⟨fun h => if flag.1 (oracleHistorySeed d q h) = true then P.decode.1 h else Q.decode.1 h,
    Measurable.ite ((flag.2.comp (measurable_oracleHistorySeed d q S))
      (measurableSet_singleton true)) P.decode.2 Q.decode.2⟩

theorem run_choose (flag : MeasurableStateMap S Bool) (P Q : Procedure d q S O)
    (A : Matrix (Fin d) (Fin d) ℝ) (s : S) :
    (choose flag P Q).run A s = if flag.1 s = true then P.run A s else Q.run A s := by
  change (if flag.1 (oracleHistorySeed d q
    (runAmbientOracle d q (choosePolicy d q flag P.policy Q.policy) A s)) = true
    then P.decode.1 (runAmbientOracle d q (choosePolicy d q flag P.policy Q.policy) A s)
    else Q.decode.1 (runAmbientOracle d q (choosePolicy d q flag P.policy Q.policy) A s)) = _
  rw [oracleHistorySeed_runAmbientOracle, run_choosePolicy]
  by_cases h : flag.1 s = true <;> simp only [h, Bool.false_eq_true, if_true, if_false, run]

/-- One genuine ambient matrix-vector query. -/
def product (d : ℕ) : Procedure d 1 (Fin d → ℝ) (Fin d → ℝ) where
  policy := (⟨id, measurable_id⟩, PUnit.unit)
  decode := ⟨Prod.snd, measurable_snd⟩

theorem run_product (d : ℕ) (A : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) :
    (product d).run A s = A *ᵥ s := rfl

end
end GradientHessian.OracleComposition.Procedure
