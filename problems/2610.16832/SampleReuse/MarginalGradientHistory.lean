import SampleReuse.MarginalGradientTesting
import SampleReuse.HiddenBinaryTesting
import SampleReuse.PersistentTableKernel
import SampleReuse.PersistentSeededTable
import SampleReuse.OraclePersistent

open SecondOrder MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SampleReuse
noncomputable section

abbrev MarginalQuery (Handle : Type) (d : ℕ) := Bool × (Handle × Point d)

/-- Only the requested derivative is returned. The Hessian branch does not
read a sample coefficient because the actual Hessian is coefficient-free. -/
def marginalDecodedReply {Handle : Type} {d : ℕ} (ε : ℝ) (v : Point d)
    (q : MarginalQuery Handle d) (a : ℝ) : PersistentReply d :=
  if q.1 then (gradient (marginalLoss ε v (2*ε*a)) q.2.2,0)
  else (0,hessian (marginalLoss ε v 0) q.2.2)

theorem marginalDecodedReply_actual {Handle : Type} {d : ℕ} (ε : ℝ) (v : Point d)
    (q : MarginalQuery Handle d) (a : ℝ) :
    marginalDecodedReply ε v q a =
      if q.1 then (gradient (marginalLoss ε v (2*ε*a)) q.2.2,0)
      else (0,hessian (marginalLoss ε v (2*ε*a)) q.2.2) := by
  unfold marginalDecodedReply
  split_ifs
  · rfl
  · rw [marginal_hessian_no_information ε v 0 (2*ε*a)]

variable {Ξ S Handle : Type} {d : ℕ} {R : ℝ}

def marginalHistoryState (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) : ∀ n, FiniteHistory Ξ (SignedCoefficient R) n → S
  | 0,h => (P h).initial
  | n+1,h =>
    let ξ := finiteHistoryInitial n h.1
    let s := marginalHistoryState P ε v n h.1
    (P ξ).update n s (marginalDecodedReply ε v ((P ξ).query n s) h.2.1)

def marginalHistoryQuery (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) (n : ℕ) (h : FiniteHistory Ξ (SignedCoefficient R) n) :
    MarginalQuery Handle d :=
  (P (finiteHistoryInitial n h)).query n (marginalHistoryState P ε v n h)

/-- Gradient calls reveal their sample handle; Hessian calls use a common
dummy key and reveal no sign-dependent random variable. -/
def marginalHistoryKey (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) (n : ℕ) (h : FiniteHistory Ξ (SignedCoefficient R) n) : Option Handle :=
  if (marginalHistoryQuery P ε v n h).1 then some (marginalHistoryQuery P ε v n h).2.1 else none

def marginalHistoryOutput
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (n : ℕ) (h : FiniteHistory Ξ (SignedCoefficient R) n) : Point d :=
  (P (finiteHistoryInitial n h)).output n
    (marginalHistoryState (fun ξ => (P ξ).toQueryPolicy) ε v n h)

section Measurable
variable [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle]
  [MeasurableSingletonClass Handle] [Countable Handle]

local instance marginalHistory_option_measurable : MeasurableSpace (Option Handle) := ⊤
local instance marginalHistory_option_singleton : MeasurableSingletonClass (Option Handle) := ⟨fun _ => trivial⟩

omit [MeasurableSingletonClass Handle] [Countable Handle] in
theorem marginalDecodedReply_measurable (ε : ℝ) (v : Point d) :
    Measurable (fun z : MarginalQuery Handle d × SignedCoefficient R =>
      marginalDecodedReply ε v z.1 z.2.1) := by
  have hg : Measurable (fun z : MarginalQuery Handle d × SignedCoefficient R =>
      gradient (marginalLoss ε v (2*ε*z.2.1)) z.1.2.2) := by
    simp only [marginalLoss_gradient]
    exact (measurable_const.smul
      ((GradientHessian.SmoothNormCompression.unitCompression_contDiff (m := 1)).continuous.measurable.comp
        measurable_fst.snd.snd)).add
      ((measurable_const.mul (measurable_subtype_coe.comp measurable_snd)).smul measurable_const)
  have hH : Measurable (fun z : MarginalQuery Handle d × SignedCoefficient R =>
      hessian (marginalLoss ε v 0) z.1.2.2) :=
    (continuous_hessian (marginalLoss_contDiff ε v 0 2)).measurable.comp measurable_fst.snd.snd
  exact Measurable.ite ((measurableSet_singleton true).preimage measurable_fst.fst)
    (hg.prodMk measurable_const) (measurable_const.prodMk hH)

omit [MeasurableSingletonClass Handle] [Countable Handle] in
theorem marginalHistoryState_measurable
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (hP : MeasurableQueryPolicyFamily P) (ε : ℝ) (v : Point d) :
    ∀ n, Measurable (marginalHistoryState (R := R) P ε v n) := by
  intro n
  induction n with
  | zero => exact hP.initial
  | succ n ih =>
    have hξ : Measurable (fun h : FiniteHistory Ξ (SignedCoefficient R) (n+1) =>
        finiteHistoryInitial n h.1) := (finiteHistoryInitial_measurable n).comp measurable_fst
    have hs : Measurable (fun h : FiniteHistory Ξ (SignedCoefficient R) (n+1) =>
        marginalHistoryState P ε v n h.1) := ih.comp measurable_fst
    have hq := (hP.query n).comp (hξ.prodMk hs)
    have hr := (marginalDecodedReply_measurable ε v).comp (hq.prodMk measurable_snd)
    exact (hP.update n).comp (hξ.prodMk (hs.prodMk hr))

omit [MeasurableSingletonClass Handle] [Countable Handle] in
theorem marginalHistoryQuery_measurable
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (hP : MeasurableQueryPolicyFamily P) (ε : ℝ) (v : Point d) (n : ℕ) :
    Measurable (marginalHistoryQuery (R := R) P ε v n) :=
  (hP.query n).comp ((finiteHistoryInitial_measurable n).prodMk
    (marginalHistoryState_measurable P hP ε v n))

theorem marginalHistoryKey_measurable
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (hP : MeasurableQueryPolicyFamily P) (ε : ℝ) (v : Point d) (n : ℕ) :
    Measurable (marginalHistoryKey (R := R) P ε v n) :=
  Measurable.ite ((measurableSet_singleton true).preimage
    (marginalHistoryQuery_measurable P hP ε v n).fst)
    ((measurable_of_countable (some : Handle → Option Handle)).comp
      (marginalHistoryQuery_measurable P hP ε v n).snd.fst) measurable_const

omit [MeasurableSingletonClass Handle] [Countable Handle] in
theorem marginalHistoryOutput_measurable
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P) (ε : ℝ) (v : Point d) (n : ℕ) :
    Measurable (marginalHistoryOutput (R := R) P ε v n) :=
  (hP.output n).comp ((finiteHistoryInitial_measurable n).prodMk
    (marginalHistoryState_measurable _ hP.toMeasurableQueryPolicyFamily ε v n))

end Measurable

/-- Immutable sample-table execution of the actual derivative oracle. -/
def marginalPersistentRun (P : QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) (table : Handle → SignedCoefficient R) : ℕ → S
  | 0 => P.initial
  | n+1 =>
    let s := marginalPersistentRun P ε v table n
    let q := P.query n s
    P.update n s (marginalDecodedReply ε v q (table q.2.1).1)

def marginalExtendedTable (table : Handle → SignedCoefficient R) (a₀ : SignedCoefficient R) :
    Option Handle → SignedCoefficient R := fun key => key.elim a₀ table

theorem marginalDecodedReply_extended (ε : ℝ) (v : Point d)
    (table : Handle → SignedCoefficient R) (a₀ : SignedCoefficient R) (q : MarginalQuery Handle d) :
    marginalDecodedReply ε v q
        (marginalExtendedTable table a₀ (if q.1 then some q.2.1 else none)).1 =
      marginalDecodedReply ε v q (table q.2.1).1 := by
  cases hq : q.1 <;> simp [marginalDecodedReply,marginalExtendedTable,hq]

theorem marginalHistoryState_table
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) (ξ : Ξ) (table : Handle → SignedCoefficient R) (a₀ : SignedCoefficient R) :
    ∀ n, marginalHistoryState P ε v n
      (tableHistory (marginalHistoryKey P ε v) ξ (marginalExtendedTable table a₀) n) =
      marginalPersistentRun (P ξ) ε v table n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tableHistory,marginalHistoryState,tableHistory_initial]
    simp only [marginalHistoryKey,marginalHistoryQuery,tableHistory_initial]
    rw [ih,marginalDecodedReply_extended]
    rfl

def marginalHistoryGradientCount
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) : ∀ n, FiniteHistory Ξ (SignedCoefficient R) n → ℕ
  | 0,_ => 0
  | n+1,h => marginalHistoryGradientCount P ε v n h.1+
    if (marginalHistoryQuery P ε v n h.1).1 then 1 else 0

theorem marginalHistoryGradientCount_hidden
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) : ∀ n (h : FiniteHistory (Bool × Ξ) (SignedCoefficient R) n),
    finiteHistoryCost
        (hiddenSelectedCost (marginalHistoryKey P ε v) (fun key => key.isSome) 1) n h =
      (marginalHistoryGradientCount P ε v n (finiteHistoryMapInitial Prod.snd n h) : ℝ) := by
  intro n
  induction n with
  | zero => intro h; simp only [finiteHistoryCost,marginalHistoryGradientCount,Nat.cast_zero]
  | succ n ih =>
    intro h
    simp only [finiteHistoryCost,hiddenSelectedCost,marginalHistoryKey,
      finiteHistoryMapInitial,marginalHistoryGradientCount,ih,Nat.cast_add]
    by_cases hq : (marginalHistoryQuery P ε v n (finiteHistoryMapInitial Prod.snd n h.1)).1 = true <;>
      simp [hq]

theorem marginalHistoryGradientCount_table
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) (ξ : Ξ) (table : Handle → SignedCoefficient R) (a₀ : SignedCoefficient R) :
    ∀ n, marginalHistoryGradientCount P ε v n
      (tableHistory (marginalHistoryKey P ε v) ξ (marginalExtendedTable table a₀) n) =
      ∑ k ∈ Finset.range n, if ((P ξ).query k (marginalPersistentRun (P ξ) ε v table k)).1 then 1 else 0 := by
  intro n
  induction n with
  | zero => simp only [marginalHistoryGradientCount,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    simp only [tableHistory,marginalHistoryGradientCount,ih,Finset.sum_range_succ,
      marginalHistoryQuery,tableHistory_initial,marginalHistoryState_table]

theorem marginalHistoryGradientCount_le
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) : ∀ n (h : FiniteHistory Ξ (SignedCoefficient R) n),
    marginalHistoryGradientCount P ε v n h ≤ n := by
  intro n
  induction n with
  | zero => intro h; exact le_rfl
  | succ n ih =>
    intro h
    have hh := ih h.1
    simp only [marginalHistoryGradientCount]
    split_ifs <;> omega

theorem marginalHistoryGradientCount_measurable
    [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace Handle]
    (P : Ξ → QueryPolicy (MarginalQuery Handle d) (PersistentReply d) S)
    (hP : MeasurableQueryPolicyFamily P) (ε : ℝ) (v : Point d) :
    ∀ n, Measurable (marginalHistoryGradientCount (R := R) P ε v n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add (Measurable.ite
      ((measurableSet_singleton true).preimage
        ((marginalHistoryQuery_measurable P hP ε v n).fst.comp measurable_fst))
      measurable_const measurable_const)

theorem marginalHistoryOutput_table
    (P : Ξ → OracleAlgorithm (MarginalQuery Handle d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (ξ : Ξ) (table : Handle → SignedCoefficient R) (a₀ : SignedCoefficient R)
    (n : ℕ) : marginalHistoryOutput P ε v n
      (tableHistory (marginalHistoryKey (fun ξ => (P ξ).toQueryPolicy) ε v)
        ξ (marginalExtendedTable table a₀) n) =
      (P ξ).output n (marginalPersistentRun (P ξ).toQueryPolicy ε v table n) := by
  simp only [marginalHistoryOutput,tableHistory_initial,marginalHistoryState_table]

theorem marginalPersistentRun_actual {H : ℕ}
    (P : QueryPolicy (PersistentQuery H d) (PersistentReply d) S)
    (ε : ℝ) (v : Point d) (table : Fin H → SignedCoefficient R) (n : ℕ) :
    marginalPersistentRun P ε v table n = persistentRun P
      (fun a : SignedCoefficient R => marginalLoss ε v (2*ε*a.1)) table n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [marginalPersistentRun,persistentRun]
    rw [ih,marginalDecodedReply_actual]
    rfl

end
end SampleReuse
