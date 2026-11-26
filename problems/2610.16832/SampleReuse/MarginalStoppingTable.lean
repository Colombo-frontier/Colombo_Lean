import SampleReuse.MarginalGradientTruncation
import SampleReuse.OracleFreeze
import SampleReuse.StoppingSuccessApproximation

/-! Unbounded stopping with a finite reusable handle set. A stopped run is
frozen and issues only Hessian queries thereafter; those add no gradient
cost. Successful first stops are approximated by one common finite horizon. -/

open SecondOrder MeasureTheory
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {Ξ S H : Type} {d : ℕ} {R : ℝ}

def marginalFreeze (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (idleHandle : H) := freezeOracle P stop (false,idleHandle,0)

theorem marginalPersistentRun_as_queryRun
    (P : QueryPolicy (MarginalQuery H d) (PersistentReply d) S) (ε : ℝ) (v : Point d)
    (table : H → SignedCoefficient R) : ∀ n,
    marginalPersistentRun P ε v table n = queryPolicyRun P
      (fun q (_ : Unit) => marginalDecodedReply ε v q (table q.2.1).1) (fun _ => ()) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [marginalPersistentRun,queryPolicyRun,ih]

def marginalTableFirstStop
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (ε : ℝ) (v : Point d) (table : H → SignedCoefficient R) (k : ℕ) : Prop :=
  stop k (marginalPersistentRun P.toQueryPolicy ε v table k) = true ∧
    ∀ j < k, stop j (marginalPersistentRun P.toQueryPolicy ε v table j) = false

theorem marginalFreeze_first_stop
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (table : H → SignedCoefficient R) {k N : ℕ}
    (hk : marginalTableFirstStop P stop ε v table k) (hN : k ≤ N) :
    marginalPersistentRun (marginalFreeze P stop idle).toQueryPolicy ε v table N =
      (marginalPersistentRun P.toQueryPolicy ε v table k,true,
        P.output k (marginalPersistentRun P.toQueryPolicy ε v table k)) := by
  unfold marginalTableFirstStop at hk
  simp only [marginalPersistentRun_as_queryRun] at hk ⊢
  exact freezeOracle_first_stop P stop (false,idle,0) _ _ hN hk.1 hk.2

def marginalStoppedSuccessBy
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (ε : ℝ) (v : Point d) (θ : Bool) (N : ℕ) :
    Set (Ξ × (H → SignedCoefficient R)) := {w | ∃ k ≤ N,
      marginalTableFirstStop (P w.1) (stop w.1) ε v w.2 k ∧
      ‖gradient (marginalLoss ε v (2*ε*signValue θ))
        ((P w.1).output k (marginalPersistentRun (P w.1).toQueryPolicy ε v w.2 k))‖ ≤ ε}

def marginalStoppedSuccess
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (ε : ℝ) (v : Point d) (θ : Bool) :
    Set (Ξ × (H → SignedCoefficient R)) := ⋃ N, marginalStoppedSuccessBy P stop ε v θ N

theorem marginalStoppedSuccessBy_mono
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (ε : ℝ) (v : Point d) (θ : Bool) :
    Monotone (marginalStoppedSuccessBy (R := R) P stop ε v θ) := by
  intro n m hnm w hw
  obtain ⟨k,hk,hs,hg⟩ := hw
  exact ⟨k,hk.trans hnm,hs,hg⟩

def marginalExtendedGradientCount
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (w : Ξ × (H → SignedCoefficient R)) : ℝ≥0∞ :=
  ⨆ N : ℕ, ((marginalTableObservation (fun ξ => marginalFreeze (P ξ) (stop ξ) idle) ε v N w).1 : ℝ≥0∞)

variable [Fintype H] [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace H]
  [MeasurableSingletonClass H]

theorem marginal_stopping_table_gradient_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (hP : MeasurableOracleAlgorithmFamily P)
    (stop : Ξ → ℕ → S → Bool)
    (hs : ∀ n, Measurable (fun w : Ξ × S => stop w.1 n w.2)) (idle : H)
    {ε : ℝ} (hε : 0 < ε) {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R)
    (hsolve : ∀ θ, (2/3:ℝ) ≤ (marginalActualLaw μ hR θ).real
      (marginalStoppedSuccess P stop ε v θ)) :
    ∃ θ, ENNReal.ofReal (truncatedTestingConstant*R^2) ≤
      ∫⁻ w, marginalExtendedGradientCount P stop idle ε v w ∂marginalActualLaw μ hR θ := by
  let frozen := fun ξ => marginalFreeze (P ξ) (stop ξ) idle
  have hF : MeasurableOracleAlgorithmFamily frozen := freezeOracle_measurable P hP stop hs (false,idle,0)
  obtain ⟨N,hN⟩ := binary_success_finite_horizon (fun θ => marginalActualLaw (Handle := H) μ hR θ)
    (marginalStoppedSuccessBy P stop ε v) (marginalStoppedSuccessBy_mono P stop ε v) hsolve
  have hgood (θ : Bool) : (3/5:ℝ) ≤ (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ))
        (marginalTableObservation frozen ε v N w).2‖ ≤ ε} := by
    apply (hN θ).trans
    apply measureReal_mono
    · intro w hw
      obtain ⟨k,hk,hstop,hgrad⟩ := hw
      change ‖gradient _ ((frozen w.1).output N (marginalPersistentRun (frozen w.1).toQueryPolicy ε v w.2 N))‖ ≤ ε
      rw [marginalFreeze_first_stop (P w.1) (stop w.1) idle ε v w.2 hstop hk]
      exact hgrad
    · finiteness
  obtain ⟨θ,hθ⟩ := truncated_marginal_actual_gradient_lower μ frozen hF hε hv hR N hgood
  refine ⟨θ,?_⟩
  have hm : Measurable (fun w : Ξ × (H → SignedCoefficient R) =>
      ((marginalTableObservation frozen ε v N w).1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (marginalTableObservation_measurable frozen hF ε v N).fst
  have hb (w : Ξ × (H → SignedCoefficient R)) :
      ‖((marginalTableObservation frozen ε v N w).1 : ℝ)‖ ≤ (N:ℝ) := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hh : (marginalTableObservation frozen ε v N w).1 ≤ N := by
      dsimp only [marginalTableObservation]
      calc
        _ ≤ ∑ _k ∈ Finset.range N, 1 := Finset.sum_le_sum (fun k _ => by split_ifs <;> omega)
        _ = N := by simp
    exact_mod_cast hh
  have hi : Integrable (fun w : Ξ × (H → SignedCoefficient R) =>
      ((marginalTableObservation frozen ε v N w).1 : ℝ)) (marginalActualLaw μ hR θ) :=
    (integrable_const (N:ℝ)).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hh := ENNReal.ofReal_le_ofReal hθ
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))] at hh
  apply hh.trans
  apply lintegral_mono
  intro w
  dsimp only
  rw [ENNReal.ofReal_natCast]
  exact le_iSup (fun N : ℕ => ((marginalTableObservation frozen ε v N w).1 : ℝ≥0∞)) N

end
end SampleReuse
