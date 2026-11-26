import SampleReuse.MarginalLazyLaw
import SampleReuse.MarginalStoppingTable
import SampleReuse.PersistentFreeze

open SecondOrder MeasureTheory
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {Ξ H S : Type} {d : ℕ} {R : ℝ}

theorem marginalFreeze_asPersistent
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (idle : H) :
    marginalAsPersistent (marginalFreeze P stop idle) =
      freezeOracle (marginalAsPersistent P) stop ((false,0),idle) := by
  unfold marginalAsPersistent marginalFreeze freezeOracle
  congr 2
  funext n s
  dsimp only
  split_ifs <;> rfl

def marginalLazyFirstStop
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (ε : ℝ) (v : Point d) (tape : ℕ → SignedCoefficient R) (k : ℕ) : Prop :=
  stop k (lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape k).1 = true ∧
    ∀ j < k, stop j (lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape j).1 = false

theorem marginalFreeze_lazy_first_stop
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (tape : ℕ → SignedCoefficient R) {k N : ℕ}
    (hk : marginalLazyFirstStop P stop ε v tape k) (hN : k ≤ N) :
    (lazyPersistentRun (marginalAsPersistent (marginalFreeze P stop idle)).toQueryPolicy
      (marginalLazyReply ε v) tape N).1 =
      ((lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape k).1,true,
        P.output k (lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape k).1) := by
  rw [marginalFreeze_asPersistent]
  exact freezeOracle_lazy_first_stop (marginalAsPersistent P) stop ((false,0),idle)
    (marginalLazyReply ε v) tape hN hk.1 hk.2

def marginalLazyStoppedSuccessBy
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (ε : ℝ) (v : Point d) (θ : Bool) (N : ℕ) :
    Set (Ξ × (ℕ → SignedCoefficient R)) := {w | ∃ k ≤ N,
      marginalLazyFirstStop (P w.1) (stop w.1) ε v w.2 k ∧
      ‖gradient (marginalLoss ε v (2*ε*signValue θ))
        ((P w.1).output k (lazyPersistentRun (marginalAsPersistent (P w.1)).toQueryPolicy
          (marginalLazyReply ε v) w.2 k).1)‖ ≤ ε}

def marginalLazyStoppedSuccess
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (ε : ℝ) (v : Point d) (θ : Bool) :
    Set (Ξ × (ℕ → SignedCoefficient R)) := ⋃ N, marginalLazyStoppedSuccessBy P stop ε v θ N

theorem marginalLazyStoppedSuccessBy_mono
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (ε : ℝ) (v : Point d) (θ : Bool) :
    Monotone (marginalLazyStoppedSuccessBy (R := R) P stop ε v θ) := by
  intro n m hnm w hw
  obtain ⟨k,hk,hs,hg⟩ := hw
  exact ⟨k,hk.trans hnm,hs,hg⟩

def marginalLazyExtendedGradientCount
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (w : Ξ × (ℕ → SignedCoefficient R)) : ℝ≥0∞ :=
  ⨆ N : ℕ, ((marginalLazyObservation (fun ξ => marginalFreeze (P ξ) (stop ξ) idle) ε v N w).1 : ℝ≥0∞)

variable [MeasurableSpace Ξ] [MeasurableSpace S] [MeasurableSpace (List H)]

/-- The appendix's expected-gradient lower bound under arbitrary opaque
labels and one infinite iid sample tape. The normalization measurability
premise is solely operational regularity; no probability or cost bound is assumed. -/
theorem marginal_stopping_gradient_lower (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (idle : H)
    (hN : ∀ N, MeasurableOracleAlgorithmFamily
      (fun ξ => normalizeMarginalOracle N (marginalFreeze (P ξ) (stop ξ) idle)))
    {ε : ℝ} (hε : 0 < ε) {v : Point d} (hv : ‖v‖=1) (hR : 2 ≤ R)
    (hsolve : ∀ θ, (2/3:ℝ) ≤ (marginalLazyLaw μ hR θ).real
      (marginalLazyStoppedSuccess P stop ε v θ)) :
    ∃ θ, ENNReal.ofReal (truncatedTestingConstant*R^2) ≤
      ∫⁻ w, marginalLazyExtendedGradientCount P stop idle ε v w ∂marginalLazyLaw μ hR θ := by
  let frozen := fun ξ => marginalFreeze (P ξ) (stop ξ) idle
  obtain ⟨N,hcap⟩ := binary_success_finite_horizon (fun θ => marginalLazyLaw μ hR θ)
    (marginalLazyStoppedSuccessBy P stop ε v) (marginalLazyStoppedSuccessBy_mono P stop ε v) hsolve
  have hgood (θ : Bool) : (3/5:ℝ) ≤ (marginalLazyLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ)) (marginalLazyObservation frozen ε v N w).2‖ ≤ ε} := by
    apply (hcap θ).trans
    apply measureReal_mono
    · intro w hw
      obtain ⟨k,hk,hstop,hgrad⟩ := hw
      change ‖gradient _ ((frozen w.1).output N (lazyPersistentRun
        (marginalAsPersistent (frozen w.1)).toQueryPolicy (marginalLazyReply ε v) w.2 N).1)‖ ≤ ε
      rw [marginalFreeze_lazy_first_stop (P w.1) (stop w.1) idle ε v w.2 hstop hk]
      exact hgrad
    · finiteness
  have htable (θ : Bool) : (3/5:ℝ) ≤ (marginalActualLaw μ hR θ).real
      {w | ‖gradient (marginalLoss ε v (2*ε*signValue θ))
        (marginalTableObservation (fun ξ => normalizeMarginalOracle N (frozen ξ)) ε v N w).2‖ ≤ ε} := by
    rw [← marginal_lazy_success_probability μ frozen N (hN N) ε v hR θ]
    exact hgood θ
  obtain ⟨θ,hθ⟩ := truncated_marginal_actual_gradient_lower μ
    (fun ξ => normalizeMarginalOracle N (frozen ξ)) (hN N) hε hv hR N htable
  rw [← marginal_lazy_expected_gradients μ frozen N (hN N) ε v hR θ] at hθ
  refine ⟨θ,?_⟩
  have hm : Measurable (fun w : Ξ × (ℕ → SignedCoefficient R) =>
      ((marginalLazyObservation frozen ε v N w).1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (marginalLazyObservation_measurable frozen N (hN N) ε v).fst
  have hb (w : Ξ × (ℕ → SignedCoefficient R)) :
      ‖((marginalLazyObservation frozen ε v N w).1 : ℝ)‖ ≤ (N:ℝ) := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have hh : (marginalLazyObservation frozen ε v N w).1 ≤ N := by
      dsimp only [marginalLazyObservation]
      calc
        _ ≤ ∑ _k ∈ Finset.range N, 1 := Finset.sum_le_sum (fun k _ => by split_ifs <;> omega)
        _ = N := by simp
    exact_mod_cast hh
  have hi : Integrable (fun w : Ξ × (ℕ → SignedCoefficient R) =>
      ((marginalLazyObservation frozen ε v N w).1 : ℝ)) (marginalLazyLaw μ hR θ) :=
    (integrable_const (N:ℝ)).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hh := ENNReal.ofReal_le_ofReal hθ
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))] at hh
  apply hh.trans
  apply lintegral_mono
  intro w
  dsimp only
  rw [ENNReal.ofReal_natCast]
  exact le_iSup (fun N : ℕ => ((marginalLazyObservation frozen ε v N w).1 : ℝ≥0∞)) N

end
end SampleReuse
