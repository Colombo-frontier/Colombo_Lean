import FullJet.RestartMeasurability
import FullJet.TrialCost

open MeasureTheory
open scoped ENNReal

namespace FullJet

variable {α E : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {n p : ℕ}

/-- General Las Vegas conversion for actual positive-length oracle programs.
The probability source, measurability, termination, and both integrals are
constructed here; only the one-trial cost, certification, and failure bound
are inputs. -/
theorem restartStoppingAlgorithm_expectedGuarantee (μ : Measure α) [IsProbabilityMeasure μ]
    (index : Fin n) (trials : α → OracleProgram (Fin n × E) (JetPacket p E) (Option E))
    (N : ℕ) (hN : 0 < N) (htrials : ∀ a, (trials a).Uses N) (Δ L ε : ℝ)
    (hvalid : ∀ f, Admissible p n Δ L f → ∀ a x,
      (trials a).eval (fun q => fullJet p (f q.1) q.2) = some x → ‖fderiv ℝ (average f) x‖ ≤ ε)
    (hbad : ∀ f, Admissible p n Δ L f →
      μ.real {a | (trials a).eval (fun q => fullJet p (f q.1) q.2) = none} ≤ 1 / 4) :
    (restartStoppingAlgorithm index trials).ExpectedGuarantee (independentTrialLaw μ)
      Δ L ((N : ℝ) * (4 / 3)) ε := by
  classical
  let A := restartStoppingAlgorithm index trials
  have hm := restartStoppingAlgorithm_measurableOn index trials Δ L
  have hinstance (f : Fin n → E → ℝ) (hf : Admissible p n Δ L f) :
      (∀ᵐ seeds ∂independentTrialLaw μ, A.Halts f seeds) ∧
      Integrable (fun seeds => (A.stopIndex f seeds : ℝ)) (independentTrialLaw μ) ∧
      Integrable (fun seeds => ‖fderiv ℝ (average f) (A.stoppedResult f seeds)‖) (independentTrialLaw μ) ∧
      (∫ seeds, (A.stopIndex f seeds : ℝ) ∂independentTrialLaw μ) ≤ (N : ℝ) * (4 / 3) ∧
      (∫ seeds, ‖fderiv ℝ (average f) (A.stoppedResult f seeds)‖ ∂independentTrialLaw μ) ≤ ε := by
    let oracle := fun q : Fin n × E => fullJet p (f q.1) q.2
    let good := fun a => ∃ x, (trials a).eval oracle = some x
    have hgood : MeasurableSet {a | good a} := (Set.toFinite _).measurableSet
    have hbad' : μ.real {a | ¬ good a} ≤ 1 / 4 := by
      have heq : {a | ¬ good a} = {a | (trials a).eval oracle = none} := by
        ext a
        simp only [Set.mem_setOf_eq, good]
        cases (trials a).eval oracle <;> simp
      rw [heq]
      exact hbad f hf
    have hex := independentTrials_success_ae μ good hgood hbad'
    have hpath : ∀ᵐ seeds ∂independentTrialLaw μ, A.Halts f seeds ∧
        ENNReal.ofReal (A.stopIndex f seeds : ℝ) ≤ (N : ℝ≥0∞) * trialEnvelope good seeds := by
      filter_upwards [hex] with seeds hs
      let K := Nat.find hs
      obtain ⟨x, hx⟩ := Nat.find_spec hs
      have hfail (i : ℕ) (hi : i < K) : ¬ good (seeds i) := Nat.find_min hs hi
      have hnone (i : ℕ) (hi : i < K) : (trials (seeds i)).eval oracle = none := by
        cases he : (trials (seeds i)).eval oracle with
        | none => rfl
        | some x => exact False.elim (hfail i hi ⟨x, he⟩)
      have hh := restartStoppingAlgorithm_halts index trials f seeds N hN htrials K hnone hx
      refine ⟨hh.1, ?_⟩
      rw [ENNReal.ofReal_natCast]
      calc
        (A.stopIndex f seeds : ℝ≥0∞) ≤ ((K + 1) * N : ℕ) := by exact_mod_cast hh.2.1
        _ = (N : ℝ≥0∞) * (K + 1) := by push_cast; rw [mul_comm]
        _ ≤ _ := mul_le_mul_left' (trialEnvelope_ge_of_failures good seeds K hfail) _
    have hh : ∀ᵐ seeds ∂independentTrialLaw μ, A.Halts f seeds := hpath.mono fun _ hs => hs.1
    have hcostmeas : Measurable fun seeds => (A.stopIndex f seeds : ℝ) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (A.stopIndex_measurable f (hm.1 f hf))
    have hc := trialCost_integrable_bound μ good hgood hbad'
      (fun seeds => (A.stopIndex f seeds : ℝ)) hcostmeas (fun _ => Nat.cast_nonneg _) N
      (hpath.mono fun _ hs => hs.2)
    have hg : ∀ᵐ seeds ∂independentTrialLaw μ, ‖fderiv ℝ (average f) (A.stoppedResult f seeds)‖ ≤ ε := by
      filter_upwards [hh] with seeds hhalt
      exact restartStoppingAlgorithm_certified index trials f
        (fun x => ‖fderiv ℝ (average f) x‖ ≤ ε) (hvalid f hf) seeds hhalt
    have hgradmeas := A.stoppedGradient_measurable f (hm.1 f hf) (fun N => hm.2 N f hf)
    have hgi : Integrable (fun seeds => ‖fderiv ℝ (average f) (A.stoppedResult f seeds)‖)
        (independentTrialLaw μ) :=
      integrable_of_le_of_le hgradmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hg (integrable_const 0) (integrable_const ε)
    refine ⟨hh, hc.1, hgi, hc.2, ?_⟩
    simpa using
      integral_mono_ae hgi (integrable_const ε) hg
  exact ⟨hm, fun f hf => (hinstance f hf).1, fun f hf => (hinstance f hf).2.1,
    fun f hf => (hinstance f hf).2.2.1, fun f hf => (hinstance f hf).2.2.2.1,
    fun f hf => (hinstance f hf).2.2.2.2⟩

end FullJet
