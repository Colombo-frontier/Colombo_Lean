import Geode.TerminalCompletion
import Geode.StateQuery
import Geode.InitialState
import Geode.LowerReduction

/-! A complete deterministic resisting-oracle proof with one fixed objective
and one fixed legal oracle for the entire actual execution. -/
namespace Geode.Lorentz

open Geode.OracleReplay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {o : Point E} {R L ε : ℝ}

theorem archive_failure_completion (A : FirstOrderAlgorithm E)
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hdim : Geode.queryHorizon R ε + 3 ≤ Module.finrank ℝ (Ambient E))
    (n t : ℕ) (s : PublicState o R (4 * ε))
    (history : History (Point E) (FirstOrderReply E))
    (harchive : ArchiveValid s history L) (hcuts : s.cuts ≤ t)
    (ht : t + n ≤ Geode.queryHorizon R ε) :
    ∃ (f : Point E → ℝ) (O : Point E → FirstOrderReply E) (p : Point E),
      AdmissibleObjective o R L f ∧ LegalOracle f O ∧
      (∀ y, (∀ z, f y ≤ f z) ↔ y = p) ∧ f p = 0 ∧ dist o p = R ∧
      (∀ y r, (y, r) ∈ history → O y = r) ∧
      RunFails (fun output => 2 * ε * L * R ≤ f output - f p)
        (run A (fixedResponder O) n history) := by
  classical
  induction n generalizing t s history with
  | zero =>
    have hk : s.cuts ≤ Geode.queryHorizon R ε := by omega
    cases hd : A.decide history with
    | stop x =>
      obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree, hgap⟩ :=
        harchive.bad_output_completion hR hL hε hεmax hk hdim x
      exact ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree,
        by simpa only [run, hd, RunFails] using hgap⟩
    | query x =>
      obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree, _⟩ :=
        harchive.bad_output_completion hR hL hε hεmax hk hdim x
      exact ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree,
        by simp only [run, hd, RunFails]⟩
  | succ n ih =>
    have hk : s.cuts ≤ Geode.queryHorizon R ε := by omega
    cases hd : A.decide history with
    | stop x =>
      obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree, hgap⟩ :=
        harchive.bad_output_completion hR hL hε hεmax hk hdim x
      exact ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree,
        by simpa only [run, hd, RunFails] using hgap⟩
    | query y =>
      by_cases hc : ∃ r, (y, r) ∈ history
      · obtain ⟨r, hr⟩ := hc
        obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree, hfail⟩ :=
          ih (t + 1) s (history ++ [(y, r)]) (harchive.append_cached hr)
            (by omega) (by omega)
        have hreply : O y = r := hagree y r (List.mem_append_right _ (by simp))
        refine ⟨f, O, p, hf, hO, hmin, hzero, hp,
          fun x v hv => hagree x v (List.mem_append_left _ hv), ?_⟩
        simpa only [run, hd, fixedResponder, hreply] using hfail
      · have hμ : 0 < 4 * ε := by positivity
        have hμmax : 4 * ε ≤ 1 / 16 := by linarith
        have hη : Geode.eta (4 * ε) ^ 2 < 1 := by
          rw [Geode.eta_four_mul]
          have hh := (Geode.latitude_bounds hε hεmax).2.2
          linarith
        obtain ⟨s', a, he, hay, ha⟩ := s.query_extension hμ hμmax hη
          (s.residual_capacity hk hdim) y
        let r := a.reply (4 * ε) L
        have hafresh : ∀ v, (a.y, v) ∉ history := by
          intro v hv
          exact hc ⟨v, by simpa only [hay] using hv⟩
        have harchive' : ArchiveValid s' (history ++ [(y, r)]) L := by
          simpa only [hay] using (harchive.extend he).append_fresh a ha hafresh
        obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, hagree, hfail⟩ :=
          ih (t + 1) s' (history ++ [(y, r)]) harchive'
            (by have hh := he.cuts; omega) (by omega)
        have hreply : O y = r := hagree y r (List.mem_append_right _ (by simp))
        refine ⟨f, O, p, hf, hO, hmin, hzero, hp,
          fun x v hv => hagree x v (List.mem_append_left _ hv), ?_⟩
        simpa only [run, hd, fixedResponder, hreply] using hfail

/-- The precise fixed-instance assertion, including a unique global minimizer
on the original localization sphere and arbitrary, possibly unqueried outputs. -/
theorem precise_failure_witness (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hdim : Geode.queryHorizon R ε + 3 ≤ Module.finrank ℝ (Ambient E))
    (A : FirstOrderAlgorithm E) :
    ∃ (f : Point E → ℝ) (O : Point E → FirstOrderReply E) (p : Point E),
      AdmissibleObjective o R L f ∧ LegalOracle f O ∧
      (∀ y, (∀ z, f y ≤ f z) ↔ y = p) ∧ f p = 0 ∧ dist o p = R ∧
      RunFails (fun output => 2 * ε * L * R ≤ f output - f p)
        (run A (fixedResponder O) (Geode.queryHorizon R ε) []) := by
  have hμ : 0 < 4 * ε := by positivity
  have hμmax : 4 * ε ≤ 1 / 16 := by linarith
  let s := initialPublicState o R (4 * ε) hR hμ hμmax
  obtain ⟨f, O, p, hf, hO, hmin, hzero, hp, _, hfail⟩ :=
    archive_failure_completion A hR hL hε hεmax hdim (Geode.queryHorizon R ε) 0 s []
      (ArchiveValid.nil s L) (by rfl) (by omega)
  exact ⟨f, O, p, hf, hO, hmin, hzero, hp, hfail⟩

theorem horizon_failure_witness (o : Point E) {R L ε : ℝ}
    (hR : 0 < R) (hL : 0 < L) (hε : 0 < ε) (hεmax : ε ≤ 1 / 64)
    (hdim : Geode.queryHorizon R ε + 3 ≤ Module.finrank ℝ (Ambient E)) :
    HorizonFailureWitness o R L ε (Geode.queryHorizon R ε) := by
  intro A
  obtain ⟨f, O, p, hf, hO, hmin, _, _, hfail⟩ :=
    precise_failure_witness o hR hL hε hεmax hdim A
  exact ⟨f, O, p, hf, hO, (hmin p).mpr rfl, hfail⟩

end Geode.Lorentz
