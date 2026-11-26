import Bilevel.PolishedHistoryFreshRun

/-! Every finite marginal of the embedded stationary experiment agrees with
the original adaptive seed experiment, for the same public program and the
same independent private initialization. No stopped-law equality is postulated. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false

theorem historyOracle_ext {Q O H : Type*} [MeasurableSpace Q]
    [MeasurableSpace O] [MeasurableSpace H] {R T : HistoryProgram.Oracle Q O H}
    (hl : R.law=T.law) (hu : R.update=T.update) : R=T := by
  cases R
  cases T
  cases hl
  cases hu
  rfl

variable {G : Geometry} {μ L ρ Δ R₀ σf σg : ℝ}
variable (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg)

theorem stationary_reply_measurable : Measurable (Function.uncurry (I.reply ())) :=
  I.upper.sample_measurable.prodMk I.lower.sample_measurable

theorem ofStationary_historyOracle :
    (ofStationary I).historyOracle=
      freshOracle I.law (I.reply ()) (stationary_reply_measurable I) := by
  apply historyOracle_ext
  · apply Kernel.ext
    rintro ⟨q,h⟩
    change (ofStationary I).packedLaw (q,h)=_
    rw [ofStationary_packedLaw]
    exact (freshOracle_law I.law (I.reply ()) (stationary_reply_measurable I) q h).symm
  · rfl

/-- Exact actual finite-horizon distribution, including the full algorithm
state (which may contain private randomness and the entire transcript). -/
theorem ofStationary_execution_endpoint (A : Algorithm G) (n : ℕ) :
    ((ofStationary I).execution A).map (fun w => w n)=
      (A.privateLaw.prod (IndependentStream.law I.law)).map
        (fun z => (BorelAdaptive.run A.program I.reply () z.2 (A.start z.1) n,())) := by
  rw [Instance.execution,HistoryProgram.trajectoryLaw_endpoint _ _ _ _ A.start_measurable]
  rw [ofStationary_historyOracle]
  exact (fresh_private_run_law I.law (I.reply ()) (stationary_reply_measurable I)
    A.program A.privateLaw A.start A.start_measurable n).symm

end Bilevel.PolishedHistory
