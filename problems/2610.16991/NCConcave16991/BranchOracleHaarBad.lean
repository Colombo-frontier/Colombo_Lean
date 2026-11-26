import NCConcave16991.BranchOracleHaarFamily
import NCConcave16991.BranchOracleStaticBadMeasurable
import NCConcave16991.LowerYao
import NCConcave16991.ConditionalHaarProduct

/-! # The actual measurable Haar bad event and unrestricted Yao contradiction -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NCConcave16991.BranchOracle

open GlobalHard GlobalHardEuclidean MixedHaar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 6000
set_option maxSynthPendingDepth 32
set_option backward.isDefEq.respectTransparency false

variable (n M m D : ℕ) (hn : 0 < n) (hD : 0 < D)
  {Ω : Type} [MeasurableSpace Ω]
  (P : StaticPolicy (M := M) (m := m) (Space D) hn Ω)

def haarBadEvent (budget : ℕ) (j : Fin M) : Set (Ω × HaarParameter n M m D) := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact staticBadEvent (Space D) (haarRotations n M m D) (haarSource D hD) hn P budget j

theorem haarBadEvent_measurable (budget : ℕ) (j : Fin M) :
    MeasurableSet (haarBadEvent n M m D hn hD P budget j) := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI := macroJoint_borelSpace (ι := Fin n) (Space D) M m
  letI := macroSources_borelSpace (ι := Fin n) (Space D) M m
  letI := macroActions_borelSpace (ι := Fin n) (Space D) M m
  exact staticBadEvent_measurable (Space D) (haarRotations n M m D)
    (haarRotations_forward_measurable n M m D) (haarRotations_inverse_measurable n M m D)
    (haarSource D hD) hn P budget j

theorem haar_stationary_implies_bad (hM : 0 < M) (seed : Ω) (budget : ℕ) (j : Fin M)
    (θ : HaarParameter n M m D)
    (hs : StationaryOutput (haarPaperProblem n M m D hn hM hD θ)
      (OraclePolicy.run (paperDualDomain (MacroSpaces (ι := Fin n) (Space D) M m) hn) P
        (oracleResponse (haarPaperProblem n M m D hn hM hD θ)) seed budget).1) :
    (seed,θ) ∈ haarBadEvent n M m D hn hD P budget j := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact stationary_implies_staticBadAt (Space D) hn hM (haarRotations n M m D θ)
    (haarSource D hD) (haarSource_unit D hD) P seed budget j hs

theorem invalid_budget_of_haar_bad_bound (hM : 0 < M) (budget : ℕ) (j : Fin M)
    (hBad : ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : StaticPolicy (M := M) (m := m) (Space D) hn Ω) (seed : Ω),
      (staticHaarLaw n M m D).real {θ | (seed,θ) ∈ haarBadEvent n M m D hn hD P budget j} ≤ 1 / 6) :
    ¬ ValidBudget (paperParameters n hn M hM m) .individual budget := by
  intro hvalid
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨A,hA⟩ := hvalid (primalDimension (MacroSpaces (ι := Fin n) (Space D) M m))
    (dualDimension (MacroSpaces (ι := Fin n) (Space D) M m))
    (paperDualDomain (MacroSpaces (ι := Fin n) (Space D) M m) hn) 0
  letI : MeasurableSpace A.Seed := A.seedSpace
  letI : IsProbabilityMeasure A.law := A.law_probability
  let family := haarPaperProblem n M m D hn hM hD
  let success := fun θ : HaarParameter n M m D ↦ {seed : A.Seed |
    StationaryOutput (family θ)
      (OraclePolicy.run (paperDualDomain (MacroSpaces (ι := Fin n) (Space D) M m) hn)
        A.policy (oracleResponse (family θ)) seed budget).1}
  let B := haarBadEvent n M m D hn hD A.policy budget j
  have hB : MeasurableSet B := haarBadEvent_measurable n M m D hn hD A.policy budget j
  have hprob (θ : HaarParameter n M m D) : (2 / 3 : ℝ≥0∞) ≤ A.law (success θ) :=
    (hA (family θ) rfl (haarPaperProblem_individualSmooth n M m D hn hM hD θ)).2
  have hsub (θ : HaarParameter n M m D) : success θ ⊆ {seed | (seed,θ) ∈ B} := by
    intro seed hs
    exact haar_stationary_implies_bad n M m D hn hD A.policy hM seed budget j θ hs
  have hlo := seed_prior_bad_mass_lower (staticHaarLaw n M m D) A.law B hB success hprob hsub
  have hhi : (A.law.prod (staticHaarLaw n M m D)).real B ≤ 1 / 6 :=
    Haar.product_event_bound A.law (staticHaarLaw n M m D) hB
      (fun seed ↦ hBad A.Seed A.policy seed)
  have hlR := ENNReal.toReal_mono (measure_ne_top (A.law.prod (staticHaarLaw n M m D)) B) hlo
  change (2 / 3 : ℝ≥0∞).toReal ≤ (A.law.prod (staticHaarLaw n M m D)).real B at hlR
  norm_num at hlR
  linarith

end NCConcave16991.BranchOracle
