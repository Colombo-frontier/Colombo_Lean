import NCConcave16991.UpperAssembly

/-! # Public gap, diameter and accuracy bounds in the actual oracle model -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NCConcave16991.ProblemBounds

abbrev parameters (p : ProblemParameters) (Δ ε D : ℝ)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hD : 0 ≤ D) : ProblemParameters where
  n := p.n
  n_pos := p.n_pos
  L := p.L
  L_pos := p.L_pos
  gap := Δ
  gap_pos := hΔ
  epsilon := ε
  epsilon_pos := hε
  diameter := D
  diameter_nonneg := hD

def dualDomain {dy : ℕ} {D E : ℝ} (K : KnownDualDomain dy D) (h : D ≤ E) : KnownDualDomain dy E where
  carrier := K.carrier
  nonempty := K.nonempty
  compact := K.compact
  convex := K.convex
  diameter_bound := fun y hy y' hy' ↦ (K.diameter_bound y hy y' hy').trans h

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}
  {Δ ε D : ℝ} {hΔ : 0 < Δ} {hε : 0 < ε} {hD : 0 ≤ D}

def toProblem (P : Problem p dx dy K) (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D) :
    Problem (parameters p Δ ε D hΔ hε hD) dx dy (dualDomain K hdiam) where
  component := P.component
  componentGradient := P.componentGradient
  neighborhood := P.neighborhood
  neighborhood_open := P.neighborhood_open
  domain_subset := P.domain_subset
  gradient_correct := P.gradient_correct
  average_dual_concave := P.average_dual_concave
  initialPoint := P.initialPoint
  value_bddBelow := P.value_bddBelow
  initial_gap := P.initial_gap.trans hgap

theorem toProblem_individualSmooth (P : Problem p dx dy K)
    (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D) (hP : P.individualSmooth) :
    (toProblem (ε := ε) (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam).individualSmooth := hP

theorem moreau_eq (P : Problem p dx dy K) (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D) :
    problemMoreauEnvelope (toProblem (ε := ε) (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam) =
      problemMoreauEnvelope P := rfl

theorem stationary_transfer (P : Problem p dx dy K) (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D)
    (haccuracy : ε ≤ p.epsilon) (x : PrimalSpace dx)
    (hx : StationaryOutput (toProblem (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam) x) :
    StationaryOutput P x := by
  obtain ⟨g, hg, hn⟩ := hx
  exact ⟨g, hg, hn.trans haccuracy⟩

abbrev sourcePolicy (hdiam : p.diameter ≤ D)
    (A : RandomizedPolicy (dualDomain K hdiam) (n := p.n) (dx := dx)) :
    RandomizedPolicy K (n := p.n) (dx := dx) := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  exact {
    Seed := A.Seed
    seedSpace := A.seedSpace
    law := A.law
    law_probability := A.law_probability
    policy := {
      next := A.policy.next
      final := A.policy.final
      next_measurable := A.policy.next_measurable
      final_measurable := A.policy.final_measurable } }

theorem source_output_eq (P : Problem p dx dy K) (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D)
    (A : RandomizedPolicy (dualDomain K hdiam) (n := p.n) (dx := dx)) (T : ℕ) (seed : A.Seed) :
    randomizedOutput (sourcePolicy hdiam A) P T seed =
      randomizedOutput A (toProblem (ε := ε) (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam) T seed := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  have hrun (t : ℕ) (hist : OraclePolicy.History K (n := p.n) (dx := dx)) :
      (OraclePolicy.runAux K (sourcePolicy hdiam A).policy (oracleResponse P) seed t hist).1 =
        (OraclePolicy.runAux (dualDomain K hdiam) A.policy
          (oracleResponse (p := parameters p Δ ε D hΔ hε hD)
            (toProblem (ε := ε) (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam)) seed t hist).1 := by
    induction t generalizing hist with
    | zero => rfl
    | succ t ih =>
      simp only [OraclePolicy.runAux]
      cases he : A.policy.next seed hist with
      | inl x => rfl
      | inr q => exact ih _
  exact hrun T (OraclePolicy.emptyHistory K)

theorem success_transfer (P : Problem p dx dy K) (hP : P.individualSmooth)
    (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D) (haccuracy : ε ≤ p.epsilon)
    (A : RandomizedPolicy (dualDomain K hdiam) (n := p.n) (dx := dx)) (T : ℕ)
    (hA : Success A (toProblem (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam) T) :
    Success (sourcePolicy hdiam A) P T := by
  letI : MeasurableSpace A.Seed := A.seedSpace
  refine ⟨stationarity_event_measurable (sourcePolicy hdiam A) P (P.individual_implies_averaged hP) T, ?_⟩
  apply hA.2.trans
  apply measure_mono
  intro seed hs
  change StationaryOutput P (randomizedOutput (sourcePolicy hdiam A) P T seed)
  rw [source_output_eq (ε := ε) (hΔ := hΔ) (hε := hε) (hD := hD) P hgap hdiam A T seed]
  exact stationary_transfer P hgap hdiam haccuracy _ hs

theorem validBudget_source_of_bounds (p : ProblemParameters)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hD : 0 ≤ D)
    (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D) (haccuracy : ε ≤ p.epsilon)
    {T : ℕ} (hT : ValidBudget (parameters p Δ ε D hΔ hε hD) .individual T) :
    ValidBudget p .individual T := by
  intro dx dy K x0
  obtain ⟨A, hA⟩ := hT dx dy (dualDomain K hdiam) x0
  refine ⟨sourcePolicy (p := p) hdiam A, ?_⟩
  intro P h0 hP
  exact success_transfer P hP hgap hdiam haccuracy A T
    (hA (toProblem P hgap hdiam) h0 (toProblem_individualSmooth P hgap hdiam hP))

theorem lowerBudget_transfer (p : ProblemParameters)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hD : 0 ≤ D)
    (hgap : p.gap ≤ Δ) (hdiam : p.diameter ≤ D) (haccuracy : ε ≤ p.epsilon)
    {bound : ℝ} (h : LowerBudgetBound p .individual bound) :
    LowerBudgetBound (parameters p Δ ε D hΔ hε hD) .individual bound := by
  intro T hT
  exact h T (validBudget_source_of_bounds p hΔ hε hD hgap hdiam haccuracy hT)

end NCConcave16991.ProblemBounds
