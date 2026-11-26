import VIReference.Pilot.ModelMeasurableSelector

open Set
open scoped RealInnerProductSpace BigOperators

namespace VIReference.Pilot

noncomputable section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : DecidableEq E := Classical.decEq E

/-- Canonical public datum used by the total ambient model selector.  The
selector's extension outside the valid-jet set is nonunique, so feeding it the
original `x0` would make counterfactual transcript behavior depend on an
irrelevant anchor through `Classical.choose`.  This record fixes that anchor
from `X_nonempty`; all mathematical class fields are unchanged. -/
noncomputable def canonicalModelData (data : VIPublicData E) : VIPublicData E where
  dimension_pos := data.dimension_pos
  p := data.p
  p_ge_two := data.p_ge_two
  Lp := data.Lp
  Lp_pos := data.Lp_pos
  D := data.D
  D_pos := data.D_pos
  X := data.X
  X_nonempty := data.X_nonempty
  X_compact := data.X_compact
  X_convex := data.X_convex
  x0 := Classical.choose data.X_nonempty
  x0_mem := Classical.choose_spec data.X_nonempty
  diameter_le := data.diameter_le


/-- Backwards-compatible executable name.  Unlike the previous unrestricted
`Classical.choose`, this is the continuous ambient selector. -/
noncomputable def knownModelStep (data : VIPublicData E) (x : data.X)
    (jet : SymmetricExactJet E data.p) : data.X × E :=
  borelKnownModelStep (canonicalModelData data) (x, jet)


theorem knownModelStep_genuine_spec (data : VIPublicData E) (G : E → E)
    (hG : IsAdmissibleOperator data G)
    (oracle : FeasibleExactSymmetricJetOracle data G) (center : data.X) :
    IsKnownModelStep data center (oracle.answer center)
      (knownModelStep data center (oracle.answer center)) :=
  by
    let canonicalOracle : FeasibleExactSymmetricJetOracle
        (canonicalModelData data) G := {
      answer := oracle.answer
      exact := oracle.exact }
    have hcanonical : IsAdmissibleOperator (canonicalModelData data) G := by
      constructor
      · obtain ⟨U, hU, hXU, hreg⟩ := hG.regularity
        exact ⟨U, hU, by simpa [canonicalModelData] using hXU,
          by simpa [canonicalModelData] using hreg⟩
      · intro x hx y hy
        exact hG.monotone_on x (by simpa [canonicalModelData] using hx) y
          (by simpa [canonicalModelData] using hy)
      · intro x hx y hy
        exact hG.top_derivative_lipschitz x
          (by simpa [canonicalModelData] using hx) y
          (by simpa [canonicalModelData] using hy)
    have hs := borelKnownModelStep_genuine_spec (canonicalModelData data) G
      hcanonical canonicalOracle center
    constructor
    · intro z hz
      exact hs.1 z (by simpa [canonicalModelData] using hz)
    · exact hs.2

/-- The first-answer continuation used by every Halve iteration is total and
continuous on the whole ambient center--jet space, including invalid jets. -/
theorem continuous_knownModelStep (data : VIPublicData E) :
    Continuous (fun a : data.X × SymmetricExactJet E data.p ↦
      knownModelStep data a.1 a.2) :=
  continuous_borelKnownModelStep data

/-- Norm-Borel evidence for the next query selected after the first answer of
a Halve iteration.  This is the local rule consumed by the policy compiler. -/
theorem halving_model_query_normBorel (data : VIPublicData E)
    (x : data.X) :
    @Measurable (SymmetricExactJet E data.p) data.X
      (upperJetBorelMeasurableSpace data.p)
      (upperFeasibleBorelMeasurableSpace data)
      (fun jet ↦ (knownModelStep data x jet).1) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact measurable_borelKnownModelPoint_fixedCenter data x

/-- The early-stop branch test in Halve is Borel on every hypothetical first
answer, not merely on genuine oracle answers. -/
theorem halving_early_branch_normBorel (data : VIPublicData E)
    (x : data.X) :
    @MeasurableSet (SymmetricExactJet E data.p)
      (upperJetBorelMeasurableSpace data.p)
      {jet | (knownModelStep data x jet).1 = x} := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  exact (halving_model_query_normBorel data x)
    (measurableSet_singleton x)

structure HalvingOutput (data : VIPublicData E) where
  point : E
  early : Bool
  normal : E
  value : E

/-- Exact-oracle syntax tree for the finite halving loop. Every ordinary
iteration makes one jet query at `x` and one value-containing jet query at
`y`. The exact-solution branch stops after the first query. -/
noncomputable def halvingProgramAux (data : VIPublicData E) (mu : ℝ) :
    (remaining : ℕ) → (x : data.X) → (weighted : E) → (Lambda : ℝ) →
      ExactJetProgram data.X (SymmetricExactJet E data.p) (HalvingOutput data)
  | 0, x, weighted, Lambda =>
      .halt (some {
        point := if Lambda = 0 then x.1 else (1 / Lambda) • weighted
        early := false
        normal := 0
        value := 0 })
  | remaining + 1, x, weighted, Lambda =>
      .query x (fun jetx =>
        let yn := knownModelStep data x jetx
        if hxy : yn.1.1 = x.1 then
          .halt (some {
            point := yn.1.1
            early := true
            normal := yn.2
            value := symmetricJetValue data jetx })
        else
          .query yn.1 (fun jety =>
            let lambda := 1 / ((tensorBetaCoefficient data.p * data.Lp) *
              ‖yn.1.1 - x.1‖ ^ (data.p - 1))
            let xp := compactConvexProjection data.X data.X_nonempty data.X_compact
              data.X_convex (x.1 - lambda • symmetricJetValue data jety)
            halvingProgramAux data mu remaining
              ⟨xp, compactConvexProjection_mem data.X data.X_nonempty data.X_compact
                data.X_convex _⟩
              (weighted + lambda • yn.1.1) (Lambda + lambda)))

noncomputable def halvingProgram (data : VIPublicData E) (center : data.X)
    (mu r : ℝ) :
    ExactJetProgram data.X (SymmetricExactJet E data.p) (HalvingOutput data) :=
  halvingProgramAux data mu
    (halvingIterationCount data.p data.Lp r mu) center 0 0

theorem halvingProgramAux_queries_le (data : VIPublicData E) (mu : ℝ)
    (remaining : ℕ) (x : data.X) (weighted : E) (Lambda : ℝ)
    (oracle : data.X → SymmetricExactJet E data.p)
    {used : ℕ} {result : Option (HalvingOutput data)}
    (heval : ExactJetProgram.Evaluates oracle
      (halvingProgramAux data mu remaining x weighted Lambda) used result) :
    used ≤ 2 * remaining := by
  induction remaining generalizing x weighted Lambda used result with
  | zero =>
      simp [halvingProgramAux] at heval
      cases heval
      omega
  | succ remaining ih =>
      simp only [halvingProgramAux] at heval
      cases heval with
      | query point next childUsed childResult hnext =>
          dsimp only at hnext
          split at hnext
          · cases hnext
            omega
          · cases hnext with
            | query point₂ next₂ tailUsed tailResult htail =>
                have hle := ih _ _ _ htail
                omega

/-- Every branch, including early return, uses at most the source's
`2 T_p(r,μ)` original exact-jet queries. -/
theorem halvingProgram_queries_le (data : VIPublicData E) (center : data.X)
    (mu r : ℝ) (oracle : data.X → SymmetricExactJet E data.p)
    {used : ℕ} {result : Option (HalvingOutput data)}
    (heval : ExactJetProgram.Evaluates oracle
      (halvingProgram data center mu r) used result) :
    used ≤ 2 * halvingIterationCount data.p data.Lp r mu := by
  exact halvingProgramAux_queries_le data mu _ center 0 0 oracle heval

end

end VIReference.Pilot
