import Bilevel.PolishedSourcePostUpper

/-! Source minimax classes may impose an actual mean-curvature constraint
and strictly positive outer dimension without changing execution semantics. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery PrimitiveGeometry
set_option autoImplicit false
variable {μ L ρ Δ R₀ σf σg : ℝ}

abbrev SourceMeanClass (μ L ρ Δ R₀ : ℝ) := (G : Geometry) → SourceMean G μ L ρ Δ R₀ → Prop

def SourceMean.CurvatureBound {G : Geometry} (M : SourceMean G μ L ρ Δ R₀) (Λ : ℝ) : Prop :=
  ∀ x y,‖gradient (M.primitive.hyperobjective M.response) x-
    gradient (M.primitive.hyperobjective M.response) y‖≤Λ*‖x-y‖

def positiveSourceClass (C : SourceMeanClass μ L ρ Δ R₀) : SourceMeanClass μ L ρ Δ R₀ :=
  fun G M => C G M ∧ Nontrivial G.X

def sourceCurvatureClass (Λ : ℝ) : SourceMeanClass μ L ρ Δ R₀ := fun _ M => M.CurvatureBound Λ

def restrictedPostAccurate (C : SourceMeanClass μ L ρ Δ R₀) (conservative : Bool)
    (ε : ℝ) (A : PostSolverAt) : Prop :=
  ∀ K : PostSourceChallenge A μ L ρ Δ R₀ σf σg,
    C K.geometry K.mean → (conservative=true → K.execution.IsConservative) →
      K.execution.postRisk≤ENNReal.ofReal ε

def restrictedPostWorstCost (C : SourceMeanClass μ L ρ Δ R₀) (conservative : Bool)
    (A : PostSolverAt) : ℝ≥0∞ :=
  ⨆ K : {K : PostSourceChallenge A μ L ρ Δ R₀ σf σg //
    C K.geometry K.mean ∧ (conservative=true → K.execution.IsConservative)},K.val.execution.cost

def restrictedPostComplexity (C : SourceMeanClass μ L ρ Δ R₀) (conservative : Bool) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ A : {A : PostSolverAt // restrictedPostAccurate (σf:=σf) (σg:=σg) C conservative ε A},
    restrictedPostWorstCost (σf:=σf) (σg:=σg) C conservative A.val

theorem restricted_post_complexity_le_of_solver (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) (ε : ℝ) (A : PostSolverAt) (b : ℝ≥0∞)
    (hrisk : restrictedPostAccurate (σf:=σf) (σg:=σg) C conservative ε A)
    (hcost : ∀ K : PostSourceChallenge A μ L ρ Δ R₀ σf σg,
      C K.geometry K.mean → (conservative=true → K.execution.IsConservative) → K.execution.cost≤b) :
    restrictedPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤b := by
  unfold restrictedPostComplexity
  apply iInf_le_of_le ⟨A,hrisk⟩
  apply iSup_le
  intro K
  exact hcost K.val K.property.1 K.property.2

theorem source_post_restricted_normalized_upper (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) {ε : ℝ} (hL : 0<L) (hΔ : 0≤Δ) (hε : 0<ε) (hκ : 1≤L/μ) :
    restrictedPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤
      ENNReal.ofReal (CachedUpper.normalizedBound L μ L L L ρ σf σg Δ ε R₀) := by
  apply restricted_post_complexity_le_of_solver C conservative ε
    (fun G x y => sourceFrozenPostAlgorithm G μ L ρ Δ ε R₀ σf σg x y)
  · intro K _ _
    exact (K.mean.source_frozen_post_upper K.execution hL hΔ hε hκ).1
  · intro K _ _
    exact (K.mean.source_frozen_post_upper K.execution hL hΔ hε hκ).2

theorem source_post_restricted_three_term_upper (C : SourceMeanClass μ L ρ Δ R₀)
    (conservative : Bool) {ε : ℝ} (hL : 0<L) (hΔ : 0<Δ) (hε : 0<ε)
    (hθ : 1≤ρ/μ) (hκ : 1≤L/μ) (haccuracy : ε≤min L (Real.sqrt (L*Δ))) :
    restrictedPostComplexity (σf:=σf) (σg:=σg) C conservative ε≤
      ENNReal.ofReal (CachedUpper.threeRateBound L μ L L L ρ σf σg Δ ε R₀) :=
  (source_post_restricted_normalized_upper C conservative hL hΔ.le hε hκ).trans
    (ENNReal.ofReal_le_ofReal (CachedUpper.normalizedBound_le_threeRateBound hL hΔ hθ hκ hε haccuracy))

end Bilevel.PolishedHistory
