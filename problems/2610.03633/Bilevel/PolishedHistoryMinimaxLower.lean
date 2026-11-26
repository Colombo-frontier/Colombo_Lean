import Bilevel.PolishedHistoryStationaryStopping
import Bilevel.ChiUniformLowerModelTheorem
import Bilevel.PolishedPositiveDimension

/-! Minimax transfer from genuine stationary instances to the broader
history-kernel instance class. Algorithms receive the supplied initialization.
The proof handles infinite worst-case cost before using finite-cost risk
identification; nontermination fallback losses are not silently equated. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.PolishedHistory
open PrimitiveQuery
set_option autoImplicit false
variable {μ L ρ Δ R₀ σf σg : ℝ}

theorem stationary_complexity_le_history
    (C : PrimitiveQuery.InstanceClass μ L ρ Δ R₀ σf σg)
    (D : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    (hCD : ∀ G (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg),C G I → D G (ofStationary I)) :
    PrimitiveQuery.Complexity C ε≤Complexity D ε := by
  unfold Complexity PrimitiveQuery.Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  let T : ℝ≥0∞ := ⨆ I : {I : (G : Geometry) × Instance G μ L ρ Δ R₀ σf σg // D I.1 I.2},
    I.val.2.cost (A.val I.val.1 I.val.2.x₀ I.val.2.yinit)
  by_cases hT : T=⊤
  · change _≤T
    rw [hT]
    exact le_top
  have hbound (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (hI : C G I) :
      (ofStationary I).cost (A.val G 0 0)≤T :=
    le_iSup_of_le ⟨⟨G,ofStationary I⟩,hCD G I hI⟩ le_rfl
  have hfinite (G : Geometry) (I : PrimitiveQuery.Instance G μ L ρ Δ R₀ σf σg) (hI : C G I) :
      (ofStationary I).cost (A.val G 0 0)≠⊤ := by
    intro hc
    have ht : (⊤:ℝ≥0∞)≤T := by rw [← hc];exact hbound G I hI
    exact hT (top_le_iff.mp ht)
  let oldSolver : PrimitiveQuery.Solver := fun G => A.val G 0 0
  have hacc : PrimitiveQuery.Accurate C ε oldSolver := by
    intro G I hI
    have h := A.property G (ofStationary I) (hCD G I hI)
    change (ofStationary I).risk (A.val G 0 0)≤ENNReal.ofReal ε at h
    rw [ofStationary_risk_of_cost_finite I _ (hfinite G I hI)] at h
    exact h
  refine (iInf_le _ ⟨oldSolver,hacc⟩).trans ?_
  apply iSup_le
  intro I
  have hh := hbound I.val.1 I.val.2 I.property
  rw [ofStationary_cost] at hh
  exact hh

theorem stationary_conservative_complexity_le_history (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
    Complexity (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε :=
  stationary_complexity_le_history _ _ ε (fun _ I hI => ofStationary_isConservative I hI)

theorem complexity_mono_class
    (C D : InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ)
    (hCD : ∀ G I,C G I → D G I) : Complexity C ε≤Complexity D ε := by
  unfold Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  refine (iInf_le _ ⟨A.val,fun G I hI => A.property G I (hCD G I hI)⟩).trans ?_
  apply iSup_le
  intro I
  exact le_iSup_of_le ⟨I.val,hCD I.val.1 I.val.2 I.property⟩ le_rfl


/-- Removing zero-dimensional outer spaces leaves the stationary minimax
value unchanged in the direction needed by lower bounds. The completion is
a real zero-call algorithm, not an assumed complexity-zero interface. -/
theorem stationary_complexity_le_positive
    (C : PrimitiveQuery.InstanceClass μ L ρ Δ R₀ σf σg) (ε : ℝ) :
    PrimitiveQuery.Complexity C ε≤
      PrimitiveQuery.Complexity (PolishedPositiveDimension.positiveClass C) ε := by
  classical
  unfold PrimitiveQuery.Complexity ChiMinimax.complexity
  apply le_iInf
  intro A
  have hacc : PrimitiveQuery.Accurate C ε (PolishedPositiveDimension.extend A.val) := by
    intro G I hI
    by_cases hG : Nontrivial G.X
    · simpa only [PolishedPositiveDimension.extend,if_pos hG] using A.property G I ⟨hI,hG⟩
    · letI : Subsingleton G.X := not_nontrivial_iff_subsingleton.mp hG
      rw [PolishedPositiveDimension.trivial_risk]
      exact zero_le _
  refine (iInf_le _ ⟨PolishedPositiveDimension.extend A.val,hacc⟩).trans ?_
  apply iSup_le
  intro I
  change I.val.2.cost (PolishedPositiveDimension.extend A.val I.val.1)≤_
  by_cases hG : Nontrivial I.val.1.X
  · rw [PolishedPositiveDimension.extend,if_pos hG]
    exact le_iSup_of_le ⟨I.val,⟨I.property,hG⟩⟩ le_rfl
  · rw [PolishedPositiveDimension.extend,if_neg hG,PolishedPositiveDimension.zeroAlgorithm_cost]
    exact zero_le _

def positiveClass (C : InstanceClass μ L ρ Δ R₀ σf σg) :
    InstanceClass μ L ρ Δ R₀ σf σg := fun G I => C G I ∧ Nontrivial G.X

theorem stationary_conservative_complexity_le_positive_history (ε : ℝ) :
    PrimitiveQuery.Complexity (PrimitiveQuery.conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg)) ε≤
    Complexity (positiveClass (conservativeClass (μ:=μ) (L:=L) (ρ:=ρ)
      (Δ:=Δ) (R₀:=R₀) (σf:=σf) (σg:=σg))) ε := by
  apply (stationary_complexity_le_positive _ ε).trans
  exact stationary_complexity_le_history _ _ ε
    (fun _ I hI => ⟨ofStationary_isConservative I hI.1,hI.2⟩)

/-- The uniform three-family lower rate now holds for the actual
history-kernel model, with arbitrary supplied public initialization. -/
theorem uniform_history_conservative_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,h⟩ := ChiUniformLower.uniform_conservative_minimax_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  exact (h L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc).trans
    (stationary_conservative_complexity_le_history ε)

theorem uniform_history_unrestricted_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (unrestrictedClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg)) ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,h⟩ := uniform_history_conservative_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  exact (h L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc).trans
    (complexity_mono_class _ _ ε (fun _ _ _ => True.intro))


/-- Source-positive dimensions (both public finite dimensions are at least
one) and arbitrary supplied initialization in the actual history-kernel model. -/
theorem uniform_positive_history_conservative_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε := by
  obtain ⟨c,cq,hc,hc1,hcq,q,h⟩ := ChiUniformLower.uniform_conservative_minimax_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  exact (h L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc).trans
    (stationary_conservative_complexity_le_positive_history ε)


/-- One set of numerical constants works for both source-positive classes. -/
theorem uniform_positive_history_both_lower :
    ∃ c cq : ℝ,0<c ∧ c≤1 ∧ 0<cq ∧ ∃ q : ℕ,
    ∀ (L μ κ θ Δ ε R₀ σf σg : ℝ),
      0<L → 0<μ → 2≤κ → κ=L/μ → 1≤θ → θ≤κ^2 →
      0<Δ → 0<ε → 0≤R₀ → ε≤c*min L (Real.sqrt (L*Δ)) →
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (conservativeClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε) ∧
      (ENNReal.ofReal (cq*ChiUniformLower.lowerBracket q L κ θ σf σg Δ ε)≤
        Complexity (positiveClass (unrestrictedClass (μ:=μ) (L:=L) (ρ:=θ*μ) (Δ:=Δ)
          (R₀:=R₀) (σf:=σf) (σg:=σg))) ε) := by
  obtain ⟨c,cq,hc,hc1,hcq,q,h⟩ := uniform_positive_history_conservative_lower
  refine ⟨c,cq,hc,hc1,hcq,q,?_⟩
  intro L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  have hh := h L μ κ θ Δ ε R₀ σf σg hL hμ hκ hκeq hθ hθκ hΔ hε hR₀ hacc
  exact ⟨hh,hh.trans (complexity_mono_class _ _ ε (fun _ _ hI => ⟨True.intro,hI.2⟩))⟩

end Bilevel.PolishedHistory
