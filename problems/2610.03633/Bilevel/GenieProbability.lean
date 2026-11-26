import Bilevel.GenieProtocol
import Bilevel.ProjectionConcentration

/-! A complete conditional-probability induction for finite adaptive projection protocols. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace Bilevel.GenieProtocol
open EuclideanGaussian ProjectionPosterior
set_option maxHeartbeats 600000

def failurePerQuery (T n : ℕ) (b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((T : ℝ) * (2 * Real.exp (-(n : ℝ) * b / 8)))

theorem failure_bound {d T : ℕ} (n : ℕ) (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    {m r : ℕ} (P : Protocol d T m r) :
    ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V + m + r + (n+1) ≤ d →
    ∀ (μ : Measure (Frame d T)) [IsProbabilityMeasure μ], Invariant d T V μ →
      (∀ᵐ U ∂μ, Orthonormal ℝ U) → Regular b P → Valid P V →
      μ {U | bad b P U} ≤ (m : ℝ≥0∞) * failurePerQuery T n b := by
  induction P with
  | halt =>
    intro V _ μ _ _ _ _ _
    simp only [bad, Set.setOf_false, measure_empty]
    exact zero_le _
  | @query m r w next ih =>
    intro V hdim μ _ hμ hU hP hV
    let W := V ⊔ Submodule.span ℝ {w}
    have hdE : Module.finrank ℝ (Space d) = d := by simp [Space]
    have hn : n+1 ≤ Module.finrank ℝ Vᗮ := by
      have hh := V.finrank_add_finrank_orthogonal
      omega
    have hdW : Module.finrank ℝ W + m + r + (n+1) ≤ d := by
      have hh := ProjectionQuery.finrank_insert_le V w
      change Module.finrank ℝ W ≤ Module.finrank ℝ V + 1 at hh
      omega
    have hhead : μ {U : Frame d T | ∃ i : Fin T, b ≤ ⟪w,U i⟫ ^ 2} ≤ failurePerQuery T n b := by
      have h := ProjectionConcentration.query_tail_dimension d T V n hn b hb hb2 μ hμ w hV.1 hV.2.1 hU
      simpa only [failurePerQuery, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        ENNReal.ofReal_le_ofReal h
    have htail : μ {U | bad b (next (queryObservation d T w U)) U} ≤
        (m : ℝ≥0∞) * failurePerQuery T n b := by
      let o := queryObservation d T w
      letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map (query_measurable d T w).aemeasurable
      have he := ConditionalSupport.event_disintegration μ o (query_measurable d T w)
        {p : (Fin T → ℝ) × Frame d T | bad b (next p.1) p.2} hP.1
      change μ {U | bad b (next (queryObservation d T w U)) U} = _ at he
      rw [he]
      calc
        _ ≤ ∫⁻ _y, (m : ℝ≥0∞) * failurePerQuery T n b ∂μ.map o := by
          apply lintegral_mono_ae
          filter_upwards [query_posterior_invariant d T V μ hμ w,
            ProjectionConcentration.conditioned_orthonormal d T μ hU o (query_measurable d T w)] with y hy hyU
          exact ih y W hdW (condDistrib id o μ y) hy hyU (hP.2 y) (hV.2.2 y)
        _ = _ := by simp
    have he : {U : Frame d T | bad b (.query w next) U} =
        {U | ∃ i : Fin T, b ≤ ⟪w,U i⟫ ^ 2} ∪
        {U | bad b (next (queryObservation d T w U)) U} := rfl
    rw [he]
    apply (measure_union_le _ _).trans
    have hsum := add_le_add hhead htail
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hsum
  | @reveal m r i next ih =>
    intro V hdim μ _ hμ hU hP hV
    let o := revealObservation d T i
    letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map (reveal_measurable d T i).aemeasurable
    have he := ConditionalSupport.event_disintegration μ o (reveal_measurable d T i)
      {p : Space d × Frame d T | bad b (next p.1) p.2} hP.1
    change μ {U | bad b (.reveal i next) U} = _ at he
    rw [he]
    calc
      _ ≤ ∫⁻ _y, (m : ℝ≥0∞) * failurePerQuery T n b ∂μ.map o := by
        apply lintegral_mono_ae
        filter_upwards [reveal_posterior_invariant d T V μ hμ i,
          ProjectionConcentration.conditioned_orthonormal d T μ hU o (reveal_measurable d T i)] with y hy hyU
        have hdW : Module.finrank ℝ (V ⊔ Submodule.span ℝ {y} : Submodule ℝ (Space d)) + m + r + (n+1) ≤ d := by
          have hh := ProjectionQuery.finrank_insert_le V y
          omega
        exact ih y _ hdW (condDistrib id o μ y) hy hyU (hP.2 y) (hV y)
      _ = _ := by simp

theorem haar_failure_bound (d T M R n : ℕ) (hT : T ≤ d)
    (P : Protocol d T M R) (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2)
    (hd : M+R+(n+1) ≤ d) (hP : Regular b P) (hV : Valid P ⊥) :
    (HaarFrame.frameLaw d T hT) {U | bad b P U} ≤ (M : ℝ≥0∞) * failurePerQuery T n b := by
  apply failure_bound n b hb hb2 P ⊥ (by simpa using hd) (HaarFrame.frameLaw d T hT)
    (frame_law_invariant d T hT ⊥) (ProjectionConcentration.haar_orthonormal_ae d T hT) hP hV

end Bilevel.GenieProtocol
