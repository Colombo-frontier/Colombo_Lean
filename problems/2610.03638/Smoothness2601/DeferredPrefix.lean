import Smoothness2601.DeferredTail

/-! Deferred-prefix protocols. An inspection records a bad-coordinate event
but returns no projection information. Thus inspections cost no residual
dimension; only actual column revelations enlarge the known subspace. -/
noncomputable section
namespace Smoothness2601.DeferredPrefix
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior
open scoped RealInnerProductSpace ENNReal
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

inductive Protocol (d T : ℕ) : ℕ → ℕ → ℕ → Type
  | halt {k m r : ℕ} : Protocol d T k m r
  | inspect {k m r : ℕ} (w : Space d) (next : Protocol d T k m r) : Protocol d T k (m+1) r
  | reveal {k m r : ℕ} (i : Fin T) (hi : i.val = k)
      (next : Space d → Protocol d T (k+1) m r) : Protocol d T k m (r+1)

def bad {d T : ℕ} (δ : ℝ) : {k m r : ℕ} → Protocol d T k m r → Frame d T → Prop
  | _,_,_,.halt,_ => False
  | k,_,_,.inspect w next,U =>
      (∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|) ∨ bad δ next U
  | _,_,_,.reveal i _ next,U => bad δ (next (U i)) U

/-- Bounded queries and measurable execution only; no probability estimates. -/
def Regular {d T : ℕ} (δ R : ℝ) : {k m r : ℕ} → Protocol d T k m r → Prop
  | _,_,_,.halt => True
  | _,_,_,.inspect w next => ‖w‖ ≤ R ∧ Regular δ R next
  | _,_,_,.reveal _ _ next =>
      MeasurableSet {p : Space d × Frame d T | bad δ (next p.1) p.2} ∧
        ∀ y, Regular δ R (next y)

theorem bad_measurable {d T k m r : ℕ} (δ R : ℝ) (P : Protocol d T k m r)
    (hP : Regular δ R P) : MeasurableSet {U : Frame d T | bad δ P U} := by
  induction P with
  | halt => exact MeasurableSet.empty
  | @inspect k m r w next ih =>
    have hh : MeasurableSet {U : Frame d T | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|} := by
      simp only [Set.setOf_exists]
      apply MeasurableSet.iUnion
      intro i
      by_cases hi : k ≤ i.val
      · simpa only [hi,true_and] using
          (measurableSet_le measurable_const ((continuous_const.inner (continuous_apply i)).abs.measurable) :
            MeasurableSet {U : Frame d T | δ ≤ |⟪w,U i⟫|})
      · simp only [hi,false_and,Set.setOf_false]
        exact MeasurableSet.empty
    exact hh.union (ih hP.2)
  | reveal i _ next _ =>
    exact ((reveal_measurable d T i).prodMk measurable_id) hP.1

def failurePerInspection (T n : ℕ) (δ R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((T : ℝ)*(2*Real.exp (-(n : ℝ)*(δ^2/R^2)/8)))

/-- The dimension condition has no query-count term. It only reserves room
for the remaining full-column revelations and a residual sphere. -/
theorem failure_bound {d T k m r : ℕ} (P : Protocol d T k m r)
    (n : ℕ) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R) :
    ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V+r+(n+1) ≤ d →
    ∀ (μ : Measure (Frame d T)) [IsProbabilityMeasure μ], Invariant d T V μ →
      (∀ᵐ U ∂μ, Orthonormal ℝ U) →
      (∀ᵐ U ∂μ, UnseenOrthogonal d T k V U) → Regular δ R P →
      μ {U | bad δ P U} ≤ (m : ℝ≥0∞)*failurePerInspection T n δ R := by
  induction P with
  | halt =>
    intro V _ μ _ _ _ _ _
    simp only [bad,Set.setOf_false,measure_empty]
    exact zero_le _
  | @inspect k m r w next ih =>
    intro V hdim μ _ hμ hU horth hP
    have hdE : Module.finrank ℝ (Space d) = d := by simp [Space]
    have hn : n+1 ≤ Module.finrank ℝ Vᗮ := by
      have hh := V.finrank_add_finrank_orthogonal
      omega
    have hh := bounded_query_tail d T k n V hn hδ hR hδR μ hμ hU horth w hP.1
    have ht := ih V hdim μ hμ hU horth hP.2
    change μ ({U | ∃ i : Fin T, k ≤ i.val ∧ δ ≤ |⟪w,U i⟫|} ∪ {U | bad δ next U}) ≤ _
    apply (measure_union_le _ _).trans
    have hsum := add_le_add hh ht
    simpa only [failurePerInspection,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hsum
  | @reveal k m r i hi next ih =>
    intro V hdim μ _ hμ hU horth hP
    let o := revealObservation d T i
    letI : IsProbabilityMeasure (μ.map o) := isProbabilityMeasure_map (reveal_measurable d T i).aemeasurable
    have he := ConditionalSupport.event_disintegration μ o (reveal_measurable d T i)
      {p : Space d × Frame d T | bad δ (next p.1) p.2} hP.1
    change μ {U | bad δ (.reveal i hi next) U} = _ at he
    rw [he]
    calc
      _ ≤ ∫⁻ _y, (m : ℝ≥0∞)*failurePerInspection T n δ R ∂μ.map o := by
        apply lintegral_mono_ae
        filter_upwards [reveal_posterior_invariant d T V μ hμ i,
          ProjectionConcentration.conditioned_orthonormal d T μ hU o (reveal_measurable d T i),
          unseen_after_reveal d T k V μ hU horth i hi] with y hy hyU hyO
        have hdim' : Module.finrank ℝ (V ⊔ Submodule.span ℝ {y} : Submodule ℝ (Space d))+r+(n+1) ≤ d := by
          have hh := ProjectionQuery.finrank_insert_le V y
          omega
        exact ih y _ hdim' (condDistrib id o μ y) hy hyU hyO (hP.2 y)
      _ = _ := by simp

theorem haar_failure_bound (d T M n : ℕ) (hT : T ≤ d)
    (P : Protocol d T 0 M T) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hδR : δ ≤ R)
    (hd : T+(n+1) ≤ d) (hP : Regular δ R P) :
    (HaarFrame.frameLaw d T hT) {U | bad δ P U} ≤
      (M : ℝ≥0∞)*failurePerInspection T n δ R := by
  apply failure_bound P n hδ hR hδR ⊥ (by simpa using hd) (HaarFrame.frameLaw d T hT)
    (frame_law_invariant d T hT ⊥) (ProjectionConcentration.haar_orthonormal_ae d T hT) ?_ hP
  exact Filter.Eventually.of_forall fun U i _ => by simp

end Smoothness2601.DeferredPrefix
