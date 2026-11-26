import Bilevel.CachedOuterGoodEvent
import Bilevel.CachedOuterInitialization
import Bilevel.CappedAccuracy

/-! Adaptive first-failure control for the actual cached outer procedure.
All oracle laws retain full history. The public cap certifies initialization
on every entering trace; cached accuracy is propagated only on the good event. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedOuterProcedure
open Stateful ConditionalConfidence

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] [MeasurableSpace History]
  [FiniteDimensional ℝ Y] [Nontrivial Y] {σf σg μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)

theorem maybeRefresh_failure
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (D rA η Λ cap radius e : ℝ) (hr : 0 < rA) (hη : 0 < η) (hrad : 0 ≤ radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (hinit : ‖yinit-P.canonicalResponse.y (current Λ cap x₀ n s)‖ ≤ D) (h : History) :
    ((maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n).law (s,h)).real
      {z | z.1 ∈ middleBad P Λ cap radius e rA η x₀ n} ≤
        flag (bad P Λ cap e rA η x₀ n) s + 2*Real.exp (-(q:ℝ)/8) := by
  classical
  by_cases href : n = 0 ∨ radius < ‖current Λ cap x₀ n s-s.2.1‖
  · rw [maybeRefresh, Procedure.choose_law]
    simp only [refreshIndex, if_pos href, Nat.one_ne_zero, ite_false]
    have hh := Procedure.map_failure_union_bound
      ((CachedAnchorProcedure.refresh O μ Lg Cf D rA η q).reparam
        (fun s : State X Y => (current Λ cap x₀ n s,yinit))
        ((current_measurable Λ cap x₀ n).prodMk measurable_const))
      (fun z => (z.1.1,(current Λ cap x₀ n z.1,z.2)))
      ((measurable_fst.comp measurable_fst).prodMk
        (((current_measurable Λ cap x₀ n).comp measurable_fst).prodMk measurable_snd)) s h
      (middleBad P Λ cap radius e rA η x₀ n)
      (middleBad_measurable P Λ cap radius e rA η x₀ n)
      {z | ¬ CachedAnchorProcedure.Certificate P (current Λ cap x₀ n s) rA η z}
      (CachedAnchorProcedure.certificate_measurable P _ rA η).compl
      (s ∈ bad P Λ cap e rA η x₀ n) (fun z hz => by
        change s ∈ traceBad P Λ cap e x₀ n ∨
          ¬ CachedAnchorProcedure.Certificate P (current Λ cap x₀ n s) rA η z ∨
          radius < ‖current Λ cap x₀ n s-current Λ cap x₀ n s‖ at hz
        rcases hz with hz | hz | hz
        · exact Or.inl (Or.inl hz)
        · exact Or.inr hz
        · simp only [sub_self,norm_zero] at hz
          exact False.elim (not_lt_of_ge hrad hz))
      (CachedAnchorProcedure.refresh_certificate_probability P O hfx hfy hgy D rA η hr hη q
        (current Λ cap x₀ n s,yinit) hinit h)
    simpa only [flag,Set.indicator_apply] using hh
  · rw [maybeRefresh, Procedure.choose_law]
    simp only [refreshIndex, if_neg href, ite_true]
    rw [← Procedure.failure_integral _ _ _ _ (middleBad_measurable P Λ cap radius e rA η x₀ n),
      Procedure.pure_law]
    have hf : StronglyMeasurable (fun z : Outcome (State X Y) History =>
        flag (middleBad P Λ cap radius e rA η x₀ n) z.1) :=
      ((measurable_const.indicator (middleBad_measurable P Λ cap radius e rA η x₀ n)).comp measurable_fst).stronglyMeasurable
    rw [integral_dirac' _ _ hf]
    have hsub : s ∈ middleBad P Λ cap radius e rA η x₀ n → s ∈ bad P Λ cap e rA η x₀ n := by
      intro hs
      rcases hs with hs | hs | hs
      · exact Or.inl hs
      · exact Or.inr ⟨fun hn => href (Or.inl hn),hs⟩
      · exact False.elim (href (Or.inr hs))
    have hm : flag (middleBad P Λ cap radius e rA η x₀ n) s ≤ flag (bad P Λ cap e rA η x₀ n) s := by
      by_cases hs : s ∈ middleBad P Λ cap radius e rA η x₀ n
      · simp [flag,Set.indicator_apply,hs,hsub hs]
      · simpa only [flag,Set.indicator_of_not_mem hs] using (flag_bounds (bad P Λ cap e rA η x₀ n) s).1
    have he := Real.exp_pos (-(q:ℝ)/8)
    simpa only [id_eq] using hm.trans (by linarith)

omit [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem estimateStep_failure
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    (t D r rA δ η Λ cap radius e : ℝ) (ht : 0 < t) (hr : 0 < r) (hδ : 0 < δ)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (h₀ : ‖yinit-P.canonicalResponse.y (current Λ cap x₀ n s)‖ ≤ D)
    (hₜ : ‖yinit-P.tiltedResponse (current Λ cap x₀ n s) t (Clipping.clip Cf s.2.2.2.2.1)‖ ≤ D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius) + t⁻¹*(2*Lg*r+2*δ) +
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t ≤ e) (h : History) :
    ((estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (s,h)).real
      {z | z.1 ∈ bad P Λ cap e rA η x₀ (n+1)} ≤
        flag (middleBad P Λ cap radius e rA η x₀ n) s + 4*Real.exp (-(q:ℝ)/8) := by
  classical
  by_cases hs : s ∈ middleBad P Λ cap radius e rA η x₀ n
  · have hh := measureReal_mono (μ := (estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (s,h))
      (Set.subset_univ {z | z.1 ∈ bad P Λ cap e rA η x₀ (n+1)})
    rw [measureReal_univ_eq_one] at hh
    simp only [flag,Set.indicator_of_mem hs]
    have he := Real.exp_pos (-(q:ℝ)/8)
    linarith
  · have hh := Procedure.map_failure_union_bound
      ((CachedEstimatorProcedure.estimator O μ Lg t D r δ q).reparam
        (estimatorInput Cf Λ cap x₀ yinit n) (estimatorInput_measurable Cf Λ cap x₀ yinit n))
      (fun z => (put z.1.1 n z.2,z.1.2))
      (((put_measurable n).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst)) s h
      (bad P Λ cap e rA η x₀ (n+1)) (bad_measurable P Λ cap e rA η x₀ (n+1))
      {v | e < ‖v-gradient (P.hyperobjective P.canonicalResponse) (current Λ cap x₀ n s)‖}
      (measurableSet_lt measurable_const (measurable_id.sub_const _).norm) False
      (fun v hv => Or.inr (bad_put_subset P Λ cap radius e rA η x₀ n s hs v hv))
      (CachedEstimatorProcedure.estimator_confidence O P hgy hgx t D r δ ht hr hδ q
        (estimatorInput Cf Λ cap x₀ yinit n s) h₀ hₜ
        (middle_good_cache_error P Λ cap radius e rA η x₀ yinit n s hs) hbudget h)
    simpa only [ite_false,zero_add,flag,Set.indicator_of_not_mem hs] using hh

theorem iteration_failure
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    (t D r rA δ η Λ cap radius e R₀ : ℝ) (ht : 0 < t) (hr : 0 < r) (hrA : 0 < rA)
    (hδ : 0 < δ) (hη : 0 < η) (hΛ : 0 < Λ) (hcap : 0 ≤ cap) (hrad : 0 ≤ radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀)
    (N : ℕ) (hD : R₀+Lg/μ*(Real.sqrt (N*cap)/Λ)+t*Cf/μ ≤ D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius) + t⁻¹*(2*Lg*r+2*δ) +
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t ≤ e)
    (n : ℕ) (hn : n ≤ N) (s : State X Y) (h : History) :
    ((iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h)).real
      {z | z.1 ∈ bad P Λ cap e rA η x₀ (n+1)} ≤
        flag (bad P Λ cap e rA η x₀ n) s + 6*Real.exp (-(q:ℝ)/8) := by
  have hc (v : State X Y) := all_history_initialization P hΛ hcap ht x₀ yinit hinit N hD v n hn
  have hh := Procedure.bind_failure_bound
    (maybeRefresh O μ Lg Cf D rA η Λ cap radius q x₀ yinit n)
    ((estimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).reparam Prod.snd measurable_snd) s h
    (middleBad P Λ cap radius e rA η x₀ n) (middleBad_measurable P Λ cap radius e rA η x₀ n)
    (bad P Λ cap e rA η x₀ (n+1)) (bad_measurable P Λ cap e rA η x₀ (n+1))
    (maybeRefresh_failure P O hfx hfy hgy D rA η Λ cap radius e hrA hη hrad q x₀ yinit n s (hc s).1 h)
    (fun v h' => estimateStep_failure P O hgy hgx t D r rA δ η Λ cap radius e ht hr hδ q
      x₀ yinit n v (hc v).1 (hc v).2 hbudget h')
  exact hh.trans (by ring_nf; rfl)

end Bilevel.CachedOuterProcedure
