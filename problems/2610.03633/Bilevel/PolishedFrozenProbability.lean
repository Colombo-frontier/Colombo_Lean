import Bilevel.PolishedFrozenProcedure
import Bilevel.CachedOuterProbability

/-! Conditional accuracy of the literal reused-anchor estimator. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace Bilevel.PolishedFrozenProcedure
open Stateful CachedOuterProcedure ConditionalConfidence
variable {X Y : Type} {History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] [MeasurableSpace History]
  [FiniteDimensional ℝ Y] [Nontrivial Y] {σf σg μ Lf Lg Cf ρ : ℝ}
  (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
  (O : HistorySFO (Query:=X × Y) (History:=History) (X:=X) (Y:=Y) σf σg)

omit [MeasurableSpace (PrimitiveGeometry.Joint X Y)] [BorelSpace (PrimitiveGeometry.Joint X Y)]
  [SecondCountableTopology (PrimitiveGeometry.Joint X Y)] in
theorem reuseEstimateStep_failure
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    (t D r rA δ η Λ cap radius e : ℝ) (ht : 0<t) (hr : 0<r) (hrA : rA≤r)
    (hδ : 0<δ) (hrad : 0≤radius) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (hT : ‖yinit-P.tiltedResponse (current Λ cap x₀ n s) t (Clipping.clip Cf s.2.2.2.2.1)‖≤D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius)+t⁻¹*(2*Lg*r+2*δ)+
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t≤e) (h : History) :
    ((reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (s,h)).real
      {z | z.1∈CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)}≤
      flag (middleBad P Λ cap 0 e rA η x₀ n) s+3*Real.exp (-(q:ℝ)/8) := by
  classical
  by_cases hs : s∈middleBad P Λ cap 0 e rA η x₀ n
  · have hp := measureReal_mono (μ:=(reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).law (s,h))
      (Set.subset_univ {z | z.1∈CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)})
    rw [measureReal_univ_eq_one] at hp
    simp only [flag,Set.indicator_of_mem hs]
    exact hp.trans (by have he := Real.exp_pos (-(q:ℝ)/8);linarith)
  · have hs0 : s∉traceBad P Λ cap e x₀ n ∧
        CachedAnchorProcedure.Certificate P s.2.1 rA η s.2.2 ∧
        ‖current Λ cap x₀ n s-s.2.1‖≤0 := by
      simpa only [middleBad,Set.mem_setOf_eq,not_or,not_not,not_lt] using hs
    have hx : current Λ cap x₀ n s=s.2.1 :=
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hs0.2.2 (norm_nonneg _)))
    have hsR : s∉middleBad P Λ cap radius e rA η x₀ n := by
      simp only [middleBad,Set.mem_setOf_eq,not_or,not_not,not_lt]
      exact ⟨hs0.1,hs0.2.1,hs0.2.2.trans hrad⟩
    have hy : ‖s.2.2.1-P.canonicalResponse.y (current Λ cap x₀ n s)‖≤r := by
      rw [hx]
      exact hs0.2.1.1.trans hrA
    have hh := Procedure.map_failure_union_bound
      ((reuseEstimator O μ Lg t D r δ q).reparam
        (fun s : State X Y => (estimatorInput Cf Λ cap x₀ yinit n s,s.2.2.1))
        ((estimatorInput_measurable Cf Λ cap x₀ yinit n).prodMk (by fun_prop)))
      (fun z => (put z.1.1 n z.2,z.1.2))
      (((put_measurable n).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        (measurable_snd.comp measurable_fst)) s h
      (CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)) (bad_measurable P Λ cap e rA η x₀ (n+1))
      {v | e<‖v-gradient (P.hyperobjective P.canonicalResponse) (current Λ cap x₀ n s)‖}
      (measurableSet_lt measurable_const (measurable_id.sub_const _).norm) False
      (fun v hv => Or.inr (bad_put_subset P Λ cap radius e rA η x₀ n s hsR v hv))
      (reuseEstimator_confidence O P hgy hgx t D r δ ht hr hδ q
        (estimatorInput Cf Λ cap x₀ yinit n s,s.2.2.1) hy hT
        (middle_good_cache_error P Λ cap radius e rA η x₀ yinit n s hsR) hbudget h)
    simpa only [reuseEstimateStep,ite_false,zero_add,flag,Set.indicator_of_not_mem hs] using hh

theorem refreshIteration_failure
    (hfx : ∀ x y,O.upper.truth_x (x,y)=P.fx x y)
    (hfy : ∀ x y,O.upper.truth_y (x,y)=P.fy x y)
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    (t D r rA δ η Λ cap radius e : ℝ) (ht : 0<t) (hr : 0<r) (hrA : 0<rA) (hrAr : rA≤r)
    (hδ : 0<δ) (hη : 0<η) (hrad : 0≤radius) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (href : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖)
    (h0 : ‖yinit-P.canonicalResponse.y (current Λ cap x₀ n s)‖≤D)
    (hT : ∀ v : State X Y,‖yinit-P.tiltedResponse (current Λ cap x₀ n v) t (Clipping.clip Cf v.2.2.2.2.1)‖≤D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius)+t⁻¹*(2*Lg*r+2*δ)+
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t≤e) (h : History) :
    ((refreshIteration O μ Lg Cf t D r rA δ η Λ cap q x₀ yinit n).law (s,h)).real
      {z | z.1∈CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)}≤
      flag (CachedOuterProcedure.bad P Λ cap e rA η x₀ n) s+5*Real.exp (-(q:ℝ)/8) := by
  have href0 : n=0 ∨ 0<‖current Λ cap x₀ n s-s.2.1‖ := by
    rcases href with hn|hd
    · exact Or.inl hn
    · exact Or.inr (hrad.trans_lt hd)
  have hfresh := CachedOuterProcedure.maybeRefresh_failure P O hfx hfy hgy D rA η Λ cap 0 e
    hrA hη (by norm_num) q x₀ yinit n s h0 h
  rw [CachedOuterProcedure.maybeRefresh,Procedure.choose_law] at hfresh
  simp only [refreshIndex,if_pos href0,Nat.one_ne_zero,ite_false] at hfresh
  have hh := Procedure.bind_failure_bound
    (CachedOuterProcedure.refreshAt O μ Lg Cf D rA η Λ cap q x₀ yinit n)
    ((reuseEstimateStep O μ Lg Cf t D r δ Λ cap q x₀ yinit n).reparam Prod.snd measurable_snd)
    s h (middleBad P Λ cap 0 e rA η x₀ n) (middleBad_measurable P Λ cap 0 e rA η x₀ n)
    (CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)) (bad_measurable P Λ cap e rA η x₀ (n+1))
    hfresh (fun v h' => reuseEstimateStep_failure P O hgy hgx t D r rA δ η Λ cap radius e ht hr hrAr hδ hrad
      q x₀ yinit n v (hT v) hbudget h')
  exact hh.trans (by ring_nf;rfl)

end Bilevel.PolishedFrozenProcedure
