import Bilevel.PolishedFrozenProbability

/-! Five-operation first-failure control with immediate absorbing abort. -/
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

theorem liveIteration_failure
    (hfx : ∀ x y,O.upper.truth_x (x,y)=P.fx x y)
    (hfy : ∀ x y,O.upper.truth_y (x,y)=P.fy x y)
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    (t D r rA δ η Λ cap radius e : ℝ) (ht : 0<t) (hr : 0<r) (hrA : 0<rA) (hrAr : rA≤r)
    (hδ : 0<δ) (hη : 0<η) (hrad : 0≤radius) (q : ℕ) [NeZero q]
    (x₀ : X) (yinit : Y) (n : ℕ) (s : State X Y)
    (h0 : ∀ v : State X Y,‖yinit-P.canonicalResponse.y (current Λ cap x₀ n v)‖≤D)
    (hT : ∀ v : State X Y,‖yinit-P.tiltedResponse (current Λ cap x₀ n v) t (Clipping.clip Cf v.2.2.2.2.1)‖≤D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius)+t⁻¹*(2*Lg*r+2*δ)+
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t≤e) (h : History) :
    ((liveIteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h)).real
      {z | z.1∈CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)}≤
      flag (CachedOuterProcedure.bad P Λ cap e rA η x₀ n) s+5*Real.exp (-(q:ℝ)/8) := by
  classical
  by_cases href : n=0 ∨ radius<‖current Λ cap x₀ n s-s.2.1‖
  · rw [liveIteration,Procedure.choose_law]
    simp only [refreshIndex,if_pos href,Nat.one_ne_zero,ite_false]
    exact refreshIteration_failure P O hfx hfy hgy hgx t D r rA δ η Λ cap radius e ht hr hrA hrAr hδ hη hrad
      q x₀ yinit n s href (h0 s) hT hbudget h
  · rw [liveIteration,Procedure.choose_law]
    simp only [refreshIndex,if_neg href,ite_true]
    have he := CachedOuterProcedure.estimateStep_failure P O hgy hgx t D r rA δ η Λ cap radius e ht hr hδ
      q x₀ yinit n s (h0 s) (hT s) hbudget h
    have hsub : s∈middleBad P Λ cap radius e rA η x₀ n → s∈CachedOuterProcedure.bad P Λ cap e rA η x₀ n := by
      rintro (hb|hc|hd)
      · exact Or.inl hb
      · exact Or.inr ⟨fun hn => href (Or.inl hn),hc⟩
      · exact False.elim (href (Or.inr hd))
    have hf : flag (middleBad P Λ cap radius e rA η x₀ n) s≤
        flag (CachedOuterProcedure.bad P Λ cap e rA η x₀ n) s := by
      by_cases hs : s∈middleBad P Λ cap radius e rA η x₀ n
      · simp only [flag,Set.indicator_of_mem hs,Set.indicator_of_mem (hsub hs),le_refl]
      · simpa only [flag,Set.indicator_of_not_mem hs] using (flag_bounds (CachedOuterProcedure.bad P Λ cap e rA η x₀ n) s).1
    exact he.trans (by have hp := Real.exp_pos (-(q:ℝ)/8);linarith)

theorem iteration_failure
    (hfx : ∀ x y,O.upper.truth_x (x,y)=P.fx x y)
    (hfy : ∀ x y,O.upper.truth_y (x,y)=P.fy x y)
    (hgy : ∀ x y,O.lower.truth_y (x,y)=P.gy x y)
    (hgx : ∀ x y,O.lower.truth_x (x,y)=P.gx x y)
    (t D r rA δ η Λ cap radius e R₀ : ℝ) (ht : 0<t) (hr : 0<r) (hrA : 0<rA) (hrAr : rA≤r)
    (hδ : 0<δ) (hη : 0<η) (hΛ : 0<Λ) (hcap : 0≤cap) (hrad : 0≤radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (hinit : ‖yinit-P.canonicalResponse.y x₀‖≤R₀)
    (N : ℕ) (hD : R₀+Lg/μ*(Real.sqrt (N*cap)/Λ)+t*Cf/μ≤D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius)+t⁻¹*(2*Lg*r+2*δ)+
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t≤e)
    (n : ℕ) (hn : n≤N) (s : State X Y) (h : History) :
    ((iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h)).real
      {z | z.1∈liveBad P Λ cap e rA η x₀ (n+1)}≤
      flag (liveBad P Λ cap e rA η x₀ n) s+5*Real.exp (-(q:ℝ)/8) := by
  classical
  by_cases hstop : (CappedExecution.run Λ cap x₀ s.1 n).stopped=true
  · rw [iteration,Procedure.choose_law]
    simp only [PolishedFrozenCode.liveIndex,hstop,ite_true]
    rw [←Procedure.failure_integral _ _ _ _ (liveBad_measurable P Λ cap e rA η x₀ (n+1)),Procedure.pure_law]
    have hf : StronglyMeasurable (fun z : Outcome (State X Y) History => flag (liveBad P Λ cap e rA η x₀ (n+1)) z.1) :=
      ((measurable_const.indicator (liveBad_measurable P Λ cap e rA η x₀ (n+1))).comp measurable_fst).stronglyMeasurable
    rw [integral_dirac' _ _ hf]
    have hi : flag (liveBad P Λ cap e rA η x₀ (n+1)) s=flag (liveBad P Λ cap e rA η x₀ n) s := by
      have hb := liveBad_halted_succ P Λ cap e rA η x₀ n s hstop
      simp only [flag,Set.indicator_apply,hb]
    change flag (liveBad P Λ cap e rA η x₀ (n+1)) s≤_
    rw [hi]
    have hp := Real.exp_pos (-(q:ℝ)/8)
    linarith
  · have hlive : (CappedExecution.run Λ cap x₀ s.1 n).stopped=false := Bool.eq_false_of_not_eq_true hstop
    rw [iteration,Procedure.choose_law]
    simp only [PolishedFrozenCode.liveIndex,hstop,ite_false,Nat.one_ne_zero]
    have hc (v : State X Y) := all_history_initialization P hΛ hcap ht x₀ yinit hinit N hD v n hn
    have hh := liveIteration_failure P O hfx hfy hgy hgx t D r rA δ η Λ cap radius e
      ht hr hrA hrAr hδ hη hrad q x₀ yinit n s (fun v => (hc v).1) (fun v => (hc v).2) hbudget h
    have hmono := measureReal_mono (μ:=(liveIteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law (s,h))
      (show {z : Outcome (State X Y) History | z.1∈liveBad P Λ cap e rA η x₀ (n+1)}⊆
        {z | z.1∈CachedOuterProcedure.bad P Λ cap e rA η x₀ (n+1)} from
        fun z hz => liveBad_subset_bad P Λ cap e rA η x₀ (n+1) hz)
    have hi : flag (CachedOuterProcedure.bad P Λ cap e rA η x₀ n) s=flag (liveBad P Λ cap e rA η x₀ n) s := by
      have hb := liveBad_iff_bad_of_live P Λ cap e rA η x₀ n s hlive
      simp only [flag,Set.indicator_apply,←hb]
    exact hmono.trans (by simpa only [hi] using hh)

end Bilevel.PolishedFrozenProcedure
