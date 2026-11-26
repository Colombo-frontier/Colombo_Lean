import Bilevel.CachedOuterProbability

/-! Expected stationarity of the actual history-threaded cached procedure,
with a genuinely independent uniform terminal index. -/
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

theorem run_failure_probability
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
    (n : ℕ) (hn : n ≤ N) (h : History) :
    ((run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).law ((),h)).real
      {z | z.1 ∈ bad P Λ cap e rA η x₀ n} ≤ (6*n:ℝ)*Real.exp (-(q:ℝ)/8) := by
  induction n with
  | zero =>
    rw [← Procedure.failure_integral _ _ _ _ (bad_measurable P Λ cap e rA η x₀ 0), run, Procedure.pure_law]
    have hf : StronglyMeasurable (fun z : Outcome (State X Y) History => flag (bad P Λ cap e rA η x₀ 0) z.1) :=
      ((measurable_const.indicator (bad_measurable P Λ cap e rA η x₀ 0)).comp measurable_fst).stronglyMeasurable
    rw [integral_dirac' _ _ hf]
    simp only [flag,Set.indicator_of_not_mem (initial_not_bad P Λ cap e rA η x₀),
      Nat.cast_zero,mul_zero,zero_mul,le_refl]
  | succ n ih =>
    have hh := Procedure.bind_failure_bound
      (run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n)
      ((iteration O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit n).reparam Prod.snd measurable_snd)
      () h (bad P Λ cap e rA η x₀ n) (bad_measurable P Λ cap e rA η x₀ n)
      (bad P Λ cap e rA η x₀ (n+1)) (bad_measurable P Λ cap e rA η x₀ (n+1))
      (ih (by omega)) (fun s h' => iteration_failure P O hfx hfy hgy hgx
        t D r rA δ η Λ cap radius e R₀ ht hr hrA hδ hη hΛ hcap hrad q x₀ yinit hinit N hD hbudget
        n (by omega) s h')
    exact hh.trans (by push_cast; ring_nf; rfl)

theorem capped_bad_probability
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    (t D r rA δ η Λ cap radius ε R₀ : ℝ) (ht : 0 < t) (hr : 0 < r) (hrA : 0 < rA)
    (hδ : 0 < δ) (hη : 0 < η) (hΛ : 0 < Λ) (hcap : 0 ≤ cap) (hrad : 0 ≤ radius)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀)
    (N : ℕ) (hD : R₀+Lg/μ*(Real.sqrt (N*cap)/Λ)+t*Cf/μ ≤ D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius) + t⁻¹*(2*Lg*r+2*δ) +
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t ≤ ε/8) (h : History) :
    ((run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit N).law ((),h)).real
      (CappedAccuracy.bad Λ cap ε (gradient (P.hyperobjective P.canonicalResponse)) x₀
        (fun i z => z.1.1 i) N) ≤ (6*N:ℝ)*Real.exp (-(q:ℝ)/8) := by
  apply (measureReal_mono (μ := (run O μ Lg Cf t D r rA δ η Λ cap radius q x₀ yinit N).law ((),h))
    (s₂ := {z | z.1 ∈ bad P Λ cap (ε/8) rA η x₀ N}) ?_).trans
      (run_failure_probability P O hfx hfy hgy hgx t D r rA δ η Λ cap radius (ε/8) R₀
        ht hr hrA hδ hη hΛ hcap hrad q x₀ yinit hinit N hD hbudget N (le_refl N) h)
  rintro z ⟨i,hi,_,he⟩
  exact Or.inl ⟨i,hi,he⟩

set_option maxHeartbeats 1200000 in
theorem expected_gradient_norm
    (hfx : ∀ x y, O.upper.truth_x (x,y) = P.fx x y)
    (hfy : ∀ x y, O.upper.truth_y (x,y) = P.fy x y)
    (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    (t D r rA δ η Λ radius ε Δ lower R₀ β : ℝ) (ht : 0 < t) (hr : 0 < r) (hrA : 0 < rA)
    (hδ : 0 < δ) (hη : 0 < η) (hΛ : 0 < Λ) (hrad : 0 ≤ radius) (hε : 0 < ε) (hΔ : 0 ≤ Δ)
    (hlip : ∀ x y, ‖gradient (P.hyperobjective P.canonicalResponse) x-
      gradient (P.hyperobjective P.canonicalResponse) y‖ ≤ Λ*‖x-y‖)
    (hlower : ∀ x, lower ≤ P.hyperobjective P.canonicalResponse x)
    (q : ℕ) [NeZero q] (x₀ : X) (yinit : Y) (hgap : P.hyperobjective P.canonicalResponse x₀-lower ≤ Δ)
    (hinit : ‖yinit-P.canonicalResponse.y x₀‖ ≤ R₀)
    (N : ℕ) [NeZero N] (hN : 32*Λ*Δ ≤ N*ε^2)
    (hD : R₀+Lg/μ*(Real.sqrt (N*(16*Λ*Δ+N*ε^2))/Λ)+t*Cf/μ ≤ D)
    (hbudget : (1+Lg/μ)*(η+Lf*rA+Lf*(1+Lg/μ)*radius) + t⁻¹*(2*Lg*r+2*δ) +
      ((1+Lg/μ)*ρ*Cf^2/(2*μ^2))*t ≤ ε/8)
    (hprob : (6*N:ℝ)*Real.exp (-(q:ℝ)/8) ≤ β)
    (hfail : β*(Real.sqrt (2*Λ*Δ)+Real.sqrt (N*(16*Λ*Δ+N*ε^2))) ≤ ε/2) (h : History) :
    let ν := (run O μ Lg Cf t D r rA δ η Λ (16*Λ*Δ+N*ε^2) radius q x₀ yinit N).law ((),h)
    Integrable (fun z : Fin N × Outcome (State X Y) History =>
      ‖gradient (P.hyperobjective P.canonicalResponse)
        (CappedExecution.output Λ (16*Λ*Δ+N*ε^2) x₀ z.2.1.1 N z.1)‖)
      (StochasticOuter.outputLaw N ν) ∧
    (∫ z : Fin N × Outcome (State X Y) History,
      ‖gradient (P.hyperobjective P.canonicalResponse)
        (CappedExecution.output Λ (16*Λ*Δ+N*ε^2) x₀ z.2.1.1 N z.1)‖
      ∂StochasticOuter.outputLaw N ν) ≤ ε := by
  have hgrad (x : X) : HasGradientAt (P.hyperobjective P.canonicalResponse)
      (gradient (P.hyperobjective P.canonicalResponse) x) x := by
    rw [P.gradient_hyperobjective P.canonicalResponse x]
    exact P.hasGradient_hyperobjective P.canonicalResponse x
  have hp := capped_bad_probability P O hfx hfy hgy hgx t D r rA δ η Λ (16*Λ*Δ+N*ε^2)
    radius ε R₀ ht hr hrA hδ hη hΛ (by positivity) hrad q x₀ yinit hinit N hD hbudget h
  exact CappedAccuracy.expected_gradient_norm
    (ν := (run O μ Lg Cf t D r rA δ η Λ (16*Λ*Δ+N*ε^2) radius q x₀ yinit N).law ((),h))
    (P.hyperobjective P.canonicalResponse)
    (gradient (P.hyperobjective P.canonicalResponse)) hΛ hΔ hε hgrad hlip hlower x₀ hgap
    (fun i z => z.1.1 i) (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
    N hN (hp.trans hprob) hfail

end Bilevel.CachedOuterProcedure
