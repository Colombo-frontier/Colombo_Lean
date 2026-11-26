import Bilevel.OrdinaryFrameDimension

/-! Direct arbitrary-output consequence of the actual ordinary observer.
The output is inserted after all oracle calls and is bounded only by its
public radius, never by membership in a previous query span. -/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
universe u
namespace Bilevel.OrdinaryFrame
open EuclideanGaussian ProjectionPosterior ProjectionGeometry TransportControllerMachine

theorem observed_final {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) (cap : ℝ) :
    ∀ Q R t (s : State H d T) (U : Frame d T),Observed L cap Q R t s U →
      GenieProtocol.BoundedEnergy (run L Q R t s U).2.1 (run L Q R t s U).2.2 U cap := by
  classical
  intro Q
  induction Q with
  | zero => exact fun _ _ _ _ h => h
  | succ Q ih =>
    intro R t s U h
    cases R with
    | zero => exact ih 0 (t+1) _ U h.2
    | succ R =>
      have hn := h.2
      by_cases ha : (precoin L t s U).1∈L.success t
      · rw [if_pos ha] at hn
        simpa only [run,if_pos ha] using ih R (t+1) _ U hn
      · rw [if_neg ha] at hn
        simpa only [run,if_neg ha] using ih (R+1) (t+1) _ U hn

theorem observed_output_bound {d T : ℕ} {H : Memory.{u}} (L : Rules H d T)
    (Q r t : ℕ) (s : State H d T) (U : Frame d T) (R τ : ℝ) (hR : 0<R) (hτ : 0<τ)
    (hgood : Observed L (τ^2/(4*R^2)) Q r t s U)
    (hnorm : ‖L.output (run L Q r t s U).1‖≤R)
    (i : Fin T) (hi : i∉(run L Q r t s U).2.2) :
    |⟪U i,L.output (run L Q r t s U).1⟫|≤τ/2 := by
  have hE := observed_final L _ Q r t s U hgood
  have h := boundedEnergy_inner _ _ U (τ^2/(4*R^2)) (by positivity) hE _
    (run_output_mem L Q r t s U) i hi
  have he : Real.sqrt (τ^2/(4*R^2))*R=τ/2 := by
    rw [Real.sqrt_div (sq_nonneg τ),Real.sqrt_sq_eq_abs,
      show 4*R^2=(2*R)^2 by ring,Real.sqrt_sq_eq_abs,abs_of_pos hτ,
      abs_of_pos (by positivity : 0<2*R)]
    field_simp
    ring
  exact h.trans ((mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)).trans_eq he)

theorem terminal_failure_probability {d T Q : ℕ} {H : Memory.{u}} {C : Type*} [MeasurableSpace C]
    (hT : T≤d) (hTpos : 0<T) (L : Rules H d T)
    (initial : C → H) (hi : Measurable initial) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (t : ℕ) (δ K θ R τ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hK : 1≤K) (hθ : 1≤θ) (hR : 0<R) (hτ : 0<τ)
    (hratio : R^2≤K^2*θ^2*T*τ^2)
    (hD : 128*K^2*(((2*Q+1:ℕ):ℝ)+T)*θ^2*T*
      Real.log (4*((2*Q+1:ℕ):ℝ)*T/δ)≤d)
    (hnorm : ∀ c U,‖L.output (run L Q T t (initial c,(⊥,∅)) U).1‖≤R) :
    (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ∃ i : Fin T,
      i∉(run L Q T t (initial p.1,(⊥,∅)) p.2).2.2 ∧
      τ/2 < |⟪p.2 i,L.output (run L Q T t (initial p.1,(⊥,∅)) p.2).1⟫|}≤ENNReal.ofReal (δ/2) := by
  refine (measure_mono ?_).trans (dimension_observer hT hTpos L initial hi ρ t
    δ K θ R τ hδ hδ1 hK hθ hR hτ hratio hD)
  intro p hp hgood
  obtain ⟨i,hi,hbad⟩ := hp
  exact (not_lt_of_ge (observed_output_bound L Q T t _ _ R τ hR hτ hgood
    (hnorm p.1 p.2) i hi)) hbad

end Bilevel.OrdinaryFrame
