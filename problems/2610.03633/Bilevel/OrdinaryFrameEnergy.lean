import Bilevel.OrdinaryFrameProtocol
import Bilevel.TransportObserverGeometry

/-! Actual precoin and terminal-output projection bounds. The terminal
output need not be a previous query or lie in a pre-existing information
space: its own final raw insertion is included in the query budget. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
universe u
namespace Bilevel.OrdinaryFrame
open EuclideanGaussian ProjectionPosterior ProjectionGeometry TransportControllerMachine RawGenieBorel

theorem safe_precoin {d T : ℕ} {H : Memory.{u}} (L : Rules H d T)
    (cap : ℝ) (Q R t : ℕ) (s : State H d T) (U : Frame d T)
    (h : RawGenieProtocol.Safe cap (compile (policy L (Q+1) R t) s.1) s.2.1 s.2.2 U) :
    GenieProtocol.BoundedEnergy (precoin L t s U).2.1 (precoin L t s U).2.2 U cap := by
  cases R with
  | zero => exact RawGenieProtocol.safe_current _ _ _ _ _ h.2.2
  | succ R => exact RawGenieProtocol.safe_current _ _ _ _ _ h.2.2

theorem run_output_mem {d T : ℕ} {H : Memory.{u}} (L : Rules H d T) :
    ∀ Q R t (s : State H d T) (U : Frame d T),
    L.output (run L Q R t s U).1∈(run L Q R t s U).2.1 := by
  classical
  intro Q
  induction Q with
  | zero =>
    intro R t s U
    exact (show Submodule.span ℝ {L.output s.1}≤s.2.1 ⊔ Submodule.span ℝ {L.output s.1}
      from le_sup_right) (Submodule.mem_span_singleton_self _)
  | succ Q ih =>
    intro R t s U
    cases R with
    | zero => exact ih 0 (t+1) (precoin L t s U) U
    | succ R =>
      by_cases h : (precoin L t s U).1∈L.success t
      · simpa only [run,if_pos h] using
          ih R (t+1) (revealStep (L.column t) (L.afterReveal t) (precoin L t s U) U) U
      · simpa only [run,if_neg h] using ih (R+1) (t+1) (precoin L t s U) U

theorem boundedEnergy_inner {d T : ℕ} (V : Submodule ℝ (Space d)) (S : Set (Fin T))
    (U : Frame d T) (cap : ℝ) (hcap : 0≤cap) (hE : GenieProtocol.BoundedEnergy V S U cap)
    (q : Space d) (hq : q∈V) (i : Fin T) (hi : i∉S) :
    |⟪U i,q⟫|≤Real.sqrt cap*‖q‖ := by
  have henergy := hE i hi
  have hn : ‖project V (U i)‖≤Real.sqrt cap := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    simpa only [Real.sq_sqrt hcap,energy] using henergy
  rw [TransportObserver.inner_project_mem V _ q hq]
  exact (abs_real_inner_le_norm _ q).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg q))

theorem terminal_inner_bound {d T : ℕ} {H : Memory.{u}} (L : Rules H d T)
    (cap : ℝ) (hcap : 0≤cap) (Q R t : ℕ) (s : State H d T) (U : Frame d T)
    (h : RawGenieProtocol.Safe cap (compile (policy L Q R t) s.1) s.2.1 s.2.2 U)
    (i : Fin T) (hi : i∉(run L Q R t s U).2.2) :
    |⟪U i,L.output (run L Q R t s U).1⟫|≤Real.sqrt cap*‖L.output (run L Q R t s U).1‖ :=
  boundedEnergy_inner _ _ _ cap hcap (safe_run L cap Q R t s U h) _
    (run_output_mem L Q R t s U) i hi

theorem first_mem_precoin {d T : ℕ} {H : Memory.{u}} (L : Rules H d T)
    (t : ℕ) (s : State H d T) (U : Frame d T) :
    L.first t s.1∈(precoin L t s U).2.1 :=
  (show s.2.1 ⊔ Submodule.span ℝ {L.first t s.1}≤(precoin L t s U).2.1
    from le_sup_left)
      ((show Submodule.span ℝ {L.first t s.1}≤s.2.1 ⊔ Submodule.span ℝ {L.first t s.1}
        from le_sup_right) (Submodule.mem_span_singleton_self _))

theorem second_mem_precoin {d T : ℕ} {H : Memory.{u}} (L : Rules H d T)
    (t : ℕ) (s : State H d T) (U : Frame d T) :
    L.second t (queryStep (L.first t) (L.afterFirst t) s U).1∈(precoin L t s U).2.1 :=
  (show Submodule.span ℝ {L.second t (queryStep (L.first t) (L.afterFirst t) s U).1}≤
    (precoin L t s U).2.1 from le_sup_right) (Submodule.mem_span_singleton_self _)

theorem precoin_inner_bounds {d T : ℕ} {H : Memory.{u}} (L : Rules H d T)
    (cap : ℝ) (hcap : 0≤cap) (Q R t : ℕ) (s : State H d T) (U : Frame d T)
    (h : RawGenieProtocol.Safe cap (compile (policy L (Q+1) R t) s.1) s.2.1 s.2.2 U)
    (i : Fin T) (hi : i∉s.2.2) :
    |⟪U i,L.first t s.1⟫|≤Real.sqrt cap*‖L.first t s.1‖ ∧
    |⟪U i,L.second t (queryStep (L.first t) (L.afterFirst t) s U).1⟫|≤
      Real.sqrt cap*‖L.second t (queryStep (L.first t) (L.afterFirst t) s U).1‖ := by
  have he := safe_precoin L cap Q R t s U h
  exact ⟨boundedEnergy_inner _ _ _ cap hcap he _ (first_mem_precoin L t s U) i hi,
    boundedEnergy_inner _ _ _ cap hcap he _ (second_mem_precoin L t s U) i hi⟩

end Bilevel.OrdinaryFrame
