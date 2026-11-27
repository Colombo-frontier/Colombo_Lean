import UpperGhostMarginal
import UpperOptimizationFresh

/-! The actual marginal in the ghost coupling is the same finite iid recursive
process used by the public algorithm, proved by a pushforward identity. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
namespace Task006.Full

def iidState {T : ℕ} {E B : Type*} (step : E × B → E) (x0 : E) (w : Fin T → B) : ℕ → E
  | 0 => x0
  | n + 1 => if hn : n < T then step (iidState step x0 w n, w ⟨n, hn⟩) else iidState step x0 w n

theorem iidState_measurable {T : ℕ} {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (step : E × B → E) (hstep : Measurable step) (x0 : E) (n : ℕ) :
    Measurable (fun w : Fin T → B => iidState step x0 w n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases hn : n < T
    · simpa only [iidState, dif_pos hn, Function.comp_def] using hstep.comp (ih.prodMk (measurable_pi_apply ⟨n, hn⟩))
    · simpa only [iidState, dif_neg hn] using ih

theorem iidState_past {T : ℕ} {E B : Type*} (step : E × B → E) (x0 : E) (n : ℕ)
    (w w' : Fin T → B) (hh : ∀ j : Fin T, j.val < n → w j = w' j) :
    iidState step x0 w n = iidState step x0 w' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iidState, iidState]
    have hp : ∀ j : Fin T, j.val < n → w j = w' j := fun j hj => hh j (by omega)
    split_ifs with hn
    · rw [ih hp, hh ⟨n, hn⟩ (Nat.lt_succ_self n)]
    · exact ih hp

theorem iidState_map {T : ℕ} {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (step : E × B → E) (hstep : Measurable step)
    (x0 : E) (n : ℕ) (hn : n ≤ T) :
    (Measure.pi (fun _ : Fin T => μ)).map (fun w => iidState step x0 w n) = iidStateLaw μ step x0 n := by
  induction n with
  | zero => simp [iidState, iidStateLaw]
  | succ n ih =>
    have hnT : n < T := by omega
    have hnle : n ≤ T := by omega
    let X := fun w : Fin T → B => iidState step x0 w n
    have hX : Measurable X := iidState_measurable step hstep x0 n
    have hpast : ∀ w w', (∀ j : Fin T, j.val < (⟨n, hnT⟩ : Fin T).val → w j = w' j) → X w = X w' :=
      fun w w' hh => iidState_past step x0 n w w' hh
    have hi := finite_past_indep_current μ ⟨n, hnT⟩ X hX hpast
    have hpair := hi.map_prod_eq_prod_map_map hX.aemeasurable (measurable_pi_apply ⟨n, hnT⟩).aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin T => μ) ⟨n, hnT⟩).map_eq] at hpair
    have hsucc : (fun w : Fin T → B => iidState step x0 w (n + 1)) =
        step ∘ (fun w => (X w, w ⟨n, hnT⟩)) := by
      funext w
      exact dif_pos hnT
    letI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin T => μ)).map X) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    rw [hsucc, ← Measure.map_map hstep (hX.prodMk (measurable_pi_apply ⟨n, hnT⟩)), hpair,
      iidStateLaw, ← ih hnle, iidStepKernel_comp_eq_map_prod μ step hstep]

theorem ghostProcess_actual_iid {T : ℕ} {E B : Type*} [MeasurableSpace E] [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (G : E → Set B)
    (hG : MeasurableSet {p : E × B | p.2 ∈ G p.1})
    (hpos : ∀ x, μ (G x) ≠ 0) (step : E × B → E) (hstep : Measurable step) (x0 : E) :
    (ghostProcessLaw μ G hG hpos step hstep x0 T).map (fun j => j.1.1) =
      (Measure.pi (fun _ : Fin T => μ)).map (fun w => iidState step x0 w T) := by
  rw [ghostProcess_actual_marginal, iidState_map μ step hstep x0 T le_rfl]

#print axioms iidState_map
#print axioms ghostProcess_actual_iid
end Task006.Full
