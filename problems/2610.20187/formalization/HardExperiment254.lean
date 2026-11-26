import ExperimentRisk254
import Problem254

noncomputable section
open scoped BigOperators
namespace Paper254

def coordinatePredictor {d T : ℕ} (A : OnlineLearner (ballDomain d) T)
    (coordinate : Fin T → Fin d) (t : Fin T) (history : Fin t.val → Bool) : ℝ :=
  (A t (fun i => coordinateSquare (coordinate ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩) (history i))).val (coordinate t)

theorem hard_experiment_regret {d T : ℕ} (A : OnlineLearner (ballDomain d) T)
    (coordinate : Fin T → Fin d) (ω : Fin T → Bool) (u : Fin T → (ballDomain d).carrier) :
    regret A (hardSequence (fun t => (coordinate t,ω t))) u =
      ∑ t : Fin T, roundExcess t (coordinatePredictor A coordinate t) ((u t).val (coordinate t)) ω := by
  unfold regret
  apply Finset.sum_congr rfl
  intro t _
  rfl

theorem hard_experiment_lower {κ : Type*} [Fintype κ] [DecidableEq κ] {d T : ℕ}
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin T → κ) (coordinate : Fin T → Fin d)
    (A : OnlineLearner (ballDomain d) T) (u : (κ → Bool) → Fin T → (ballDomain d).carrier)
    (hu : ∀ s t, (u s t).val (coordinate t) = signedMean θ (s (query t)))
    (good : Finset (Fin T))
    (hinfo : ∀ t ∈ good, (∑ i : Fin t.val, if query ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩ = query t then θ^2 else 0) ≤ 1/32) :
    (good.card : ℝ)*θ^2/4 ≤
      finiteExpectation (uniformFinite (κ → Bool)) (fun s =>
        finiteExpectation (productWeights (fun r => signObservation θ hθ s (query r)))
          (fun ω => regret A (hardSequence (fun t => (coordinate t,ω t))) (u s))) := by
  simp_rw [hard_experiment_regret,hu]
  exact experiment_total_lower θ hθ query (coordinatePredictor A coordinate) good hinfo

end Paper254
#print axioms Paper254.hard_experiment_lower
