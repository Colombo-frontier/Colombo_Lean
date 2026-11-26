import SecondOrder.FiniteObservableMean

open scoped Classical

namespace SecondOrder
noncomputable section
variable {A : Type} [Fintype A] {B : Type*}

/-- A deterministic state machine driven by a finite coefficient history. -/
def finiteStateRun (b₀ : B) (U : ℕ → B → A → B) : (n : ℕ) → FiniteHistory Unit A n → B
  | 0, _ => b₀
  | n+1, h => U n (finiteStateRun b₀ U n h.1) h.2

def finiteStateTransition (b₀ : B) (U : ℕ → B → A → B) (K : ℕ → B → PMF A)
    (n : ℕ) (h : FiniteHistory Unit A n) : PMF A := K n (finiteStateRun b₀ U n h)

def finiteStateSamplingLaw (b₀ : B) (U : ℕ → B → A → B) (K : ℕ → B → PMF A) (n : ℕ) :=
  finiteAdaptiveLaw (PMF.pure ()) (finiteStateTransition b₀ U K) n

/-- One-step equality of observable transition laws propagates through the
entire adaptive execution. The state can itself retain the full transcript. -/
theorem finiteStateSamplingLaw_transport (b₀ : B) (U : ℕ → B → A → B)
    (K L : ℕ → B → PMF A)
    (hstep : ∀ n b (F : B → ℝ), pmfMean (K n b) (fun a => F (U n b a))=
      pmfMean (L n b) (fun a => F (U n b a))) :
    ∀ n (F : B → ℝ), pmfMean (finiteStateSamplingLaw b₀ U K n) (fun h => F (finiteStateRun b₀ U n h))=
      pmfMean (finiteStateSamplingLaw b₀ U L n) (fun h => F (finiteStateRun b₀ U n h)) := by
  intro n
  induction n with
  | zero => intro F; rfl
  | succ n ih =>
    intro F
    change pmfMean (finiteConditionalPMF _ _) (fun h => F (U n (finiteStateRun b₀ U n h.1) h.2))=
      pmfMean (finiteConditionalPMF _ _) (fun h => F (U n (finiteStateRun b₀ U n h.1) h.2))
    rw [finiteConditionalPMF_mean, finiteConditionalPMF_mean]
    change pmfMean (finiteStateSamplingLaw b₀ U K n)
      (fun h => pmfMean (K n (finiteStateRun b₀ U n h)) (fun a => F (U n (finiteStateRun b₀ U n h) a)))=
      pmfMean (finiteStateSamplingLaw b₀ U L n)
        (fun h => pmfMean (L n (finiteStateRun b₀ U n h)) (fun a => F (U n (finiteStateRun b₀ U n h) a)))
    simp_rw [hstep n _ F]
    exact ih (fun b => pmfMean (L n b) (fun a => F (U n b a)))

end
end SecondOrder
