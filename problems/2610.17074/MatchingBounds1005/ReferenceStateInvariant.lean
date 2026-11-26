import MatchingBounds1005.ReferenceStateFinish
import MatchingBounds1005.ReadoutCalendar

/-! Private-noise independence and exact public-state disclosure updates. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace MatchingBounds1005.ReferenceState
open GaussianVector TensorChannelRows FiniteGaussianSampler

variable {Seed : Type} [MeasurableSpace Seed] {d H N : ℕ}

def zeroNoise (d : ℕ) : (H : ℕ) → Noise d H
  | 0 => ()
  | H + 1 => (zeroNoise d H, 0)

def withNoise (z : Noise (jointDim d) H) (s : State Seed d H N) : State Seed d H N :=
  ((s.1.1, z), s.2)

theorem withNoise_measurable :
    Measurable (fun p : Noise (jointDim d) H × State Seed d H N => withNoise p.1 p.2) :=
  (measurable_snd.fst.fst.prodMk measurable_fst).prodMk measurable_snd.snd

theorem queryPoint_withNoise (A : Model.Algorithm d Seed) (j : ℕ)
    (z : Noise (jointDim d) H) (s : State Seed d H N) :
    queryPoint A j (withNoise z s) = queryPoint A j s := rfl

theorem confinedQuery_withNoise (A : Model.Algorithm d Seed) (R : ℝ) (j : ℕ)
    (z : Noise (jointDim d) H) (s : State Seed d H N) :
    confinedQuery A R j (withNoise z s) = confinedQuery A R j s := rfl

theorem queryInput_withNoise (A : Model.Algorithm d Seed) (τ a σ₃ σ₄ R : ℝ) (j : ℕ)
    (z : Noise (jointDim d) H) (s : State Seed d H N) :
    queryInput A τ a σ₃ σ₄ R j (withNoise z s) = queryInput A τ a σ₃ σ₄ R j s := rfl

theorem finishQuery_withNoise (A : Model.Algorithm d Seed) (constant R η σ₃ σ₄ : ℝ)
    (correction : (Fin N → Vec d) × Vec d → Model.Response d) (j : ℕ)
    (z : Noise (jointDim d) H) (s : State Seed d H N)
    (q : Vec d) (y : Fin (H * (d + d)) → ℝ) :
    finishQuery A constant R η σ₃ σ₄ correction j (withNoise z s, (q, y)) =
      withNoise z (finishQuery A constant R η σ₃ σ₄ correction j (s, (q, y))) := rfl

def revealRows (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (xs : List (Fin N)) (s : State Seed d H N) : State Seed d H N :=
  (s.1, ((VisibleReadouts.reveal b U xs s.2.1.1, s.2.1.2), s.2.2))

theorem revealState_eq (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (xs : List (Fin N)) (s : State Seed d H N) :
    ReadoutCalendar.revealState b (fun i => ⟨setReadout i, setReadout_measurable i⟩)
      U xs s = revealRows b U xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
      rw [ReadoutCalendar.revealState, ih]
      rfl

theorem revealRows_withNoise (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (xs : List (Fin N)) (z : Noise (jointDim d) H) (s : State Seed d H N) :
    revealRows b U xs (withNoise z s) = withNoise z (revealRows b U xs s) := rfl

theorem revealRows_measurable (b : Fin N → Vec d) (U : Vec d →L[ℝ] Vec d)
    (xs : List (Fin N)) : Measurable (revealRows (Seed := Seed) (H := H) b U xs) := by
  have hr : Measurable (fun s : State Seed d H N => VisibleReadouts.reveal b U xs s.2.1.1) := by
    apply measurable_pi_lambda
    intro i
    simp only [VisibleReadouts.reveal_apply]
    split_ifs
    · exact measurable_const
    · exact (measurable_pi_apply i).comp measurable_snd.fst.fst
  exact measurable_fst.prodMk ((hr.prodMk measurable_snd.fst.snd).prodMk measurable_snd.snd)

theorem revealRows_joint_measurable {Rot : Type} [MeasurableSpace Rot]
    (b : Fin N → Vec d) (U : Rot → Vec d →L[ℝ] Vec d)
    (hU : ∀ i, Measurable (fun ρ => U ρ (b i))) (xs : List (Fin N)) :
    Measurable (fun p : Rot × State Seed d H N => revealRows b (U p.1) xs p.2) := by
  have hr : Measurable (fun p : Rot × State Seed d H N =>
      VisibleReadouts.reveal b (U p.1) xs p.2.2.1.1) := by
    apply measurable_pi_lambda
    intro i
    simp only [VisibleReadouts.reveal_apply]
    split_ifs
    · exact (hU i).comp measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd.snd.fst.fst
  exact measurable_snd.fst.prodMk
    ((hr.prodMk measurable_snd.snd.fst.snd).prodMk measurable_snd.snd.snd)

end MatchingBounds1005.ReferenceState
