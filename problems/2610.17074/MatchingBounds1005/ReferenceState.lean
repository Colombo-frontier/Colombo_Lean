import MatchingBounds1005.VisibleReadouts
import MatchingBounds1005.GaussianNoiseStream
import MatchingBounds1005.GaussianReferenceCommand
import MatchingBounds1005.OracleReconstruction

/-!
# Concrete accessible state of the two-channel reference experiment

The state contains only the private algorithm/Gaussian seeds, disclosed
physical readouts and linear coefficient, past assembled oracle answers,
and finite measurement rows with their raw answers. There is no rotation
field. All update functions are actual measurable calculations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ContDiff

namespace MatchingBounds1005.ReferenceState
open GaussianVector TensorChannelRows GaussianNoiseStream FiniteGaussianSampler
open ReferenceTransition
open TensorGeometry hiding Vec

abbrev PublicData (d N : ℕ) := (Fin N → Vec d) × Vec d
abbrev Memory (d H : ℕ) := (ℕ → Model.Response d) ×
  ((Fin (H * (d + d)) → Vec (jointDim d)) × (Fin (H * (d + d)) → ℝ))
abbrev State (Seed : Type) (d H N : ℕ) :=
  (Seed × Noise (jointDim d) H) × (PublicData d N × Memory d H)

variable {Seed : Type} [MeasurableSpace Seed] {d H N : ℕ}

def initial (p : Seed × Noise (jointDim d) H) : State Seed d H N := (p, ((0, 0), (0, (0, 0))))

theorem initial_measurable : Measurable (initial (Seed := Seed) (d := d) (H := H) (N := N)) :=
  measurable_id.prodMk measurable_const

def setReadout (i : Fin N) (p : State Seed d H N × Vec d) : State Seed d H N :=
  (p.1.1, ((Function.update p.1.2.1.1 i p.2, p.1.2.1.2), p.1.2.2))

theorem setReadout_measurable (i : Fin N) : Measurable (setReadout (Seed := Seed) (d := d) (H := H) i) := by
  have hb : Measurable (fun p : State Seed d H N × Vec d => Function.update p.1.2.1.1 i p.2) :=
    (VisibleReadouts.update_measurable i).comp
      ((measurable_fst.snd.fst.fst).prodMk measurable_snd)
  exact measurable_fst.fst.prodMk ((hb.prodMk measurable_fst.snd.fst.snd).prodMk measurable_fst.snd.snd)

def setLinear (p : State Seed d H N × Vec d) : State Seed d H N :=
  (p.1.1, ((p.1.2.1.1, p.2), p.1.2.2))

theorem setLinear_measurable : Measurable (setLinear (Seed := Seed) (d := d) (H := H) (N := N)) :=
  measurable_fst.fst.prodMk ((measurable_fst.snd.fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd.snd)

def algorithmInput (j : ℕ) (s : State Seed d H N) : Seed × (Fin j → Model.Response d) :=
  (s.1.1, fun i => s.2.2.1 i.val)

theorem algorithmInput_measurable (j : ℕ) :
    Measurable (algorithmInput (Seed := Seed) (d := d) (H := H) (N := N) j) := by
  apply measurable_fst.fst.prodMk
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply i.val).comp measurable_snd.snd.fst

def queryPoint (A : Model.Algorithm d Seed) (j : ℕ) (s : State Seed d H N) : Vec d :=
  A.query j s.1.1 (fun i => s.2.2.1 i.val)

theorem queryPoint_measurable (A : Model.Algorithm d Seed) (j : ℕ) :
    Measurable (queryPoint (H := H) (N := N) A j) :=
  (A.query_measurable j).comp (algorithmInput_measurable j)

def confinedQuery (A : Model.Algorithm d Seed) (R : ℝ) (j : ℕ) (s : State Seed d H N) : Vec d :=
  radial R (queryPoint A j s)

theorem confinedQuery_measurable (A : Model.Algorithm d Seed) (R : ℝ) (j : ℕ) :
    Measurable (confinedQuery (H := H) (N := N) A R j) :=
  ((radial_contDiff (E := Vec d) R ∞).continuous.measurable).comp (queryPoint_measurable A j)

def insertRows (j : ℕ) (new : Fin (d + d) → Vec (jointDim d))
    (old : Fin (H * (d + d)) → Vec (jointDim d)) : Fin (H * (d + d)) → Vec (jointDim d) :=
  fun i => if (AccumulatedRows.slot i).val = j then new (AccumulatedRows.coordinate i) else old i

def queryRows (A : Model.Algorithm d Seed) (σ₃ σ₄ R : ℝ) (j : ℕ) (s : State Seed d H N) :
    Fin (H * (d + d)) → Vec (jointDim d) :=
  insertRows j (jointRows σ₃ σ₄ (confinedQuery A R j s)) s.2.2.2.1

theorem queryRows_measurable (A : Model.Algorithm d Seed) (σ₃ σ₄ R : ℝ) (j : ℕ) :
    Measurable (queryRows (H := H) (N := N) A σ₃ σ₄ R j) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : (AccumulatedRows.slot i).val = j
  · simpa only [queryRows, insertRows, if_pos hi] using
      (jointRows_measurable σ₃ σ₄ (AccumulatedRows.coordinate i)).comp (confinedQuery_measurable A R j)
  · simpa only [queryRows, insertRows, if_neg hi] using
      (measurable_pi_apply i).comp (measurable_snd.snd.snd.fst :
        Measurable (fun s : State Seed d H N => s.2.2.2.1))

def visibleSignal (τ a σ₃ σ₄ : ℝ) (s : State Seed d H N) : Vec (jointDim d) :=
  normalizedSignal σ₃ σ₄
    (tensorCoordinates d 3 (cubicSignal τ a s.2.1.1))
    (tensorCoordinates d 4 (quarticSignal τ a s.2.1.1))

theorem visibleSignal_measurable (τ a σ₃ σ₄ : ℝ) :
    Measurable (visibleSignal (Seed := Seed) (d := d) (H := H) (N := N) τ a σ₃ σ₄) := by
  have h3 : Measurable (fun s : State Seed d H N => tensorCoordinates d 3 (cubicSignal τ a s.2.1.1)) :=
    (tensorCoordinates d 3).continuous.measurable.comp
      ((VisibleReadouts.signal_measurable 3 (-120 * τ * a ^ 3)).comp measurable_snd.fst.fst)
  have h4 : Measurable (fun s : State Seed d H N => tensorCoordinates d 4 (quarticSignal τ a s.2.1.1)) :=
    (tensorCoordinates d 4).continuous.measurable.comp
      ((VisibleReadouts.signal_measurable 4 (120 * τ * a ^ 4)).comp measurable_snd.fst.fst)
  exact TensorAdaptiveRows.normalizedSignal_measurable σ₃ σ₄ _ _ h3 h4

def queryInput (A : Model.Algorithm d Seed) (τ a σ₃ σ₄ R : ℝ) (j : ℕ) (s : State Seed d H N) :
    Input (jointDim d) (H * (d + d)) :=
  ((s.2.2.2.1, s.2.2.2.2), (queryRows A σ₃ σ₄ R j s, visibleSignal τ a σ₃ σ₄ s))

theorem queryInput_measurable (A : Model.Algorithm d Seed) (τ a σ₃ σ₄ R : ℝ) (j : ℕ) :
    Measurable (queryInput (H := H) (N := N) A τ a σ₃ σ₄ R j) :=
  measurable_snd.snd.snd.prodMk
    ((queryRows_measurable A σ₃ σ₄ R j).prodMk (visibleSignal_measurable τ a σ₃ σ₄))

def privateNoise (j : ℕ) (s : State Seed d H N) : Vec (jointDim d) := noiseAt H s.1.2 j

theorem privateNoise_measurable (j : ℕ) :
    Measurable (privateNoise (Seed := Seed) (d := d) (H := H) (N := N) j) :=
  (noiseAt_measurable _ _ _).comp measurable_fst.snd

end MatchingBounds1005.ReferenceState
