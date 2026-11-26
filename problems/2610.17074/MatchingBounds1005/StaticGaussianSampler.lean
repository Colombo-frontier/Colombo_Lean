import MatchingBounds1005.CensoredGaussianProcess

/-! Actual static-parameter execution of an adaptive finite row protocol. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.StaticGaussianSampler
open GaussianVector GaussianFitter SequentialPosterior ShiftedSequential CensoredGaussianProcess

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def run (rows : (n : ℕ) → History Ω T n → Fin T → Vec d)
    (ω : Ω) (x : Vec d) : (n : ℕ) → History Ω T n
  | 0 => ω
  | n + 1 => (run rows ω x n, rowResponse (rows n (run rows ω x n)) x)

theorem run_measurable (A : RowProtocol Ω d T) (n : ℕ) :
    Measurable (fun p : Ω × Vec d => run A.rows p.1 p.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact ih.prodMk ((PosteriorGaussian.measurable_rowResponse_family (A.rows n)
        (A.measurable_rows n)).comp (ih.prodMk measurable_snd))

theorem initialSeed_run (rows : (n : ℕ) → History Ω T n → Fin T → Vec d)
    (ω : Ω) (x : Vec d) (n : ℕ) : initialSeed n (run rows ω x n) = ω := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

def sample (A : ShiftedProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (p : Ω × Vec d) : History Ω T n × Vec d :=
  (run A.rowProtocol.rows p.1 (A.signal p.1 + σ • p.2) n, A.signal p.1 + σ • p.2)

theorem sample_measurable (A : ShiftedProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Measurable (sample A σ n) := by
  have hx : Measurable (fun p : Ω × Vec d => A.signal p.1 + σ • p.2) :=
    (A.measurable_signal.comp measurable_fst).add (measurable_const.smul measurable_snd)
  exact ((run_measurable A.rowProtocol n).comp (measurable_fst.prodMk hx)).prodMk hx

theorem sample_law (A : ShiftedProtocol Ω d T) (σ : ℝ) (ν : Measure Ω) (n : ℕ) :
    (ν.prod (standardGaussian d)).map (sample A σ n) = ShiftedSequential.staticJointLaw A σ ν n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ShiftedSequential.staticJointLaw, ← ih, Measure.map_map (measurable_staticUpdate A.rowProtocol n)
        (sample_measurable A σ n)]
      rfl

theorem trueLaw_sample (A : CensoredProtocol Ω d T) (σ : ℝ)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) :
    (ν.prod (standardGaussian d)).map
      (fun p => run A.original.rowProtocol.rows p.1 (A.original.signal p.1 + σ • p.2) n) =
        trueLaw A σ ν n := by
  rw [trueLaw_eq_static, ← sample_law,
    Measure.map_map measurable_fst (sample_measurable A.original σ n)]
  rfl

end MatchingBounds1005.StaticGaussianSampler
