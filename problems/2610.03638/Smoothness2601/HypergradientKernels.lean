import Smoothness2601.HypergradientGeometry
import Smoothness2601.AdjointSolve

/-! The final full-gradient direction estimate, executed with fresh serial
node/upper samples, and its source conditional expected error. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful
namespace Smoothness2601.HypergradientKernels
open AdjointGeometry HypergradientGeometry

theorem norm_center_shift {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {ν : Measure Ω} [IsProbabilityMeasure ν] (f : Ω → E) (center target : E)
    (hf : AEStronglyMeasurable f ν) (hi : Integrable (fun z => ‖f z-center‖) ν) :
    Integrable (fun z => ‖f z-target‖) ν ∧
    (∫ z, ‖f z-target‖ ∂ν) ≤ (∫ z, ‖f z-center‖ ∂ν)+‖center-target‖ := by
  have hp (z : Ω) := norm_sub_le_norm_sub_add_norm_sub (f z) center target
  have hm : AEStronglyMeasurable (fun z => ‖f z-target‖) ν := (hf.sub aestronglyMeasurable_const).norm
  have hdom := hi.add (integrable_const ‖center-target‖)
  have hout : Integrable (fun z => ‖f z-target‖) ν := by
    apply hdom.mono' hm
    filter_upwards with z
    simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hp z
  refine ⟨hout,?_⟩
  have hh := integral_mono hout hdom hp
  have he := integral_add hi (integrable_const ‖center-target‖)
  simp only [Pi.add_apply,integral_const,measureReal_univ_eq_one,one_smul] at he
  simp only [Pi.add_apply] at hh
  rwa [he] at hh

def outputBatch (b : Budgets) (W ε : ℝ) : ℕ :=
  max 1 ⌈1024*b.σ ^ 2*(1+W ^ 2)/ε ^ 2⌉₊

theorem outputBatch_pos (b : Budgets) (W ε : ℝ) : 0 < outputBatch b W ε :=
  lt_of_lt_of_le (by decide) (le_max_left _ _)

theorem outputBatch_noise (b : Budgets) (W : ℝ) {ε : ℝ} (hε : 0 < ε) :
    b.σ ^ 2*(1+W ^ 2)/(outputBatch b W ε:ℝ) ≤ (ε/32) ^ 2 := by
  have hN : 0 < (outputBatch b W ε:ℝ) := Nat.cast_pos.mpr (outputBatch_pos b W ε)
  have hc : 1024*b.σ ^ 2*(1+W ^ 2)/ε ^ 2 ≤ (outputBatch b W ε:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right (1:ℕ) _)
  have hm := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  apply (div_le_iff₀ hN).mpr
  nlinarith

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def rawDirection (k : ℕ) (h : ℝ) (N : ℕ) : Procedure (X × Y × Y) History X :=
  AdjointKernels.rawStep (InnerOracle.blockX P O false)
    (DifferencingOracle.estimatorX P O k h N) (fun p => (p.1,p.2.1)) (by fun_prop)
    (fun _ => 0) measurable_const N 1

def direction (k : ℕ) (h : ℝ) (N : ℕ) : Procedure ((X × Y) × Y) History X :=
  (rawDirection P O k h N).reparam (AdjointSolve.clippedInput b) (AdjointSolve.clippedInput_measurable b)

def center (k : ℕ) (h : ℝ) (p : (X × Y) × Y) : X :=
  P.primitive.fx p.1.1 p.1.2-
    (P.gradientDifference p.1.1 p.1.2 (Bilevel.Clipping.clip (ballRadius b) p.2) k h).fst

theorem direction_calls (k : ℕ) (h : ℝ) (N : ℕ) :
    (direction P O k h N).CallsEq (fun _ => AdjointSolve.stepSamples k h N) := by
  have hu : (AdjointKernels.upperStep (InnerOracle.blockX P O false)
      (fun p : X × Y × Y => (p.1,p.2.1)) (by fun_prop)
      (fun _ => 0) measurable_const N 1).CallsEq (fun _ => N) :=
    Procedure.CallsEq.reparam _ _ (InnerBatch.affineBatch_calls _ N (-1)) _ _
  have hr : (rawDirection P O k h N).CallsEq (fun _ => AdjointSolve.stepSamples k h N) :=
    Procedure.CallsEq.bind _ _ _ _ (DifferencingOracle.estimatorX_calls P O k h N) hu
  exact Procedure.CallsEq.reparam _ _ hr
    (AdjointSolve.clippedInput b) (AdjointSolve.clippedInput_measurable b)

theorem direction_mse (k : ℕ) {h : ℝ} (hh : 0 < h) (N : ℕ) (hN : 0 < N)
    (p : (X × Y) × Y) (history : History) :
    Integrable (fun z => ‖z.1-center P k h p‖ ^ 2) ((direction P O k h N).law (p,history)) ∧
    (∫ z, ‖z.1-center P k h p‖ ^ 2 ∂(direction P O k h N).law (p,history)) ≤
      b.σ ^ 2*(1+((2*k+1:ℕ)/h) ^ 2)/(N:ℝ) := by
  let pp := AdjointSolve.clippedInput b p
  let m := (P.gradientDifference pp.1 pp.2.1 pp.2.2 k h).fst
  have hm := AdjointKernels.rawStep_error (InnerOracle.blockX P O false)
    (DifferencingOracle.estimatorX P O k h N) (fun p => (p.1,p.2.1)) (by fun_prop)
    (fun _ => 0) measurable_const N hN (by norm_num : (1:ℝ) ≠ 0) pp history m (center P k h p)
    (fun c => DifferencingOracle.estimatorX_center_error P O k hh (Nat.cast_pos.mpr hN) pp history c)
  refine ⟨hm.1,hm.2.trans_eq ?_⟩
  rw [InnerOracle.upperX_truth]
  have he : (0:X)-(1:ℝ) • (m-P.primitive.fx pp.1 pp.2.1)-center P k h p = 0 := by
    simp only [one_smul,zero_sub]
    dsimp [m,pp,center,AdjointSolve.clippedInput]
    abel
  rw [he,norm_zero,zero_pow (by norm_num : 2 ≠ 0),zero_add,one_pow,one_mul]
  ring

theorem direction_noise (k : ℕ) {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (p : (X × Y) × Y) (history : History) :
    Integrable (fun z => ‖z.1-center P k h p‖)
      ((direction P O k h (outputBatch b ((2*k+1:ℕ)/h) ε)).law (p,history)) ∧
    (∫ z, ‖z.1-center P k h p‖ ∂(direction P O k h
      (outputBatch b ((2*k+1:ℕ)/h) ε)).law (p,history)) ≤ ε/32 := by
  have hm := direction_mse P O k hh (outputBatch b ((2*k+1:ℕ)/h) ε)
    (outputBatch_pos b ((2*k+1:ℕ)/h) ε) p history
  exact InnerSolve.expected_norm_of_mse _ (measurable_fst.sub_const _).aestronglyMeasurable hm.1
    (by positivity) (hm.2.trans (outputBatch_noise b _ hε))

variable [FiniteDimensional ℝ Y]

theorem direction_error (k : ℕ) {h ε a : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hbias : ∀ x y v, ‖v‖ ≤ ballRadius b → ‖(P.gradientDifference x y v k h).fst-P.gxy x y v‖ ≤ a)
    (p : (X × Y) × Y) (history : History) :
    Integrable (fun z => ‖z.1-gradient P.objective p.1.1‖)
      ((direction P O k h (outputBatch b ((2*k+1:ℕ)/h) ε)).law (p,history)) ∧
    (∫ z, ‖z.1-gradient P.objective p.1.1‖ ∂(direction P O k h
      (outputBatch b ((2*k+1:ℕ)/h) ε)).law (p,history)) ≤
      ε/32+a+b.L₁*‖p.2-target P p.1‖+innerSensitivity b*‖p.1.2-P.yStar p.1.1‖ := by
  have hn := direction_noise P O k hh hε p history
  have hs := norm_center_shift (fun z : Outcome X History => z.1) (center P k h p)
    (gradient P.objective p.1.1) measurable_fst.aestronglyMeasurable hn.1
  have hb := biased_direction_error P p.1.1 p.1.2 p.2
    (P.gradientDifference p.1.1 p.1.2 (Bilevel.Clipping.clip (ballRadius b) p.2) k h).fst
    (hbias _ _ _ (Bilevel.Clipping.bounded _ (ballRadius_nonneg b) p.2))
  change ‖center P k h p-gradient P.objective p.1.1‖ ≤
    a+b.L₁*‖p.2-target P p.1‖+innerSensitivity b*‖p.1.2-P.yStar p.1.1‖ at hb
  exact ⟨hs.1,hs.2.trans (by linarith [hn.2])⟩

end Smoothness2601.HypergradientKernels
