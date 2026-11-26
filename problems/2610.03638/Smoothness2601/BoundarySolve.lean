import Smoothness2601.BoundaryDecoupling
import Smoothness2601.HypergradientKernels

/-! A boundary upper routine using one fresh lower-gradient batch and one
fresh upper-X batch per outer iteration. At μ=L₁ the exact lower-gradient
step has zero deterministic error, at every input and without a radius bound. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Bilevel.Stateful
namespace Smoothness2601.BoundarySolve
open HypergradientGeometry HypergradientKernels

def innerScale (b : Budgets) : ℝ := InnerGeometry.stepsize b*innerSensitivity b
def innerCount (b : Budgets) (ε : ℝ) : ℕ := outputBatch b 0 (ε/innerScale b)
def upperCount (b : Budgets) (ε : ℝ) : ℕ := outputBatch b 0 ε
def count (b : Budgets) (ε : ℝ) : ℕ := innerCount b ε+upperCount b ε

theorem innerScale_pos (b : Budgets) : 0 < innerScale b :=
  mul_pos (InnerGeometry.stepsize_pos b) (innerSensitivity_pos b)

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

def inner (ε : ℝ) : Procedure (X × Y) H Y :=
  (InnerBatch.affineBatch (InnerOracle.blockY P O true) (innerCount b ε)
    (InnerGeometry.stepsize b)).reparam (fun p => (p,p.2)) (measurable_id.prodMk measurable_snd)

def upper (ε : ℝ) : Procedure (X × Y) H X :=
  (InnerBatch.affineBatch (InnerOracle.blockX P O false) (upperCount b ε) (-1)).reparam
    (fun p => (p,0)) (measurable_id.prodMk measurable_const)

def program (ε : ℝ) : Procedure (X × Y) H X :=
  (inner P O ε).bind ((upper P O ε).reparam (fun z => (z.1.1,z.2))
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem program_calls (ε : ℝ) : (program P O ε).CallsEq (fun _ => count b ε) :=
  Procedure.CallsEq.bind _ _ _ _
    (Procedure.CallsEq.reparam _ _ (InnerBatch.affineBatch_calls _ _ _) _ _)
    (Procedure.CallsEq.reparam _ _
      (Procedure.CallsEq.reparam _ _ (InnerBatch.affineBatch_calls _ _ _) _ _) _ _)

variable [FiniteDimensional ℝ Y]

theorem inner_error (heq : b.L₁ = b.μ) {ε : ℝ} (hε : 0 < ε)
    (p : X × Y) (history : H) :
    Integrable (fun z => ‖z.1-P.yStar p.1‖) ((inner P O ε).law (p,history)) ∧
    (∫ z, ‖z.1-P.yStar p.1‖ ∂(inner P O ε).law (p,history)) ≤ ε/(32*innerSensitivity b) := by
  have hα := InnerGeometry.stepsize_pos b
  have hC := innerSensitivity_pos b
  have hs := innerScale_pos b
  have hn : 0 < innerCount b ε := outputBatch_pos _ _ _
  have hh := InnerBatch.affineBatch_error (InnerOracle.blockY P O true) _ hn hα.ne'
    p p.2 (P.yStar p.1) history
  have hd := InnerGeometry.contraction P p.1 p.2
  have hr : InnerGeometry.rate b = 0 := by
    unfold InnerGeometry.rate
    rw [heq,div_self (ne_of_gt (sq_pos_of_pos b.μ_pos))]
    ring
  rw [hr,zero_mul] at hd
  have hnvar := outputBatch_noise b 0 (div_pos hε hs)
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,mul_one] at hnvar
  have hm := mul_le_mul_of_nonneg_left hnvar (sq_nonneg (InnerGeometry.stepsize b))
  have he : InnerGeometry.stepsize b ^ 2*((ε/innerScale b)/32) ^ 2 =
      (ε/(32*innerSensitivity b)) ^ 2 := by
    unfold innerScale
    field_simp
    ring
  rw [he] at hm
  have hb : (∫ z, ‖z.1-P.yStar p.1‖ ^ 2 ∂(inner P O ε).law (p,history)) ≤
      (ε/(32*innerSensitivity b)) ^ 2 := by
    change (∫ z, ‖z.1-P.yStar p.1‖ ^ 2
      ∂(InnerBatch.affineBatch (InnerOracle.blockY P O true) _ _).law ((p,p.2),history)) ≤ _
    have hh' := hh.2
    change _ ≤ ‖p.2-InnerGeometry.stepsize b • P.primitive.gy p.1 p.2-P.yStar p.1‖ ^ 2+
      InnerGeometry.stepsize b ^ 2*b.σ ^ 2/(innerCount b ε:ℝ) at hh'
    exact hh'.trans (calc
      _ ≤ 0+InnerGeometry.stepsize b ^ 2*b.σ ^ 2/(innerCount b ε:ℝ) := add_le_add_right hd _
      _ = InnerGeometry.stepsize b ^ 2*(b.σ ^ 2/(innerCount b ε:ℝ)) := by ring
      _ ≤ _ := hm)
  exact InnerSolve.expected_norm_of_mse (ν := (inner P O ε).law (p,history))
    (fun z : Outcome Y H => z.1-P.yStar p.1) (measurable_fst.sub measurable_const).aestronglyMeasurable hh.1
    (div_pos hε (mul_pos (by norm_num) hC)) hb

omit [FiniteDimensional ℝ Y] in
theorem upper_noise {ε : ℝ} (hε : 0 < ε) (p : X × Y) (history : H) :
    Integrable (fun z => ‖z.1-P.primitive.fx p.1 p.2‖) ((upper P O ε).law (p,history)) ∧
    (∫ z, ‖z.1-P.primitive.fx p.1 p.2‖ ∂(upper P O ε).law (p,history)) ≤ ε/32 := by
  have hh := InnerBatch.affineBatch_error (InnerOracle.blockX P O false) _
    (outputBatch_pos b 0 ε) (by norm_num : (-1:ℝ) ≠ 0) p 0 (P.primitive.fx p.1 p.2) history
  have hn := outputBatch_noise b 0 hε
  simp only [zero_pow (by decide : 2 ≠ 0),add_zero,mul_one] at hn
  have hb : (∫ z, ‖z.1-P.primitive.fx p.1 p.2‖ ^ 2 ∂(upper P O ε).law (p,history)) ≤ (ε/32) ^ 2 := by
    exact hh.2.trans (by simpa [InnerOracle.upperX_truth] using hn)
  exact InnerSolve.expected_norm_of_mse (ν := (upper P O ε).law (p,history))
    (fun z : Outcome X H => z.1-P.primitive.fx p.1 p.2) (measurable_fst.sub measurable_const).aestronglyMeasurable
    hh.1 (div_pos hε (by norm_num)) hb

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem upper_bias (heq : b.L₁ = b.μ) (x : X) (y : Y) :
    ‖P.primitive.fx x y-gradient P.objective x‖ ≤ innerSensitivity b*‖y-P.yStar x‖ := by
  have hz := (Boundary.source_forced_decoupling P heq).2.1 x y
  simpa only [surrogate,hz,ContinuousLinearMap.zero_apply,sub_zero] using surrogate_error P x y

theorem upper_error (heq : b.L₁ = b.μ) {ε : ℝ} (hε : 0 < ε) (p : X × Y) (history : H) :
    Integrable (fun z => ‖z.1-gradient P.objective p.1‖) ((upper P O ε).law (p,history)) ∧
    (∫ z, ‖z.1-gradient P.objective p.1‖ ∂(upper P O ε).law (p,history)) ≤
      ε/32+innerSensitivity b*‖p.2-P.yStar p.1‖ := by
  have hn := upper_noise P O hε p history
  have hs := norm_center_shift (ν := (upper P O ε).law (p,history)) (fun z => z.1)
    (P.primitive.fx p.1 p.2) (gradient P.objective p.1) (by fun_prop) hn.1
  exact ⟨hs.1,hs.2.trans (add_le_add hn.2 (upper_bias P heq p.1 p.2))⟩

theorem program_error (heq : b.L₁ = b.μ) {ε : ℝ} (hε : 0 < ε) (p : X × Y) (history : H) :
    Integrable (fun z => ‖z.1-gradient P.objective p.1‖) ((program P O ε).law (p,history)) ∧
    (∫ z, ‖z.1-gradient P.objective p.1‖ ∂(program P O ε).law (p,history)) ≤ ε/8 := by
  have hy := inner_error P O heq hε p history
  have hb := Procedure.bind_output_bound (inner P O ε)
    ((upper P O ε).reparam (fun z => (z.1.1,z.2))
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) p history
    (fun q => ‖q-gradient P.objective p.1‖) (by fun_prop) (fun _ => norm_nonneg _)
    (fun y => ε/32+innerSensitivity b*‖y-P.yStar p.1‖)
    ((integrable_const _).add (hy.1.const_mul _))
    (fun z => (upper_error P O heq hε (p.1,z.1) z.2.1).1)
    (fun z => (upper_error P O heq hε (p.1,z.1) z.2.1).2)
  refine ⟨hb.1,hb.2.trans ?_⟩
  have he := integral_add (integrable_const (μ := (inner P O ε).law (p,history)) (ε/32))
    (hy.1.const_mul (innerSensitivity b))
  simp only [Pi.add_apply] at he
  rw [he,integral_const_mul]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  have hh := mul_le_mul_of_nonneg_left hy.2 (innerSensitivity_pos b).le
  have he' : innerSensitivity b*(ε/(32*innerSensitivity b)) = ε/32 := by
    have := innerSensitivity_pos b
    field_simp
    ring
  rw [he'] at hh
  linarith

end Smoothness2601.BoundarySolve
