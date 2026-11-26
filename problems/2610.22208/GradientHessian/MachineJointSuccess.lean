import GradientHessian.MachineJointRun
import Mathlib.MeasureTheory.Measure.Prod

/-! Success over the presampled objective and independent seed, with an
arbitrary finite internal cutoff and its exact increasing union. -/

noncomputable section
namespace GradientHessian.Machine
open Classical MeasureTheory Set Filter
open scoped Topology ENNReal

variable {Ω Seed S X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable (P : Policy Seed S X Y Z) (o : Ω → X → Y) (r : Ω → X → Z) (good : Set (Ω × X))

def Policy.jointSuccessBy (N : ℕ) : Set (Ω × Seed) :=
  {w | w.2∈P.successBy (o w.1) (r w.1) {x | (w.1,x)∈good} N}

def Policy.jointSuccess : Set (Ω × Seed) :=
  {w | w.2∈P.success (o w.1) (r w.1) {x | (w.1,x)∈good}}

theorem Policy.jointSuccessBy_mono : Monotone (P.jointSuccessBy o r good) := by
  intro i j hij w hw
  exact P.successBy_mono (o w.1) (r w.1) _ hij hw

theorem Policy.jointSuccess_eq_iUnion : P.jointSuccess o r good=⋃ N,P.jointSuccessBy o r good N := by
  ext w
  simp only [Policy.jointSuccess,Policy.jointSuccessBy,mem_setOf_eq,mem_iUnion,P.success_eq_iUnion]

theorem Policy.jointSuccessBy_subset_output (N : ℕ) : P.jointSuccessBy o r good N ⊆
    {w | (w.1,P.output (P.run (o w.1) (r w.1) N w.2))∈good} := by
  rintro w ⟨n,hn,hh,hg⟩
  have he := P.run_after_halt (o w.1) (r w.1) w.2 hh (N-n)
  rw [Nat.add_sub_of_le hn] at he
  change (w.1,P.output (P.run (o w.1) (r w.1) N w.2))∈good
  rw [he]
  exact hg

variable (ho : Measurable (fun w : Ω × X => o w.1 w.2))
  (hr : Measurable (fun w : Ω × X => r w.1 w.2)) (hg : MeasurableSet good)

include ho hr hg in
theorem Policy.jointSuccessBy_measurable (N : ℕ) : MeasurableSet (P.jointSuccessBy o r good N) := by
  have hn (n : ℕ) : MeasurableSet {w : Ω × Seed |
      P.mode (P.run (o w.1) (r w.1) n w.2)=0 ∧
      (w.1,P.output (P.run (o w.1) (r w.1) n w.2))∈good} :=
    ((P.mode_measurable.comp (P.run_joint_measurable o r ho hr n)) (measurableSet_singleton 0)).inter
      ((measurable_fst.prodMk (P.output_joint_measurable o r ho hr n)) hg)
  have heq : P.jointSuccessBy o r good N = ⋃ n : ℕ, ⋃ (_ : n≤N),
      {w : Ω × Seed | P.mode (P.run (o w.1) (r w.1) n w.2)=0 ∧
        (w.1,P.output (P.run (o w.1) (r w.1) n w.2))∈good} := by
    ext w
    simp [Policy.jointSuccessBy,Policy.successBy,and_comm,and_left_comm,and_assoc]
  rw [heq]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun (_ : n≤N) => hn n

include ho hr hg in
theorem Policy.jointSuccess_measurable : MeasurableSet (P.jointSuccess o r good) := by
  rw [P.jointSuccess_eq_iUnion]
  exact MeasurableSet.iUnion (P.jointSuccessBy_measurable o r good ho hr hg)

theorem Policy.joint_success_le_of_cutoffs (μ : Measure (Ω × Seed)) (c : ℝ≥0∞)
    (hc : ∀ N,μ {w | (w.1,P.output (P.run (o w.1) (r w.1) N w.2))∈good}≤c) :
    μ (P.jointSuccess o r good)≤c := by
  have ht : Tendsto (fun N => μ (P.jointSuccessBy o r good N)) atTop
      (𝓝 (μ (P.jointSuccess o r good))) := by
    rw [P.jointSuccess_eq_iUnion]
    exact tendsto_measure_iUnion_atTop (P.jointSuccessBy_mono o r good)
  apply le_of_tendsto ht
  exact Filter.Eventually.of_forall (fun N =>
    (measure_mono (P.jointSuccessBy_subset_output o r good N)).trans (hc N))

include ho hr hg in
theorem Policy.joint_success_lower (μ : Measure Ω) [IsProbabilityMeasure μ]
    (σ : Measure Seed) [SFinite σ] (c : ℝ≥0∞)
    (hc : ∀ᵐ w ∂μ,c≤σ (P.success (o w) (r w) {x | (w,x)∈good})) :
    c≤(μ.prod σ) (P.jointSuccess o r good) := by
  rw [Measure.prod_apply (P.jointSuccess_measurable o r good ho hr hg)]
  calc
    c = ∫⁻ _ : Ω,c ∂μ := by simp
    _ ≤ _ := lintegral_mono_ae hc

end GradientHessian.Machine
