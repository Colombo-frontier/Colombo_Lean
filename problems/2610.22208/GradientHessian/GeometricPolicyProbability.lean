import GradientHessian.GeometricPolicyRepair
import GradientHessian.PolicyEarlyIntegrability
import GradientHessian.GeometricPolicyLedger
import GradientHessian.Ledger

/-! The actual geometric policy ledger implies the source probability
bound once its two expectation estimates hold. Success-to-retirement,
resource correspondence, measurability and integrability are discharged. -/

noncomputable section
namespace GradientHessian.GeometricPolicyProbability
open Classical MeasureTheory Machine TaskState TaskSlots ComparisonController
  ComparisonControllerLedger ControllerMeasurable ControllerRepairProbability
  GeometricRepair HigherHierarchy PolicyRepairExpectation

variable {Ω Seed S O V : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [MeasurableSpace S] [MeasurableSpace O] [MeasurableSpace V]
variable {Y E : Type} {H : ℕ → Type} {t m ell : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h, NormedAddCommGroup (H h)] [∀ h, InnerProductSpace ℝ (H h)]
  [MeasurableSpace (Space Y E H m t)]
variable (K : ℝ) (data : Ω → Data Y E H m t)
  (Q : Policy Seed S (Space Y E H m t) O V)
  (o : Ω → Space Y E H m t → O) (v : Ω → Space Y E H m t → V)

def earlyCount (steps : ℕ) (q : Ω × Seed) : ℕ :=
  tally (rules (ell := ell) K (data q.1)) (early (rules (ell := ell) K (data q.1)))
    (policyPoints Q o v steps q) initial

def repairCount (steps : ℕ) (q : Ω × Seed) : ℕ :=
  count (fun q : Ω × Seed => rules (ell := ell) K (data q.1))
    (policyPoints Q o v steps) (fun _ => initial) q

variable (htr : ∀ s a, Measurable (fun q : Ω × Space Y E H m t =>
    trigger (ell := ell) K (data q.1) s q.2 a))
  (hhi : ∀ s, Measurable (fun q : Ω × Space Y E H m t => hit (ell := ell) (data q.1) s q.2))
  (ho : Measurable (fun q : Ω × Space Y E H m t => o q.1 q.2))
  (hv : Measurable (fun q : Ω × Space Y E H m t => v q.1 q.2))

include htr hhi ho hv in
theorem earlyCount_integrable (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (steps : ℕ) (hell : 0<ell) :
    Integrable (fun q => (earlyCount (ell := ell) K data Q o v steps q:ℝ)) μ :=
  PolicyEarlyIntegrability.early_integrable (priority t m) target
    (fun w => trigger K (data w)) (fun w => hit (data w)) htr hhi Q o v ho hv μ steps hell

include htr hhi ho hv in
theorem repairCount_integrable (μ : Measure (Ω × Seed)) [IsFiniteMeasure μ]
    (steps : ℕ) (hell : 0<ell) :
    Integrable (fun q => (repairCount (ell := ell) K data Q o v steps q:ℝ)) μ :=
  PolicyRepairExpectation.repair_integrable (priority t m) target
    (fun w => trigger K (data w)) (fun w => hit (data w)) htr hhi Q o v ho hv μ steps hell

variable [CompleteSpace Y] [CompleteSpace E] [∀ h, CompleteSpace (H h)]

include htr hhi ho hv in
theorem success_probability (μ : Measure (Ω × Seed)) [IsProbabilityMeasure μ]
    (steps G Hcap : ℕ) (hK : 16≤K) (hell : 0<ell)
    (hvalid : ∀ᵐ q ∂μ, Valid Y E H m t (data q.1))
    (hcaps : ∀ᵐ q ∂μ, Q.HasCaps (o q.1) (v q.1) G Hcap)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(m+1)*ell/4)
    (hearly : (∫ q, (earlyCount (ell := ell) K data Q o v steps q:ℝ) ∂μ) ≤
      (8:ℝ)^(t+1)*(m+1)/256)
    (hrepair : (∫ q, (repairCount (ell := ell) K data Q o v steps q:ℝ) ∂μ) ≤
      (8:ℝ)^(t+1)*(m+1)/256) :
    μ.real {q | ‖gradient (scalar K t (data q.1)) (Q.output (Q.run (o q.1) (v q.1) steps q.2))‖≤1} ≤ 1/32 := by
  let good : Set (Ω × Seed) := {q | Valid Y E H m t (data q.1) ∧
    Q.HasCaps (o q.1) (v q.1) G Hcap ∧
    ‖gradient (scalar K t (data q.1)) (Q.output (Q.run (o q.1) (v q.1) steps q.2))‖≤1}
  have heq : {q | ‖gradient (scalar K t (data q.1))
      (Q.output (Q.run (o q.1) (v q.1) steps q.2))‖≤1} =ᵐ[μ] good := by
    filter_upwards [hvalid,hcaps] with q hq hc
    apply propext
    change _ ↔ Valid Y E H m t (data q.1) ∧ Q.HasCaps (o q.1) (v q.1) G Hcap ∧ _
    simp only [hq,hc,true_and]
    rfl
  rw [measureReal_congr heq]
  apply Ledger.success_probability_le_one_thirty_second μ good
    (fun q => (earlyCount (ell := ell) K data Q o v steps q:ℝ))
    (fun q => (repairCount (ell := ell) K data Q o v steps q:ℝ))
    (n := (8:ℝ)^(t+1)) (M := (m:ℝ)+1) (h := (Hcap:ℝ)) (G := (G:ℝ)) (ell := (ell:ℝ))
    (by positivity) (by positivity) (by exact_mod_cast hell) hrich hordinary
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _)
    (earlyCount_integrable K data Q o v htr hhi ho hv μ steps hell)
    (repairCount_integrable K data Q o v htr hhi ho hv μ steps hell) hearly hrepair
  intro q hq
  have hb := GeometricPolicyLedger.policy_capped_ledger hK (data q.1) hq.1 Q
    (o q.1) (v q.1) steps q.2 hell G Hcap hq.2.1 hq.2.2
  have hb' : (8:ℝ)^(t+1)*(m+1) ≤ (Hcap:ℝ)*(m+1)+(((G+1)/ell:ℕ):ℝ)+
      earlyCount (ell := ell) K data Q o v steps q+repairCount (ell := ell) K data Q o v steps q := by
    exact_mod_cast hb
  have hd : (((G+1)/ell:ℕ):ℝ)≤((G:ℝ)+1)/ell := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.cast_div_le (α := ℝ) (m := G+1) (n := ell))
  linarith

end GradientHessian.GeometricPolicyProbability
