import GradientHessian.PresampledRepairCost
import GradientHessian.GeometricPolicyProbability

/-! The finite-cutoff probability ledger for the literal presampled source.
All repair, validity and measurability premises are discharged. Its sole
remaining probabilistic input is the actual normal-early expectation. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory DirectionPolicyReplay RepairAllocation HigherHierarchy JetLocality

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (Cp : ℝ) (s : Settings)
variable [∀ t,MeasurableSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [mO : ∀ t,MeasurableSpace (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [mV : ∀ t,MeasurableSpace (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
  [∀ t,BorelSpace (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy Seed S (Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
  (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t))

def earlyCount {ell : ℕ} (K : ℝ) (N : ℕ) (w : Sample Cp s t × Seed) : ℕ :=
  GeometricPolicyProbability.earlyCount (ell := ell) K (coefficients Cp s t) policy
    (fun x => ordinaryJet (objective Cp K s t x)) (fun x => richJet (objective Cp K s t x)) N w

theorem source_success_probability {ell : ℕ} {K : ℝ} (hK : 384≤K) (hCp : lowAllocation≤Cp)
    (hr : markAllocation*(s.M:ℝ)≤s.r) (N G Hcap : ℕ) (hell : 0<ell) (hellM : ell≤s.M)
    (hcaps : ∀ᵐ x ∂law Cp s t,policy.HasCaps (ordinaryJet (objective Cp K s t x))
      (richJet (objective Cp K s t x)) G Hcap)
    (hrich : (Hcap:ℝ)≤(8:ℝ)^(t+1)/2)
    (hordinary : (G:ℝ)+1≤(8:ℝ)^(t+1)*(s.M:ℝ)*ell/4)
    (hearly : (∫ w,(earlyCount (ell := ell) Cp s t policy K N w:ℝ) ∂(law Cp s t).prod σ)≤
      (8:ℝ)^(t+1)*(s.M:ℝ)/256) :
    ((law Cp s t).prod σ).real {w | ‖gradient (objective Cp K s t w.1)
      (policy.output (policy.run (ordinaryJet (objective Cp K s t w.1))
        (richJet (objective Cp K s t w.1)) N w.2))‖≤1}≤1/32 := by
  have hK0 : 0<K := by linarith
  have ho : @Measurable (Sample Cp s t × Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
      (Ordinary s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) _ (mO t)
      (fun q => ordinaryJet (objective Cp K s t q.1) q.2) :=
    (RawHierarchy.ordinaryJet_joint_measurable (n := s.columnsCount) (J := s.J)
      (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 hK0 t).mono
        le_rfl (le_of_eq BorelSpace.measurable_eq)
  have hv : @Measurable (Sample Cp s t × Point s.D s.J (LowSpace Cp s) (HighSpace Cp s) t)
      (Rich s.D s.J (LowSpace Cp s) (HighSpace Cp s) t) _ (mV t)
      (fun q => richJet (objective Cp K s t q.1) q.2) :=
    (RawHierarchy.richJet_joint_measurable (n := s.columnsCount) (J := s.J)
      (E := LowSpace Cp s) (H := HighSpace Cp s) s.P s.B 0 hK0 t).mono
        le_rfl (le_of_eq BorelSpace.measurable_eq)
  have htr := GeometricRepair.projected_trigger_measurable (ell := ell) s.P s.B 0 t K
    (id : Sample Cp s t → _) measurable_id
  have hhi := GeometricRepair.projected_hit_measurable (ell := ell) s.P s.B 0 t
    (id : Sample Cp s t → _) measurable_id
  have hvalid : ∀ᵐ w ∂(law Cp s t).prod σ,Valid _ _ _ _ t (coefficients Cp s t w.1) :=
    Measure.quasiMeasurePreserving_fst.ae (coefficients_valid Cp s t)
  have hc : ∀ᵐ w ∂(law Cp s t).prod σ,policy.HasCaps (ordinaryJet (objective Cp K s t w.1))
      (richJet (objective Cp K s t w.1)) G Hcap := Measure.quasiMeasurePreserving_fst.ae hcaps
  have hre := expected_repair_cost Cp s σ t policy hK hCp hr N hell hellM
  apply GeometricPolicyProbability.success_probability (ell := ell) K (coefficients Cp s t) policy
    (fun x => ordinaryJet (objective Cp K s t x)) (fun x => richJet (objective Cp K s t x))
    htr hhi ho hv ((law Cp s t).prod σ) N G Hcap (by linarith) hell hvalid hc hrich
  · simpa only [Settings.M,Nat.cast_add,Nat.cast_one] using hordinary
  · simpa only [earlyCount,Settings.M,Nat.cast_add,Nat.cast_one] using hearly
  · simpa only [Settings.M,Nat.cast_add,Nat.cast_one] using hre

end GradientHessian.PresampledConstruction
