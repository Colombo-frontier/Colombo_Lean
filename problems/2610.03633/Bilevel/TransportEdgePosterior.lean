import Bilevel.TransportNetworkStandardBorel

/-! Genuine conditional laws of one fixed orthogonal edge after its successive
forward/reverse probes. Left isotropy fixes the paired RANGE; the reverse
direction enlarges that range by its input before conditioning its response. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.TransportEdgePosterior
open EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

instance leftAction (d : ℕ) (B : Submodule ℝ (Space d)) :
    MulAction (ProjectionStabilizer.subgroup d B) (OrthogonalHaar.Group d) where
  smul S O := S.val*O
  one_smul O := one_mul O
  mul_smul S R O := mul_assoc S.val R.val O

instance leftMeasurableAction (d : ℕ) (B : Submodule ℝ (Space d)) :
    MeasurableSMul₂ (ProjectionStabilizer.subgroup d B) (OrthogonalHaar.Group d) := by
  constructor
  exact (continuous_subtype_val.measurable.comp measurable_fst).mul measurable_snd

def Invariant {d : ℕ} (B : Submodule ℝ (Space d)) (μ : Measure (OrthogonalHaar.Group d)) : Prop :=
  ∀ S : ProjectionStabilizer.subgroup d B, MeasurePreserving (fun O => S.val*O) μ μ

theorem invariant_mono {d : ℕ} {B C : Submodule ℝ (Space d)} (hBC : B ≤ C)
    (μ : Measure (OrthogonalHaar.Group d)) (hμ : Invariant B μ) : Invariant C μ := by
  intro S
  let R : ProjectionStabilizer.subgroup d B :=
    ⟨S.val,(ProjectionStabilizer.membership d B S.val).mpr (fun y hy =>
      (ProjectionStabilizer.membership d C S.val).mp S.property y (hBC hy))⟩
  exact hμ R

def forward {d : ℕ} (q : Space d) (O : OrthogonalHaar.Group d) : Space d := O • q
def reverse {d : ℕ} (q : Space d) (O : OrthogonalHaar.Group d) : Space d := O⁻¹ • q

theorem forward_measurable {d : ℕ} (q : Space d) : Measurable (forward q) :=
  measurable_id.smul measurable_const
theorem reverse_measurable {d : ℕ} (q : Space d) : Measurable (reverse q) :=
  measurable_inv.smul measurable_const

theorem forward_posterior_invariant {d : ℕ} (B : Submodule ℝ (Space d))
    (μ : Measure (OrthogonalHaar.Group d)) [IsProbabilityMeasure μ] (hμ : Invariant B μ)
    (q : Space d) :
    ∀ᵐ y ∂μ.map (forward q),
      Invariant (B ⊔ Submodule.span ℝ {y}) (condDistrib id (forward q) μ y) := by
  have he : ∀ (S : ProjectionStabilizer.subgroup d B) (O : OrthogonalHaar.Group d),
      forward q (S • O) = S • forward q O := fun S O => mul_smul S.val O q
  have hp := ConditionalSupport.equivariant_observation μ (forward q) (forward_measurable q)
    (ProjectionStabilizer.law d B) hμ he
  filter_upwards [hp] with y hy
  intro S
  let R : ProjectionStabilizer.subgroup d B :=
    ⟨S.val,(ProjectionStabilizer.membership d B S.val).mpr (fun x hx =>
      (ProjectionStabilizer.membership d (B ⊔ Submodule.span ℝ {y}) S.val).mp
        S.property x ((show B ≤ B ⊔ Submodule.span ℝ {y} from le_sup_left) hx))⟩
  have hf : R • y = y :=
    (ProjectionStabilizer.membership d (B ⊔ Submodule.span ℝ {y}) S.val).mp S.property y
      ((show Submodule.span ℝ {y} ≤ B ⊔ Submodule.span ℝ {y} from le_sup_right)
        (Submodule.mem_span_singleton_self y))
  exact hy R hf

theorem reverse_posterior_invariant {d : ℕ} (B : Submodule ℝ (Space d))
    (μ : Measure (OrthogonalHaar.Group d)) [IsProbabilityMeasure μ] (hμ : Invariant B μ)
    (q : Space d) :
    ∀ᵐ x ∂μ.map (reverse q),
      Invariant (B ⊔ Submodule.span ℝ {q}) (condDistrib id (reverse q) μ x) := by
  let C := B ⊔ Submodule.span ℝ {q}
  have hp : Invariant C μ := invariant_mono le_sup_left μ hμ
  have he : ∀ (S : ProjectionStabilizer.subgroup d C) (O : OrthogonalHaar.Group d),
      reverse q (S • O) = reverse q O := by
    intro S O
    have hqC : q ∈ C := (show Submodule.span ℝ {q} ≤ C from le_sup_right)
      (Submodule.mem_span_singleton_self q)
    have hf := (ProjectionStabilizer.membership d C S⁻¹.val).mp S⁻¹.property q hqC
    change S.val⁻¹ • q = q at hf
    change (S.val*O)⁻¹ • q = O⁻¹ • q
    rw [mul_inv_rev,mul_smul,hf]
  exact ConditionalSupport.invariant_observation μ (reverse q) (reverse_measurable q)
    (ProjectionStabilizer.law d C) hp he

theorem forward_fiber {d : ℕ} (μ : Measure (OrthogonalHaar.Group d)) [IsProbabilityMeasure μ]
    (q : Space d) : ∀ᵐ y ∂μ.map (forward q), ∀ᵐ O ∂condDistrib id (forward q) μ y, O • q = y := by
  apply ConditionalSupport.fiber μ (forward q) (forward_measurable q)
  exact measurableSet_eq_fun ((forward_measurable q).comp measurable_snd) measurable_fst

theorem reverse_fiber {d : ℕ} (μ : Measure (OrthogonalHaar.Group d)) [IsProbabilityMeasure μ]
    (q : Space d) : ∀ᵐ x ∂μ.map (reverse q), ∀ᵐ O ∂condDistrib id (reverse q) μ x, O • x = q := by
  have hp := ConditionalSupport.fiber μ (reverse q) (reverse_measurable q)
    (measurableSet_eq_fun ((reverse_measurable q).comp measurable_snd) measurable_fst)
  filter_upwards [hp] with x hx
  filter_upwards [hx] with O hO
  change O⁻¹ • q = x at hO
  rw [← hO,smul_inv_smul]

end Bilevel.TransportEdgePosterior
