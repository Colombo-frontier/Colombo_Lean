import GradientHessian.SecondJetAlgebra
import GradientHessian.InverseGateFunctions
import GradientHessian.InnerFunctions

/-! The numerical gate has a zero second jet throughout its closed miss
region, including the seam. It may multiply any C2 coefficient on the full
physical space, without a support or global size restriction. -/

noncomputable section
namespace GradientHessian.NumericalGateJets
open SecondJetAlgebra JetLocality
open scoped InnerProductSpace

theorem step_zero_secondJet {t : ℝ} (ht : t ≤ 0) : ZeroSecondJet Profiles.step t :=
  zeroSecondJet_of_deriv (Profiles.step_nonpos ht)
    (Profiles.derivatives_flat_outside (Or.inl ht)).1
    (Profiles.derivatives_flat_outside (Or.inl ht)).2.1

theorem chi_zero_secondJet {t : ℝ} (ht : t ≤ 1/4) : ZeroSecondJet Profiles.chi t := by
  have hs := step_zero_secondJet (show 4*t-1 ≤ 0 by linarith)
  exact hs.comp (Profiles.contDiff_step.of_le (by decide : (2:WithTop ℕ∞) ≤ 3))
    (show ContDiff ℝ 2 (fun u : ℝ => 4*u-1) by fun_prop)

theorem chi_zero_richJet {t : ℝ} (ht : t ≤ 1/4) : richJet Profiles.chi t = 0 :=
  (richJet_eq_zero_iff _ _).mpr (chi_zero_secondJet ht)

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem gate_zero_secondJet (a y : Y) (hmiss : InverseGate.gateArg a y ≤ 1/4) :
    ZeroSecondJet (InverseGate.gate a) y :=
  (chi_zero_secondJet hmiss).comp
    (Profiles.contDiff_chi.of_le (by decide : (2:WithTop ℕ∞) ≤ 3))
    ((InverseGate.gateArg_contDiff a).of_le (by decide : (2:WithTop ℕ∞) ≤ 4))

theorem gate_zero_richJet (a y : Y) (hmiss : InverseGate.gateArg a y ≤ 1/4) :
    richJet (InverseGate.gate a) y = 0 :=
  (richJet_eq_zero_iff _ _).mpr (gate_zero_secondJet a y hmiss)

theorem gate_zero_derivatives (a y : Y) (hmiss : InverseGate.gateArg a y ≤ 1/4) :
    InverseGate.gate a y = 0 ∧ fderiv ℝ (InverseGate.gate a) y = 0 ∧
      fderiv ℝ (fderiv ℝ (InverseGate.gate a)) y = 0 := by
  have h := gate_zero_secondJet a y hmiss
  exact ⟨h.value, h.first, h.second⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem gate_after_linear_zero_secondJet (L : F →L[ℝ] Y) (a : Y) (x : F)
    (hmiss : InverseGate.gateArg a (L x) ≤ 1/4) :
    ZeroSecondJet (fun z => InverseGate.gate a (L z)) x :=
  (gate_zero_secondJet a (L x) hmiss).comp_linear
    ((InverseGate.gate_contDiff a).of_le (by decide : (2:WithTop ℕ∞) ≤ 3)) L

theorem gate_after_linear_zero_richJet (L : F →L[ℝ] Y) (a : Y) (x : F)
    (hmiss : InverseGate.gateArg a (L x) ≤ 1/4) :
    richJet (fun z => InverseGate.gate a (L z)) x = 0 :=
  (richJet_eq_zero_iff _ _).mpr (gate_after_linear_zero_secondJet L a x hmiss)

theorem gate_miss_of_inner_le (a y : Y)
    (hmiss : ⟪a,RadialSquash.squash InverseGate.B₀ y⟫_ℝ ≤ InverseGate.alpha/4) :
    InverseGate.gateArg a y ≤ 1/4 := by
  unfold InverseGate.gateArg
  apply (div_le_iff₀ InverseGate.alpha_pos).mpr
  linarith

theorem gate_miss_of_abs_inner_le (a y : Y)
    (hmiss : |⟪a,RadialSquash.squash InverseGate.B₀ y⟫_ℝ| ≤ InverseGate.alpha/4) :
    InverseGate.gateArg a y ≤ 1/4 :=
  gate_miss_of_inner_le a y ((le_abs_self _).trans hmiss)

theorem gated_term_zero_richJet (L : F →L[ℝ] Y) (a : Y) (coefficient : F → ℝ)
    (hc : ContDiff ℝ 2 coefficient) (x : F) (hmiss : InverseGate.gateArg a (L x) ≤ 1/4) :
    richJet (fun z => coefficient z*InverseGate.gate a (L z)) x = 0 :=
  richJet_mul_zero hc
    (((InverseGate.gate_contDiff a).comp L.contDiff).of_le (by decide : (2:WithTop ℕ∞) ≤ 3))
    (gate_after_linear_zero_secondJet L a x hmiss)

theorem remove_gated_term (L : F →L[ℝ] Y) (a : Y) (baseline coefficient : F → ℝ)
    (hb : ContDiff ℝ 2 baseline) (hc : ContDiff ℝ 2 coefficient) (x : F)
    (hmiss : InverseGate.gateArg a (L x) ≤ 1/4) :
    richJet (fun z => baseline z+coefficient z*InverseGate.gate a (L z)) x = richJet baseline x :=
  SecondJetAlgebra.richJet_remove_gated_term hb hc
    (((InverseGate.gate_contDiff a).comp L.contDiff).of_le (by decide : (2:WithTop ℕ∞) ≤ 3))
    (gate_after_linear_zero_secondJet L a x hmiss)

theorem remove_sub_gated_term (L : F →L[ℝ] Y) (a : Y) (baseline coefficient : F → ℝ)
    (hb : ContDiff ℝ 2 baseline) (hc : ContDiff ℝ 2 coefficient) (x : F)
    (hmiss : InverseGate.gateArg a (L x) ≤ 1/4) :
    richJet (fun z => baseline z-coefficient z*InverseGate.gate a (L z)) x = richJet baseline x :=
  SecondJetAlgebra.richJet_remove_sub_gated_term hb hc
    (((InverseGate.gate_contDiff a).comp L.contDiff).of_le (by decide : (2:WithTop ℕ∞) ≤ 3))
    (gate_after_linear_zero_secondJet L a x hmiss)

theorem remove_gated_term_ordinaryJet (L : F →L[ℝ] Y) (a : Y) (baseline coefficient : F → ℝ)
    (hb : ContDiff ℝ 2 baseline) (hc : ContDiff ℝ 2 coefficient) (x : F)
    (hmiss : InverseGate.gateArg a (L x) ≤ 1/4) :
    ordinaryJet (fun z => baseline z+coefficient z*InverseGate.gate a (L z)) x = ordinaryJet baseline x :=
  ordinaryJet_eq_of_richJet_eq (remove_gated_term L a baseline coefficient hb hc x hmiss)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual inner payload loses its unknown numerical mark at a gate
miss; the identity includes every physical-coordinate Hessian entry. -/
theorem payload_censor_richJet (b a : Fin m → Y) (v : Fin m → Fin (k+2) → E)
    (Z : InnerCoordinates.Space Y E m (k+2)) (i : Fin m)
    (hmiss : InverseGate.gateArg (a i) (InnerCoordinates.numerical Y E m (k+2) Z) ≤ 1/4) :
    richJet (fun W => Inner.payload b a v W i) Z =
      richJet (fun W : InnerCoordinates.Space Y E m (k+2) =>
        InverseGate.forcing (b i) (InnerCoordinates.numerical Y E m (k+2) W)) Z := by
  apply remove_gated_term (InnerCoordinates.numerical Y E m (k+2)) (a i)
    (fun W => InverseGate.forcing (b i) (InnerCoordinates.numerical Y E m (k+2) W))
    (fun W => Inner.input (v i) (InnerCoordinates.tasks Y E m (k+2) W i)) _ _ Z hmiss
  · have hf : ContDiff ℝ 3 (InverseGate.forcing (b i)) := by
      unfold InverseGate.forcing InverseGate.forcingArg
      exact contDiff_const.mul (contDiff_const.add
        ((IntegralProfiles.theta_contDiff.of_le (by decide : (3:WithTop ℕ∞) ≤ 4)).comp
          ((innerSL ℝ (b i)).contDiff.div_const _)))
    exact (hf.comp (InnerCoordinates.numerical Y E m (k+2)).contDiff).of_le
      (by decide : (2:WithTop ℕ∞) ≤ 3)
  · exact ((Inner.input_contDiff (v i)).comp
      (Inner.taskProjection (Y := Y) (E := E) m k i).contDiff).of_le
      (by decide : (2:WithTop ℕ∞) ≤ 3)

theorem payload_censor_ordinaryJet (b a : Fin m → Y) (v : Fin m → Fin (k+2) → E)
    (Z : InnerCoordinates.Space Y E m (k+2)) (i : Fin m)
    (hmiss : InverseGate.gateArg (a i) (InnerCoordinates.numerical Y E m (k+2) Z) ≤ 1/4) :
    ordinaryJet (fun W => Inner.payload b a v W i) Z =
      ordinaryJet (fun W : InnerCoordinates.Space Y E m (k+2) =>
        InverseGate.forcing (b i) (InnerCoordinates.numerical Y E m (k+2) W)) Z :=
  ordinaryJet_eq_of_richJet_eq (payload_censor_richJet b a v Z i hmiss)

end GradientHessian.NumericalGateJets
