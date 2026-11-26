import Bilevel.ChiRecursivePayload
import Bilevel.RadialRegularity

/-! Actual first derivatives and square-root envelopes for each radially
wrapped recursive node. These are derived from the constructed profiles. -/
noncomputable section
namespace Bilevel.ChiRecursive
open ChiBoundedChain RadialWrapper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Node

def coordinateDerivative (D : Node E) (u : E) : E →L[ℝ] Space D.n :=
  D.frame.toContinuousLinearMap.adjoint.comp (compressDerivative D.radius u)

def normalizedDerivative (D : Node E) (u : E) : E →L[ℝ] Space D.n :=
  D.width⁻¹ • D.coordinateDerivative u

theorem coordinates_hasFDerivAt (D : Node E) (u : E) :
    HasFDerivAt D.coordinates (D.coordinateDerivative u) u :=
  D.frame.toContinuousLinearMap.adjoint.hasFDerivAt.comp u (compress_hasFDerivAt D.radius u)

theorem coordinates_contDiff (D : Node E) (k : ℕ) : ContDiff ℝ k D.coordinates :=
  D.frame.toContinuousLinearMap.adjoint.contDiff.comp (compress_contDiff D.radius k)

theorem H_contDiff (D : Node E) (k : ℕ) : ContDiff ℝ k D.H :=
  (payload_contDiff D.n D.ell D.width D.receiver D.nu D.force D.parentWidth D.tailRadius k).comp
    (D.coordinates_contDiff k)

theorem selector_contDiff (D : Node E) (i : Fin (D.n+1)) (k : ℕ) :
    ContDiff ℝ k (D.selector i) :=
  (ChiBoundedChain.selector_contDiff D.n k i).comp ((D.coordinates_contDiff k).const_smul D.width⁻¹)

theorem residual_contDiff (D : Node E) (i : Fin (D.n+1)) (k : ℕ) :
    ContDiff ℝ k (D.residual i) := by
  have ht : ContDiff ℝ k (residualTerm D.n i) :=
    (ChiBoundedChain.selector_contDiff D.n k i).neg.mul
      ((ZeroChainPotential.phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff)
  exact contDiff_const.mul (ht.comp ((D.coordinates_contDiff k).const_smul D.width⁻¹))

theorem release_contDiff (D : Node E) (k : ℕ) : ContDiff ℝ k D.release :=
  releaseGate_contDiff.comp (((EuclideanSpace.proj (𝕜:=ℝ) (Fin.last D.n)).contDiff.comp
    (D.coordinates_contDiff k)).div_const D.parentWidth)

theorem selector_hasFDerivAt (D : Node E) (i : Fin (D.n+1)) (u : E) :
    HasFDerivAt (D.selector i)
      ((selectorDerivative D.n i (D.width⁻¹ • D.coordinates u)).comp (D.normalizedDerivative u)) u :=
  (ChiBoundedChain.selector_hasFDerivAt D.n i _).comp u ((D.coordinates_hasFDerivAt u).const_smul D.width⁻¹)

theorem residual_hasFDerivAt (D : Node E) (i : Fin (D.n+1)) (u : E) :
    HasFDerivAt (D.residual i)
      ((D.ell*D.width^2) • (residualTermDerivative D.n i (D.width⁻¹ • D.coordinates u)).comp
        (D.normalizedDerivative u)) u :=
  ((residualTerm_hasFDerivAt D.n i _).comp u
    ((D.coordinates_hasFDerivAt u).const_smul D.width⁻¹)).const_mul (D.ell*D.width^2)

theorem coordinateDerivative_norm (D : Node E) (hR : 0<D.radius) (u : E) :
    ‖D.coordinateDerivative u‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  rw [one_mul]
  exact (frame_adjoint_norm_le D.frame _).trans (compressDerivative_norm_le D.radius hR u v)

theorem normalizedDerivative_norm (D : Node E) (hh : 0<D.width) (hR : 0<D.radius) (u : E) :
    ‖D.normalizedDerivative u‖≤1/D.width := by
  unfold normalizedDerivative
  rw [norm_smul D.width⁻¹ (D.coordinateDerivative u),Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh)]
  simpa only [one_div,mul_one] using mul_le_mul_of_nonneg_left (D.coordinateDerivative_norm hR u) (inv_nonneg.mpr hh.le)

theorem selector_derivative_bound (D : Node E) (hh : 0<D.width) (hR : 0<D.radius)
    {C : ℝ} (hC : 0≤C)
    (hbound : ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖selectorDerivative n i z‖≤C*Real.sqrt (ChiBoundedChain.selector n i z))
    (i : Fin (D.n+1)) (u : E) :
    ‖fderiv ℝ (D.selector i) u‖≤(C/D.width)*Real.sqrt (D.selector i u) := by
  rw [(D.selector_hasFDerivAt i u).fderiv]
  calc
    _ ≤ ‖selectorDerivative D.n i (D.width⁻¹ • D.coordinates u)‖*‖D.normalizedDerivative u‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (C*Real.sqrt (D.selector i u))*(1/D.width) :=
      mul_le_mul (hbound _ _ _) (D.normalizedDerivative_norm hh hR u) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem residual_derivative_bound (D : Node E) (hell : 0≤D.ell) (hh : 0<D.width) (hR : 0<D.radius)
    {C : ℝ} (hC : 0≤C)
    (hbound : ∀ (n : ℕ) (i : Fin (n+1)) (z : Space n),
      ‖residualTermDerivative n i z‖≤C*Real.sqrt (ChiBoundedChain.selector n i z))
    (i : Fin (D.n+1)) (u : E) :
    ‖fderiv ℝ (D.residual i) u‖≤C*(D.ell*D.width)*Real.sqrt (D.selector i u) := by
  rw [(D.residual_hasFDerivAt i u).fderiv]
  rw [norm_smul (D.ell*D.width^2) ((residualTermDerivative D.n i (D.width⁻¹ • D.coordinates u)).comp
    (D.normalizedDerivative u)),Real.norm_eq_abs,abs_of_nonneg (show 0≤D.ell*D.width^2 by positivity)]
  calc
    _ ≤ (D.ell*D.width^2)*(‖residualTermDerivative D.n i (D.width⁻¹ • D.coordinates u)‖*‖D.normalizedDerivative u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)
    _ ≤ (D.ell*D.width^2)*((C*Real.sqrt (D.selector i u))*(1/D.width)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (hbound _ _ _) (D.normalizedDerivative_norm hh hR u) (norm_nonneg _) (by positivity)
    _ = _ := by field_simp;ring

end Node

theorem constructed_node_derivative_envelopes : ∃ Cs Cr : ℝ,0≤Cs ∧ 0≤Cr ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → 0<D.radius → ∀ i u,
      ‖fderiv ℝ (D.selector i) u‖≤(Cs/D.width)*Real.sqrt (D.selector i u) ∧
      ‖fderiv ℝ (D.residual i) u‖≤Cr*(D.ell*D.width)*Real.sqrt (D.selector i u) := by
  obtain ⟨Cs,hCs,hs⟩ := selector_sqrt_derivative
  obtain ⟨Cr,hCr,hr⟩ := residualTerm_sqrt_derivative
  exact ⟨Cs,Cr,hCs,hCr,fun F _ _ _ D hell hh hR i u =>
    ⟨D.selector_derivative_bound hh hR hCs hs i u,D.residual_derivative_bound hell hh hR hCr hr i u⟩⟩

end Bilevel.ChiRecursive
