import Bilevel.MultiscaleAmplitudeJets
import Bilevel.MultiscaleSmallness

/-! A fixed chain amplitude pays the exact prescribed variation budget,
including theta=1. The response-core condition and the second-jet bound
are inherited from their actual numerical certificates. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem amplitude_smallness_certificate : ∃ ηmax τ : ℝ,
    0<ηmax ∧ ηmax≤1 ∧ 0<τ ∧ τ≤1 ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E:=E) n),P.c=1/64 → P.η≤ηmax → P.β*P.θ≤τ →
      (∀ y : LowerSpace E,‖iteratedFDeriv ℝ 2 P.data.perturbation y‖≤P.μ/2) ∧
      (∀ y : LowerSpace E,‖iteratedFDeriv ℝ 3 P.data.perturbation y‖≤(P.μ/2)*P.θ) ∧
      (∀ u j,j≤P.data.J → |P.data.r u/P.L|≤P.data.w j/4) := by
  obtain ⟨M,hM,hjet⟩ := actual_perturbation_bounds_with_amplitude
  obtain ⟨τ₀,Rho,hτ₀,_hRho,hsmall⟩ := numerical_smallness_certificate
  have hMp : 0<M := by linarith
  let ηmax := 1/(8194*M)
  have hηmax : 0<ηmax := by dsimp [ηmax]; positivity
  have hηmax1 : ηmax≤1 := by
    dsimp [ηmax]
    apply (div_le_iff₀ (by positivity : 0<8194*M)).mpr
    nlinarith
  refine ⟨ηmax,min τ₀ 1,hηmax,hηmax1,by positivity,min_le_right _ _,?_⟩
  intro E _ _ _ n P hc hη hs
  obtain ⟨hsecond,_hthird,hcore⟩ := hsmall E n P hc (hs.trans (min_le_left _ _))
  refine ⟨hsecond,?_,hcore⟩
  intro y
  have hμ := P.μ_pos
  have hβ := P.β_pos
  have hη0 := P.η_nonneg
  have hη1 := P.η_le_one
  have hθ := P.θ_ge_one
  have hθ0 : 0≤P.θ := by linarith
  have hβθ : P.β*P.θ≤1 := hs.trans (min_le_right _ _)
  have hβ1 : P.β≤1 := by nlinarith
  have hβle : P.β≤P.θ := by linarith
  have hηsq : P.η^2≤P.η := by nlinarith
  have hfirst : P.η^2*P.β≤P.η*P.θ :=
    (mul_le_mul_of_nonneg_right hηsq hβ.le).trans
      (mul_le_mul_of_nonneg_left hβle hη0)
  have hpay : 8194*M*P.η≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<8194*M)).mp hη
    nlinarith only [hh]
  calc
    _ ≤ M*P.μ*(P.η^2*P.β+P.η*P.θ/P.c^2) := (hjet E n P y).2
    _ ≤ M*P.μ*(4097*P.η*P.θ) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hMp.le hμ.le)
      rw [hc]
      norm_num
      linarith
    _ = ((P.μ/2)*P.θ)*(8194*M*P.η) := by ring
    _ ≤ (P.μ/2)*P.θ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpay
        (show 0≤(P.μ/2)*P.θ by positivity)

end Bilevel.MultiscaleMean
