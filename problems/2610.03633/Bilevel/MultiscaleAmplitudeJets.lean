import Bilevel.MultiscalePerturbation

/-! Retain the actual chain-amplitude factor in the compensated lower
perturbation. This permits a fixed small amplitude to pay the prescribed
variation budget, including the endpoint theta=1. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean ZeroChainResidualBounds
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem residual_jet_budget_with_amplitude : ∃ B : ℝ,1≤B ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E:=E) n) (u : E) (k : Fin 4),
      ‖iteratedFDeriv ℝ k.val P.residual u‖≤(B*P.η)*P.L*P.β^2/P.β^k.val := by
  obtain ⟨B,hB,hb⟩ := ZeroChainWrappedResidual.residual_uniform_bounds
  refine ⟨B,hB,?_⟩
  intro E _ _ _ n P u k
  have hh : ‖iteratedFDeriv ℝ k.val P.residual u‖≤B*P.amplitude/P.β^k.val := by
    have h := hb E n P.amplitude P.β P.R P.amplitude_nonneg P.β_pos P.β_le_R P.U u
    fin_cases k
    · simpa only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] using h.1
    · simpa using h.2 0
    · simpa using h.2 1
    · simpa using h.2 2
  convert hh using 1
  dsimp [Parameters.amplitude]
  ring

theorem actual_perturbation_bounds_with_amplitude : ∃ M : ℝ,1≤M ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E:=E) n) (y : LowerSpace E),
      ‖iteratedFDeriv ℝ 2 P.data.perturbation y‖≤
        M*P.μ*(P.η^2*P.β^2+P.η*P.β*Real.sqrt P.θ/P.c) ∧
      ‖iteratedFDeriv ℝ 3 P.data.perturbation y‖≤
        M*P.μ*(P.η^2*P.β+P.η*P.θ/P.c^2) := by
  obtain ⟨B,hB,hb⟩ := residual_jet_budget_with_amplitude
  obtain ⟨K,hK,hk⟩ := actual_coupling_bounds
  let M := 4*B^2+K
  have hM : 1≤M := by dsimp [M]; nlinarith [sq_nonneg B]
  have hBM : 4*B^2≤M := by dsimp [M]; linarith
  have hKM : K≤M := by dsimp [M]; nlinarith [sq_nonneg B]
  refine ⟨M,hM,?_⟩
  intro E _ _ _ n P y
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hη := P.η_nonneg
  have hβ := P.β_pos
  have hc := P.c_pos
  have hθ : 0≤P.θ := by linarith [P.θ_ge_one]
  have hcomp := P.compensation_bounds (B*P.η) (by positivity) (hb E n P) y
  have hcoupl := hk E n P y
  have hbound (k : ℕ) (hkle : k≤3) :
      ‖iteratedFDeriv ℝ k P.data.perturbation y‖≤‖iteratedFDeriv ℝ k P.compensation y‖+
        (P.μ/P.L)*‖iteratedFDeriv ℝ k P.data.coupling y‖ := by
    rw [P.perturbation_split]
    have hscaled : ContDiff ℝ 3 (fun v => (P.μ/P.L)*P.data.coupling v) :=
      contDiff_const.mul P.data.coupling_contDiff
    have hh := jet_sub_norm_le P.compensation_contDiff hscaled y k hkle
    rw [const_mul_jet_norm P.data.coupling_contDiff _ y k hkle,abs_of_pos (div_pos hμ hL)] at hh
    exact hh
  have hc2 : ‖iteratedFDeriv ℝ 2 P.compensation y‖≤M*P.μ*P.η^2*P.β^2 := by
    apply hcomp.1.trans
    have hh := mul_le_mul_of_nonneg_right (show 2*B^2≤M by nlinarith [sq_nonneg B])
      (show 0≤P.μ*P.η^2*P.β^2 by positivity)
    convert hh using 1 <;> ring
  have hc3 : ‖iteratedFDeriv ℝ 3 P.compensation y‖≤M*P.μ*P.η^2*P.β := by
    apply hcomp.2.trans
    have hh := mul_le_mul_of_nonneg_right hBM (show 0≤P.μ*P.η^2*P.β by positivity)
    convert hh using 1 <;> ring
  have hk2 : (P.μ/P.L)*‖iteratedFDeriv ℝ 2 P.data.coupling y‖≤M*P.μ*P.η*P.β*Real.sqrt P.θ/P.c := by
    calc
      _ ≤ (P.μ/P.L)*(K*P.η*P.L*P.β*Real.sqrt P.θ/P.c) :=
        mul_le_mul_of_nonneg_left hcoupl.1 (div_pos hμ hL).le
      _ = K*(P.μ*P.η*P.β*Real.sqrt P.θ/P.c) := by field_simp; ring
      _ ≤ M*(P.μ*P.η*P.β*Real.sqrt P.θ/P.c) :=
        mul_le_mul_of_nonneg_right hKM (by positivity)
      _ = _ := by ring
  have hk3 : (P.μ/P.L)*‖iteratedFDeriv ℝ 3 P.data.coupling y‖≤M*P.μ*P.η*P.θ/P.c^2 := by
    calc
      _ ≤ (P.μ/P.L)*(K*P.η*P.L*P.θ/P.c^2) :=
        mul_le_mul_of_nonneg_left hcoupl.2 (div_pos hμ hL).le
      _ = K*(P.μ*P.η*P.θ/P.c^2) := by field_simp; ring
      _ ≤ M*(P.μ*P.η*P.θ/P.c^2) :=
        mul_le_mul_of_nonneg_right hKM (by positivity)
      _ = _ := by ring
  constructor
  · exact (hbound 2 (by norm_num)).trans ((add_le_add hc2 hk2).trans_eq (by ring))
  · exact (hbound 3 (by norm_num)).trans ((add_le_add hc3 hk3).trans_eq (by ring))

end Bilevel.MultiscaleMean
