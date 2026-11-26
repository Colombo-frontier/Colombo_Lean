import Bilevel.MultiscaleCouplingJets

/-! Actual second and third derivative bounds for the compensated
perturbation. Both the square compensation and the finite clipped coupling
are differentiated, with numerical constants uniform in dimension. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChainResidualBounds CompensatedMean

theorem square_jet_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} (hf : ContDiff ℝ 3 f) (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 < β)
    (x : V) (k : ℕ) (hk : k ≤ 3)
    (hb : ∀ l,l ≤ k → ‖iteratedFDeriv ℝ l f x‖ ≤ A/β^l) :
    ‖iteratedFDeriv ℝ k (fun v => f v*f v) x‖ ≤ (2:ℝ)^k*A^2/β^k := by
  have hh := jet_mul_bound hf hf x k hk (fun l => A/β^l) (fun l => A/β^l)
    (fun l => by positivity) hb hb
  apply hh.trans_eq
  interval_cases k
  all_goals norm_num [Finset.sum_range_succ]
  all_goals try field_simp
  all_goals ring

theorem const_mul_jet_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} (hf : ContDiff ℝ 3 f) (a : ℝ) (x : V) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun v => a*f v) x‖ = |a| * ‖iteratedFDeriv ℝ k f x‖ := by
  change ‖iteratedFDeriv ℝ k (fun v => a • f v) x‖ = _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)).contDiffAt]
  simpa only [Real.norm_eq_abs] using
    map_smul_eq_mul (ContinuousMultilinearMap.seminorm ℝ (fun _ : Fin k => V) ℝ) a (iteratedFDeriv ℝ k f x)

theorem residual_jet_budget : ∃ B : ℝ, 1 ≤ B ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n) (u : E) (k : Fin 4),
      ‖iteratedFDeriv ℝ k.val P.residual u‖ ≤ B*P.L*P.β^2/P.β^k.val := by
  obtain ⟨B,hB,hb⟩ := ZeroChainWrappedResidual.residual_uniform_bounds
  refine ⟨B,hB,fun E _ _ _ n P u k => ?_⟩
  have ha : P.amplitude ≤ P.L*P.β^2 := by
    have hh := mul_le_mul_of_nonneg_right P.η_le_one (mul_nonneg P.L_pos.le (sq_nonneg P.β))
    dsimp [Parameters.amplitude]
    nlinarith only [hh]
  have hh : ‖iteratedFDeriv ℝ k.val P.residual u‖ ≤ B*P.amplitude/P.β^k.val := by
    have h := hb E n P.amplitude P.β P.R P.amplitude_nonneg P.β_pos P.β_le_R P.U u
    fin_cases k
    · simpa only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] using h.1
    · simpa using h.2 0
    · simpa using h.2 1
    · simpa using h.2 2
  apply hh.trans
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ B by linarith)
  exact (div_le_div_of_nonneg_right hm (pow_nonneg P.β_pos.le _)).trans_eq (by ring)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

def compensation (y : LowerSpace E) : ℝ := P.μ/(2*P.L^2)*(P.residual (uProj E y))^2

theorem compensation_contDiff : ContDiff ℝ 3 P.compensation :=
  contDiff_const.mul ((P.residual_contDiff.comp (uProj E).contDiff).pow 2)

theorem perturbation_split : P.data.perturbation = fun y => P.compensation y-(P.μ/P.L)*P.data.coupling y := rfl

theorem compensation_bounds (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ u : E,∀ k : Fin 4, ‖iteratedFDeriv ℝ k.val P.residual u‖ ≤ B*P.L*P.β^2/P.β^k.val)
    (y : LowerSpace E) :
    ‖iteratedFDeriv ℝ 2 P.compensation y‖ ≤ 2*P.μ*B^2*P.β^2 ∧
      ‖iteratedFDeriv ℝ 3 P.compensation y‖ ≤ 4*P.μ*B^2*P.β := by
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hβ := P.β_pos
  let f := P.residual ∘ uProj E
  have hf : ContDiff ℝ 3 f := P.residual_contDiff.comp (uProj E).contDiff
  have hjet (l : ℕ) (hl : l ≤ 3) : ‖iteratedFDeriv ℝ l f y‖ ≤ (B*P.L*P.β^2)/P.β^l :=
    (linear_comp_jet_le P.residual_contDiff y l hl).trans (hb (uProj E y) ⟨l,by omega⟩)
  have hs (k : ℕ) (hk : k ≤ 3) : ‖iteratedFDeriv ℝ k P.compensation y‖ ≤
      (P.μ/(2*P.L^2))*((2:ℝ)^k*(B*P.L*P.β^2)^2/P.β^k) := by
    have hh := square_jet_bound hf (B*P.L*P.β^2) P.β (by positivity) hβ y k hk
      (fun l hl => hjet l (by omega))
    change ‖iteratedFDeriv ℝ k (fun v => (P.μ/(2*P.L^2))*(f v)^2) y‖ ≤ _
    have he : (fun v => (f v)^2) = fun v => f v*f v := by ext v; ring
    rw [const_mul_jet_norm (hf.pow 2) _ y k hk,abs_of_pos (by positivity : 0 < P.μ/(2*P.L^2)),he]
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  constructor
  · apply (hs 2 (by norm_num)).trans_eq
    field_simp
    ring
  · apply (hs 3 (by norm_num)).trans_eq
    field_simp
    ring

end Parameters

theorem actual_perturbation_bounds : ∃ M : ℝ, 1 ≤ M ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n) (y : LowerSpace E),
      ‖iteratedFDeriv ℝ 2 P.data.perturbation y‖ ≤ M*P.μ*(P.β^2+P.β*Real.sqrt P.θ/P.c) ∧
      ‖iteratedFDeriv ℝ 3 P.data.perturbation y‖ ≤ M*P.μ*(P.β+P.θ/P.c^2) := by
  obtain ⟨B,hB,hb⟩ := residual_jet_budget
  obtain ⟨K,hK,hk⟩ := actual_coupling_bounds
  let M := 4*B^2+K
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg B]
  have hBM : 4*B^2 ≤ M := by dsimp [M]; linarith
  have hKM : K ≤ M := by dsimp [M]; nlinarith [sq_nonneg B]
  refine ⟨M,hM,fun E _ _ _ n P y => ?_⟩
  have hμ := P.μ_pos
  have hL := P.L_pos
  have hβ := P.β_pos
  have hc := P.c_pos
  have hθ : 0 ≤ P.θ := by linarith [P.θ_ge_one]
  have hcomp := P.compensation_bounds B (by linarith) (hb E n P) y
  have hcoupl := hk E n P y
  have hbound (k : ℕ) (hkle : k ≤ 3) :
      ‖iteratedFDeriv ℝ k P.data.perturbation y‖ ≤ ‖iteratedFDeriv ℝ k P.compensation y‖+
        (P.μ/P.L)*‖iteratedFDeriv ℝ k P.data.coupling y‖ := by
    rw [P.perturbation_split]
    have hscaled : ContDiff ℝ 3 (fun v => (P.μ/P.L)*P.data.coupling v) := contDiff_const.mul P.data.coupling_contDiff
    have hh := jet_sub_norm_le P.compensation_contDiff hscaled y k hkle
    rw [const_mul_jet_norm P.data.coupling_contDiff _ y k hkle,abs_of_pos (div_pos hμ hL)] at hh
    exact hh
  have hη := P.η_nonneg
  have hK0 : 0 ≤ K := by linarith
  constructor
  · have hct := mul_le_mul_of_nonneg_left hcoupl.1 (div_nonneg hμ.le hL.le)
    have he : (P.μ/P.L)*(K*P.η*P.L*P.β*Real.sqrt P.θ/P.c) = K*P.μ*P.η*P.β*Real.sqrt P.θ/P.c := by field_simp; ring
    rw [he] at hct
    have hη' := mul_le_mul_of_nonneg_left P.η_le_one
      (show 0 ≤ K*P.μ*P.β*Real.sqrt P.θ/P.c by positivity)
    have hK' := mul_le_mul_of_nonneg_right hKM (show 0 ≤ P.μ*P.β*Real.sqrt P.θ/P.c by positivity)
    have hB' := mul_le_mul_of_nonneg_right (show 2*B^2 ≤ M by nlinarith [sq_nonneg B])
      (show 0 ≤ P.μ*P.β^2 by positivity)
    have hh := hbound 2 (by norm_num)
    simp only [div_eq_mul_inv] at hct hη' hK' hB' hh ⊢
    have hbcomp := hcomp.1
    ring_nf at hct hη' hK' hB' hh hbcomp ⊢
    exact hh.trans (add_le_add (hct.trans (hη'.trans hK')) (hbcomp.trans hB'))
  · have hct := mul_le_mul_of_nonneg_left hcoupl.2 (div_nonneg hμ.le hL.le)
    have he : (P.μ/P.L)*(K*P.η*P.L*P.θ/P.c^2) = K*P.μ*P.η*P.θ/P.c^2 := by field_simp; ring
    rw [he] at hct
    have hη' := mul_le_mul_of_nonneg_left P.η_le_one (show 0 ≤ K*P.μ*P.θ/P.c^2 by positivity)
    have hK' := mul_le_mul_of_nonneg_right hKM (show 0 ≤ P.μ*P.θ/P.c^2 by positivity)
    have hB' := mul_le_mul_of_nonneg_right hBM (show 0 ≤ P.μ*P.β by positivity)
    have hh := hbound 3 (by norm_num)
    simp only [div_eq_mul_inv] at hct hη' hK' hB' hh ⊢
    have hbcomp := hcomp.2
    ring_nf at hct hη' hK' hB' hh hbcomp ⊢
    exact hh.trans (add_le_add (hct.trans (hη'.trans hK')) (hbcomp.trans hB'))

end Bilevel.MultiscaleMean
