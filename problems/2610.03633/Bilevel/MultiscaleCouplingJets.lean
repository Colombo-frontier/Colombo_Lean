import Bilevel.MultiscalePieceJets
import Bilevel.CompensatedMeanJets

/-! Actual dimension-independent second and third derivative bounds for the
multiscale coupling. The source schedule and actual overlap remove the level
count from both bounds. -/

noncomputable section
namespace Bilevel.MultiscaleMean
open ZeroChainSchedule SmallGapLiftSupport

theorem second_weight_sum (c θ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hθ : 1 ≤ θ)
    (j : ℕ) (hj : j ≤ levels θ) :
    θ^(-amplitudeExponent j)/width c 1 θ j+2+
      width c 1 θ j/pieceResolution c 1 θ j ≤ 4*Real.sqrt θ/c := by
  have hh := second_block_weights c θ hc hθ j hj
  have hs : 1 ≤ Real.sqrt θ := Real.one_le_sqrt.mpr hθ
  have hsc : Real.sqrt θ ≤ Real.sqrt θ/c := (le_div_iff₀ hc).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left hc1 (Real.sqrt_nonneg θ)])
  calc
    _ ≤ Real.sqrt θ/c+2+Real.sqrt θ := by linarith [hh.1,hh.2]
    _ ≤ 4*(Real.sqrt θ/c) := by linarith
    _ = _ := by ring

theorem third_weight_sum (c θ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hθ : 1 ≤ θ)
    (j : ℕ) (hj : j ≤ levels θ) :
    θ^(-amplitudeExponent j)/(width c 1 θ j)^2+3/width c 1 θ j+
      3/pieceResolution c 1 θ j+width c 1 θ j/(pieceResolution c 1 θ j)^2 ≤ 8*θ/c^2 := by
  obtain ⟨h0,h1,h2,h3⟩ := third_block_weights c θ hc hθ j hj
  have hc2 : c^2 ≤ c := by nlinarith
  have hr : θ/c ≤ θ/c^2 := div_le_div_of_nonneg_left (by linarith) (sq_pos_of_pos hc) hc2
  rw [h3]
  have ht1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 3)
  have ht2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 3)
  have ht1' : 3/pieceResolution c 1 θ j ≤ 3*(θ/c) := by simpa only [mul_one_div] using ht1
  have ht2' : 3/width c 1 θ j ≤ 3*(θ/c) := by simpa only [mul_one_div] using ht2
  calc
    _ ≤ θ/c^2+7*(θ/c) := by linarith
    _ ≤ 8*(θ/c^2) := by linarith
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

theorem data_overlap (u : E) : (P.data.activePieces u).card ≤ 3 := P.actual_overlap u

theorem couplingTerm_bounds (B : ℝ) (hB : 1 ≤ B) (j : ℕ) (hj : j ≤ levels P.θ)
    (y : CompensatedMean.LowerSpace E)
    (hb : |P.pieces j (CompensatedMean.uProj E y)| ≤ B*P.amplitude*P.θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (P.pieces j) (CompensatedMean.uProj E y)‖ ≤
        B*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ j)^k.val)) :
    ‖iteratedFDeriv ℝ 2 (P.data.couplingTerm j) y‖ ≤ 4*C*B*P.η*P.L*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 (P.data.couplingTerm j) y‖ ≤ 8*C*B*P.η*P.L*P.θ/P.c^2 := by
  let d := pieceResolution P.c 1 P.θ j
  let w := width P.c 1 P.θ j
  let e := P.θ^(-amplitudeExponent j)
  have hd : 0 < d := pieceResolution_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  have hw : 0 < w := width_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  have hβ := P.β_pos
  have ha := P.amplitude_nonneg
  have hη := P.η_nonneg
  have hL := P.L_pos
  have hB0 : 0 ≤ B := by linarith
  have hC := C_pos
  have he : 0 ≤ e := Real.rpow_nonneg (by linarith [P.θ_ge_one]) _
  have hdp : pieceResolution P.c P.β P.θ j = P.β*d := by dsimp [d,pieceResolution]; ring
  have hwp : P.data.w j = P.β*w := by change width P.c P.β P.θ j = _; dsimp [w,width]; ring
  have h1 : ‖iteratedFDeriv ℝ 1 (P.data.e j) (CompensatedMean.uProj E y)‖ ≤ B*P.amplitude/P.β := by
    simpa only [Fin.val_zero,zero_add,pow_zero,mul_one] using hb.2 0
  have h2 : ‖iteratedFDeriv ℝ 2 (P.data.e j) (CompensatedMean.uProj E y)‖ ≤ B*P.amplitude/(P.β*(P.β*d)) := by
    simpa only [Fin.val_one,pow_one,hdp] using hb.2 1
  have h3 : ‖iteratedFDeriv ℝ 3 (P.data.e j) (CompensatedMean.uProj E y)‖ ≤ B*P.amplitude/(P.β*(P.β*d)^2) := by
    simpa only [hdp] using hb.2 2
  have ht2 := P.data.couplingTerm_second_bound j hj y (B*P.amplitude*e) (B*P.amplitude/P.β)
    (B*P.amplitude/(P.β*(P.β*d))) (by positivity) (by positivity) (by positivity) hb.1 h1 h2
  have ht3 := P.data.couplingTerm_third_bound j hj y (B*P.amplitude*e) (B*P.amplitude/P.β)
    (B*P.amplitude/(P.β*(P.β*d))) (B*P.amplitude/(P.β*(P.β*d)^2))
    (by positivity) (by positivity) (by positivity) (by positivity) hb.1 h1 h2 h3
  rw [hwp] at ht2 ht3
  have hs2 := second_weight_sum P.c P.θ P.c_pos (by linarith [P.c_small]) P.θ_ge_one j hj
  have hs3 := third_weight_sum P.c P.θ P.c_pos (by linarith [P.c_small]) P.θ_ge_one j hj
  change e/w+2+w/d ≤ 4*Real.sqrt P.θ/P.c at hs2
  change e/w^2+3/w+3/d+w/d^2 ≤ 8*P.θ/P.c^2 at hs3
  constructor
  · have hid : C*(B*P.amplitude*e/(P.β*w)+2*(B*P.amplitude/P.β)+
        B*P.amplitude/(P.β*(P.β*d))*(P.β*w)) =
        (C*B*P.η*P.L*P.β)*(e/w+2+w/d) := by
      dsimp [Parameters.amplitude]
      field_simp
      ring
    rw [hid] at ht2
    exact ht2.trans ((mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ C*B*P.η*P.L*P.β)).trans_eq (by ring))
  · have hid : C*(B*P.amplitude*e/(P.β*w)^2+3*(B*P.amplitude/P.β)/(P.β*w)+
        3*(B*P.amplitude/(P.β*(P.β*d)))+B*P.amplitude/(P.β*(P.β*d)^2)*(P.β*w)) =
        (C*B*P.η*P.L)*(e/w^2+3/w+3/d+w/d^2) := by
      dsimp [Parameters.amplitude]
      field_simp
      ring
    rw [hid] at ht3
    exact ht3.trans ((mul_le_mul_of_nonneg_left hs3 (by positivity : 0 ≤ C*B*P.η*P.L)).trans_eq (by ring))

end Parameters

theorem actual_coupling_bounds : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (P : Parameters (E := E) n) (y : CompensatedMean.LowerSpace E),
      ‖iteratedFDeriv ℝ 2 P.data.coupling y‖ ≤ K*P.η*P.L*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 P.data.coupling y‖ ≤ K*P.η*P.L*P.θ/P.c^2 := by
  obtain ⟨B,hB,hb⟩ := actual_piece_budgets
  let K := 24*C*B
  have hCB : 1 ≤ C*B := by nlinarith [C_one_le,mul_le_mul_of_nonneg_left hB C_pos.le]
  have hK : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨K,hK,fun E _ _ _ n P y => ?_⟩
  have hB0 : 0 ≤ B := by linarith
  have hC := C_pos
  have hη := P.η_nonneg
  have hL := P.L_pos
  have hβ := P.β_pos
  have hc := P.c_pos
  have hθ : 0 ≤ P.θ := by linarith [P.θ_ge_one]
  have ht (j : ℕ) (hj : j ≤ levels P.θ) := P.couplingTerm_bounds B hB j hj y
    (hb E n P j hj (CompensatedMean.uProj E y))
  constructor
  · have hh := P.data.coupling_jet_bound y 2 (by norm_num)
      (4*C*B*P.η*P.L*P.β*Real.sqrt P.θ/P.c) (by positivity) (P.data_overlap _)
      (fun j hj => (ht j hj).1)
    apply hh.trans
    dsimp [K]
    have hn : 0 ≤ C*B*P.η*P.L*P.β*Real.sqrt P.θ/P.c := by positivity
    calc
      _ = 12*(C*B*P.η*P.L*P.β*Real.sqrt P.θ/P.c) := by ring
      _ ≤ 24*(C*B*P.η*P.L*P.β*Real.sqrt P.θ/P.c) := by linarith
      _ = _ := by ring
  · have hh := P.data.coupling_jet_bound y 3 (by norm_num)
      (8*C*B*P.η*P.L*P.θ/P.c^2) (by positivity) (P.data_overlap _)
      (fun j hj => (ht j hj).2)
    apply hh.trans_eq
    dsimp [K]
    ring

end Bilevel.MultiscaleMean
