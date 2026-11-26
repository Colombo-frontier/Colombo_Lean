import Bilevel.PolishedLiteralJointPieceBudgets
import Bilevel.PolishedLiteralSelectedOverlap
import Bilevel.MultiscaleCouplingJets

/-! The actual literal normal coupling has the manuscript's dimension-free
second/third joint derivative budgets. -/
noncomputable section
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainSchedule
open PolishedLiteralCompensated
open MultiscaleMean (second_weight_sum third_weight_sum)

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

theorem couplingTerm_bounds (c θ : ℝ) (hc : 0<c) (hcs : c≤1/16) (hθ : 1≤θ)
    (hL : 0<P.L) (hβ : 0<P.β) (hJ : P.J=levels θ) (hwidths : P.w=width c P.β θ)
    (B : ℝ) (hB : 1 ≤ B) (j : ℕ) (hj : j ≤ levels θ)
    (y : PolishedLiteralCompensated.LowerSpace (Joint X U))
    (hb : |P.selectedPiece j (PolishedLiteralCompensated.uProj (Joint X U) y)| ≤ B*(P.L*P.β^2)*θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (P.selectedPiece j) (PolishedLiteralCompensated.uProj (Joint X U) y)‖ ≤
        B*(P.L*P.β^2)/(P.β*(pieceResolution c P.β θ j)^k.val)) :
    ‖iteratedFDeriv ℝ 2 (P.data.couplingTerm j) y‖ ≤ 4*C*B*P.L*P.β*Real.sqrt θ/c ∧
      ‖iteratedFDeriv ℝ 3 (P.data.couplingTerm j) y‖ ≤ 8*C*B*P.L*θ/c^2 := by
  let d := pieceResolution c 1 θ j
  let w := width c 1 θ j
  let e := θ^(-amplitudeExponent j)
  have hd : 0 < d := pieceResolution_pos c 1 θ hc (by norm_num) hθ j
  have hw : 0 < w := width_pos c 1 θ hc (by norm_num) hθ j
  have ha : 0≤P.L*P.β^2 := by positivity
  have hB0 : 0 ≤ B := by linarith
  have hC := C_pos
  have he : 0 ≤ e := Real.rpow_nonneg (by linarith [hθ]) _
  have hdp : pieceResolution c P.β θ j = P.β*d := by dsimp [d,pieceResolution]; ring
  have hwp : P.data.w j = P.β*w := by change P.w j = _; rw [hwidths]; dsimp [w,width]; ring
  have h1 : ‖iteratedFDeriv ℝ 1 (P.data.e j) (PolishedLiteralCompensated.uProj (Joint X U) y)‖ ≤ B*(P.L*P.β^2)/P.β := by
    simpa only [Fin.val_zero,zero_add,pow_zero,mul_one] using hb.2 0
  have h2 : ‖iteratedFDeriv ℝ 2 (P.data.e j) (PolishedLiteralCompensated.uProj (Joint X U) y)‖ ≤ B*(P.L*P.β^2)/(P.β*(P.β*d)) := by
    simpa only [Fin.val_one,pow_one,hdp] using hb.2 1
  have h3 : ‖iteratedFDeriv ℝ 3 (P.data.e j) (PolishedLiteralCompensated.uProj (Joint X U) y)‖ ≤ B*(P.L*P.β^2)/(P.β*(P.β*d)^2) := by
    simpa only [hdp] using hb.2 2
  have ht2 := P.data.couplingTerm_second_bound j (by change j≤P.J;rw [hJ];exact hj) y (B*(P.L*P.β^2)*e) (B*(P.L*P.β^2)/P.β)
    (B*(P.L*P.β^2)/(P.β*(P.β*d))) (by positivity) (by positivity) (by positivity) hb.1 h1 h2
  have ht3 := P.data.couplingTerm_third_bound j (by change j≤P.J;rw [hJ];exact hj) y (B*(P.L*P.β^2)*e) (B*(P.L*P.β^2)/P.β)
    (B*(P.L*P.β^2)/(P.β*(P.β*d))) (B*(P.L*P.β^2)/(P.β*(P.β*d)^2))
    (by positivity) (by positivity) (by positivity) (by positivity) hb.1 h1 h2 h3
  rw [hwp] at ht2 ht3
  have hs2 := second_weight_sum c θ hc (by linarith [hcs]) hθ j hj
  have hs3 := third_weight_sum c θ hc (by linarith [hcs]) hθ j hj
  change e/w+2+w/d ≤ 4*Real.sqrt θ/c at hs2
  change e/w^2+3/w+3/d+w/d^2 ≤ 8*θ/c^2 at hs3
  constructor
  · have hid : C*(B*(P.L*P.β^2)*e/(P.β*w)+2*(B*(P.L*P.β^2)/P.β)+
        B*(P.L*P.β^2)/(P.β*(P.β*d))*(P.β*w)) =
        (C*B*P.L*P.β)*(e/w+2+w/d) := by
      field_simp
      ring
    rw [hid] at ht2
    exact ht2.trans ((mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ C*B*P.L*P.β)).trans_eq (by ring))
  · have hid : C*(B*(P.L*P.β^2)*e/(P.β*w)^2+3*(B*(P.L*P.β^2)/P.β)/(P.β*w)+
        3*(B*(P.L*P.β^2)/(P.β*(P.β*d)))+B*(P.L*P.β^2)/(P.β*(P.β*d)^2)*(P.β*w)) =
        (C*B*P.L)*(e/w^2+3/w+3/d+w/d^2) := by
      field_simp
      ring
    rw [hid] at ht3
    exact ht3.trans ((mul_le_mul_of_nonneg_left hs3 (by positivity : 0 ≤ C*B*P.L)).trans_eq (by ring))


end Parameters


/-- All piece amplitudes, positive jets, selector uniqueness and resolution
overlap are instantiated for the actual finite source hierarchy. -/
theorem actual_literal_coupling_bounds : ∃ K : ℝ,1≤K ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (c θ : ℝ),
      0<c → c≤1/16 → 1≤θ → 0<P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.δ=resolution c P.β θ → P.w=width c P.β θ →
      ∀ y : PolishedLiteralCompensated.LowerSpace (Joint X U),
      ‖iteratedFDeriv ℝ 2 P.data.coupling y‖≤K*P.L*P.β*Real.sqrt θ/c ∧
      ‖iteratedFDeriv ℝ 3 P.data.coupling y‖≤K*P.L*θ/c^2 := by
  obtain ⟨B,hB,hb⟩ := actual_selected_piece_budgets
  let N := PolishedLiteralCompensated.C
  have hN : 1≤N := normalJetConstant_one_le
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  let K := 24*N*B
  have hNB : 1≤N*B := by nlinarith [mul_le_mul_of_nonneg_left hB hN0.le]
  have hK : 1≤K := by dsimp [K];linarith
  refine ⟨K,hK,?_⟩
  intro X U _ _ _ _ _ _ P c θ hc hcs hθ hL hβ hR hβb hbR hJ hδ hw y
  have hB0 : 0≤B := by linarith
  have ht (j : ℕ) (hj : j≤P.J) :=
    P.couplingTerm_bounds c θ hc hcs hθ hL hβ hJ hw B hB j (by rw [← hJ];exact hj) y
      (hb X U P c θ hc hcs hθ hL.le hβ hR hβb hbR hJ hδ j (by rw [← hJ];exact hj)
        (PolishedLiteralCompensated.uProj (Joint X U) y))
  have hover := P.selectedPiece_overlap c θ hc hcs hβ hθ hJ hδ
    (PolishedLiteralCompensated.uProj (Joint X U) y)
  constructor
  · have hh := P.data.coupling_jet_bound y 2 (by norm_num)
      (4*N*B*P.L*P.β*Real.sqrt θ/c) (by positivity) hover (fun j hj => (ht j hj).1)
    apply hh.trans
    dsimp only [K]
    have hn : 0≤N*B*P.L*P.β*Real.sqrt θ/c := by positivity
    calc
      _=12*(N*B*P.L*P.β*Real.sqrt θ/c) := by ring
      _≤24*(N*B*P.L*P.β*Real.sqrt θ/c) := by linarith only [hn]
      _=_ := by ring
  · have hh := P.data.coupling_jet_bound y 3 (by norm_num)
      (8*N*B*P.L*θ/c^2) (by positivity) hover (fun j hj => (ht j hj).2)
    apply hh.trans_eq
    dsimp only [K]
    ring

end Bilevel.PolishedLiteral
