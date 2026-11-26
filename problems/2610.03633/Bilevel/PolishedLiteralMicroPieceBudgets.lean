import Bilevel.PolishedLiteralPhysicalPieces
import Bilevel.ZeroChainWrappedResidual

noncomputable section
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainSchedule ZeroChainCarry PrimitiveGeometry
theorem actual_micro_piece_budgets : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (c θ : ℝ),
      0<c → c≤1/16 → 1≤θ → 0≤P.L → 0<P.β → P.β≤P.radius →
      P.J=levels θ → P.δ=resolution c P.β θ →
      ∀ i j,j≤levels θ → ∀ u : U,
      |P.microPiece i j u| ≤ C*(P.L*P.β^2)*θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (P.microPiece i j) u‖ ≤
        C*(P.L*P.β^2)/(P.β*(pieceResolution c P.β θ j)^k.val) := by
  obtain ⟨B,hB,hb⟩ := normalized_piece_budgets
  let Kcoeff : Fin 3 → ℝ := fun k => ((k.val+1).factorial:ℝ)*B*24^(k.val+1)
  have hc (k : Fin 3) : 0 ≤ Kcoeff k := by dsimp [Kcoeff]; positivity
  let C := B+∑ k,Kcoeff k
  have hBC : B ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => hc k))
  have hcC (k : Fin 3) : Kcoeff k ≤ C := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hc l) (Finset.mem_univ k)
    dsimp [C]
    linarith
  refine ⟨C,hB.trans hBC,fun X U _ _ _ _ _ _ P c θ hcp hcs hθ hL hβ hβR hJ hδ i j hj u => ?_⟩
  let d := pieceResolution c 1 θ j
  let F := PolishedLiteralMultiscale.piece P.n (levels θ) (resolution c 1 θ) j
  let f := ZeroChainResidualScaled.scaled F (P.L*P.β^2) P.β
  have hF : ContDiff ℝ 3 F := PolishedLiteralMultiscale.piece_contDiff P.n (levels θ) (resolution c 1 θ) j
  have hf : ContDiff ℝ 3 f := contDiff_const.mul (hF.comp (contDiff_id.const_smul P.β⁻¹))
  have hd : 0 < d := pieceResolution_pos c 1 θ hcp (by norm_num) hθ j
  have hd1 : d ≤ 1 := by
    have hh := pieceResolution_le c 1 θ hcp.le (by norm_num) hθ j hj
    dsimp [d]
    linarith [hcs]
  have ha : 0≤P.L*P.β^2 := by positivity
  have hdphys : 0 < P.β*d := mul_pos hβ hd
  have hdR : P.β*d ≤ P.radius := by nlinarith [hβR]
  have hbF (z : Space P.n) := hb P.n c θ hcp hcs hθ j hj z
  have he : P.microPiece i j=f ∘ WrappedChain.coordinates P.n P.radius (P.frames i) := by
    simpa only [f,F,Function.comp_def,Parameters.coordinates] using P.microPiece_scaled c θ hcp hβ hθ hJ hδ i j
  constructor
  · rw [he]
    change |(P.L*P.β^2)*F (P.β⁻¹ • WrappedChain.coordinates P.n P.radius (P.frames i) u)| ≤ _
    rw [abs_mul,abs_of_nonneg ha]
    have hh := mul_le_mul_of_nonneg_left (hbF (P.β⁻¹ • WrappedChain.coordinates P.n P.radius (P.frames i) u)).1 ha
    calc
      _ ≤ (P.L*P.β^2)*(B*θ^(-amplitudeExponent j)) := hh
      _ ≤ C*(P.L*P.β^2)*θ^(-amplitudeExponent j) := by
        have hp := Real.rpow_nonneg (show 0 ≤ θ by linarith [hθ]) (-amplitudeExponent j)
        nlinarith [mul_le_mul_of_nonneg_right hBC (mul_nonneg ha hp)]
  · intro k
    have ho (l : ℕ) (hl0 : 1 ≤ l) (hl : l ≤ 3) (z : Space P.n) :
        ‖iteratedFDeriv ℝ l f z‖ ≤ (B*(P.L*P.β^2)/P.β)*(P.β*d)/(P.β*d)^l := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
      have hh := ZeroChainResidualScaled.scaled_jet_bound hF (P.L*P.β^2) P.β (B/d^q) ha hβ
        (q+1) (by omega) (fun w => (hbF w).2 ⟨q,by omega⟩) z
      apply hh.trans_eq
      simp only [pow_succ,mul_pow]
      field_simp
      ring
    have hcomp := positive_composition_jet_bound hf (ZeroChainWrappedResidual.coordinates_contDiff P.n P.radius (P.frames i))
      24 (B*(P.L*P.β^2)/P.β) (P.β*d) (by norm_num) (by positivity) hdphys ho
      (fun l hl0 hl v => ZeroChainWrappedResidual.coordinates_positive_jet_bound P.n P.radius (P.β*d)
        hdphys hdR (P.frames i) v l hl0 hl) u (k.val+1) (by omega) (by omega)
    rw [he]
    have hphys : pieceResolution c P.β θ j = P.β*d := by dsimp [d,pieceResolution]; ring
    rw [hphys]
    calc
      _ ≤ ((k.val+1).factorial:ℝ)*(B*(P.L*P.β^2)/P.β)*24^(k.val+1)*(P.β*d)/(P.β*d)^(k.val+1) := hcomp
      _ = Kcoeff k*(P.L*P.β^2)/(P.β*(P.β*d)^k.val) := by dsimp [Kcoeff]; rw [pow_succ]; field_simp; ring
      _ ≤ C*(P.L*P.β^2)/(P.β*(P.β*d)^k.val) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hcC k) ha) (by positivity)


end Bilevel.PolishedLiteral
