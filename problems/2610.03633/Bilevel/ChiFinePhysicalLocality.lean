import Bilevel.ChiFineInactiveAtoms

/-! Exact physical-scale active and fixed inactive fine-atom support, with
the source schedule's finest width. All interval conditions are scalar
coordinate conditions; no gradient support is assumed. -/
noncomputable section
namespace Bilevel.ChiFine.Parameters
open ChiBoundedChain ChiFine ZeroChainSchedule ZeroChainResidualScaled
variable (P : Parameters)

def inactivePiece (n k : ℕ) (z : Space n) : ℝ :=
  P.pieces n k z-if k=levels P.θ then P.residualDifference n z else 0

theorem inactivePiece_contDiff (n k : ℕ) : ContDiff ℝ 3 (P.inactivePiece n k) := by
  unfold inactivePiece
  by_cases hk : k=levels P.θ
  · simpa only [if_pos hk] using (P.pieces_contDiff n k).sub
      (signalResidual_contDiff n P.ℓ P.β P.signalResolution)
  · simpa only [if_neg hk,sub_zero] using P.pieces_contDiff n k

theorem inactivePiece_eq_scaled (n k : ℕ) : P.inactivePiece n k=
    scaled (inactiveAtom n (levels P.θ) (resolution P.c 1 P.θ) (P.signalResolution/P.β) k)
      P.amplitude P.β := by
  funext z
  by_cases hk : k=levels P.θ
  · simp only [inactivePiece,hk,if_pos rfl,Parameters.pieces,inactiveAtom,
      scaled,residualDifference,signalResidual,frontier,flatFrontier,amplitude,if_true]
    ring
  · simp only [inactivePiece,if_neg hk,sub_zero,Parameters.pieces,inactiveAtom]

theorem signalResolution_le_resolution (j : ℕ) (hj : j<levels P.θ) :
    P.signalResolution≤resolution P.c P.β P.θ j := by
  have hp : (4:ℝ)^(j+1)≤2*4^(levels P.θ) := by
    have hh : (4:ℝ)^(j+1)≤4^(levels P.θ) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hz : 0≤(4:ℝ)^(levels P.θ) := by positivity
    linarith
  have hi := one_div_le_one_div_of_le (show 0<(4:ℝ)^(j+1) by positivity) hp
  have he : aExponent j≤bExponent (levels P.θ) := by
    dsimp [aExponent,bExponent]
    linarith
  have hwidth : P.finalWidth≤resolution P.c P.β P.θ j :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le P.θ_ge_one (neg_le_neg he))
      (mul_nonneg P.c_pos.le P.β_pos.le)
  have hw := P.finalWidth_pos
  change P.finalWidth/8≤_
  linarith

theorem pieces_gradient_support (n k r : ℕ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤P.β/4)
    (j : Fin (n+1)) (hj : r+1≤j.val) : gradient (P.pieces n k) z j=0 := by
  rw [pieces,scaled_gradient ((piece_contDiff n (levels P.θ) (resolution P.c 1 P.θ) k).differentiable (by norm_num)),
    PiLp.smul_apply,piece_gradient_support n (levels P.θ) (resolution P.c 1 P.θ) k r (P.β⁻¹ • z)
      (fun a ha => scaled_coordinate_small P.β P.β_pos z a (hz a ha)) j hj,smul_zero]

theorem inactivePiece_gradient_support (n k r : ℕ) (hk : k≤levels P.θ) (z : Space n)
    (hz : ∀ j : Fin (n+1),r≤j.val → |z j|≤P.signalResolution)
    (j : Fin (n+1)) (hj : r≤j.val) : gradient (P.inactivePiece n k) z j=0 := by
  let τ := P.signalResolution/P.β
  have hτ : 0<τ := div_pos P.signalResolution_pos P.β_pos
  have hsτ : τ≤1/16 := (div_le_iff₀ P.β_pos).mpr (by linarith [P.signalResolution_small,P.β_pos])
  have hpos (a : ℕ) (_ha : a<levels P.θ) : 0<resolution P.c 1 P.θ a :=
    resolution_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one a
  have hs (a : ℕ) (_ha : a<levels P.θ) : resolution P.c 1 P.θ a≤1/16 :=
    resolution_small P.c 1 P.θ P.c_pos.le (by linarith [P.c_small]) (by norm_num) P.θ_ge_one a
  have hτδ (a : ℕ) (ha : a<levels P.θ) : τ≤resolution P.c 1 P.θ a := by
    apply (div_le_iff₀ P.β_pos).mpr
    convert P.signalResolution_le_resolution a ha using 1
    dsimp [resolution]
    ring
  have hj' : |(P.β⁻¹ • z) j|≤τ := by
    simp only [PiLp.smul_apply,smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr P.β_pos)]
    exact (mul_le_mul_of_nonneg_left (hz j hj) (inv_pos.mpr P.β_pos).le).trans_eq (by dsimp [τ];ring)
  rw [P.inactivePiece_eq_scaled,scaled_gradient
    ((inactiveAtom_contDiff n (levels P.θ) (resolution P.c 1 P.θ) τ k).differentiable (by norm_num)),
    PiLp.smul_apply,inactiveAtom_gradient_small n (levels P.θ) (resolution P.c 1 P.θ) τ
      hτ hsτ hpos hs hτδ k hk (P.β⁻¹ • z) j hj',smul_zero]

end Bilevel.ChiFine.Parameters
