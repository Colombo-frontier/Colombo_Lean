import Bilevel.TransportAugmentedRun
import Bilevel.SourceObserverBudget

/-! One public finite dimension pays the network and every auxiliary-frame
observer budget. It is chosen before the controller, private randomness,
and actual orientations. No sharp dimension estimate is asserted. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.TransportAugmented
set_option autoImplicit false

theorem exists_joint_dimension (D₀ n p Tnet k T N B : ℕ) (networkCap cap δ : ℝ)
    (hc : 0 < cap) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ D r : ℕ, ∃ e : ℝ, D₀ ≤ D ∧ Tnet ≤ D ∧ T+1 ≤ D ∧
      TransportRound.observerDimension n p Tnet (N+1) networkCap (δ/2) ≤ D ∧
      (2*(N*B)+1)+(N*B)+(r+1) ≤ D ∧ 0 < r ∧ 0 < e ∧ e ≤ 2 ∧
      ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*e) ≤ 1/2 ∧
      2*((2*(N*B)+1:ℕ):ℝ)*e ≤ cap ∧
      ENNReal.ofReal (δ/2) + ((k+1:ℕ):ℝ≥0∞)*
        (((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e) = ENNReal.ofReal δ := by
  have hk : (0:ℝ) < (k+1:ℕ) := by positivity
  have hka : (1:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hd : 0 < δ/((k+1:ℕ):ℝ) := div_pos hδ hk
  have hd1 : δ/((k+1:ℕ):ℝ) ≤ 1 := by
    apply (div_le_iff₀ hk).mpr
    nlinarith
  obtain ⟨D,r,e,hD,hT,hdim,hr,he,he2,hsmall,henergy,hprob⟩ :=
    SourceObserverBudget.exists_dimension
      (D₀+Tnet+TransportRound.observerDimension n p Tnet (N+1) networkCap (δ/2))
      (2*(N*B)+1) (N*B) (T+1) (by omega) (by omega)
      (δ/((k+1:ℕ):ℝ)) cap hd hd1 hc
  refine ⟨D,r,e,by omega,by omega,hT,by omega,hdim,hr,he,he2,hsmall,henergy,?_⟩
  rw [hprob]
  have hfactor : ((k+1:ℕ):ℝ≥0∞)*ENNReal.ofReal (δ/((k+1:ℕ):ℝ)/2)=ENNReal.ofReal (δ/2) := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg (k+1))]
    congr 1
    field_simp
    ring
  rw [hfactor,←ENNReal.ofReal_add (by positivity : 0 ≤ δ/2) (by positivity : 0 ≤ δ/2)]
  congr 1
  ring

end Bilevel.TransportAugmented
