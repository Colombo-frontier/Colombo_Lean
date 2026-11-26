import Bilevel.ZeroChainCarry
import Bilevel.RadialThird
import Bilevel.WrappedChain

/-! Actual radial/frame composition of the residual and its multiscale
decomposition. The constants are dimension independent. -/

noncomputable section
namespace Bilevel.ZeroChainWrappedResidual
open ZeroChain ZeroChainCarry ZeroChainResidualScaled ZeroChainFlatteningBounds
open RadialWrapper WrappedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem coordinates_contDiff (n : ℕ) (R : ℝ) (U : Space n →ₗᵢ[ℝ] E) :
    ContDiff ℝ 3 (coordinates n R U) :=
  U.toContinuousLinearMap.adjoint.contDiff.comp (compress_contDiff R 3)

theorem coordinates_jet_le (n : ℕ) (R : ℝ) (U : Space n →ₗᵢ[ℝ] E)
    (x : E) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (coordinates n R U) x‖ ≤ ‖iteratedFDeriv ℝ k (compress (E := E) R) x‖ := by
  have hp : ‖U.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact U.norm_toContinuousLinearMap_le
  change ‖iteratedFDeriv ℝ k (U.toContinuousLinearMap.adjoint ∘ compress R) x‖ ≤ _
  rw [U.toContinuousLinearMap.adjoint.iteratedFDeriv_comp_left (compress_contDiff R 3).contDiffAt
    (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)]
  exact (U.toContinuousLinearMap.adjoint.norm_compContinuousMultilinearMap_le _).trans
    ((mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (one_mul _))

theorem coordinates_positive_jet_bound (n : ℕ) (R δ : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R)
    (U : Space n →ₗᵢ[ℝ] E) (x : E) (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (coordinates n R U) x‖ ≤ 24*δ/δ^k := by
  have hR : 0 < R := hδ.trans_le hδR
  apply (coordinates_jet_le n R U x k hk).trans
  interval_cases k
  · rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
      (compress_hasFDerivAt R x).fderiv]
    have hb := compressDerivative_opNorm_le R hR x
    have he : 24*δ/δ^1 = 24 := by field_simp
    rw [he]
    linarith
  · rw [← norm_iteratedFDeriv_fderiv (n:=1),← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
    apply (second_derivative_norm R hR x).trans
    apply (div_le_div_iff₀ hR (pow_pos hδ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδR hδ.le]
  · rw [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),
      ← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
    apply (third_derivative_norm R hR x).trans
    apply (div_le_div_iff₀ (pow_pos hR 2) (pow_pos hδ 3)).mpr
    have hh : δ^2 ≤ R^2 := (sq_le_sq₀ hδ.le hR.le).mpr hδR
    nlinarith [mul_le_mul_of_nonneg_left hh hδ.le]

def residual (n : ℕ) (a β R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (x : E) : ℝ :=
  ZeroChainResidualScaled.R n a β (coordinates n R U x)

def piece (n J : ℕ) (δ : ℕ → ℝ) (a β R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (j : ℕ) : E → ℝ :=
  carriedPiece n J δ a (fun x => β⁻¹ • coordinates n R U x) j

theorem residual_contDiff (n : ℕ) (a β R : ℝ) (U : Space n →ₗᵢ[ℝ] E) :
    ContDiff ℝ 3 (residual n a β R U) :=
  (R_contDiff n a β).comp (coordinates_contDiff n R U)

theorem piece_contDiff (n J : ℕ) (δ : ℕ → ℝ) (a β R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (j : ℕ) :
    ContDiff ℝ 3 (piece n J δ a β R U j) :=
  carriedPiece_contDiff n J δ a ((coordinates_contDiff n R U).const_smul β⁻¹) j

theorem sum_piece (n J : ℕ) (δ : ℕ → ℝ) (a β R : ℝ) (U : Space n →ₗᵢ[ℝ] E) (x : E) :
    (∑ j ∈ Finset.range (J+1),piece n J δ a β R U j x) = residual n a β R U x :=
  sum_carriedPiece n J δ a (fun x => β⁻¹ • coordinates n R U x) x

theorem source_carried_overlap (n : ℕ) (c θ a β R : ℝ)
    (hc : 0 < c) (hcsmall : c ≤ 1/16) (hθ : 1 ≤ θ)
    (U : Space n →ₗᵢ[ℝ] E) (x : E) :
    (carriedActive n (ZeroChainSchedule.levels θ) (ZeroChainSchedule.resolution c 1 θ) a
      (fun x => β⁻¹ • coordinates n R U x) x).card ≤ 3 := by
  apply (Finset.card_le_card (carriedActive_subset _ _ _ _
    ((coordinates_contDiff n R U).const_smul β⁻¹) x)).trans
  exact ZeroChainSchedule.source_at_most_three_active_pieces n c θ hc hcsmall hθ _

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem residual_uniform_bounds : ∃ C : ℝ, 1 ≤ C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
    ∀ (n : ℕ) (a β R : ℝ), 0 ≤ a → 0 < β → β ≤ R →
    ∀ (U : Space n →ₗᵢ[ℝ] E) (x : E),
      |residual n a β R U x| ≤ C*a ∧
      ∀ j : Fin 3, ‖iteratedFDeriv ℝ (j.val+1) (residual n a β R U) x‖ ≤ C*a/β^(j.val+1) := by
  obtain ⟨b,hb0,hb⟩ := R_uniform_jet_bound
  let B := 1+∑ j,b j
  have hB : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hb0 j))
  have hbB (j : Fin 4) : b j ≤ B := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hb0 l) (Finset.mem_univ j)
    dsimp [B]
    linarith
  let d : Fin 3 → ℝ := fun j => ((j.val+1).factorial:ℝ)*B*24^(j.val+1)
  have hd (j : Fin 3) : 0 ≤ d j := by dsimp [d]; positivity
  let C := B+∑ j,d j
  have hBC : B ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hd j))
  have hdC (j : Fin 3) : d j ≤ C := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hd l) (Finset.mem_univ j)
    dsimp [C]
    linarith
  refine ⟨C,hB.trans hBC,fun E _ _ _ n a β R ha hβ hβR U x => ?_⟩
  constructor
  · have h := hb 0 n a β ha hβ (coordinates n R U x)
    simp only [Fin.val_zero,norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right ((hbB 0).trans hBC) ha)
  · intro j
    have hout (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) (z : Space n) :
        ‖iteratedFDeriv ℝ k (ZeroChainResidualScaled.R n a β) z‖ ≤ (B*a/β)*β/β^k := by
      have h := hb ⟨k,by omega⟩ n a β ha hβ z
      apply h.trans
      have he : (B*a/β)*β/β^k = B*a/β^k := by field_simp
      rw [he]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hbB ⟨k,by omega⟩) ha) (by positivity)
    have h := positive_composition_jet_bound (R_contDiff n a β) (coordinates_contDiff n R U)
      24 (B*a/β) β (by norm_num) (by positivity) hβ hout
      (fun k hk0 hk x => coordinates_positive_jet_bound n R β hβ hβR U x k hk0 hk) x (j.val+1)
      (by omega) (by omega)
    have he : ((j.val+1).factorial:ℝ)*(B*a/β)*24^(j.val+1)*β/β^(j.val+1) = d j*a/β^(j.val+1) := by
      dsimp [d]
      field_simp
      ring
    rw [he] at h
    exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hdC j) ha) (by positivity))

end Bilevel.ZeroChainWrappedResidual
