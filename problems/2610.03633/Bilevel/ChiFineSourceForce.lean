import Bilevel.ChiFineTangentLocality
import Bilevel.ChiFineSourceWidths
import Bilevel.GradientJetBounds

/-! Actual latent fine-force bound at every normal argument. The finite
normal-width sum produces the inverse-square-root variation factor. These
are the pre-wrapper derivatives required in the no-cascade equation. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainSchedule SmallGapLiftSupport

theorem finite_weighted_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} (S : Finset ι) (f : ι → E → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i)) (w : ι → ℝ) (z : E) :
    gradient (fun x => ∑ i ∈ S,f i x*w i) z=∑ i ∈ S,w i • gradient (f i) z := by
  have hd := HasFDerivAt.sum (u:=S) (fun i _ =>
    (((hf i).differentiable (by norm_num) z).hasGradientAt.hasFDerivAt).mul_const (w i))
  have hg : HasGradientAt (fun x => ∑ i ∈ S,f i x*w i) (∑ i ∈ S,w i • gradient (f i) z) z := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_sum,map_smul] using hd
  exact hg.gradient

theorem first_normal_width (c β θ : ℝ) (hθ : 0≤θ) :
    width c β θ 0=c*β/Real.sqrt θ := by
  have he : bExponent 0=(1/2:ℝ) := by norm_num [bExponent]
  rw [width,he,Real.rpow_neg hθ,← Real.sqrt_eq_rpow]
  rfl

theorem latent_active_force_bound : ∃ B : ℝ,1≤B ∧
    ∀ (P : Parameters) (n : ℕ) (lambdaExt : ℝ),0≤lambdaExt → ∀ (s : ℝ) (z : Space n),
      ‖gradient (P.activeSlice n lambdaExt s) z‖≤2*C*B*lambdaExt*P.ℓ*P.β*
        width P.c P.β P.θ 0 := by
  obtain ⟨B,hB,hpieces⟩ := actual_piece_budgets
  have hB0 : 0≤B := by linarith
  refine ⟨B,hB,fun P n lambdaExt hlambda s z => ?_⟩
  have hℓ := P.ell_nonneg
  have hβ := P.β_pos
  have hC := C_pos
  have hg (k : ℕ) (hk : k≤levels P.θ) : ‖gradient (P.pieces n k) z‖≤B*P.ℓ*P.β := by
    have hh := (hpieces P n k hk z).2 0
    simp only [Fin.val_zero,zero_add,pow_zero,mul_one] at hh
    rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
      ← GradientJetBounds.gradient_norm_eq] at hh
    exact hh.trans_eq (by dsimp [Parameters.amplitude];field_simp;ring)
  have ht (k : ℕ) (hk : k≤levels P.θ) :
      ‖(lambdaExt*SmallGapProfiles.normal (width P.c P.β P.θ k) s) • gradient (P.pieces n k) z‖≤
        (lambdaExt*C*B*P.ℓ*P.β)*width P.c P.β P.θ k := by
    have hW := width_pos P.c P.β P.θ P.c_pos hβ P.θ_ge_one k
    have hn := (normal_jet_bounds (width P.c P.β P.θ k) s hW).1
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hlambda]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hn hlambda) (hg k hk) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  rw [funext (P.activeSlice_sum n lambdaExt s),finite_weighted_gradient _ _ (P.pieces_contDiff n)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.range (levels P.θ+1),(lambdaExt*C*B*P.ℓ*P.β)*width P.c P.β P.θ k :=
      Finset.sum_le_sum (fun k hk => ht k (by have := Finset.mem_range.mp hk;omega))
    _ = (lambdaExt*C*B*P.ℓ*P.β)*(∑ k ∈ Finset.range (levels P.θ+1),width P.c P.β P.θ k) :=
      (Finset.mul_sum ..).symm
    _ ≤ (lambdaExt*C*B*P.ℓ*P.β)*(2*width P.c P.β P.θ 0) :=
      mul_le_mul_of_nonneg_left (normal_width_sum P.c P.β P.θ P.c_pos.le hβ.le P.θ_ge_one) (by positivity)
    _ = _ := by ring

end Bilevel.ChiFine
