import Bilevel.ChiFineSourceForce

/-! The fixed inactive last-atom replacement retains the pre-wrapper
inverse-square-root variation force bound at every normal argument. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainSchedule SmallGapLiftSupport

theorem gradient_const_mul_C3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ContDiff ℝ 3 f) (a : ℝ) (x : E) :
    gradient (fun y => a*f y) x=a • gradient f x := by
  have hh : HasGradientAt (fun y => a*f y) (a • gradient f x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    simpa only [map_smul] using
      ((hf.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt).const_mul a
  exact hh.gradient

theorem Parameters.inactiveSlice_gradient (P : Parameters) (n : ℕ) (lambdaExt s : ℝ) (z : Space n) :
    gradient (P.inactiveSlice n lambdaExt s) z=gradient (P.activeSlice n lambdaExt s) z-
      (lambdaExt*SmallGapProfiles.normal P.finalWidth s) • gradient (P.residualDifference n) z := by
  have he : P.inactiveSlice n lambdaExt s=(fun x => P.activeSlice n lambdaExt s x-
      (lambdaExt*SmallGapProfiles.normal P.finalWidth s)*P.residualDifference n x) := by
    funext x
    dsimp [Parameters.inactiveSlice,Parameters.activeSlice,Parameters.inactiveCoupling,
      Parameters.signal]
    simp only [CompensatedMean.uProj_pack,CompensatedMean.sProj_pack]
    ring
  have hr : ContDiff ℝ 3 (P.residualDifference n) := signalResidual_contDiff n P.ℓ P.β P.signalResolution
  rw [he,gradient_sub_C3 (P.activeSlice_contDiff n lambdaExt s) (contDiff_const.mul hr),
    gradient_const_mul_C3 hr]

theorem latent_inactive_force_bound : ∃ B : ℝ,1≤B ∧
    ∀ (P : Parameters) (n : ℕ) (lambdaExt : ℝ),0≤lambdaExt → ∀ (s : ℝ) (z : Space n),
      ‖gradient (P.inactiveSlice n lambdaExt s) z‖≤2*C*B*lambdaExt*P.ℓ*P.β*
        width P.c P.β P.θ 0 := by
  obtain ⟨A,hA,ha⟩ := latent_active_force_bound
  obtain ⟨B,hB,hb⟩ := signal_residual_bounds
  refine ⟨A+B,by linarith,fun P n lambdaExt hlambda s z => ?_⟩
  have hℓ := P.ell_nonneg
  have hβ := P.β_pos
  have hC := C_pos
  have hτ := P.signalResolution_pos
  have hw := P.finalWidth_pos
  have hA0 : 0≤A := by linarith
  have hB0 : 0≤B := by linarith
  have hg : ‖gradient (P.residualDifference n) z‖≤2*B*P.ℓ*P.β := by
    have hj := (hb n P.ℓ P.β P.signalResolution hℓ hβ hτ
      (by linarith [P.signalResolution_small]) z).2 0
    simp only [Fin.val_zero,zero_add,pow_zero,div_one] at hj
    rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero,
      ← GradientJetBounds.gradient_norm_eq] at hj
    exact hj
  have hn := (normal_jet_bounds P.finalWidth s hw).1
  have hws : P.finalWidth≤width P.c P.β P.θ 0 :=
    width_antitone P.c P.β P.θ P.c_pos.le hβ.le P.θ_ge_one 0 _ (Nat.zero_le _)
  have hs : ‖(lambdaExt*SmallGapProfiles.normal P.finalWidth s) •
      gradient (P.residualDifference n) z‖≤2*C*B*lambdaExt*P.ℓ*P.β*width P.c P.β P.θ 0 := by
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hlambda]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hn hlambda) hg (norm_nonneg _) (by positivity)).trans
    calc
      _ = (2*C*B*lambdaExt*P.ℓ*P.β)*P.finalWidth := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hws (by positivity)
  rw [P.inactiveSlice_gradient]
  exact (norm_sub_le _ _).trans ((add_le_add (ha P n lambdaExt hlambda s z) hs).trans_eq (by ring))

end Bilevel.ChiFine
