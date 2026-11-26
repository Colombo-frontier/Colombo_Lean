import Bilevel.ChiExtensionReadout
import Bilevel.ChiExtensionCalibration

/-! Exact normal-gradient norm of the upper readout, including the source's
2J coordinates and d=L/(4 sqrt(2J)) normalization. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiExtension

def normalOnes (s : ℕ) : Normals s := (WithLp.equiv 2 (Fin s → ℝ)).symm (fun _ => 1)

theorem normalOnes_apply (s : ℕ) (i : Fin s) : normalOnes s i=1 := rfl

theorem normalOnes_norm (s : ℕ) : ‖normalOnes s‖=Real.sqrt (s:ℝ) := by
  rw [EuclideanSpace.norm_eq]
  simp only [normalOnes_apply,norm_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem normalOnes_toDual (s : ℕ) : InnerProductSpace.toDual ℝ (Normals s) (normalOnes s)=normalReadout s := by
  ext q
  rw [InnerProductSpace.toDual_apply,normalReadout_apply,EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct,normalOnes]

theorem normalReadout_hasGradientAt (s : ℕ) (q : Normals s) : HasGradientAt (normalReadout s) (normalOnes s) q := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  rw [normalOnes_toDual]
  exact (normalReadout s).hasFDerivAt

theorem weightedReadout_hasGradientAt (s : ℕ) (d : ℝ) (q : Normals s) :
    HasGradientAt (fun r : Normals s => d*normalReadout s r) (d • normalOnes s) q := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [map_smul] using ((normalReadout_hasGradientAt s q).hasFDerivAt.const_mul d)

theorem weightedReadout_gradient_norm (s : ℕ) (d : ℝ) (q : Normals s) :
    ‖gradient (fun r : Normals s => d*normalReadout s r) q‖=|d| * Real.sqrt (s:ℝ) := by
  rw [(weightedReadout_hasGradientAt s d q).gradient,norm_smul,Real.norm_eq_abs,normalOnes_norm]

theorem source_readout_gradient_norm {L : ℝ} (hL : 0<L) (J : ℕ) (hJ : 1≤J) (q : Normals (2*J)) :
    ‖gradient (fun r : Normals (2*J) => ChiExtensionCalibration.normalCoefficient L J*normalReadout (2*J) r) q‖=L/4 := by
  rw [weightedReadout_gradient_norm,abs_of_pos (ChiExtensionCalibration.normalCoefficient_pos hL hJ)]
  norm_num only [Nat.cast_mul,Nat.cast_ofNat]
  exact ChiExtensionCalibration.normalCoefficient_norm J hJ

end Bilevel.ChiExtension
