import Bilevel.ChiCoarseArithmetic
import Bilevel.CompensatedMeanJets

/-! Actual coarse normal extension with the source width h*N^(1/3).
All mixed tangent/normal derivatives are included. The visible input ledger
is supplied by the separately proved actual selected-carrier construction. -/
noncomputable section
namespace Bilevel.ChiCoarse
open CompensatedMean SmallGapProfiles SmallGapLiftSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def extension (f : E → ℝ) (W : ℝ) (y : LowerSpace E) : ℝ :=
  f (uProj E y)*normal W (sProj E y)

def singleData (f : E → ℝ) (hf : ContDiff ℝ 3 f) (W : ℝ) (hW : 0<W) : Data (E:=E) where
  μ := 1
  L := 1
  J := 0
  r := f
  A := fun _ => 0
  e := fun _ => f
  w := fun _ => W
  r_smooth := hf
  A_smooth := contDiff_const
  e_smooth := fun _ => hf
  w_pos := fun _ _ => hW
  decomposition := by intro u;simp

theorem extension_contDiff {f : E → ℝ} (hf : ContDiff ℝ 3 f) {W : ℝ} (hW : 0<W) :
    ContDiff ℝ 3 (extension f W) :=
  (hf.comp (uProj E).contDiff).mul ((normal_contDiff W hW).comp (sProj E).contDiff)

theorem extension_zero_trace (f : E → ℝ) {W : ℝ} (hW : 0<W) (z : E) :
    extension f W (pack E z 0 0)=0 := by
  simp only [extension,uProj_pack,sProj_pack,normal_core W 0 hW (by rw [abs_zero];positivity),mul_zero]

theorem extension_normal_trace (f : E → ℝ) {W : ℝ} (hW : 0<W) (z : E) :
    HasDerivAt (fun s => extension f W (pack E z s 0)) (f z) 0 := by
  have hd := ((normal_contDiff W hW).differentiable (by norm_num) 0).hasDerivAt
  rw [normal_deriv_core W 0 hW (by rw [abs_zero];positivity)] at hd
  simpa only [extension,uProj_pack,sProj_pack,mul_one] using hd.const_mul (f z)

theorem actual_coarse_extension_jets {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {N ℓ h M : ℝ} (hN : 1 ≤ N) (hℓ : 0 ≤ ℓ) (hh : 0<h) (hM : 0 ≤ M)
    (hb : ∀ z,|f z| ≤ M*N*ℓ*h^2 ∧
      ‖iteratedFDeriv ℝ 1 f z‖ ≤ M*ℓ*h*Real.sqrt N ∧
      ‖iteratedFDeriv ℝ 2 f z‖ ≤ M*ℓ ∧
      ‖iteratedFDeriv ℝ 3 f z‖ ≤ M*ℓ/h) (y : LowerSpace E) :
    ‖iteratedFDeriv ℝ 2 (extension f (h*N^(1/3:ℝ))) y‖ ≤
        4*C*M*ℓ*h*(N^(1/3:ℝ))^2 ∧
    ‖iteratedFDeriv ℝ 3 (extension f (h*N^(1/3:ℝ))) y‖ ≤
        8*C*M*ℓ*N^(1/3:ℝ) := by
  have hNp : 0<N := by linarith
  have hW : 0<h*N^(1/3:ℝ) := mul_pos hh (Real.rpow_pos_of_pos hNp _)
  let D := singleData f hf (h*N^(1/3:ℝ)) hW
  have hD : D.J=0 := rfl
  have hs2 := D.couplingTerm_second_bound 0 (by rw [hD]) y
    (M*N*ℓ*h^2) (M*ℓ*h*Real.sqrt N) (M*ℓ) (by positivity) (by positivity) (by positivity)
    (hb _).1 (hb _).2.1 (hb _).2.2.1
  have hs3 := D.couplingTerm_third_bound 0 (by rw [hD]) y
    (M*N*ℓ*h^2) (M*ℓ*h*Real.sqrt N) (M*ℓ) (M*ℓ/h)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (hb _).1 (hb _).2.1 (hb _).2.2.1 (hb _).2.2.2
  have ht2 := coarse_second_blocks hN hℓ hh hM
  have ht3 := coarse_third_blocks hN hℓ hh hM
  constructor
  · exact hs2.trans ((mul_le_mul_of_nonneg_left ht2 C_pos.le).trans_eq (by ring))
  · exact hs3.trans ((mul_le_mul_of_nonneg_left ht3 C_pos.le).trans_eq (by ring))

end Bilevel.ChiCoarse
