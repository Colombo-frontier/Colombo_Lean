import Bilevel.ChiFineSignalBounds

/-! The globally fixed inactive fine potential: only the last atom is
replaced by e_last-(R-R_tau), with tau=w_last/8. -/
noncomputable section
namespace Bilevel.ChiFine.Parameters
open ChiBoundedChain ZeroChainSchedule CompensatedMean SmallGapProfiles
variable (P : Parameters)

def finalWidth : ℝ := width P.c P.β P.θ (levels P.θ)
def signalResolution : ℝ := P.finalWidth/8
def residualDifference (n : ℕ) : Space n → ℝ := signalResidual n P.ℓ P.β P.signalResolution

theorem finalWidth_pos : 0<P.finalWidth :=
  width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one _

theorem signalResolution_pos : 0<P.signalResolution := div_pos P.finalWidth_pos (by norm_num)

theorem signalResolution_small : P.signalResolution ≤ P.β/1024 := by
  have hh := P.normal_width_small (levels P.θ)
  change P.finalWidth ≤ P.β/128 at hh
  dsimp [signalResolution]
  linarith

def signal (n : ℕ) (lambdaExt : ℝ) (y : LowerSpace (Space n)) : ℝ :=
  lambdaExt*P.residualDifference n (uProj (Space n) y)*normal P.finalWidth (sProj (Space n) y)

def inactiveCoupling (n : ℕ) (lambdaExt : ℝ) (y : LowerSpace (Space n)) : ℝ :=
  P.coupling n lambdaExt y-P.signal n lambdaExt y

theorem signal_contDiff (n : ℕ) (lambdaExt : ℝ) : ContDiff ℝ 3 (P.signal n lambdaExt) :=
  (contDiff_const.mul ((signalResidual_contDiff n P.ℓ P.β P.signalResolution).comp
    (uProj (Space n)).contDiff)).mul ((normal_contDiff P.finalWidth P.finalWidth_pos).comp
      (sProj (Space n)).contDiff)

theorem inactiveCoupling_contDiff (n : ℕ) (lambdaExt : ℝ) : ContDiff ℝ 3 (P.inactiveCoupling n lambdaExt) :=
  (P.coupling_contDiff n lambdaExt).sub (P.signal_contDiff n lambdaExt)

theorem inactiveCoupling_source (n : ℕ) (lambdaExt : ℝ) (y : LowerSpace (Space n)) :
    P.inactiveCoupling n lambdaExt y=lambdaExt*((∑ j ∈ Finset.range (levels P.θ),
      P.pieces n j (uProj (Space n) y)*normal (width P.c P.β P.θ j) (sProj (Space n) y))+
      (P.pieces n (levels P.θ) (uProj (Space n) y)-P.residualDifference n (uProj (Space n) y))*
        normal P.finalWidth (sProj (Space n) y)) := by
  simp only [inactiveCoupling,coupling,CompensatedMean.Data.coupling,CompensatedMean.Data.couplingTerm,
    data,Finset.sum_range_succ,signal,finalWidth]
  ring

theorem signal_normal_trace (n : ℕ) (lambdaExt : ℝ) (z : Space n) :
    HasDerivAt (fun s => P.signal n lambdaExt (pack (Space n) z s 0))
      (lambdaExt*P.residualDifference n z) 0 := by
  have hp := P.finalWidth_pos
  have hd := ((normal_contDiff P.finalWidth hp).differentiable (by norm_num) 0).hasDerivAt
  rw [SmallGapLiftSupport.normal_deriv_core P.finalWidth 0 hp (by rw [abs_zero];positivity)] at hd
  have hh := hd.const_mul (lambdaExt*P.residualDifference n z)
  simpa only [signal,uProj_pack,sProj_pack,mul_one] using hh

theorem inactive_normal_trace (n : ℕ) (lambdaExt : ℝ) (z : Space n) :
    HasDerivAt (fun s => P.inactiveCoupling n lambdaExt (pack (Space n) z s 0))
      (lambdaExt*flatFrontier n P.ℓ P.β P.signalResolution z) 0 := by
  have hh := (P.coupling_normal_trace n lambdaExt z).sub (P.signal_normal_trace n lambdaExt z)
  convert hh using 1
  dsimp [residualDifference,signalResidual]
  ring

theorem inactive_zero_trace (n : ℕ) (lambdaExt : ℝ) (z : Space n) :
    P.inactiveCoupling n lambdaExt (pack (Space n) z 0 0)=0 := by
  have hp := P.finalWidth_pos
  rw [inactiveCoupling,P.coupling_zero_trace]
  simp only [signal,uProj_pack,sProj_pack,
    normal_core P.finalWidth 0 hp (by rw [abs_zero];positivity),mul_zero,sub_zero]

end Bilevel.ChiFine.Parameters
