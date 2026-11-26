import Bilevel.PolishedLiteralGlobalCertificate
import Bilevel.PolishedLiteralGapRate
import Bilevel.PolishedLiteralGapCoercive

/-! The gap and coercivity clauses of hier:thm:mean, for the actual literal
mean with the source's numerical parameter calibration. The bound is
linear in S=n_macro+1, with no hidden dimension or kappa dependence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Filter
open scoped Topology
namespace Bilevel.PolishedLiteral.Parameters
open PrimitiveGeometry ChiBoundedChain
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (P : Parameters (X:=X) (U:=U))

def sourceGapConstant (A ζ : ℝ) : ℝ :=
  Real.exp 1*gaussianBound*(1+2*Real.exp 1)+3*Real.exp 1*A*(3*ζ+1)

omit [CompleteSpace X] [CompleteSpace U] in
theorem sourceGapConstant_nonneg (A ζ : ℝ) (hA : 0≤A) (hζ : 0≤ζ) :
    0≤sourceGapConstant A ζ := by
  unfold sourceGapConstant gaussianBound
  positivity

theorem source_calibrated_gap {Km A Cu ζ κ : ℝ}
    (hcal : P.SourceCalibration Km A Cu ζ κ)
    (hA : 0≤A) (hζ : 0≤ζ) (hζ1 : ζ≤1) (hκ : 4≤κ)
    (hL : 0<P.L) (hb : 0<P.macroNode.width) :
    P.outerMean κ 0-sInf (Set.range (P.outerMean κ))≤
      sourceGapConstant A ζ*((P.macroNode.n:ℝ)+1)*P.L*P.macroNode.width^2 := by
  have hk : 0<κ := by linarith
  have hζ6 : ζ^6≤1 := pow_le_one₀ hζ hζ1
  have hfloor : (Nat.floor (ζ^6*κ^2):ℝ)≤ζ^6*κ^2 := Nat.floor_le (by positivity)
  have hcount : (P.n:ℝ)+1≤2*κ^2 := by
    have hn : (P.n:ℝ)≤(Nat.floor (ζ^6*κ^2):ℝ) := by
      exact_mod_cast (show P.n≤Nat.floor (ζ^6*κ^2) by rw [hcal.microDimension];omega)
    have hz := mul_le_mul_of_nonneg_right hζ6 (sq_nonneg κ)
    nlinarith only [hn,hfloor,hz,hκ]
  have hscale : κ*P.β=P.macroNode.width := by
    rw [hcal.microWidth]
    field_simp
  have hforce : P.force=1*P.L*P.β := by
    rw [hcal.force,hcal.microWidth,one_mul]
  have ht := P.source_gap_rate κ 2 ζ 1 (by linarith) (by norm_num) hζ (by norm_num)
    hL.le (by rw [hcal.receiver];exact hA) (by rw [hcal.microWidth];positivity)
    hscale hcal.macroEll hcount hcal.microRadial hforce (by rw [hcal.macroRadial];positivity)
  simpa only [hcal.receiver,sourceGapConstant,mul_comm (Real.exp 1) (2:ℝ)] using ht

theorem source_calibrated_coercive [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
    {Km A Cu ζ κ : ℝ} (hcal : P.SourceCalibration Km A Cu ζ κ)
    (hKm : 0<Km) (hA : 0≤A) (hCu : 0<Cu) (hζ : 0<ζ) (hκ : 0<κ)
    (hL : 0<P.L) (hb : 0<P.macroNode.width) :
    Tendsto (P.outerMean κ) (cocompact (Joint X U)) atTop := by
  apply P.outerMean_coercive κ hκ
  · rw [hcal.macroEll];exact hL.le
  · exact hL.le
  · rw [hcal.receiver];exact hA
  · rw [hcal.microRadial];positivity
  · rw [hcal.macroRadial];positivity
  · rw [hcal.force];positivity
  · rw [hcal.microWidth];positivity
  · exact hb
  · rw [hcal.microRadius];positivity
  · rw [hcal.macroRadius]
    have hs : 0<Real.sqrt ((P.macroNode.n:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
    positivity

end Bilevel.PolishedLiteral.Parameters
