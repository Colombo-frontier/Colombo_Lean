import Smoothness2601.SineOracle

/-! The oracle observations are actual gradients of two fixed scalar losses.
The full f-gradient is exact for both coin values. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.SineGeometry.Profiles
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (F : Profiles X) {b : Budgets} (S : F.Calibration b)

def inactivePotential (z : Joint X ℝ) : ℝ := S.m/2*z.snd^2

def informativePotential (z : Joint X ℝ) : ℝ :=
  -S.m*S.a*S.h*F.B z.fst*Real.sin (z.snd/S.h)

theorem inactive_hasGradient (z : Joint X ℝ) :
    HasGradientAt (F.inactivePotential S) (pack (0:X) (S.m*z.snd)) z := by
  have he : lower F.B S.m 0 S.h = F.inactivePotential S := by
    funext w
    simp [lower,inactivePotential,SineLift.lowerObjective]
  have hd := lower_hasGradientAt F.B F.gB F.has_B S.m 0 S.h_pos.ne' z
  rw [he] at hd
  simpa [lowerGradient,SineLift.lowerGradient] using hd

theorem informative_hasGradient (z : Joint X ℝ) :
    HasGradientAt (F.informativePotential S) (F.signal S.m S.a S.h z) z := by
  have hd := ((F.population S).has_g z).hasFDerivAt.sub (F.inactive_hasGradient S z).hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hd using 1
  · funext w
    change -S.m*S.a*S.h*F.B w.fst*Real.sin (w.snd/S.h) =
      (S.m/2*w.snd^2-S.m*S.a*S.h*F.B w.fst*Real.sin (w.snd/S.h))-S.m/2*w.snd^2
    ring
  · rw [show (F.population S).grad_g z = pack (0:X) (S.m*z.snd)+F.signal S.m S.a S.h z from
      F.lowerGradient_decompose S.m S.a S.h z,map_add,add_sub_cancel_left]

def samplePotential (p : ℝ) (coin : Bool) : Joint X ℝ → ℝ :=
  BernoulliOracle.sampleLoss p (F.inactivePotential S) (F.informativePotential S) coin

theorem samplePotential_hasGradient (p : ℝ) (coin : Bool) (z : Joint X ℝ) :
    HasGradientAt (F.samplePotential S p coin)
      (BernoulliOracle.response p (pack (0:X) (S.m*z.snd)) (F.signal S.m S.a S.h z) coin) z :=
  BernoulliOracle.sampleLoss_hasGradient (F.inactive_hasGradient S z) (F.informative_hasGradient S z) p coin

theorem samplePotential_source_formula (p : ℝ) (coin : Bool) (z : Joint X ℝ) :
    F.samplePotential S p coin z = S.m/2*z.snd^2-
      (if coin then p⁻¹ else 0)*S.m*S.a*S.h*F.B z.fst*Real.sin (z.snd/S.h) := by
  unfold samplePotential BernoulliOracle.sampleLoss inactivePotential informativePotential
  ring

theorem sample_lower_is_gradient (p : ℝ) (coin : Bool) (x : X) (y : ℝ) :
    FreshBernoulli.sample (F.population S)
      (fun q => F.signal S.m S.a S.h (pack q.2.1 q.2.2)) p (true,(x,y)) coin =
        gradient (F.samplePotential S p coin) (pack x y) := by
  rw [FreshBernoulli.sample_lower,(F.samplePotential_hasGradient S p coin (pack x y)).gradient]
  congr 1
  change lowerGradient F.B F.gB S.m S.a S.h (pack x y)-F.signal S.m S.a S.h (pack x y) = _
  rw [F.lowerGradient_decompose,add_sub_cancel_right]

end Smoothness2601.SineGeometry.Profiles
