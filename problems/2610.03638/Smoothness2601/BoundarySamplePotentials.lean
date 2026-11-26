import Smoothness2601.BoundaryOracle

/-! Actual fixed two-point sample losses for the boundary f-oracle. -/
noncomputable section
open Bilevel.PrimitiveGeometry
namespace Smoothness2601.BoundaryInstance
open SineGeometry ExtensiveChain HardProfiles
variable {b : Budgets} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (U : Space n →ₗᵢ[ℝ] E) {s : ℝ} (hs : 0 < s)

def splitScaled : Profiles E :=
  (HardProfiles.profiles U).scaled (amp := s^2/spatialConstant b) (scale := s/spatialConstant b)
    (by have := spatialConstant_pos b; positivity) (by have := spatialConstant_pos b; positivity)

def basePotential : Joint E ℝ → ℝ := upper (splitScaled (b := b) U hs).A 0

def informativePotential (hμL : b.μ ≤ b.L₁) (z : Joint E ℝ) : ℝ :=
  (population U hs hμL).f z-basePotential (b := b) U hs z

theorem base_hasGradient (z : Joint E ℝ) :
    HasGradientAt (basePotential (b := b) U hs) (upperGradient (splitScaled (b := b) U hs).gA 0 z) z :=
  upper_hasGradientAt _ _ (splitScaled (b := b) U hs).has_A 0 z

theorem signal_decomposition (hμL : b.μ ≤ b.L₁) (z : Joint E ℝ) :
    (population U hs hμL).grad_f z-upperGradient (splitScaled (b := b) U hs).gA 0 z =
      signalField (b := b) U hs z.fst := by
  have he : (s^2/spatialConstant b)/(s/spatialConstant b) = s := by
    field_simp [(spatialConstant_pos b).ne',hs.ne']
    all_goals ring
  apply (WithLp.equiv 2 (E × ℝ)).injective
  apply Prod.ext
  · change ((s^2/spatialConstant b)/(s/spatialConstant b)) •
      ((HardProfiles.profiles U).gA ((s/spatialConstant b)⁻¹ • z.fst)+
        (HardProfiles.profiles U).gB ((s/spatialConstant b)⁻¹ • z.fst))-
      ((s^2/spatialConstant b)/(s/spatialConstant b)) •
        (HardProfiles.profiles U).gA ((s/spatialConstant b)⁻¹ • z.fst) = _
    rw [he,smul_add,add_sub_cancel_left]
    rfl
  · change (0:ℝ)-0 = 0
    ring

theorem informative_hasGradient (hμL : b.μ ≤ b.L₁) (z : Joint E ℝ) :
    HasGradientAt (informativePotential U hs hμL) (signalField (b := b) U hs z.fst) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  rw [← signal_decomposition U hs hμL z,map_sub]
  exact ((population U hs hμL).has_f z).hasFDerivAt.sub (base_hasGradient (b := b) U hs z).hasFDerivAt

def samplePotential (hμL : b.μ ≤ b.L₁) (p : ℝ) (coin : Bool) : Joint E ℝ → ℝ :=
  BernoulliOracle.sampleLoss p (basePotential (b := b) U hs) (informativePotential U hs hμL) coin

theorem samplePotential_hasGradient (hμL : b.μ ≤ b.L₁) (p : ℝ) (coin : Bool) (z : Joint E ℝ) :
    HasGradientAt (samplePotential U hs hμL p coin)
      (BernoulliOracle.response p (upperGradient (splitScaled (b := b) U hs).gA 0 z) (signalField (b := b) U hs z.fst) coin) z :=
  BernoulliOracle.sampleLoss_hasGradient (base_hasGradient (b := b) U hs z) (informative_hasGradient U hs hμL z) p coin

theorem sample_is_gradient (hμL : b.μ ≤ b.L₁) (p : ℝ) (coin : Bool) (x : E) (y : ℝ) :
    FreshUpperBernoulli.sample (population U hs hμL) (fun q => signalField (b := b) U hs q.2.1) p (false,(x,y)) coin =
      gradient (samplePotential U hs hμL p coin) (pack x y) := by
  rw [FreshUpperBernoulli.sample_upper,(samplePotential_hasGradient U hs hμL p coin (pack x y)).gradient]
  congr 1
  change (population U hs hμL).grad_f (pack x y)-signalField (b := b) U hs x = _
  have he := signal_decomposition U hs hμL (pack x y)
  change (population U hs hμL).grad_f (pack x y)-upperGradient (splitScaled (b := b) U hs).gA 0 (pack x y) =
    signalField (b := b) U hs x at he
  rw [← he,sub_sub_cancel]

end Smoothness2601.BoundaryInstance
