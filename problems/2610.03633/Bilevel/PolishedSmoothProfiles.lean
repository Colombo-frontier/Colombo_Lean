import Bilevel.SmallGapLiftSupport
import Bilevel.ZeroChainFlatteningCutoff
import Bilevel.PolishedLiteralNormal
import Bilevel.PolishedLiteralFlattenCutoff

/-! The working canonical normal and flattening profiles are the same
genuine C-infinity choices as the literal source construction. Their old
C3-facing interfaces remain valid, with actual compactness-derived bounds. -/
noncomputable section
namespace Bilevel.PolishedSmoothProfiles

theorem normal_eq_literal {w : ℝ} (hw : w≠0) :
    SmallGapProfiles.normal w=PolishedLiteral.normalAtWidth w := by
  funext s
  dsimp only [SmallGapProfiles.normal,PolishedLiteral.normalAtWidth,PolishedLiteral.normal,
    PolishedLiteral.normalCutoff]
  field_simp

theorem omega_eq_literal :
    ZeroChainFlatteningCutoff.omega=PolishedLiteralFlattenCutoff.omega := by
  funext t
  dsimp only [ZeroChainFlatteningCutoff.omega,PolishedLiteralFlattenCutoff.omega,
    ChiBoundedChain.coordinateCutoff]
  congr 1
  ring

theorem normal_smooth (w : ℝ) (k : ℕ) : ContDiff ℝ k (SmallGapProfiles.normal w) :=
  SmallGapProfiles.normal_contDiff_all w

theorem omega_smooth (k : ℕ) : ContDiff ℝ k ZeroChainFlatteningCutoff.omega :=
  ZeroChainFlatteningCutoff.omega_contDiff_all

theorem normal_profile_properties :
    (∀ k : ℕ,ContDiff ℝ k (SmallGapProfiles.normal 1)) ∧
    (∀ s : ℝ,SmallGapProfiles.normal 1 (-s)= -SmallGapProfiles.normal 1 s) ∧
    HasCompactSupport (SmallGapProfiles.normal 1) ∧
    (∀ s : ℝ,|s|≤1/4 → SmallGapProfiles.normal 1 s=s) := by
  refine ⟨normal_smooth 1,SmallGapProfiles.normal_odd 1,
    SmallGapProfileBounds.normal_compactSupport 1 (by norm_num),?_⟩
  intro s hs
  exact SmallGapProfiles.normal_core 1 s (by norm_num) (by simpa using hs)

end Bilevel.PolishedSmoothProfiles
