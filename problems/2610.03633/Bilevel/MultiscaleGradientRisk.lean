import Bilevel.MultiscaleMeanCertificate
import Bilevel.WrappedChainConstants

/-! The actual hyperobjective has a uniform finite gradient bound and the source end-game margin. -/
noncomputable section
namespace Bilevel.MultiscaleMean.Parameters
open ZeroChain WrappedChain RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n : ℕ} (P : Parameters (E := E) n)

theorem outer_gradient_norm_le (B : ℝ) (hB : 0 ≤ B)
    (hchain : ∀ z : Space n, ∀ j, |gradient (ZeroChain.value n) z j| ≤ B) (u : E) :
    ‖gradient P.outer u‖ ≤ P.amplitude/P.β*B*Real.sqrt (n+1:ℕ)+P.ν*P.R := by
  have hR : 0 < P.R := P.β_pos.trans_le P.β_le_R
  rw [show P.outer = WrappedChain.value n P.amplitude P.β P.ν P.R P.U from rfl,
    (value_hasGradientAt n P.amplitude P.β P.ν P.R hR P.U u).gradient]
  exact wrappedGradient_bound P.ν P.R _ P.ν_nonneg hR u _
    (carriedGradient_norm_bound n P.amplitude P.β P.R B P.amplitude_nonneg P.β_pos hB hchain P.U u)

theorem realized_gradient_norm_le (B : ℝ) (hB : 0 ≤ B)
    (hchain : ∀ z : Space n, ∀ j, |gradient (ZeroChain.value n) z j| ≤ B) (x : E) :
    ‖gradient P.realized x‖ ≤ (P.L/P.μ)*(P.amplitude/P.β*B*Real.sqrt (n+1:ℕ)+P.ν*P.R) := by
  rw [(P.realized_hasGradientAt x).gradient,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos P.L_pos P.μ_pos)]
  exact mul_le_mul_of_nonneg_left (P.outer_gradient_norm_le B hB hchain _)
    (div_pos P.L_pos P.μ_pos).le

theorem source_endgame (B : ℝ) (hB : 0 ≤ B)
    (hchain : ∀ z : Space n, ∀ j, |gradient (ZeroChain.value n) z j| ≤ B)
    (hη : 0 < P.η) (hR : P.R=48*(B+1)*P.β*Real.sqrt (n+1:ℕ))
    (hν : P.ν=P.η*P.L/24) (x : E)
    (hlast : |coordinates n P.R P.U ((P.L/P.μ) • x) (Fin.last n)| < P.β) :
    (P.L/P.μ)*P.η*P.L*P.β/2 ≤ ‖gradient P.realized x‖ := by
  have ha : 0 < P.amplitude := by dsimp [amplitude]; have := P.L_pos; have := P.β_pos; positivity
  have hν' : P.ν=P.amplitude/(24*P.β^2) := by
    rw [hν]
    dsimp [amplitude]
    field_simp [P.β_pos.ne']
    ring
  have hh := explicit_endgame n P.amplitude P.β B ha P.β_pos hB hchain P.U ((P.L/P.μ) • x)
  rw [← hR,← hν'] at hh
  have hlow := hh hlast
  rw [(P.realized_hasGradientAt x).gradient,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos P.L_pos P.μ_pos)]
  have h := mul_le_mul_of_nonneg_left hlow (div_pos P.L_pos P.μ_pos).le
  convert h using 1
  dsimp [amplitude]
  field_simp [P.μ_pos.ne', P.β_pos.ne']
  ring

/-! The numerical margin used by the good-event risk reduction is isolated
from the geometric end-game. This lets the probabilistic layer use the exact
`8*ε` threshold appearing in the manuscript. -/
theorem source_endgame_margin (B ε : ℝ) (hB : 0 ≤ B)
    (hchain : ∀ z : Space n, ∀ j, |gradient (ZeroChain.value n) z j| ≤ B)
    (hη : 0 < P.η) (hR : P.R=48*(B+1)*P.β*Real.sqrt (n+1:ℕ))
    (hν : P.ν=P.η*P.L/24) (hmargin : 8*ε ≤ (P.L/P.μ)*P.η*P.L*P.β/2)
    (x : E)
    (hlast : |coordinates n P.R P.U ((P.L/P.μ) • x) (Fin.last n)| < P.β) :
    8*ε ≤ ‖gradient P.realized x‖ := by
  exact hmargin.trans (P.source_endgame B hB hchain hη hR hν x hlast)

end Bilevel.MultiscaleMean.Parameters
