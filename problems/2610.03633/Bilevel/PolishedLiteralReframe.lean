import Bilevel.PolishedLiteralRawColumns
import Bilevel.PolishedLiteralGlobalCertificate

/-! The raw evaluator depends only on public numerical data. Replacing all
hidden isometries changes the actual instance and leaves the disclosed
scalar and full-gradient reply formulas definitionally unchanged. -/
noncomputable section
namespace Bilevel.PolishedLiteral.Parameters
open ChiBoundedChain
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def reframe (macroFrame : Space P.macroNode.n →ₗᵢ[ℝ] X)
    (microFrames : Fin (P.macroNode.n+1) → Space P.n →ₗᵢ[ℝ] U) : Parameters (X:=X) (U:=U) :=
  { P with macroNode := { P.macroNode with frame := macroFrame }, frames := microFrames }

@[simp] theorem rawReply_reframe (macroFrame : Space P.macroNode.n →ₗᵢ[ℝ] X)
    (microFrames : Fin (P.macroNode.n+1) → Space P.n →ₗᵢ[ℝ] U)
    (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns)
    (τ p : ℝ) (coin : Bool) :
    (P.reframe macroFrame microFrames).rawReply r counts a b τ p coin=P.rawReply r counts a b τ p coin := rfl

omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem rawInactiveLower_reframe (macroFrame : Space P.macroNode.n →ₗᵢ[ℝ] X)
    (microFrames : Fin (P.macroNode.n+1) → Space P.n →ₗᵢ[ℝ] U)
    (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns) (τ : ℝ) :
    (P.reframe macroFrame microFrames).rawInactiveLower r counts a b τ=P.rawInactiveLower r counts a b τ := rfl

omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem rawActiveLower_reframe (macroFrame : Space P.macroNode.n →ₗᵢ[ℝ] X)
    (microFrames : Fin (P.macroNode.n+1) → Space P.n →ₗᵢ[ℝ] U)
    (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns) :
    (P.reframe macroFrame microFrames).rawActiveLower r counts a b=P.rawActiveLower r counts a b := rfl

omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem rawExactUpper_reframe (macroFrame : Space P.macroNode.n →ₗᵢ[ℝ] X)
    (microFrames : Fin (P.macroNode.n+1) → Space P.n →ₗᵢ[ℝ] U)
    (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (a : P.MacroColumns) (b : P.MicroColumns) :
    (P.reframe macroFrame microFrames).rawExactUpper r counts a b=P.rawExactUpper r counts a b := rfl

omit [CompleteSpace X] [CompleteSpace U] in
@[simp] theorem sourceCalibration_reframe (macroFrame : Space P.macroNode.n →ₗᵢ[ℝ] X)
    (microFrames : Fin (P.macroNode.n+1) → Space P.n →ₗᵢ[ℝ] U) (Km A Cu ζ κ : ℝ) :
    (P.reframe macroFrame microFrames).SourceCalibration Km A Cu ζ κ ↔ P.SourceCalibration Km A Cu ζ κ := by
  constructor <;> intro h <;>
    exact ⟨h.macroEll,h.macroRadial,h.macroRadius,h.microDimension,h.microWidth,h.microRadial,h.microRadius,h.receiver,h.force⟩

end Bilevel.PolishedLiteral.Parameters
