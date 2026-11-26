import Bilevel.PolishedLiteralRawContinuity
import Bilevel.PolishedLiteralReframe

/-! Borel full-gradient reply channel computed from raw disclosed arrays.
Continuity is required only for scalar families; the canonical gradient is
Borel even at invalid arrays, without an orthonormal completion. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteral.Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ U]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace U] [BorelSpace U]
  [MeasurableSpace (FullMeanSpace (X:=X) (U:=U))] [BorelSpace (FullMeanSpace (X:=X) (U:=U))]

abbrev RawArrays := P.MacroColumns × P.MicroColumns
abbrev RawReplyInput := P.RawArrays × FullMeanSpace (X:=X) (U:=U)

theorem rawInactiveLower_gradient_measurable (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ : ℝ) :
    Measurable (fun z : P.RawReplyInput => gradient (P.rawInactiveLower r counts z.1.1 z.1.2 τ) z.2) :=
  ParametricGradient.gradient_measurable
    (fun a : P.RawArrays => P.rawInactiveLower r counts a.1 a.2 τ)
    (P.rawInactiveLower_continuous r counts τ _ _ _
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd)

theorem rawActiveLower_gradient_measurable (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) :
    Measurable (fun z : P.RawReplyInput => gradient (P.rawActiveLower r counts z.1.1 z.1.2) z.2) :=
  ParametricGradient.gradient_measurable
    (fun a : P.RawArrays => P.rawActiveLower r counts a.1 a.2)
    (P.rawActiveLower_continuous r counts _ _ _
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd)

theorem rawExactUpper_gradient_measurable (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) :
    Measurable (fun z : P.RawReplyInput => gradient (P.rawExactUpper r counts z.1.1 z.1.2) z.2) :=
  ParametricGradient.gradient_measurable
    (fun a : P.RawArrays => P.rawExactUpper r counts a.1 a.2)
    (P.rawExactUpper_continuous r counts _ _ _
      (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst) continuous_snd)

theorem rawReply_measurable (r : ℕ) (counts : Fin (P.macroNode.n+1) → ℕ) (τ p : ℝ) (coin : Bool) :
    Measurable (fun z : P.RawReplyInput => P.rawReply r counts z.1.1 z.1.2 τ p coin z.2) := by
  have hu := P.rawExactUpper_gradient_measurable r counts
  have h0 := P.rawInactiveLower_gradient_measurable r counts τ
  have h1 := P.rawActiveLower_gradient_measurable r counts
  exact hu.prodMk (h0.add ((h1.sub h0).const_smul (if coin then p⁻¹ else 0)))

theorem rawReply_varying_measurable (τ p : ℝ) :
    Measurable (fun z : P.RawReplyInput × (ℕ × (Fin (P.macroNode.n+1) → ℕ) × Bool) =>
      P.rawReply z.2.1 z.2.2.1 z.1.1.1 z.1.1.2 τ p z.2.2.2 z.1.2) :=
  measurable_from_prod_countable (fun s => P.rawReply_measurable s.1 s.2.1 τ p s.2.2)

end Bilevel.PolishedLiteral.Parameters
