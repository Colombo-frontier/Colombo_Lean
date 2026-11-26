import Bilevel.ChiPrimitiveAssembly
import Bilevel.ChiConservativeScalar

/-! The scalar oracle's full gradient is exactly the lower derivative pair
of the same Primitive; its variance uses the source's Euclidean joint norm. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem lower_full_gradient {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (g : Joint X Y → ℝ) (hg : Differentiable ℝ g)
    (he : ∀ x y,P.g x y=g (pack x y)) (z : Joint X Y) :
    gradient g z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd) := by
  have hx : (gradient g z).fst=P.gx z.fst z.snd := by
    have h₁ := (partial_x (hg z).hasGradientAt).gradient
    have h₂ := (P.has_gx z.fst z.snd).gradient
    have heq : (fun x => g (pack x z.snd))=(fun x => P.g x z.snd) := funext (fun x => (he x z.snd).symm)
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  have hy : (gradient g z).snd=P.gy z.fst z.snd := by
    have h₁ := (partial_y (hg z).hasGradientAt).gradient
    have h₂ := (P.has_gy z.fst z.snd).gradient
    have heq : (fun y => g (pack z.fst y))=(fun y => P.g z.fst y) := funext (fun y => (he z.fst y).symm)
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  apply (WithLp.equiv 2 (X×Y)).injective
  exact Prod.ext hx hy

variable [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)]

theorem conservativeOracle_truth {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (g g₀ : Joint X Y → ℝ) (hg : Differentiable ℝ g)
    (he : ∀ x y,P.g x y=g (pack x y))
    (hc : Continuous (gradient g)) (hc₀ : Continuous (gradient g₀))
    {B σ : ℝ} (hB : 0 < B) (henv : ∀ z,‖gradient g z-gradient g₀ z‖ ≤ B)
    (z : Joint X Y) :
    (ChiConservative.freshOracle g g₀ hc hc₀ (σ:=σ) hB henv).truth z=
      pack (P.gx z.fst z.snd) (P.gy z.fst z.snd) :=
  lower_full_gradient P g hg he z

theorem conservativeOracle_joint_variance {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (g g₀ : Joint X Y → ℝ) (hg : Differentiable ℝ g)
    (he : ∀ x y,P.g x y=g (pack x y))
    (hc : Continuous (gradient g)) (hc₀ : Continuous (gradient g₀))
    {B σ : ℝ} (hB : 0 < B) (henv : ∀ z,‖gradient g z-gradient g₀ z‖ ≤ B)
    (z : Joint X Y) :
    let O := ChiConservative.freshOracle g g₀ hc hc₀ (σ:=σ) hB henv
    (∫ b,‖(O.sample z b).fst-P.gx z.fst z.snd‖^2+‖(O.sample z b).snd-P.gy z.fst z.snd‖^2
      ∂BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) ≤ σ^2 := by
  dsimp only
  have hh := (ChiConservative.freshOracle g g₀ hc hc₀ (σ:=σ) hB henv).variance z
  rw [conservativeOracle_truth P g g₀ hg he hc hc₀ hB henv z] at hh
  simpa only [norm_sq] using hh

end Bilevel.ChiPrimitive
