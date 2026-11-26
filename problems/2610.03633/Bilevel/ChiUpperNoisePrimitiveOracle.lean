import Bilevel.ChiUpperNoisePrimitive
import Bilevel.ChiPrimitiveOracle

/-! Full upper/lower SFO pair for the same Primitive: the upper sample
is a fixed conservative Bernoulli scalar, and every lower sample is exact. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiUpperNoise
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

def HasUpperNoiseOracle {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f f₀ g : Joint X Y → ℝ) (B : ℝ) : Prop :=
  ∀ [MeasurableSpace (Joint X Y)] [BorelSpace (Joint X Y)] [SecondCountableTopology (Joint X Y)] (σ : ℝ),
  ∃ hB : 0<B,
  ∃ Of : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
    (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ,
  ∃ Og : FreshOracle.Oracle (Query:=Joint X Y) (E:=Joint X Y)
    (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) 0,
    (∀ z,Of.truth z=pack (P.fx z.fst z.snd) (P.fy z.fst z.snd)) ∧
    (∀ z coin,Of.sample z coin=gradient (ChiConservative.samplePotential f f₀ (BernoulliOracle.probability B σ) coin) z) ∧
    (∀ z,Og.truth z=pack (P.gx z.fst z.snd) (P.gy z.fst z.snd)) ∧
    (∀ z coin,Og.sample z coin=gradient g z)

theorem upper_full_gradient {μ Lf Lg Cf ρ : ℝ}
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (f : Joint X Y → ℝ) (hf : Differentiable ℝ f)
    (he : ∀ x y,P.f x y=f (pack x y)) (z : Joint X Y) :
    gradient f z=pack (P.fx z.fst z.snd) (P.fy z.fst z.snd) := by
  have hx : (gradient f z).fst=P.fx z.fst z.snd := by
    have h₁ := (partial_x (hf z).hasGradientAt).gradient
    have h₂ := (P.has_fx z.fst z.snd).gradient
    have heq : (fun x => f (pack x z.snd))=(fun x => P.f x z.snd) := funext (fun x => (he x z.snd).symm)
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  have hy : (gradient f z).snd=P.fy z.fst z.snd := by
    have h₁ := (partial_y (hf z).hasGradientAt).gradient
    have h₂ := (P.has_fy z.fst z.snd).gradient
    have heq : (fun y => f (pack z.fst y))=(fun y => P.f z.fst y) := funext (fun y => (he z.fst y).symm)
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  apply (WithLp.equiv 2 (X×Y)).injective
  exact Prod.ext hx hy

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] in
theorem direct_hasUpperNoiseOracle (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {μ Lf Lg Cf ρg B : ℝ} (hB : 0<B) (hb : ∀ z,‖gradient (signal m M D) z‖≤B)
    (P : Model.Primitive (X:=Joint E (Blocks m F)) (Y:=Blocks m F) μ Lf Lg Cf ρg)
    (hf : ∀ x u,P.f x u=core m M ν D ρ R (pack x.fst u))
    (g : Queries E (Blocks m F) → ℝ) (hg : ContDiff ℝ 3 g)
    (hPg : ∀ x u,P.g x u=g (pack x u)) :
    HasUpperNoiseOracle P (fullCore m M ν D ρ R) (fullInactiveCore m M ν D ρ R) g B := by
  intro instM instB instS σ
  let Of := directFreshOracle m M ν D ρ R (σ:=σ) hB hb
  let Og : FreshOracle.Oracle (Query:=Queries E (Blocks m F)) (E:=Queries E (Blocks m F))
      (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) 0 :=
    { truth := gradient g
      sample := fun z _ => gradient g z
      truth_measurable := (GradientJetBounds.gradient_contDiff hg).continuous.measurable
      sample_measurable := (GradientJetBounds.gradient_contDiff hg).continuous.measurable.comp measurable_fst
      square_integrable := by intro z; simp
      mean := by intro z; simp
      variance := by intro z; simp }
  refine ⟨hB,Of,Og,?_,directFreshOracle_conservative m M ν D ρ R hB hb,?_,fun _ _ => rfl⟩
  · intro z
    exact upper_full_gradient P (fullCore m M ν D ρ R)
      ((fullCore_contDiff m M ν D ρ R).differentiable (by norm_num)) hf z
  · intro z
    exact ChiPrimitive.lower_full_gradient P g (hg.differentiable (by norm_num)) hPg z

end Bilevel.ChiUpperNoise
