import Bilevel.ChiUpperNoiseGeometry
import Bilevel.ChiConservativeScalar
import Bilevel.ChiPrimitiveAssembly

/-! The stochastic coin is in the full upper response. The sample is a
globally fixed scalar on (x,v,u), with zero derivative in spectator v. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev Queries (E U : Type*) [NormedAddCommGroup E] [NormedAddCommGroup U] := Joint (Joint E U) U

def queryProjection {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] :
    Queries E U →L[ℝ] Joint E U :=
  packLinear.comp ((jointFstLinear.comp jointFstLinear).prod jointSndLinear)

omit [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem queryProjection_norm {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] :
    ‖(queryProjection : Queries E U →L[ℝ] Joint E U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖pack q.fst.fst q.snd‖≤1*‖q‖
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq]
  change ‖q.fst.fst‖^2+‖q.snd‖^2≤(‖q.fst.fst‖^2+‖q.fst.snd‖^2)+‖q.snd‖^2
  nlinarith only [sq_nonneg ‖q.fst.snd‖]

def fullCore (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    Queries E (Blocks m F) → ℝ := core m M ν D ρ R ∘ queryProjection

def fullInactiveCore (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    Queries E (Blocks m F) → ℝ := inactiveCore m M ν D ρ R ∘ queryProjection

theorem fullCore_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    ContDiff ℝ 3 (fullCore m M ν D ρ R) :=
  (core_contDiff m M ν D ρ R).comp
    (queryProjection (E:=E) (U:=Blocks m F)).contDiff

theorem fullInactiveCore_contDiff (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) :
    ContDiff ℝ 3 (fullInactiveCore m M ν D ρ R) :=
  (inactiveCore_contDiff m M ν D ρ R).comp
    (queryProjection (E:=E) (U:=Blocks m F)).contDiff

theorem full_informative_gradient_bound (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {B : ℝ} (hb : ∀ z,‖gradient (signal m M D) z‖≤B) (q : Queries E (Blocks m F)) :
    ‖gradient (fullCore m M ν D ρ R) q-gradient (fullInactiveCore m M ν D ρ R) q‖≤B := by
  let π : Queries E (Blocks m F) →L[ℝ] Joint E (Blocks m F) := queryProjection
  have ha := ((fullCore_contDiff m M ν D ρ R).differentiable (by norm_num) q).hasGradientAt
  have hi := ((fullInactiveCore_contDiff m M ν D ρ R).differentiable (by norm_num) q).hasGradientAt
  have hd : HasGradientAt (signal m M D ∘ π)
      (gradient (fullCore m M ν D ρ R) q-gradient (fullInactiveCore m M ν D ρ R) q) q := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    have hh := ha.hasFDerivAt.sub hi.hasFDerivAt
    have he : (fun z => fullCore m M ν D ρ R z-fullInactiveCore m M ν D ρ R z)=
        signal m M D ∘ π := by
      funext z
      dsimp [fullCore,fullInactiveCore,inactiveCore]
      ring
    simpa only [he,map_sub] using hh
  rw [← hd.gradient,GradientJetBounds.gradient_norm_eq,← Composition.norm_first]
  have hj := contraction_jet_bound π (queryProjection_norm (E:=E) (U:=Blocks m F)) (signal_contDiff m M D) q 1 (by norm_num)
  apply hj.trans
  rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq]
  exact hb _

variable (m : ℕ) [MeasurableSpace (Queries E (Blocks m F))] [BorelSpace (Queries E (Blocks m F))]
  [SecondCountableTopology (Queries E (Blocks m F))]

def directFreshOracle (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {B σ : ℝ} (hB : 0<B) (hb : ∀ z,‖gradient (signal m M D) z‖≤B) :
    FreshOracle.Oracle (Query:=Queries E (Blocks m F)) (E:=Queries E (Blocks m F))
      (BernoulliOracle.law (BernoulliOracle.probability B σ) (BernoulliOracle.probability_le_one hB)) σ :=
  ChiConservative.freshOracle (fullCore m M ν D ρ R) (fullInactiveCore m M ν D ρ R)
    (GradientJetBounds.gradient_contDiff (fullCore_contDiff m M ν D ρ R)).continuous
    (GradientJetBounds.gradient_contDiff (fullInactiveCore_contDiff m M ν D ρ R)).continuous hB
    (full_informative_gradient_bound m M ν D ρ R hb)

theorem directFreshOracle_conservative (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    {B σ : ℝ} (hB : 0<B) (hb : ∀ z,‖gradient (signal m M D) z‖≤B)
    (q : Queries E (Blocks m F)) (coin : Bool) :
    (directFreshOracle m M ν D ρ R (σ:=σ) hB hb).sample q coin=
      gradient (ChiConservative.samplePotential (fullCore m M ν D ρ R) (fullInactiveCore m M ν D ρ R)
        (BernoulliOracle.probability B σ) coin) q :=
  ChiConservative.freshOracle_conservative _ _
    ((fullCore_contDiff m M ν D ρ R).differentiable (by norm_num))
    ((fullInactiveCore_contDiff m M ν D ρ R).differentiable (by norm_num)) _ _ hB _ q coin

end Bilevel.ChiUpperNoise
