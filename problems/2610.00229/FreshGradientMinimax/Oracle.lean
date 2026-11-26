import FreshGradientMinimax.Objective
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The fixed fresh-gradient oracle contract of Definition 3.1, as an actual
Markov kernel on the complete joint Euclidean space. The second moment uses
the Euclidean squared norm even though the product's topology uses max norm. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

structure FreshOracle {dx dy : ℕ} {L μ : ℝ} (O : NCObjective dx dy L μ) (σ : ℝ) where
  kernel : Kernel (Joint dx dy) (Joint dx dy)
  [markov : IsMarkovKernel kernel]
  integrable : ∀ z, Integrable id (kernel z)
  mean : ∀ z, (∫ r, r ∂kernel z) = O.jointGradient z
  square_integrable : ∀ z, Integrable (fun r => jointNormSq (r - O.jointGradient z)) (kernel z)
  variance_le : ∀ z, (∫ r, jointNormSq (r - O.jointGradient z) ∂kernel z) ≤ σ ^ 2

attribute [instance] FreshOracle.markov

namespace FreshOracle
variable {dx dy : ℕ} {L μ σ : ℝ} {O : NCObjective dx dy L μ}

def exact (O : NCObjective dx dy L μ) (σ : ℝ) : FreshOracle O σ where
  kernel := Kernel.deterministic O.jointGradient O.jointGradient_continuous.measurable
  integrable := by intro z; exact integrable_dirac
  mean := by intro z; simp [Kernel.deterministic_apply]
  square_integrable := by intro z; exact integrable_dirac
  variance_le := by
    intro z
    simp only [Kernel.deterministic_apply, integral_dirac, sub_self, jointNormSq,
      Prod.fst_zero, Prod.snd_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
    exact sq_nonneg σ

theorem exact_kernel (O : NCObjective dx dy L μ) (σ : ℝ) (z : Joint dx dy) :
    (exact O σ).kernel z = Measure.dirac (O.jointGradient z) := rfl

def weaken (K : FreshOracle O σ) {τ : ℝ} (hστ : σ ^ 2 ≤ τ ^ 2) : FreshOracle O τ where
  kernel := K.kernel
  integrable := K.integrable
  mean := K.mean
  square_integrable := K.square_integrable
  variance_le := fun z => (K.variance_le z).trans hστ

/-- Pulling back through an arbitrary measurable query map retains the exact
conditional response law, including for dense and unbounded query maps. -/
def atQuery {S : Type*} [MeasurableSpace S] (K : FreshOracle O σ)
    (q : S → Joint dx dy) (hq : Measurable q) : Kernel S (Joint dx dy) := K.kernel.comap q hq

instance atQuery_markov {S : Type*} [MeasurableSpace S] (K : FreshOracle O σ)
    (q : S → Joint dx dy) (hq : Measurable q) : IsMarkovKernel (K.atQuery q hq) := by
  unfold atQuery
  infer_instance

theorem atQuery_contract {S : Type*} [MeasurableSpace S] (K : FreshOracle O σ)
    (q : S → Joint dx dy) (hq : Measurable q) (s : S) :
    (∫ r, r ∂K.atQuery q hq s) = O.jointGradient (q s) ∧
    (∫ r, jointNormSq (r - O.jointGradient (q s)) ∂K.atQuery q hq s) ≤ σ ^ 2 :=
  ⟨K.mean (q s), K.variance_le (q s)⟩

end FreshOracle
end FreshGradientMinimax
