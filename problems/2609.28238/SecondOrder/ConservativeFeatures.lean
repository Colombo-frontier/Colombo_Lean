import SecondOrder.ConservativeFrontierFormula
import SecondOrder.CoefficientResponse

open MeasureTheory
open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

/-- Public scalar features with hidden signs. The feature functions do not
depend on the hidden block. Different blocks may have different spaces. -/
structure ConservativeFeatureData (T m : ℕ) (E : Fin (T+1) → Type*) (Θ : Type*) where
  offset : (i : Fin (T+1)) → E i → ℝ
  feature : (i : Fin (T+1)) → Fin m → E i → ℝ
  sign : Fin (T+1) → Θ → Fin m → ℝ
  sign_sq : ∀ i θ a, sign i θ a^2=1

variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

namespace ConservativeFeatureData

def population (D : ConservativeFeatureData T m E Θ) (i : Fin (T+1)) (θ : Θ) (y : E i) : ℝ :=
  D.offset i y+∑ a, D.sign i θ a*D.feature i a y

def sample (D : ConservativeFeatureData T m E Θ) (i : Fin (T+1)) {R : ℝ}
    (z : Fin m → SignedCoefficient R) (y : E i) : ℝ :=
  D.offset i y+∑ a, (z a).1*D.feature i a y

def blockLaw (D : ConservativeFeatureData T m E Θ) (i : Fin (T+1)) (θ : Θ)
    (R : ℝ) (hR : 2 ≤ R) : PMF (Fin m → SignedCoefficient R) :=
  finitePiPMF (fun a => coefficientPMF R (D.sign i θ a) hR (D.sign_sq i θ a))

def arrayLaw (D : ConservativeFeatureData T m E Θ) (θ : Fin (T+1) → Θ)
    (R : ℝ) (hR : 2 ≤ R) : PMF (Fin (T+1) → Fin m → SignedCoefficient R) :=
  finitePiPMF (fun i => D.blockLaw i (θ i) R hR)

theorem population_contDiff (D : ConservativeFeatureData T m E Θ)
    (h0 : ∀ i, ContDiff ℝ 2 (D.offset i)) (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a))
    (i : Fin (T+1)) (θ : Θ) : ContDiff ℝ 2 (D.population i θ) :=
  (h0 i).add (ContDiff.sum (fun a _ => contDiff_const.mul (hφ i a)))

theorem sample_contDiff (D : ConservativeFeatureData T m E Θ)
    (h0 : ∀ i, ContDiff ℝ 2 (D.offset i)) (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a))
    (i : Fin (T+1)) {R : ℝ} (z : Fin m → SignedCoefficient R) : ContDiff ℝ 2 (D.sample i z) :=
  (h0 i).add (ContDiff.sum (fun a _ => contDiff_const.mul (hφ i a)))

theorem blockLaw_ne_zero (D : ConservativeFeatureData T m E Θ) (i : Fin (T+1)) (θ : Θ)
    (R : ℝ) (hR : 2 ≤ R) (z : Fin m → SignedCoefficient R) : D.blockLaw i θ R hR z≠0 :=
  finitePiPMF_ne_zero _ (fun a => coefficientPMF_ne_zero R (D.sign i θ a) hR (D.sign_sq i θ a)) z

theorem sample_mean (D : ConservativeFeatureData T m E Θ) (i : Fin (T+1)) (θ : Θ)
    (R : ℝ) (hR : 2 ≤ R) (y : E i) :
    (∫ z, D.sample i z y ∂(D.blockLaw i θ R hR).toMeasure)=D.population i θ y := by
  change (∫ z, D.offset i y+coefficientPotential (fun a => D.feature i a y) z
    ∂(D.blockLaw i θ R hR).toMeasure)=_
  rw [integral_add (integrable_const _) Integrable.of_finite,integral_const]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  rw [blockLaw,coefficientPotential_mean]
  rfl

/-- All coefficient arrays are sampled independently from laws fixed before
the query is chosen. Gates are never part of the sampling law. -/
def loss (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) {R : ℝ}
    (z : Fin (T+1) → Fin m → SignedCoefficient R) : PiLp 2 E → ℝ :=
  conservativeChain reg (fun i => D.population i (θ i)) (fun i => D.sample i (z i)) (fun i => gate i (θ i))

def truncatedLoss (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) {R : ℝ}
    (z : Fin (T+1) → Fin m → SignedCoefficient R) (k : ℕ) : PiLp 2 E → ℝ :=
  conservativeTruncatedChain reg (fun i => D.population i (θ i)) (fun i => D.sample i (z i))
    (fun i => gate i (θ i)) k

theorem loss_contDiff (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) : ContDiff ℝ 2 (D.loss reg gate θ z) :=
  conservativeChain_contDiff reg _ _ _ hreg (fun i => D.population_contDiff h0 hφ i (θ i))
    (fun i => D.sample_contDiff h0 hφ i (z i)) (fun i => hgate i (θ i))

theorem truncatedLoss_contDiff (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) (k : ℕ) :
    ContDiff ℝ 2 (D.truncatedLoss reg gate θ z k) :=
  conservativeTruncatedChain_contDiff reg _ _ _ hreg (fun i => D.population_contDiff h0 hφ i (θ i))
    (fun i => D.sample_contDiff h0 hφ i (z i)) (fun i => hgate i (θ i)) k

theorem truncatedLoss_prefix_invariant (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ θ' : Fin (T+1) → Θ) {R : ℝ}
    (z z' : Fin (T+1) → Fin m → SignedCoefficient R) {k : ℕ} (hk : k ≤ T)
    (hθ : ∀ i, i.val<k → θ i=θ' i) (hz : ∀ i, i.val ≤ k → z i=z' i) :
    D.truncatedLoss reg gate θ z k=D.truncatedLoss reg gate θ' z' k :=
  conservativeTruncatedChain_prefix_invariant reg _ _ _ _ _ _ hk
    (fun i hi => by rw [hθ i hi]) (fun i hi => by rw [hθ i hi]) (fun i hi => by rw [hz i hi])

end ConservativeFeatureData
end
end SecondOrder
