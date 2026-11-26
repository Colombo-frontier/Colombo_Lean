import HeavyTail.AdaptiveKernelModel

/-!
Minimax quantiles with genuinely extended nonnegative loss, including infinite
objective error outside the effective domain. The model quantile below ranges
over public-data-only policies and actual fresh-kernel execution laws. It is
the exactly-T-call quantity; at-most-T stopping/padding equivalence is not
assumed here.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HeavyTail

section ExtendedQuantile
variable {Algorithm Instance : Type*} {Ω : Instance → Algorithm → Type*}
  [∀ i a, MeasurableSpace (Ω i a)]

def uniformExtendedThresholds (P : ∀ i a, Measure (Ω i a))
    (loss : ∀ i a, Ω i a → ℝ≥0∞) (δ : ℝ) (a : Algorithm) : Set ℝ≥0∞ :=
  {ε | ∀ i, (P i a).real {ω | ε < loss i a ω} ≤ δ}

def extendedMinimaxQuantile (P : ∀ i a, Measure (Ω i a))
    (loss : ∀ i a, Ω i a → ℝ≥0∞) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ a, sInf (uniformExtendedThresholds P loss δ a)

theorem extendedMinimaxQuantile_upper (P : ∀ i a, Measure (Ω i a))
    (loss : ∀ i a, Ω i a → ℝ≥0∞) (δ : ℝ) (a : Algorithm) (ε : ℝ≥0∞)
    (h : ∀ i, (P i a).real {ω | ε < loss i a ω} ≤ δ) :
    extendedMinimaxQuantile P loss δ ≤ ε := iInf_le_of_le a (sInf_le h)

/-- Strict excess failure probability below a non-strict loss event handles
atoms and remains valid when the lower threshold is infinity. -/
theorem extendedMinimaxQuantile_lower (P : ∀ i a, Measure (Ω i a))
    [∀ i a, IsFiniteMeasure (P i a)] (loss : ∀ i a, Ω i a → ℝ≥0∞)
    (δ : ℝ) (α : ℝ≥0∞)
    (h : ∀ a, ∃ i, δ < (P i a).real {ω | α ≤ loss i a ω}) :
    α ≤ extendedMinimaxQuantile P loss δ := by
  apply le_iInf
  intro a
  apply le_sInf
  intro ε hε
  by_contra hn
  have hlt : ε < α := lt_of_not_ge hn
  obtain ⟨i, hi⟩ := h a
  have hsub : {ω | α ≤ loss i a ω} ⊆ {ω | ε < loss i a ω} :=
    fun _ hω => hlt.trans_le hω
  exact (not_lt_of_ge (hε i)) (hi.trans_le (measureReal_mono hsub))

theorem extendedMinimaxQuantile_instance_lower (P : ∀ i a, Measure (Ω i a))
    (loss : ∀ i a, Ω i a → ℝ≥0∞) (δ : ℝ) (J : Type*) (embed : J → Instance) :
    extendedMinimaxQuantile (fun j a => P (embed j) a) (fun j a => loss (embed j) a) δ ≤
      extendedMinimaxQuantile P loss δ := by
  apply iInf_mono
  intro a
  apply sInf_le_sInf
  intro ε hε j
  exact hε (embed j)

end ExtendedQuantile

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {θ : OracleParameters}

def modelOutputLaw (I : ModelInstance E θ) (A : PublicAlgorithm E θ) : Measure I.1.X :=
  PublicPolicy.outputLaw (A I.1) I.2

instance modelOutputLaw_probability (I : ModelInstance E θ) (A : PublicAlgorithm E θ) :
    IsProbabilityMeasure (modelOutputLaw I A) := by
  unfold modelOutputLaw
  infer_instance

def fixedCallMinimax (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (θ : OracleParameters) : ℝ≥0∞ :=
  extendedMinimaxQuantile (modelOutputLaw (E := E) (θ := θ)) (fun I _ => I.2.loss) θ.δ

theorem fixedCallMinimax_upper (A : PublicAlgorithm E θ) (ε : ℝ≥0∞)
    (h : ∀ B : PublicProblem E θ, ∀ I : PrivateInstance B,
      (PublicPolicy.outputLaw (A B) I).real {x | ε < I.loss x} ≤ θ.δ) :
    fixedCallMinimax E θ ≤ ε := by
  apply extendedMinimaxQuantile_upper _ _ _ A ε
  rintro ⟨B, I⟩
  exact h B I

theorem fixedCallMinimax_lower (α : ℝ≥0∞)
    (h : ∀ A : PublicAlgorithm E θ, ∃ B : PublicProblem E θ, ∃ I : PrivateInstance B,
      θ.δ < (PublicPolicy.outputLaw (A B) I).real {x | α ≤ I.loss x}) :
    α ≤ fixedCallMinimax E θ := by
  apply extendedMinimaxQuantile_lower _ _ _ α
  intro A
  obtain ⟨B, I, hi⟩ := h A
  exact ⟨⟨B, I⟩, hi⟩

/-- Minimax within a fixed public block, allowing arbitrary private families. -/
def publicFamilyMinimax (B : PublicProblem E θ) {J : Type*} (family : J → PrivateInstance B) :
    ℝ≥0∞ :=
  extendedMinimaxQuantile (fun j (A : PublicPolicy B) => PublicPolicy.outputLaw A (family j))
    (fun j _ => (family j).loss) θ.δ

/-- A lower bound for a family with common public data applies to the full model.
The proof restricts a public-data-only algorithm to that one public block. -/
theorem publicFamilyMinimax_le_fixedCallMinimax (B : PublicProblem E θ)
    {J : Type*} (family : J → PrivateInstance B) :
    publicFamilyMinimax B family ≤ fixedCallMinimax E θ := by
  apply le_iInf
  intro A
  apply le_trans (iInf_le (fun a : PublicPolicy B =>
    sInf (uniformExtendedThresholds (fun j a => PublicPolicy.outputLaw a (family j))
      (fun j _ => (family j).loss) θ.δ a)) (A B))
  apply sInf_le_sInf
  intro ε hε j
  exact hε ⟨B, family j⟩

end HeavyTail
