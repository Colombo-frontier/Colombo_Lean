import LowRank.RectangularHardDimension
import LowRank.JoinedOrthogonalColumns

/-! Minimax randomized query complexity for rectangular low-rank
approximation. The seed distribution is fixed independently of the input;
all calls have a uniform finite budget and actual outputs are orthonormal
column matrices. An empty feasible class has complexity infinity. -/

namespace LowRank
open Matrix MeasureTheory
open scoped ENNReal Matrix
noncomputable section
universe u

structure RectangularColumnAlgorithm (a b k n : ℕ) : Type (u + 1) where
  Seed : Type u
  [measurableSeed : MeasurableSpace Seed]
  law : Measure Seed
  [probability : IsProbabilityMeasure law]
  policy : BoundedRectangularPolicy a b (Matrix (Fin b) (Fin k) ℝ) n Seed
  orthonormal : ∀ (A : Matrix (Fin a) (Fin b) ℝ) (seed : Seed),
    let Z := runBoundedRectangular a b n policy A seed
    Zᵀ * Z = 1

attribute [instance] RectangularColumnAlgorithm.measurableSeed RectangularColumnAlgorithm.probability

def RectangularColumnAlgorithm.Succeeds {a b k n : ℕ}
    (alg : RectangularColumnAlgorithm.{u} a b k n) (p ε δ : ℝ) : Prop :=
  ∀ A : Matrix (Fin a) (Fin b) ℝ, δ ≤ alg.law.real (rectangularSchattenSuccess p ε alg.policy A)

theorem RectangularColumnAlgorithm.output_projector {a b k n : ℕ}
    (alg : RectangularColumnAlgorithm.{u} a b k n)
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : alg.Seed) :
    let Z := runBoundedRectangular a b n alg.policy A seed
    IsOrthogonalProjector (Z * Zᵀ) ∧ (Z * Zᵀ).rank = k :=
  ⟨column_projector _ (alg.orthonormal A seed), column_projector_rank _ (alg.orthonormal A seed)⟩

theorem RectangularColumnAlgorithm.calls_le {a b k n : ℕ}
    (alg : RectangularColumnAlgorithm.{u} a b k n)
    (A : Matrix (Fin a) (Fin b) ℝ) (seed : alg.Seed) :
    (alg.policy.toProgram a b n seed).calls (rectangularOracle A) ≤ n :=
  alg.policy.calls_le a b n A seed

def rectangularQueryComplexity (a b k : ℕ) (p ε δ : ℝ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (alg : RectangularColumnAlgorithm.{u} a b k n) (_ : alg.Succeeds p ε δ), (n : ℝ≥0∞)

theorem rectangularQueryComplexity_le_budget {a b k n : ℕ} {p ε δ : ℝ}
    (alg : RectangularColumnAlgorithm.{u} a b k n) (hs : alg.Succeeds p ε δ) :
    rectangularQueryComplexity.{u} a b k p ε δ ≤ (n : ℝ≥0∞) :=
  iInf_le_of_le n (iInf_le_of_le alg (iInf_le_of_le hs le_rfl))

theorem le_rectangularQueryComplexity {a b k : ℕ} {p ε δ B : ℝ}
    (hbound : ∀ (n : ℕ) (alg : RectangularColumnAlgorithm.{u} a b k n),
      alg.Succeeds p ε δ → B ≤ (n : ℝ)) :
    ENNReal.ofReal B ≤ rectangularQueryComplexity.{u} a b k p ε δ := by
  apply le_iInf
  intro n
  apply le_iInf
  intro alg
  apply le_iInf
  intro hs
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (hbound n alg hs)

theorem rectangularQueryComplexity_lower_of_wishart_probability {p L c₀ : ℝ}
    (hp : 0 < p) (hL : 0 < L) (hc : 0 < c₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b d k : ℕ) (ε δ : ℝ),
      d ≤ a → d ≤ b → 0 < k → 0 ≤ ε → ε ≤ 1 → 1 / 5 ≤ δ →
      (k : ℝ) ≤ (d : ℝ) / 100 → C * ε * (d : ℝ) ^ 3 ≤ (k : ℝ) ^ 3 / 4 →
      (gaussianMatrixLaw d (d - k)).real (wishartSpectralEvent d (d - k) L c₀ k)ᶜ ≤ 1 / 20 →
      ENNReal.ofReal ((d : ℝ) / 100) ≤ rectangularQueryComplexity.{u} a b k p ε δ := by
  obtain ⟨C, hC, hmain⟩ := rectangular_schatten_budget_gt_of_wishart_probability hp hL hc
  refine ⟨C, hC, ?_⟩
  intro a b d k ε δ ha hb hk hε hε1 hδ hkd hsmall hbad
  apply le_rectangularQueryComplexity
  intro n alg hs
  exact (hmain a b d k n ε ha hb alg.law alg.policy hk hε hε1 hkd hsmall hbad
    (fun A => hδ.trans (hs A))).le

end
end LowRank
