import GradientHessian.Machine
import GradientHessian.JetLocality
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Normalized objectives and the exact mixed-query minimax problem

The function class uses actual first and second Fréchet derivatives. A curried
bilinear form represents the Hessian, with its operator norm. The Riesz
identification preserves the gradient norm. Queries and outputs range over all
Euclidean points; no radius, span, precision or Hessian-norm restriction occurs.

The theorem targets at the end are propositions, not asserted theorems. Their
construction-dependent proofs must be supplied separately.
-/

noncomputable section

namespace GradientHessian.Model

open MeasureTheory Set
open scoped ENNReal

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev First (d : ℕ) := Point d →L[ℝ] ℝ
abbrev Second (d : ℕ) := Point d →L[ℝ] First d

instance firstMeasurable (d : ℕ) : MeasurableSpace (First d) := borel _
instance firstBorel (d : ℕ) : BorelSpace (First d) := ⟨rfl⟩
instance secondMeasurable (d : ℕ) : MeasurableSpace (Second d) := borel _
instance secondBorel (d : ℕ) : BorelSpace (Second d) := ⟨rfl⟩

abbrev OrdinaryReply (d : ℕ) := ℝ × First d
abbrev RichReply (d : ℕ) := ℝ × First d × Second d

structure Admissible {d : ℕ} (T : ℝ) (f : Point d → ℝ) : Prop where
  smooth : ContDiff ℝ 2 f
  boundedBelow : BddBelow (range f)
  gap : f 0 - sInf (range f) ≤ T
  hessianLip : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))

def ordinaryOracle {d : ℕ} (f : Point d → ℝ) : Point d → OrdinaryReply d :=
  JetLocality.ordinaryJet f

def richOracle {d : ℕ} (f : Point d → ℝ) : Point d → RichReply d :=
  JetLocality.richJet f

def stationary {d : ℕ} (f : Point d → ℝ) : Set (Point d) :=
  {x | ‖fderiv ℝ f x‖ ≤ 1}

theorem gradient_norm_eq {d : ℕ} (f : Point d → ℝ) (x : Point d) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.norm_map _

theorem stationary_iff_gradient {d : ℕ} (f : Point d → ℝ) (x : Point d) :
    x ∈ stationary f ↔ ‖gradient f x‖ ≤ 1 := by
  simp only [stationary, mem_setOf_eq, gradient_norm_eq]

theorem Admissible.nonnegative_budget {d : ℕ} {T : ℝ} {f : Point d → ℝ}
    (hf : Admissible T f) : 0 ≤ T := by
  have h := csInf_le hf.boundedBelow (mem_range_self (0 : Point d))
  linarith [hf.gap]

theorem Admissible.mono {d : ℕ} {S T : ℝ} {f : Point d → ℝ}
    (hf : Admissible S f) (hST : S ≤ T) : Admissible T f :=
  ⟨hf.smooth, hf.boundedBelow, hf.gap.trans hST, hf.hessianLip⟩

theorem admissible_of_lower_bound {d : ℕ} {T lower : ℝ} {f : Point d → ℝ}
    (hs : ContDiff ℝ 2 f) (hl : ∀ x, lower ≤ f x) (hg : f 0 - lower ≤ T)
    (hH : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) : Admissible T f := by
  have hb : BddBelow (range f) := ⟨lower, by rintro _ ⟨x, rfl⟩; exact hl x⟩
  have hi : lower ≤ sInf (range f) := le_csInf (range_nonempty f)
    (by rintro _ ⟨x, rfl⟩; exact hl x)
  exact ⟨hs, hb, by linarith, hH⟩

theorem ordinaryOracle_measurable {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : Measurable (ordinaryOracle f) := by
  exact (hf.continuous.prodMk (hf.continuous_fderiv (by norm_num))).measurable

theorem richOracle_measurable {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : Measurable (richOracle f) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  exact (hf.continuous.prodMk ((hf.continuous_fderiv (by norm_num)).prodMk
    (hd.continuous_fderiv (by norm_num)))).measurable

theorem stationary_measurable {d : ℕ} {f : Point d → ℝ}
    (hf : ContDiff ℝ 2 f) : MeasurableSet (stationary f) :=
  (isClosed_le (hf.continuous_fderiv (by norm_num)).norm continuous_const).measurableSet

/-- State and private-seed spaces are arbitrary measurable types. The seed law
is part of the algorithm, not a function of the unknown objective. -/
structure Algorithm (d : ℕ) where
  Seed : Type
  State : Type
  seedSpace : MeasurableSpace Seed
  stateSpace : MeasurableSpace State
  seedLaw : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace seedLaw
  policy : @Machine.Policy Seed State (Point d) (OrdinaryReply d) (RichReply d)
    seedSpace stateSpace inferInstance inferInstance inferInstance

def Algorithm.Guarantees {d : ℕ} (A : Algorithm d) (T : ℝ) (G H : ℕ) : Prop :=
  letI := A.seedSpace
  letI := A.stateSpace
  ∀ f : Point d → ℝ, Admissible T f →
    A.policy.TerminatesAlmostSurely (ordinaryOracle f) (richOracle f) A.seedLaw ∧
    A.policy.HasCaps (ordinaryOracle f) (richOracle f) G H ∧
    (2 / 3 : ℝ≥0∞) ≤ A.seedLaw
      (A.policy.success (ordinaryOracle f) (richOracle f) (stationary f))

/-- The least achievable ordinary cap with prescribed rich cap, or infinity
when no such algorithm exists. -/
def complexity (H d : ℕ) (T : ℝ) : ℝ≥0∞ :=
  ⨅ G : ℕ, ⨅ A : Algorithm d, ⨅ (_ : A.Guarantees T G H), (G : ℝ≥0∞)

theorem complexity_le {d G H : ℕ} {T : ℝ} (A : Algorithm d)
    (hA : A.Guarantees T G H) : complexity H d T ≤ G :=
  iInf_le_of_le G (iInf_le_of_le A (iInf_le_of_le hA le_rfl))

theorem complexity_lower_of_failure {d H : ℕ} {T lower : ℝ}
    (hfail : ∀ G : ℕ, (G : ℝ) < lower → ∀ A : Algorithm d, ¬ A.Guarantees T G H) :
    ENNReal.ofReal lower ≤ complexity H d T := by
  apply le_iInf
  intro G
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  have hg : lower ≤ (G : ℝ) := le_of_not_gt (fun h => hfail G h A hA)
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hg

def lowerRate (H d : ℕ) (T : ℝ) : ℝ :=
  min (T * (d : ℝ) ^ (1 / 3 : ℝ)) (T ^ (3 / 2 : ℝ) / Real.sqrt ((H : ℝ) + 1))

/-- Exact theorem target from `thm:main`. No proof is asserted here. -/
def MainLowerBound : Prop :=
  ∃ C a c Tstar : ℝ, 0 < C ∧ 0 < a ∧ a < 1 ∧ 0 < c ∧ 0 < Tstar ∧
    ∀ (T : ℝ) (d H : ℕ), Tstar ≤ T → C * Real.log (2 + T) ≤ d →
      1 ≤ H → (H : ℝ) + 1 ≤ a * T →
      ENNReal.ofReal (c * lowerRate H d T) ≤ complexity H d T

/-- Exact theorem target from `thm:parameter`, with all random-algorithm
quantifiers inside the defined complexity. No proof is asserted here. -/
def UniformParameterLowerBound : Prop :=
  ∃ CE Cd c₀ : ℝ, ∃ J₀ : ℕ, 0 < CE ∧ 0 < Cd ∧ 0 < c₀ ∧ 0 < J₀ ∧
    ∀ J L d H : ℕ, ∀ T : ℝ, J₀ ≤ J → 1 ≤ L →
      let M : ℝ := 1 + 4096 * (J : ℝ) ^ 2
      let n : ℝ := (8 : ℝ) ^ L
      CE * n * M ≤ T → Cd * (M ^ (3 / 2 : ℝ) + Real.log (2 + n)) ≤ d →
      (H : ℝ) ≤ n / 2 → ENNReal.ofReal (c₀ * n * M ^ (3 / 2 : ℝ)) ≤ complexity H d T

end GradientHessian.Model
