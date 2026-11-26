import SecondOrder.ConservativeFrontierKernel
import SecondOrder.CurvatureProgress

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]
  [MeasurableSpace (PiLp 2 E)] [BorelSpace (PiLp 2 E)]

def conservativeProgress (gate : (i : Fin (T+1)) → Θ → E i → ℝ)
    (θ : Fin (T+1) → Θ) (x : PiLp 2 E) : ℕ :=
  positiveGateFrontier (fun i => gate i (θ i) (x i))

theorem conservativeProgress_le (gate : (i : Fin (T+1)) → Θ → E i → ℝ)
    (θ : Fin (T+1) → Θ) (x : PiLp 2 E) : conservativeProgress gate θ x ≤ T+1 :=
  positiveGateFrontier_le _

theorem conservativeProgress_future_zero (gate : (i : Fin (T+1)) → Θ → E i → ℝ)
    (θ : Fin (T+1) → Θ) (x : PiLp 2 E) (hpos : ∀ i, 0 ≤ gate i (θ i) (x i))
    (i : Fin (T+1)) (hi : conservativeProgress gate θ x ≤ i.val) : gate i (θ i) (x i)=0 :=
  positiveGateFrontier_future_zero _ hpos i hi

theorem conservativeProgress_measurable (gate : (i : Fin (T+1)) → Θ → E i → ℝ)
    (θ : Fin (T+1) → Θ) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ)) :
    Measurable (conservativeProgress gate θ) := by
  apply positiveGateFrontier_measurable
  intro i
  exact ((hgate i (θ i)).continuous.comp (dependentBlockProj (E := E) i).continuous).measurable

namespace ConservativeFeatureData

/-- The general manuscript's uniform information bound at every query point. -/
theorem extendedKernel_kl (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) (θ₀ : Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    {k : ℕ} (hk : k ≤ T) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    klDiv (D.extendedKernel reg gate θ hreg h0 hφ hgate R hR k x)
      (D.referenceKernel reg gate θ₀ hk (fun i : Fin k => θ ⟨i.val,by omega⟩)
        hreg h0 hφ hgate R hR x) ≤ ENNReal.ofReal ((m:ℝ)/R^2) :=
  D.truncatedReply_frontier_kl reg gate θ θ₀ hk R hR x

/-- The full-array extended law exposes precisely the revealed hidden
prefix and the next hidden block, with all later arrays integrated out. -/
theorem extendedKernel_prefix_formula (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) (θ₀ : Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    {k : ℕ} (hk : k ≤ T) (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) :
    D.extendedKernel reg gate θ hreg h0 hφ hgate R hR k x=
      D.frontierTrueLaw reg gate θ₀ hk (fun i : Fin k => θ ⟨i.val,by omega⟩)
        (θ ⟨k,by omega⟩) R hR x :=
  D.truncatedReply_law_frontier reg gate θ θ₀ hk R hR x

theorem reply_at_progress (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (hflat : ∀ i θ y, gate i θ y=0 → gradient (gate i θ) y=0 ∧ fderiv ℝ (gradient (gate i θ)) y=0)
    {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) (x : PiLp 2 E)
    (hpos : ∀ i, 0 ≤ gate i (θ i) (x i)) :
    D.reply reg gate θ z x=D.truncatedReply reg gate θ z (conservativeProgress gate θ x) x :=
  D.reply_truncate reg gate θ hreg h0 hφ hgate hflat z _ x
    (conservativeProgress_future_zero gate θ x hpos)

/-- The actual rich oracle, at its true maximal positive-gate progress,
obeys the m/R² information bound against a past-only reference kernel. -/
theorem reply_progress_kl (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) (θ₀ : Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (hflat : ∀ i θ y, gate i θ y=0 → gradient (gate i θ) y=0 ∧ fderiv ℝ (gradient (gate i θ)) y=0)
    (R : ℝ) (hR : 2 ≤ R) (x : PiLp 2 E) (hpos : ∀ i, 0 ≤ gate i (θ i) (x i))
    (hk : conservativeProgress gate θ x ≤ T) :
    klDiv ((D.arrayLaw θ R hR).toMeasure.map (fun z => D.reply reg gate θ z x))
      (D.referenceKernel reg gate θ₀ hk
        (fun i : Fin (conservativeProgress gate θ x) => θ ⟨i.val,by omega⟩)
        hreg h0 hφ hgate R hR x) ≤ ENNReal.ofReal ((m:ℝ)/R^2) := by
  have he : (fun z : Fin (T+1) → Fin m → SignedCoefficient R => D.reply reg gate θ z x)=
      (fun z => D.truncatedReply reg gate θ z (conservativeProgress gate θ x) x) :=
    funext (fun z => D.reply_at_progress reg gate θ hreg h0 hφ hgate hflat z x hpos)
  rw [he]
  exact D.extendedKernel_kl reg gate θ θ₀ hreg h0 hφ hgate hk R hR x

end ConservativeFeatureData
end
end SecondOrder
