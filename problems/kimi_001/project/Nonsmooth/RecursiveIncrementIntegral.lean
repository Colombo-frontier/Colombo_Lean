import Nonsmooth.RecursiveMeanMoments
import Nonsmooth.ParametricSupportEnergy
import Nonsmooth.RecursiveResponseChain
import Nonsmooth.KernelExponentialJensen

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

theorem recursiveSupportResponse_pair_law (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Q.map (fun a => (recursiveSupportResponse u n a,
      supportSingleObservation (u n (recursiveSupportResponse u n a)) a)) =
        (Q.map (recursiveSupportResponse u n)) ⊗ₘ recursiveResponseKernel Q u hu n := by
  exact observedPosterior_update_base Q (recursiveSupportResponse u n)
    (recursiveSupportResponse_measurable u hu n) id measurable_id
    (recursiveSupportBelief Q u hu n) (recursiveSupportBelief_disintegrates Q u hu n)
    (fun p => supportSingleObservation (u n p.1) p.2)
    (supportParametricObservation_measurable (u n) (hu n))

theorem recursiveSupportMean_increment_formula (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ)
    (h : ResponseHistory k n) (y : Fin k × ℝ) :
    recursiveSupportMean Q u hu (n + 1) (responseHistoryJoin (h, y)) -
      recursiveSupportMean Q u hu n h =
        supportUpdateMeanIncrement (recursiveSupportBelief Q u hu n) (u n) (hu n) (h, y) := by
  unfold recursiveSupportMean supportUpdateMeanIncrement
  rw [recursiveSupportBelief_succ]

/-- The conditional one-step energy integrates to the actual mean increment
under the original prior; all required second moments are derived. -/
theorem recursiveSupportMean_increment_integral (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (hL : MemLp (fun a : Fin k → E => ∑ i, a i) 2 Q)
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    Integrable (supportUpdateMeanEnergy (recursiveSupportBelief Q u hu n) (u n) (hu n))
      (Q.map (recursiveSupportResponse u n)) ∧
      (∫ a : Fin k → E,
        ‖recursiveSupportMean Q u hu (n + 1) (recursiveSupportResponse u (n + 1) a) -
          recursiveSupportMean Q u hu n (recursiveSupportResponse u n a)‖ ^ 2 ∂Q) =
        ∫ h, supportUpdateMeanEnergy (recursiveSupportBelief Q u hu n) (u n) (hu n) h
          ∂Q.map (recursiveSupportResponse u n) := by
  let X := recursiveSupportResponse u n
  let W : (Fin k → E) → ResponseHistory k n × (Fin k × ℝ) :=
    fun a => (X a, supportSingleObservation (u n (X a)) a)
  let φ : ResponseHistory k n × (Fin k × ℝ) → ℝ :=
    fun p => ‖supportUpdateMeanIncrement (recursiveSupportBelief Q u hu n) (u n) (hu n) p‖ ^ 2
  have hX : Measurable X := recursiveSupportResponse_measurable u hu n
  have hW : Measurable W := by
    have hObs := (supportParametricObservation_measurable (k := k) (u n) (hu n)).comp
      (hX.prodMk (show Measurable (fun a : Fin k → E => a) from measurable_id))
    dsimp only [Function.comp_def] at hObs
    exact hX.prodMk hObs
  have hφ : Measurable φ := (supportUpdateMeanIncrement_measurable _ _ _).norm.pow_const 2
  have hpoint (a : Fin k → E) :
      ‖recursiveSupportMean Q u hu (n + 1) (recursiveSupportResponse u (n + 1) a) -
        recursiveSupportMean Q u hu n (X a)‖ ^ 2 = φ (W a) := by
    rw [recursiveSupportResponse, recursiveSupportMean_increment_formula]
  have hdiff := (recursiveSupportMean_composed_memLp Q hL u hu (n + 1)).sub
    (recursiveSupportMean_composed_memLp Q hL u hu n)
  have hiRaw : Integrable (fun a => φ (W a)) Q := by
    have h := (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
    exact h.congr (Eventually.of_forall hpoint)
  have hiMap : Integrable φ (Q.map W) :=
    (integrable_map_measure hφ.aestronglyMeasurable hW.aemeasurable).mpr hiRaw
  have hbase : Q.map W = (Q.map X) ⊗ₘ recursiveResponseKernel Q u hu n :=
    recursiveSupportResponse_pair_law Q u hu n
  have hiJoint : Integrable φ ((Q.map X) ⊗ₘ recursiveResponseKernel Q u hu n) := by
    rwa [hbase] at hiMap
  have hiOuter := kernel_mean_integrable (Q.map X) (recursiveResponseKernel Q u hu n) φ hφ hiJoint
  refine ⟨hiOuter, ?_⟩
  calc
    _ = ∫ a, φ (W a) ∂Q := integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∫ p, φ p ∂Q.map W := (integral_map_of_stronglyMeasurable hW hφ.stronglyMeasurable).symm
    _ = _ := by rw [hbase, Measure.integral_compProd hiJoint]; rfl

end
end Nonsmooth
