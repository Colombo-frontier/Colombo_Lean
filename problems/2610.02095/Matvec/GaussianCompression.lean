import LowRank.GaussianMatrixCompression
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic

/-!
# Fresh Gaussian compression by a state-dependent orthonormal frame

This is the final probabilistic compression step of `lem:gaussian-core` in
`matvec.tex`. A rectangular iid Gaussian matrix, independent of the exposed
state, remains iid Gaussian and independent of that state after multiplication
by a measurable orthonormal frame selected from the state. The conditional
bounded-test identity is an actual conditional expectation theorem.

The independent product law of the pre-compression matrix and the measurable
orthonormal frame are hypotheses. This module does not assert that arbitrary
adaptive two-sided oracle transcripts have that product law, nor does it
construct the required measurable kernel frame.
-/

namespace Matvec

open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix
noncomputable section

variable {S : Type*} [MeasurableSpace S] {r d k : ℕ}

theorem measurable_state_compression (V : S → Matrix (Fin d) (Fin k) ℝ)
    (hV : Measurable V) :
    Measurable (fun p : S × Matrix (Fin r) (Fin d) ℝ => p.2 * V p.1) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply]
  fun_prop

/-- Compression preserves the entire joint product measure, not only the
marginal distribution of the Gaussian matrix. -/
theorem state_dependent_gaussian_compression (ν : Measure S) [SFinite ν]
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1) (v : NNReal) :
    MeasurePreserving
      (fun p : S × Matrix (Fin r) (Fin d) ℝ => (p.1, p.2 * V p.1))
      (ν.prod (LowRank.iidMatrixLaw r d v)) (ν.prod (LowRank.iidMatrixLaw r k v)) := by
  exact (MeasurePreserving.id ν).skew_product (measurable_state_compression V hV)
    (Filter.Eventually.of_forall (fun s => LowRank.iidMatrixLaw_right_compression
      (r := r) (V s) (horth s) v))

section UnderlyingSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Joint-law form on an arbitrary underlying probability space. -/
theorem hidden_gaussian_compression_joint_law
    (ν : Measure S) [SFinite ν]
    (Y : Ω → S) (W : Ω → Matrix (Fin r) (Fin d) ℝ)
    (hjoint : Measurable (fun ω => (Y ω, W ω)))
    (hlaw : μ.map (fun ω => (Y ω, W ω)) = ν.prod (LowRank.iidMatrixLaw r d v))
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1) :
    μ.map (fun ω => (Y ω, W ω * V (Y ω))) = ν.prod (LowRank.iidMatrixLaw r k v) := by
  have hp := state_dependent_gaussian_compression (r := r) ν V hV horth v
  have h := hp.map_eq
  rw [← hlaw, Measure.map_map hp.measurable hjoint] at h
  exact h

/-- Independence and an iid Gaussian marginal imply the required full product
law after state-dependent compression. -/
theorem independent_gaussian_compression_joint_law [IsProbabilityMeasure μ]
    (Y : Ω → S) (W : Ω → Matrix (Fin r) (Fin d) ℝ)
    (hY : Measurable Y) (hW : Measurable W) (hind : IndepFun Y W μ)
    (v : NNReal) (hWlaw : μ.map W = LowRank.iidMatrixLaw r d v)
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1) :
    μ.map (fun ω => (Y ω, W ω * V (Y ω))) =
      (μ.map Y).prod (LowRank.iidMatrixLaw r k v) := by
  have hj := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hW.aemeasurable).mp hind
  rw [hWlaw] at hj
  exact hidden_gaussian_compression_joint_law (μ.map Y) Y W (hY.prodMk hW) hj V hV horth

/-- The compressed matrix itself has the claimed iid Gaussian marginal. -/
theorem independent_gaussian_compression_law [IsProbabilityMeasure μ]
    (Y : Ω → S) (W : Ω → Matrix (Fin r) (Fin d) ℝ)
    (hY : Measurable Y) (hW : Measurable W) (hind : IndepFun Y W μ)
    (v : NNReal) (hWlaw : μ.map W = LowRank.iidMatrixLaw r d v)
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1) :
    μ.map (fun ω => W ω * V (Y ω)) = LowRank.iidMatrixLaw r k v := by
  have hZ : Measurable (fun ω => W ω * V (Y ω)) :=
    (measurable_state_compression V hV).comp (hY.prodMk hW)
  have hmap := independent_gaussian_compression_joint_law Y W hY hW hind v hWlaw V hV horth
  haveI : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
  calc
    _ = (μ.map (fun ω => (Y ω, W ω * V (Y ω)))).map Prod.snd :=
      (Measure.map_map measurable_snd (hY.prodMk hZ)).symm
    _ = _ := by rw [hmap]; simp

/-- Compression preserves independence from the whole exposed state. -/
theorem independent_gaussian_compression_independent [IsProbabilityMeasure μ]
    (Y : Ω → S) (W : Ω → Matrix (Fin r) (Fin d) ℝ)
    (hY : Measurable Y) (hW : Measurable W) (hind : IndepFun Y W μ)
    (v : NNReal) (hWlaw : μ.map W = LowRank.iidMatrixLaw r d v)
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1) :
    IndepFun Y (fun ω => W ω * V (Y ω)) μ := by
  have hZ : Measurable (fun ω => W ω * V (Y ω)) :=
    (measurable_state_compression V hV).comp (hY.prodMk hW)
  apply (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mpr
  rw [independent_gaussian_compression_law Y W hY hW hind v hWlaw V hV horth]
  exact independent_gaussian_compression_joint_law Y W hY hW hind v hWlaw V hV horth

/-- Conditional-law identity tested against any integrable measurable real
function, with conditioning on the sigma-field generated by the exposed state. -/
theorem gaussian_compression_conditional_test [IsProbabilityMeasure μ]
    (Y : Ω → S) (W : Ω → Matrix (Fin r) (Fin d) ℝ)
    (hY : Measurable Y) (hW : Measurable W) (hind : IndepFun Y W μ)
    (v : NNReal) (hWlaw : μ.map W = LowRank.iidMatrixLaw r d v)
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1)
    (φ : Matrix (Fin r) (Fin k) ℝ → ℝ) (hφ : Measurable φ)
    (hφint : Integrable φ (LowRank.iidMatrixLaw r k v)) :
    Integrable (fun ω => φ (W ω * V (Y ω))) μ ∧
      μ[(fun ω => φ (W ω * V (Y ω))) | MeasurableSpace.comap Y inferInstance] =ᵐ[μ]
        (fun _ => ∫ D, φ D ∂LowRank.iidMatrixLaw r k v) := by
  let Z : Ω → Matrix (Fin r) (Fin k) ℝ := fun ω => W ω * V (Y ω)
  have hZ : Measurable Z :=
    (measurable_state_compression V hV).comp (hY.prodMk hW)
  have hZlaw : MeasurePreserving Z μ (LowRank.iidMatrixLaw r k v) :=
    ⟨hZ, independent_gaussian_compression_law Y W hY hW hind v hWlaw V hV horth⟩
  refine ⟨(hZlaw.integrable_comp hφ.stronglyMeasurable.aestronglyMeasurable).mpr hφint, ?_⟩
  have hZY : IndepFun Z Y μ :=
    (independent_gaussian_compression_independent Y W hY hW hind v hWlaw V hV horth).symm
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (Matrix (Fin r) (Fin k) ℝ)).comap Z]
      (φ ∘ Z) := (hφ.comp (comap_measurable Z)).stronglyMeasurable
  have hc := condExp_indep_eq hZ.comap_le hY.comap_le hsm ((IndepFun_iff_Indep Z Y μ).mp hZY)
  have hi : (∫ ω, φ (Z ω) ∂μ) = ∫ D, φ D ∂LowRank.iidMatrixLaw r k v := by
    rw [← hZlaw.map_eq, integral_map_of_stronglyMeasurable hZ hφ.stronglyMeasurable]
  simpa only [Function.comp_def, hi] using hc

/-- Bounded measurable tests give the exact conditional Gaussian identity
used for the final square core (specialize `r = k`). -/
theorem gaussian_compression_conditional_bounded [IsProbabilityMeasure μ]
    (Y : Ω → S) (W : Ω → Matrix (Fin r) (Fin d) ℝ)
    (hY : Measurable Y) (hW : Measurable W) (hind : IndepFun Y W μ)
    (v : NNReal) (hWlaw : μ.map W = LowRank.iidMatrixLaw r d v)
    (V : S → Matrix (Fin d) (Fin k) ℝ) (hV : Measurable V)
    (horth : ∀ s, (V s)ᵀ * V s = 1)
    (φ : Matrix (Fin r) (Fin k) ℝ → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hbound : ∀ D, ‖φ D‖ ≤ C) :
    μ[(fun ω => φ (W ω * V (Y ω))) | MeasurableSpace.comap Y inferInstance] =ᵐ[μ]
      (fun _ => ∫ D, φ D ∂LowRank.iidMatrixLaw r k v) := by
  have hi : Integrable φ (LowRank.iidMatrixLaw r k v) :=
    (integrable_const C).mono' hφ.stronglyMeasurable.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  exact (gaussian_compression_conditional_test Y W hY hW hind v hWlaw V hV horth φ hφ hi).2

end UnderlyingSpace
end
end Matvec
