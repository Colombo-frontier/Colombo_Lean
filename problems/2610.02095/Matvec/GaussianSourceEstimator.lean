import Matvec.SourceEstimatorReliable
import Matvec.SourceEstimatorPolicy
import Matvec.PolicyOracleMap
import Matvec.DilationSpectrum
import Matvec.SpectralPolicyHardness

/-! Actual source-to-Gaussian oracle compilation and reciprocal spectral
estimation. The source inverse is constructed from the expansion promise. -/
namespace Matvec
open Matrix MeasureTheory LowRank MeasurableSimulation SourceIterationPolicy
open scoped Matrix
noncomputable section

theorem exists_inverse_of_expansion {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : E →L[ℝ] E)
    (hexpand : ∀ x, ‖x‖ ≤ ‖H x‖) :
    ∃ M : E →L[ℝ] E, (∀ x, H (M x) = x) ∧ (∀ x, M (H x) = x) := by
  have hi : Function.Injective H := by
    intro x y hxy
    have h := hexpand (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  let e := LinearEquiv.ofBijective H.toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
  refine ⟨LinearMap.toContinuousLinearMap e.symm.toLinearMap, ?_, ?_⟩
  · intro x
    exact e.apply_symm_apply x
  · intro x
    exact e.symm_apply_apply x

def gaussianSourceQuery (n : ℕ) (w : DilationSpace n) : AmbientQuery n n :=
  (fun i => w (Sum.inl i), fun i => w (Sum.inr i))

def gaussianSourceReply (n : ℕ) (a : ℝ) (p : AmbientQuery n n) : DilationSpace n :=
  (Real.sqrt (n : ℝ) / a) •
    (WithLp.equiv 2 ((Fin n ⊕ Fin n) → ℝ)).symm (Sum.elim p.1 p.2)

theorem measurable_gaussianSourceQuery (n : ℕ) : Measurable (gaussianSourceQuery n) := by
  unfold gaussianSourceQuery
  apply Measurable.prodMk <;> apply measurable_pi_lambda
  · intro i
    exact (measurable_pi_apply (Sum.inl i)).comp (PiLp.continuous_equiv 2 _).measurable
  · intro i
    exact (measurable_pi_apply (Sum.inr i)).comp (PiLp.continuous_equiv 2 _).measurable

theorem measurable_gaussianSourceReply (n : ℕ) (a : ℝ) :
    Measurable (gaussianSourceReply n a) := by
  have h : Measurable (fun p : AmbientQuery n n =>
      (WithLp.equiv 2 ((Fin n ⊕ Fin n) → ℝ)).symm (Sum.elim p.1 p.2)) := by
    apply (PiLp.continuous_equiv_symm 2 _).measurable.comp
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl i => exact (measurable_pi_apply i).comp measurable_fst
    | inr i => exact (measurable_pi_apply i).comp measurable_snd
  exact h.const_smul (Real.sqrt (n : ℝ) / a)

theorem gaussianSource_oracle_replay {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (a : ℝ) (w : DilationSpace n) :
    gaussianSourceReply n a (G *ᵥ (gaussianSourceQuery n w).2,
      Gᵀ *ᵥ (gaussianSourceQuery n w).1) = gaussianSourceMap G a w := by
  unfold gaussianSourceReply gaussianSourceMap
  simp only [ContinuousLinearMap.smul_apply]
  congr 1
  apply (WithLp.equiv 2 ((Fin n ⊕ Fin n) → ℝ)).injective
  funext i
  cases i with
  | inl i => exact congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (dilationMap_left G w).symm
  | inr i => exact congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) (dilationMap_right G w).symm

def gaussianSourcePolicy {n T : ℕ} {Seed O : Type*} [MeasurableSpace Seed] [MeasurableSpace O]
    (alg : Policy (DilationSpace n) (DilationSpace n) O T Seed) (a : ℝ) :
    Policy (AmbientQuery n n) (AmbientQuery n n) O T Seed :=
  alg.mapOracle (gaussianSourceQuery n) (gaussianSourceReply n a)
    (measurable_gaussianSourceQuery n) (measurable_gaussianSourceReply n a)

theorem gaussianSourcePolicy_run {n T : ℕ} {Seed O : Type*}
    [MeasurableSpace Seed] [MeasurableSpace O]
    (alg : Policy (DilationSpace n) (DilationSpace n) O T Seed) (a : ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (seed : Seed) :
    (gaussianSourcePolicy alg a).run (fun q => (G *ᵥ q.2, Gᵀ *ᵥ q.1)) seed =
      alg.run (gaussianSourceMap G a) seed := by
  rw [gaussianSourcePolicy, Policy.mapOracle_run]
  congr 1
  funext w
  exact gaussianSource_oracle_replay G a w

theorem inverse_norm_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] (H M : E →L[ℝ] E) (hHM : ∀ x, H (M x) = x) : 0 < ‖M‖ := by
  apply norm_pos_iff.mpr
  intro hz
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h := hHM x
  rw [hz, ContinuousLinearMap.zero_apply, map_zero] at h
  exact hx h.symm

theorem reciprocal_factor_two {a b m x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hx : m / 2 ≤ x ∧ x ≤ 2 * m) :
    (a / (b * m)) / 2 ≤ a / (b * x) ∧ a / (b * x) ≤ 2 * (a / (b * m)) := by
  have hxp : 0 < x := by linarith
  constructor
  · have h := div_le_div_of_nonneg_left ha.le (mul_pos hb hxp)
      (mul_le_mul_of_nonneg_left hx.2 hb.le)
    convert h using 1 <;> ring
  · have h := div_le_div_of_nonneg_left ha.le (mul_pos hb (half_pos hm))
      (mul_le_mul_of_nonneg_left hx.1 hb.le)
    convert h using 1 <;> ring

def reciprocalSpectralEstimate (n : ℕ) (a x : ℝ) : ℝ := a / (Real.sqrt (n : ℝ) * x)

theorem gaussianSource_reciprocal_success {n : ℕ} (hn : 0 < n)
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : Function.Injective G.mulVec)
    (a : ℝ) (ha : 0 < a) (M : DilationSpace n →L[ℝ] DilationSpace n)
    (hHM : ∀ x, gaussianSourceMap G a (M x) = x)
    (hMH : ∀ x, M (gaussianSourceMap G a x) = x) {x : ℝ}
    (hx : ‖M‖ / 2 ≤ x ∧ x ≤ 2 * ‖M‖) :
    reciprocalSpectralEstimate n a x ∈ Set.Icc
      (leastStretch (matrixEuclideanMap G) / 2) (2 * leastStretch (matrixEuclideanMap G)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hM := inverse_norm_pos (gaussianSourceMap G a) M hHM
  have hi := gaussianSource_inverse_norm G hn hG a ha M hHM hMH
  have heq : a / (Real.sqrt (n : ℝ) * ‖M‖) = leastStretch (matrixEuclideanMap G) := by
    have hσ := gaussianSource_leastStretch G hn hG a ha
    rw [leastStretch_eq_inverse_norm _ M hHM hMH] at hσ
    have hh := congrArg (fun y : ℝ => y * (a / Real.sqrt (n : ℝ))) hσ
    field_simp at hh ⊢
    nlinarith
  have hh := reciprocal_factor_two ha hs hM hx
  rw [heq] at hh
  exact hh

end
end Matvec
