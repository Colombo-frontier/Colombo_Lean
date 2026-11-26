import Nonsmooth.GaussianCombination
import Nonsmooth.NetOperator
import Nonsmooth.GaussianSpectralBridge

open MeasureTheory ProbabilityTheory Function
open scoped InnerProductSpace ENNReal Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
namespace Nonsmooth
noncomputable section

theorem gaussian_net_tail_numeric {d : ℝ} (hd : 256 ≤ d) {k : ℕ}
    (hk : (k : ℝ) ≤ d / 512) :
    (33 : ℝ) ^ k * (2 * Real.exp (-d / 32)) ≤ 1 / 16 := by
  have htwo : 2 ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hlog : Real.log 33 ≤ 6 := by
    have h : (33 : ℝ) ≤ Real.exp 6 := calc
      33 ≤ (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) htwo 6
      _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h' := Real.log_le_log (by norm_num : (0 : ℝ) < 33) h
    simpa only [Real.log_exp] using h'
  have hpow : (33 : ℝ) ^ k ≤ Real.exp (6 * (k : ℝ)) := calc
    _ = Real.exp ((k : ℝ) * Real.log 33) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 33)]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)
      nlinarith)
  have hexp : 32 ≤ Real.exp 5 := calc
    32 = (2 : ℝ) ^ 5 := by norm_num
    _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) htwo 5
    _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
  have hsmall : 2 * Real.exp (-5) ≤ 1 / 16 := by
    rw [Real.exp_neg]
    have h := (inv_le_inv₀ (Real.exp_pos 5) (by positivity : (0 : ℝ) < 32)).mpr hexp
    norm_num at h
    linarith
  calc
    _ ≤ Real.exp (6 * (k : ℝ)) * (2 * Real.exp (-d / 32)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 * Real.exp (6 * (k : ℝ) + -d / 32) := by rw [Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-5) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ 1 / 16 := hsmall

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem gaussianScaleRows_gram_of_raw_bound {k : ℕ} (b : Fin k → E)
    (hb : ∀ c : Fin k → ℝ, ((Module.finrank ℝ E : ℝ) / 4) * (∑ i, (c i) ^ 2) ≤
      ‖supportRowSynthesis b c‖ ^ 2) :
    gaussianScaleRows E k b ∈ supportGramGood E k := by
  intro c
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hsqrt : (Real.sqrt (Module.finrank ℝ E)) ^ 2 = (Module.finrank ℝ E : ℝ) :=
    Real.sq_sqrt hd.le
  have he : (∑ i, c i • gaussianScaleRows E k b i) =
      (Real.sqrt (Module.finrank ℝ E))⁻¹ • supportRowSynthesis b c := by
    change (∑ i, c i • ((Real.sqrt (Module.finrank ℝ E))⁻¹ • b i)) =
      (Real.sqrt (Module.finrank ℝ E))⁻¹ • ∑ i, c i • b i
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  rw [he, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, inv_pow, hsqrt]
  have h := mul_le_mul_of_nonneg_left (hb c) (inv_nonneg.mpr hd.le)
  field_simp at h ⊢
  nlinarith

theorem gaussian_rows_spectral_probability
    (hd : 256 ≤ Module.finrank ℝ E) {k : ℕ}
    (hk : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512) :
    15 / 16 ≤ (Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)).real
      ((gaussianScaleRows E k) ⁻¹' supportGramGood E k) := by
  classical
  obtain ⟨s, hunit, hcard, hnet⟩ := unit_sphere_finite_net (E := EuclideanSpace ℝ (Fin k))
  let P := Measure.pi (fun _ : Fin k => euclideanGaussianLaw E)
  let bad : EuclideanSpace ℝ (Fin k) → Set (Fin k → E) := fun c =>
    {b | ‖supportRowSynthesis b (fun i => c i)‖ ^ 2 < (Module.finrank ℝ E : ℝ) / 2 ∨
      2 * (Module.finrank ℝ E : ℝ) < ‖supportRowSynthesis b (fun i => c i)‖ ^ 2}
  let U : Set (Fin k → E) := ⋃ c ∈ s, bad c
  have htail (c : EuclideanSpace ℝ (Fin k)) (hc : c ∈ s) :
      P.real (bad c) ≤ 2 * Real.exp (-(Module.finrank ℝ E : ℝ) / 32) := by
    apply gaussianRows_unit_combination_concentration
    rw [← euclidean_coeff_norm_square, hunit c hc]
    norm_num
  have hU : P.real U ≤ 1 / 16 := calc
    _ ≤ ∑ c ∈ s, P.real (bad c) := measureReal_biUnion_finset_le s bad
    _ ≤ ∑ c ∈ s, 2 * Real.exp (-(Module.finrank ℝ E : ℝ) / 32) :=
      Finset.sum_le_sum (fun c hc => htail c hc)
    _ = (s.card : ℝ) * (2 * Real.exp (-(Module.finrank ℝ E : ℝ) / 32)) := by simp
    _ ≤ (33 : ℝ) ^ k * (2 * Real.exp (-(Module.finrank ℝ E : ℝ) / 32)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [finrank_euclideanSpace_fin, Nat.cast_pow, Nat.cast_ofNat] using
        (show (s.card : ℝ) ≤ (33 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) : ℕ) by exact_mod_cast hcard)
    _ ≤ 1 / 16 := gaussian_net_tail_numeric (by exact_mod_cast hd) hk
  have hsub : ((gaussianScaleRows E k) ⁻¹' supportGramGood E k)ᶜ ⊆ U := by
    intro b hb
    by_contra hnot
    apply hb
    change gaussianScaleRows E k b ∈ supportGramGood E k
    refine gaussianScaleRows_gram_of_raw_bound (E := E) (k := k) b ?_
    have hs (c : EuclideanSpace ℝ (Fin k)) (hc : c ∈ s) :
        (Module.finrank ℝ E : ℝ) / 2 ≤ ‖supportRowSynthesis b (fun i => c i)‖ ^ 2 ∧
          ‖supportRowSynthesis b (fun i => c i)‖ ^ 2 ≤ 2 * (Module.finrank ℝ E : ℝ) := by
      have hn : b ∉ bad c := fun h => hnot (Set.mem_iUnion₂.mpr ⟨c, hc, h⟩)
      exact ⟨le_of_not_gt (fun h => hn (Or.inl h)), le_of_not_gt (fun h => hn (Or.inr h))⟩
    have h := support_synthesis_lower_of_net b s hnet (Real.sqrt_nonneg (Module.finrank ℝ E))
      (by simpa only [Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))] using hs)
    simpa only [Real.sq_sqrt (Nat.cast_nonneg (Module.finrank ℝ E))] using h
  have hcomp := (measureReal_mono (μ := P) hsub (measure_ne_top _ _)).trans hU
  have hsum := measureReal_add_measureReal_compl (μ := P)
    ((gaussianScaleRows_measurable k) (supportGramGood_closed (E := E) k).measurableSet)
  rw [probReal_univ] at hsum
  linarith

theorem gaussianSupportPrior_negative_event
    (hd : 256 ≤ Module.finrank ℝ E) {k : ℕ} (hk : 0 < k)
    (hkd : (k : ℝ) ≤ (Module.finrank ℝ E : ℝ) / 512) :
    letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    7 / 8 ≤ (gaussianSupportPrior E k).real {a : BoundedSupportRows E (Fin k) |
      (1 / 4 : ℝ) / Real.sqrt k ≤ -minimumValue 1 (boundedFiniteSupport a)} := by
  apply gaussianSupportPrior_negative_of_spectral_probability hk _ (gaussian_rows_spectral_probability hd hkd)
  have hd0 : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
  linarith

end
end Nonsmooth
