import AdaptiveSphereSourceRisk

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Task006.AdaptiveSphereSourceEvent
open Task006.Full Task006.Full.OracleAlgorithm Task006.Full.HardFamily
open Task006.HaarRebalancing Task006.AdaptiveSphereFrame Task006.AdaptiveSphereState
open Task006.AdaptiveSphereGlobal Task006.PosteriorCenter Task006.HardFamilyBayes
noncomputable section
variable {d N : ℕ} {S : Type*} [MeasurableSpace S]

/-- Literal no-informative-handle event {K=0}={2K<1} has the source probability
25/32 in the small-dimensional regime. -/
theorem sourceHandleEvent_small_mass (alg : OracleAlgorithm d N S)
    (L A : ℝ) (hL : 0<L) (hA : 16≤A) (σ : Measure S) [IsProbabilityMeasure σ]
    (hd7 : d≤7) (j : Fin d) (hbudget : (4096/A^3)*(N:ℝ) ≤ (d:ℝ)/32) :
    (25/32:ℝ) ≤ ((σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)).real
      (sourceHandleEvent alg j 1) := by
  let μ := (σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)
  have hEK : (∫ w, (originalK alg j w:ℝ) ∂μ) ≤ 7/32 := by
    have h := (originalK_expectation alg j L A hL hA σ).trans hbudget
    have hd : (d:ℝ)≤7 := by exact_mod_cast hd7
    linarith
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Filter.Eventually.of_forall (fun w => Nat.cast_nonneg (originalK alg j w)))
    (originalK_integrable alg j μ) (1:ℝ)
  have hb : μ.real {w | (1:ℝ)≤(originalK alg j w:ℝ)} ≤ 7/32 := by
    simpa only [one_mul] using hm.trans hEK
  have he : sourceHandleEvent alg j 1 = {w | (1:ℝ)≤(originalK alg j w:ℝ)}ᶜ := by
    ext w
    change 2*originalK alg j w<1 ↔ ¬(1:ℝ)≤(originalK alg j w:ℝ)
    constructor
    · intro h
      have hz : originalK alg j w=0 := by omega
      simp [hz]
    · intro h
      have hz : originalK alg j w=0 := by
        by_contra hn
        have hNat : 1≤originalK alg j w := Nat.one_le_iff_ne_zero.mpr hn
        have hReal : (1:ℝ)≤(originalK alg j w:ℝ) := by exact_mod_cast hNat
        exact h hReal
      simp [hz]
  rw [he,probReal_compl_eq_one_sub (measurableSet_le measurable_const (originalK_measurable alg j))]
  linarith

/-- Literal small-dimensional source bound B≥(25/2)epsilon, with no assumed
risk inequality: the actual CE/output argument is used on the K=0 event. -/
theorem source_small_dimension_bayes_risk_ge (alg : OracleAlgorithm d N S) (j : Fin d)
    (L R A eps : ℝ) (hL : 0<L) (hR : 0≤R) (hA : 16≤A) (heps : 0<eps)
    (hscale : (16*L/A)*R=16*eps) (h1d : 1≤d) (hd7 : d≤7)
    (hlegal : LegalOriginal alg R) (σ : Measure S) [IsProbabilityMeasure σ]
    (hbudget : (4096/A^3)*(N:ℝ) ≤ (d:ℝ)/32) :
    (25/2:ℝ)*eps ≤ (∫ w, originalGap alg j R (16*L/A) w
      ∂(σ.prod (iidHandleLaw (law L A hA))).prod (orthogonalHaarProbability d)) := by
  have hm : 0≤16*L/A := by positivity
  have hrisk := source_originalGap_risk_lower alg 1 h1d j R (16*L/A) hR hm hlegal
    (σ.prod (iidHandleLaw (law L A hA)))
  have hzero : (sourceHandleEvent alg j 1).indicator (fun w => ‖jointCenter alg 1 h1d N j w‖) =
      (fun _ => (0:ℝ)) := by
    funext w
    by_cases hw : w∈sourceHandleEvent alg j 1
    · rw [Set.indicator_of_mem hw,center_zero_on_zero_rank_event alg h1d j w
        (source_event_subset_goodRankEvent alg R hlegal 1 h1d j w hw),norm_zero]
    · rw [Set.indicator_of_notMem hw]
  rw [hzero,integral_zero,sub_zero,hscale] at hrisk
  have ha := sourceHandleEvent_small_mass alg L A hL hA σ hd7 j hbudget
  have hmul := mul_le_mul_of_nonneg_left ha (by positivity : 0≤16*eps)
  nlinarith

/-- The displayed normalized event moments follow from the already established
actual unnormalized mass, energy and Cauchy--Schwarz estimates. -/
theorem normalized_event_moments (a n e : ℝ) (ha : 1/2≤a) (hn : 0≤n)
    (he : e≤1/3) (hCS : n^2≤a*e) :
    e/a≤2/3 ∧ n/a≤Real.sqrt (2/3:ℝ) := by
  have ha0 : 0<a := by linarith
  constructor
  · apply (div_le_iff₀ ha0).mpr
    linarith
  · have hs0 := Real.sqrt_nonneg (2/3:ℝ)
    have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hb : n^2≤a/3 := hCS.trans (by nlinarith)
    have haa := mul_nonneg ha0.le (show 0≤a-1/2 by linarith)
    have hsquare : (a*Real.sqrt (2/3:ℝ))^2 = a^2*(2/3) := by rw [mul_pow,hs2]
    have hr0 : 0≤a*Real.sqrt (2/3:ℝ) := mul_nonneg ha0.le hs0
    apply (div_le_iff₀ ha0).mpr
    nlinarith

#print axioms sourceHandleEvent_small_mass
#print axioms source_small_dimension_bayes_risk_ge
#print axioms normalized_event_moments
end
end Task006.AdaptiveSphereSourceEvent
