import HeavyTail.MaskedMomentTools
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent centered scalar moments

The elementary symmetrization argument behind the paper's independent-coordinate
oracle.  All integrals below are actual Bochner integrals under probability laws;
independence and centering, rather than a moment bound on the sum, are the inputs.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace HeavyTail.IndependentMoments
noncomputable section

lemma abs_add_rpow_le {p : ℝ} (hp : 1 ≤ p) (x y : ℝ) :
    |x + y| ^ p ≤ (2 : ℝ) ^ (p - 1) * (|x| ^ p + |y| ^ p) := by
  refine (Real.rpow_le_rpow (abs_nonneg _) (abs_add x y) (by linarith)).trans ?_
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
    (⟨|x|, abs_nonneg x⟩ : ℝ≥0) (⟨|y|, abs_nonneg y⟩ : ℝ≥0) hp

lemma scalar_clarkson {p : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2) (x y : ℝ) :
    (|x + y| ^ p + |x - y| ^ p) / 2 ≤ |x| ^ p + |y| ^ p := by
  have h := (Real.concaveOn_rpow (by linarith : 0 ≤ p / 2)
      (by linarith : p / 2 ≤ 1)).2
    (sq_nonneg (x + y)) (sq_nonneg (x - y))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul, gaussianLower_square_rpow] at h
  have hs : (1 : ℝ) / 2 * (x + y) ^ 2 + 1 / 2 * (x - y) ^ 2 = x ^ 2 + y ^ 2 := by ring
  rw [hs] at h
  have ht := Real.rpow_add_le_add_rpow (sq_nonneg x) (sq_nonneg y)
    (by linarith : 0 ≤ p / 2) (by linarith : p / 2 ≤ 1)
  rw [gaussianLower_square_rpow, gaussianLower_square_rpow] at ht
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma integrable_abs_add_rpow {X Y : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hX : Measurable X) (hY : Measurable Y)
    (hiX : Integrable (fun ω ↦ |X ω| ^ p) μ)
    (hiY : Integrable (fun ω ↦ |Y ω| ^ p) μ) :
    Integrable (fun ω ↦ |X ω + Y ω| ^ p) μ := by
  apply ((hiX.add hiY).const_mul ((2 : ℝ) ^ (p - 1))).mono'
  · exact (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp_aestronglyMeasurable
      (hX.add hY).abs.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact abs_add_rpow_le hp _ _

lemma abs_integral_rpow_le [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hi : Integrable X μ)
    (hip : Integrable (fun ω ↦ |X ω| ^ p) μ) :
    |∫ ω, X ω ∂μ| ^ p ≤ ∫ ω, |X ω| ^ p ∂μ := by
  have hnorm : |∫ ω, X ω ∂μ| ≤ ∫ ω, |X ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f := X) (μ := μ)
  refine (Real.rpow_le_rpow (abs_nonneg _) hnorm (by linarith)).trans ?_
  exact (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun ω ↦ abs_nonneg (X ω)) hi.abs hip

lemma integrable_fst {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (fun z : Ω × ℝ ↦ f z.1) (μ.prod ν) := by
  simpa using hf.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ ↦ (1 : ℝ)) ν)

lemma integrable_snd {ν : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f ν) :
    Integrable (fun z : Ω × ℝ ↦ f z.2) (μ.prod ν) := by
  simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ).mul_prod hf

lemma integrable_abs_sub_rpow {X Y : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hX : Measurable X) (hY : Measurable Y)
    (hiX : Integrable (fun ω ↦ |X ω| ^ p) μ)
    (hiY : Integrable (fun ω ↦ |Y ω| ^ p) μ) :
    Integrable (fun ω ↦ |X ω - Y ω| ^ p) μ := by
  simpa only [sub_eq_add_neg] using integrable_abs_add_rpow hp hX hY.neg hiX
    (by simpa only [abs_neg] using hiY)

/-- A centered independent increment costs at most `2^p` times its own moment.
The proof introduces an independent copy and averages the scalar Clarkson inequality. -/
theorem centered_increment_moment {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable (fun y : ℝ ↦ y) ν)
    (hip : Integrable (fun y : ℝ ↦ |y| ^ p) ν)
    (hmean : (∫ y : ℝ, y ∂ν) = 0) (x : ℝ) :
    (∫ y : ℝ, |x + y| ^ p ∂ν) ≤ |x| ^ p + (2 : ℝ) ^ p * ∫ y : ℝ, |y| ^ p ∂ν := by
  have hp0 : 0 ≤ p := by linarith
  have hd : Integrable (fun z : ℝ × ℝ ↦ |z.1 - z.2| ^ p) (ν.prod ν) :=
    integrable_abs_sub_rpow hp measurable_fst measurable_snd
      (integrable_fst hip) (integrable_snd hip)
  have hplus : Integrable (fun z : ℝ × ℝ ↦ |x + (z.1 - z.2)| ^ p) (ν.prod ν) :=
    integrable_abs_add_rpow hp measurable_const (measurable_fst.sub measurable_snd)
      (integrable_const _) hd
  have hminus : Integrable (fun z : ℝ × ℝ ↦ |x - (z.1 - z.2)| ^ p) (ν.prod ν) :=
    integrable_abs_sub_rpow hp measurable_const (measurable_fst.sub measurable_snd)
      (integrable_const _) hd
  have hsym : (∫ z : ℝ × ℝ, |x - (z.1 - z.2)| ^ p ∂ν.prod ν) =
      ∫ z : ℝ × ℝ, |x + (z.1 - z.2)| ^ p ∂ν.prod ν := by
    have hswap := integral_prod_swap (μ := ν) (ν := ν)
      (fun z : ℝ × ℝ ↦ |x - (z.1 - z.2)| ^ p)
    rw [← hswap]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z ↦ by congr 2 <;> simp only [Prod.swap]; ring
  have hc : (∫ z : ℝ × ℝ, |x + (z.1 - z.2)| ^ p ∂ν.prod ν) ≤
      |x| ^ p + ∫ z : ℝ × ℝ, |z.1 - z.2| ^ p ∂ν.prod ν := by
    have h := integral_mono ((hplus.add hminus).div_const 2)
      ((integrable_const (|x| ^ p)).add hd)
      (fun z ↦ scalar_clarkson hp0 hp2 x (z.1 - z.2))
    simp only [Pi.add_apply] at h
    rw [integral_div, integral_add hplus hminus, hsym,
      integral_add (integrable_const _) hd] at h
    simp only [integral_const, measureReal_univ_eq_one, one_smul] at h
    linarith
  have hdiff : (∫ z : ℝ × ℝ, |z.1 - z.2| ^ p ∂ν.prod ν) ≤
      (2 : ℝ) ^ p * ∫ y : ℝ, |y| ^ p ∂ν := by
    have hf := integrable_fst (μ := ν) (ν := ν) hip
    have hs := integrable_snd (μ := ν) (ν := ν) hip
    have h := integral_mono hd ((hf.add hs).const_mul ((2 : ℝ) ^ (p - 1)))
      (fun z ↦ by simpa only [sub_eq_add_neg, abs_neg] using abs_add_rpow_le hp z.1 (-z.2))
    simp only [Pi.add_apply] at h
    rw [integral_const_mul, integral_add hf hs,
      integral_fun_fst (fun y : ℝ ↦ |y| ^ p),
      integral_fun_snd (fun y : ℝ ↦ |y| ^ p)] at h
    simp only [measureReal_univ_eq_one, one_smul] at h
    have hpow : (2 : ℝ) ^ p = (2 : ℝ) ^ (p - 1) * 2 := by
      simpa only [sub_add_cancel, Real.rpow_one] using
        Real.rpow_add (by norm_num : (0 : ℝ) < 2) (p - 1) 1
    rw [hpow]
    nlinarith
  have hJ (y : ℝ) : |x + y| ^ p ≤ ∫ y' : ℝ, |x + (y - y')| ^ p ∂ν := by
    have hi' : Integrable (fun y' : ℝ ↦ x + y - y') ν := (integrable_const _).sub hi
    have hip' := integrable_abs_sub_rpow hp measurable_const measurable_id
      (integrable_const (|x + y| ^ p)) hip
    have hj := abs_integral_rpow_le hp hi' hip'
    rw [integral_sub (integrable_const _) hi, integral_const, measureReal_univ_eq_one,
      one_smul, hmean, sub_zero] at hj
    simpa only [sub_eq_add_neg, add_assoc] using hj
  have houter : (∫ y : ℝ, |x + y| ^ p ∂ν) ≤
      ∫ z : ℝ × ℝ, |x + (z.1 - z.2)| ^ p ∂ν.prod ν := by
    rw [integral_prod _ hplus]
    exact integral_mono
      (integrable_abs_add_rpow hp measurable_const measurable_id (integrable_const _) hip)
      hplus.integral_prod_left hJ
  exact houter.trans (hc.trans (add_le_add_left hdiff _))

/-- The independent-addition step, proved by transport to the product of the
two actual laws and the independent-copy estimate. -/
theorem independent_centered_add_moment [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    (hiY : Integrable Y μ) (hpX : Integrable (fun ω ↦ |X ω| ^ p) μ)
    (hpY : Integrable (fun ω ↦ |Y ω| ^ p) μ) (hmean : (∫ ω, Y ω ∂μ) = 0) :
    (∫ ω, |X ω + Y ω| ^ p ∂μ) ≤
      (∫ ω, |X ω| ^ p ∂μ) + (2 : ℝ) ^ p * ∫ ω, |Y ω| ^ p ∂μ := by
  let νX := μ.map X
  let νY := μ.map Y
  letI : IsProbabilityMeasure νX := isProbabilityMeasure_map hX.aemeasurable
  letI : IsProbabilityMeasure νY := isProbabilityMeasure_map hY.aemeasurable
  have hm : Measurable (fun y : ℝ ↦ |y| ^ p) :=
    (Real.continuous_rpow_const (by linarith : 0 ≤ p)).measurable.comp measurable_id.abs
  have hiY' : Integrable (fun y : ℝ ↦ y) νY :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hY.aemeasurable).2 hiY
  have hpX' : Integrable (fun y : ℝ ↦ |y| ^ p) νX :=
    (integrable_map_measure hm.aestronglyMeasurable hX.aemeasurable).2 hpX
  have hpY' : Integrable (fun y : ℝ ↦ |y| ^ p) νY :=
    (integrable_map_measure hm.aestronglyMeasurable hY.aemeasurable).2 hpY
  have hmean' : (∫ y : ℝ, y ∂νY) = 0 := by
    exact (integral_map (μ := μ) hY.aemeasurable
      (measurable_id.aestronglyMeasurable (μ := μ.map Y))).trans hmean
  have hprod : μ.map (fun ω ↦ (X ω, Y ω)) = νX.prod νY :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have hms : Measurable (fun z : ℝ × ℝ ↦ |z.1 + z.2| ^ p) :=
    hm.comp (measurable_fst.add measurable_snd)
  have his : Integrable (fun z : ℝ × ℝ ↦ |z.1 + z.2| ^ p) (νX.prod νY) :=
    integrable_abs_add_rpow hp measurable_fst measurable_snd
      (integrable_fst hpX') (integrable_snd hpY')
  calc
    _ = ∫ z : ℝ × ℝ, |z.1 + z.2| ^ p ∂νX.prod νY := by
      rw [← hprod, integral_map (hX.prodMk hY).aemeasurable hms.aestronglyMeasurable]
    _ = ∫ x : ℝ, (∫ y : ℝ, |x + y| ^ p ∂νY) ∂νX := integral_prod _ his
    _ ≤ ∫ x : ℝ, (|x| ^ p + (2 : ℝ) ^ p * ∫ y : ℝ, |y| ^ p ∂νY) ∂νX :=
      integral_mono his.integral_prod_left (hpX'.add (integrable_const _))
        (centered_increment_moment hp hp2 hiY' hpY' hmean')
    _ = _ := by
      rw [integral_add hpX' (integrable_const _), integral_const,
        measureReal_univ_eq_one, one_smul]
      rw [integral_map hX.aemeasurable hm.aestronglyMeasurable,
        integral_map hY.aemeasurable hm.aestronglyMeasurable]

lemma integrable_finset_sum_rpow {ι : Type*} {U : ι → Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hU : ∀ i, Measurable (U i)) (s : Finset ι)
    (hip : ∀ i ∈ s, Integrable (fun ω ↦ |U i ω| ^ p) μ) [IsFiniteMeasure μ] :
    Integrable (fun ω ↦ |∑ i ∈ s, U i ω| ^ p) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (integrable_const (|0| ^ p) : Integrable (fun _ : Ω ↦ |(0 : ℝ)| ^ p) μ)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact integrable_abs_add_rpow hp (hU i) (Finset.measurable_sum _ fun j _ ↦ hU j)
      (hip i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ hip j (Finset.mem_insert_of_mem hj)))

/-- The source's scalar independent centered moment inequality, with the
stated constant `2^p`, for every finite family and every `1 ≤ p ≤ 2`. -/
theorem independent_centered_sum_moment [IsProbabilityMeasure μ]
    {ι : Type*} {U : ι → Ω → ℝ} {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hU : ∀ i, Measurable (U i)) (hInd : iIndepFun U μ) (s : Finset ι)
    (hi : ∀ i ∈ s, Integrable (U i) μ)
    (hip : ∀ i ∈ s, Integrable (fun ω ↦ |U i ω| ^ p) μ)
    (hmean : ∀ i ∈ s, (∫ ω, U i ω ∂μ) = 0) :
    (∫ ω, |∑ i ∈ s, U i ω| ^ p ∂μ) ≤
      (2 : ℝ) ^ p * ∑ i ∈ s, ∫ ω, |U i ω| ^ p ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow (show p ≠ 0 by linarith)]
  | @insert i s his ih =>
    have hsum : Measurable (fun ω ↦ ∑ j ∈ s, U j ω) :=
      Finset.measurable_sum _ fun j _ ↦ hU j
    have hInd' : IndepFun (fun ω ↦ ∑ j ∈ s, U j ω) (U i) μ := by
      convert hInd.indepFun_finset_sum_of_not_mem hU his using 1
      ext ω
      simp
    have hbound := independent_centered_add_moment hp hp2 hsum (hU i) hInd'
      (hi i (Finset.mem_insert_self _ _))
      (integrable_finset_sum_rpow hp hU s (fun j hj ↦ hip j (Finset.mem_insert_of_mem hj)))
      (hip i (Finset.mem_insert_self _ _)) (hmean i (Finset.mem_insert_self _ _))
    have hrec := ih (fun j hj ↦ hi j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hip j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hmean j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert his]
    simp only [add_comm (U i _) (∑ j ∈ s, U j _)]
    exact hbound.trans (by linarith)

/-- Finite `p`-moment already supplies the first-moment integrability used in centering. -/
lemma integrable_of_abs_rpow [IsFiniteMeasure μ] {X : Ω → ℝ} {p : ℝ}
    (hp : 1 ≤ p) (hX : Measurable X) (hip : Integrable (fun ω ↦ |X ω| ^ p) μ) :
    Integrable X μ := by
  apply ((integrable_const (1 : ℝ)).add hip).mono' hX.aestronglyMeasurable
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  change |X ω| ≤ 1 + |X ω| ^ p
  by_cases hx : |X ω| ≤ 1
  · linarith [Real.rpow_nonneg (abs_nonneg (X ω)) p]
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hp
    rw [Real.rpow_one] at h
    linarith

/-- The independent centered inequality stated using only measurable independent
variables, their finite `p`-moments, and their zero means. -/
theorem independent_centered_sum_moment_of_rpow [IsProbabilityMeasure μ]
    {ι : Type*} {U : ι → Ω → ℝ} {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hU : ∀ i, Measurable (U i)) (hInd : iIndepFun U μ) (s : Finset ι)
    (hip : ∀ i ∈ s, Integrable (fun ω ↦ |U i ω| ^ p) μ)
    (hmean : ∀ i ∈ s, (∫ ω, U i ω ∂μ) = 0) :
    (∫ ω, |∑ i ∈ s, U i ω| ^ p ∂μ) ≤
      (2 : ℝ) ^ p * ∑ i ∈ s, ∫ ω, |U i ω| ^ p ∂μ :=
  independent_centered_sum_moment hp hp2 hU hInd s
    (fun i hi ↦ integrable_of_abs_rpow hp (hU i) (hip i hi)) hip hmean

end
end HeavyTail.IndependentMoments
