import Smoothness2601.PopulationDifferencing
import Smoothness2601.SequentialBatches
import Smoothness2601.WeightedBatches
import Smoothness2601.InnerOracle

/-! The manuscript's actual sampled Chebyshev estimator. Every node average
is executed through the original full-gradient conditional kernel, and the
finite integer count records every original oracle call. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Bilevel.PrimitiveGeometry Bilevel.Stateful
namespace Smoothness2601.DifferencingOracle
open ChebyshevDifferentiation Population

def nodeWeight (k : ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  if hj : j < 2*k+2 then explicitWeight k h ⟨j,hj⟩ else 1

theorem nodeWeight_ne_zero (k : ℕ) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    nodeWeight k h j ≠ 0 := by
  unfold nodeWeight
  split_ifs with hj
  · unfold explicitWeight
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) hh.ne')
        (endpointFactor_pos _ _).ne')
        (pow_ne_zero _ (node_ne_zero (by exact ⟨k, by omega⟩) _)))
  · norm_num

theorem nodeWeight_norm (k : ℕ) {h : ℝ} (hh : 0 < h) :
    WeightedBatches.weightNorm (Finset.range (2*k+2)) (nodeWeight k h) = (2*k+1 : ℕ)/h := by
  rw [WeightedBatches.weightNorm, ← Fin.sum_univ_eq_sum_range]
  simpa only [nodeWeight, dif_pos (Fin.isLt _)] using explicit_weights_abs_sum k hh

def nodeBatch (k : ℕ) (h B : ℝ) : ℕ → ℕ :=
  WeightedBatches.nodeCount (Finset.range (2*k+2)) (nodeWeight k h) B

theorem nodeBatch_pos (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B) (j : ℕ) :
    0 < nodeBatch k h B j := by
  apply WeightedBatches.nodeCount_pos hB _ (nodeWeight_ne_zero k hh j)
  rw [nodeWeight_norm k hh]
  positivity

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

def query (k : ℕ) (h : ℝ) (j : ℕ) (p : X × Y × Y) : Adaptive.Query X Y :=
  if hj : j < 2*k+2 then (true, p.1, p.2.1 + (h * node (2*k+1) ⟨j,hj⟩) • p.2.2)
  else (true,p.1,p.2.1)

omit [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [BorelSpace X]
  [CompleteSpace Y] [SecondCountableTopology X] in
theorem query_measurable (k : ℕ) (h : ℝ) (j : ℕ) :
    Measurable (query (X := X) (Y := Y) k h j) := by
  unfold query
  split_ifs <;> fun_prop

variable {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {History : Type} [MeasurableSpace History] (O : Adaptive.Oracle P History)

def estimator (k : ℕ) (h B : ℝ) : Procedure (X × Y × Y) History (Joint X Y) :=
  SequentialBatches.run (InnerOracle.fullJoint P O) (query k h) (query_measurable k h)
    (nodeWeight k h) (nodeBatch k h B) (2*k+2)

omit [SecondCountableTopology X] in
theorem estimator_truth (k : ℕ) (h : ℝ) (p : X × Y × Y) :
    SequentialBatches.mean (InnerOracle.fullJoint P O) (query k h) (nodeWeight k h) (2*k+2) p =
      P.gradientDifference p.1 p.2.1 p.2.2 k h := by
  rw [SequentialBatches.mean, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [nodeWeight, query, dif_pos i.isLt]
  rfl

/-- Exact conditional mean of the actually executed estimator. -/
theorem estimator_mean (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B) :
    (estimator P O k h B).Mean (fun p => P.gradientDifference p.1 p.2.1 p.2.2 k h) := by
  have he := SequentialBatches.run_mean (InnerOracle.fullJoint P O) (query k h) (query_measurable k h)
    (nodeWeight k h) (nodeBatch k h B) (nodeBatch_pos k hh hB) (nodeWeight_ne_zero k hh) (2*k+2)
  have heq : SequentialBatches.mean (InnerOracle.fullJoint P O) (query k h) (nodeWeight k h) (2*k+2) =
      fun p => P.gradientDifference p.1 p.2.1 p.2.2 k h := funext (estimator_truth P O k h)
  rwa [heq] at he

/-- Every node uses exactly its ceiling allocation of original calls. -/
theorem estimator_calls (k : ℕ) (h B : ℝ) :
    (estimator P O k h B).CallsEq
      (fun _ => ∑ j ∈ Finset.range (2*k+2), nodeBatch k h B j) :=
  SequentialBatches.run_calls _ _ _ _ _ _

theorem estimator_count_bound (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B) :
    ((∑ j ∈ Finset.range (2*k+2), nodeBatch k h B j : ℕ) : ℝ) ≤ B+(2*k+2) := by
  have hW : 0 < WeightedBatches.weightNorm (Finset.range (2*k+2)) (nodeWeight k h) := by
    rw [nodeWeight_norm k hh]
    positivity
  simpa only [Nat.cast_sum, Finset.card_range, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat] using WeightedBatches.node_cost (s := Finset.range (2*k+2))
      (d := nodeWeight k h) hB.le hW

theorem estimator_varianceBudget (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B) :
    SequentialBatches.varianceBudget (σ := b.σ) (nodeWeight k h) (nodeBatch k h B) (2*k+2) ≤
      b.σ ^ 2 * ((2*k+1 : ℕ)/h) ^ 2 / B := by
  have hW : 0 < WeightedBatches.weightNorm (Finset.range (2*k+2)) (nodeWeight k h) := by
    rw [nodeWeight_norm k hh]
    positivity
  have ha := mul_le_mul_of_nonneg_left
    (WeightedBatches.variance_allocation (s := Finset.range (2*k+2)) (d := nodeWeight k h) hB hW)
    (sq_nonneg b.σ)
  rw [nodeWeight_norm k hh] at ha
  convert ha using 1
  · simp only [SequentialBatches.varianceBudget, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    unfold nodeBatch
    ring
  · ring

/-- Squared error about any fixed center: exact squared bias plus the
conditional variance bound, proved for every entering oracle history. -/
theorem estimator_center_error (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B)
    (p : X × Y × Y) (history : History) (center : Joint X Y) :
    Integrable (fun z => ‖z.1-center‖^2) ((estimator P O k h B).law (p,history)) ∧
    (∫ z, ‖z.1-center‖^2 ∂(estimator P O k h B).law (p,history)) ≤
      ‖P.gradientDifference p.1 p.2.1 p.2.2 k h-center‖^2 +
        b.σ^2*((2*k+1:ℕ)/h)^2/B := by
  have he := SequentialBatches.run_center_error (InnerOracle.fullJoint P O) (query k h)
    (query_measurable k h) (nodeWeight k h) (nodeBatch k h B)
    (nodeBatch_pos k hh hB) (nodeWeight_ne_zero k hh) (2*k+2) p history center
  rw [estimator_truth] at he
  exact ⟨he.1, he.2.trans (add_le_add_left (estimator_varianceBudget (b := b) k hh hB) _)⟩

theorem estimator_variance (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B)
    (p : X × Y × Y) (history : History) :
    Integrable (fun z => ‖z.1-P.gradientDifference p.1 p.2.1 p.2.2 k h‖^2)
      ((estimator P O k h B).law (p,history)) ∧
    (∫ z, ‖z.1-P.gradientDifference p.1 p.2.1 p.2.2 k h‖^2
      ∂(estimator P O k h B).law (p,history)) ≤ b.σ^2*((2*k+1:ℕ)/h)^2/B := by
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add] using
    estimator_center_error P O k hh hB p history (P.gradientDifference p.1 p.2.1 p.2.2 k h)

theorem estimator_expectation (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B)
    (p : X × Y × Y) (history : History) :
    Integrable (fun z => z.1) ((estimator P O k h B).law (p,history)) ∧
    (∫ z, z.1 ∂(estimator P O k h B).law (p,history)) =
      P.gradientDifference p.1 p.2.1 p.2.2 k h := by
  have hm := estimator_mean P O k hh hB p history
  have hc := integrable_const (μ := (estimator P O k h B).law (p,history))
    (P.gradientDifference p.1 p.2.1 p.2.2 k h)
  have hi : Integrable (fun z => z.1) ((estimator P O k h B).law (p,history)) := by
    convert hm.1.add hc using 1
    funext z
    exact (sub_add_cancel _ _).symm
  refine ⟨hi, ?_⟩
  have he := integral_sub hi hc
  simp only [Pi.sub_apply, hm.2, integral_const, measureReal_univ_eq_one, one_smul] at he
  exact sub_eq_zero.mp he.symm

/-- Population bias and stochastic variance for the actual source radius,
with every hypothesis inherited from the original Population/Oracle. -/
theorem estimator_population_error {pmax : WithTop ℕ} {M Λ β V a B : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hV : 1 ≤ V) (ha : 0 < a) (hB : 0 < B)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax)
    (x : X) (y v : Y) (hv : ‖v‖ ≤ V) (history : History) :
    Integrable (fun z => ‖z.1-pack (P.gxy x y v) (P.gyy x y v)‖^2)
      ((estimator P O (stencilHalfOrder r) (populationRadius b M Λ β V a r) B).law
        ((x,y,v),history)) ∧
    (∫ z, ‖z.1-pack (P.gxy x y v) (P.gyy x y v)‖^2
      ∂(estimator P O (stencilHalfOrder r) (populationRadius b M Λ β V a r) B).law
        ((x,y,v),history)) ≤
      a^2 + b.σ^2 * ((stencilDegree r : ℝ)/(populationRadius b M Λ β V a r))^2/B := by
  have he := estimator_center_error P O (stencilHalfOrder r)
    (populationRadius_pos (b := b) (M := M) (Λ := Λ) (β := β) hV ha r)
    hB (x,y,v) history (pack (P.gxy x y v) (P.gyy x y v))
  have hb := P.populationRadius_bias hM hΛ hβ hV ha hreg r hr hrp x y v hv
  exact ⟨he.1, he.2.trans (add_le_add_right ((sq_le_sq₀ (norm_nonneg _) ha.le).mpr hb) _)⟩

omit [CompleteSpace X] [CompleteSpace Y] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem joint_snd_norm_le (z : Joint X Y) : ‖z.snd‖ ≤ ‖z‖ := by
  have he := norm_sq z
  nlinarith [sq_nonneg ‖z.fst‖, norm_nonneg z, norm_nonneg z.snd]

def estimatorY (k : ℕ) (h B : ℝ) : Procedure (X × Y × Y) History Y :=
  (estimator P O k h B).map (fun z => z.2.snd)
    ((fullSnd (X := X) (Y := Y)).continuous.measurable.comp measurable_snd)

theorem estimatorY_calls (k : ℕ) (h B : ℝ) :
    (estimatorY P O k h B).CallsEq
      (fun _ => ∑ j ∈ Finset.range (2*k+2), nodeBatch k h B j) :=
  Procedure.CallsEq.map _ _ (estimator_calls P O k h B) _ _

theorem estimatorY_mean (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B) :
    (estimatorY P O k h B).Mean (fun p => (P.gradientDifference p.1 p.2.1 p.2.2 k h).snd) := by
  intro p history
  have hm := estimator_mean P O k hh hB p history
  have hg : StronglyMeasurable
      (fun y : Y => y-(P.gradientDifference p.1 p.2.1 p.2.2 k h).snd) :=
    (by fun_prop : Measurable
      (fun y : Y => y-(P.gradientDifference p.1 p.2.1 p.2.2 k h).snd)).stronglyMeasurable
  constructor
  · rw [estimatorY, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    exact (fullSnd (X := X) (Y := Y)).integrable_comp hm.1
  · rw [estimatorY, Procedure.map_output_integral _ _ _ _ _ _ hg]
    have he := (fullSnd (X := X) (Y := Y)).integral_comp_comm hm.1
    rw [hm.2, map_zero] at he
    exact he

/-- The lower block keeps the exact arbitrary-center second-moment estimate;
this is the interface used by the actual projected adjoint iteration. -/
theorem estimatorY_center_error (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B)
    (p : X × Y × Y) (history : History) (center : Y) :
    Integrable (fun z => ‖z.1-center‖^2) ((estimatorY P O k h B).law (p,history)) ∧
    (∫ z, ‖z.1-center‖^2 ∂(estimatorY P O k h B).law (p,history)) ≤
      ‖(P.gradientDifference p.1 p.2.1 p.2.2 k h).snd-center‖^2 +
        b.σ^2*((2*k+1:ℕ)/h)^2/B := by
  let Z := P.gradientDifference p.1 p.2.1 p.2.2 k h
  let c : Joint X Y := pack Z.fst center
  have he := estimator_center_error P O k hh hB p history c
  have hg : StronglyMeasurable (fun y : Y => ‖y-center‖^2) :=
    (by fun_prop : Measurable (fun y : Y => ‖y-center‖^2)).stronglyMeasurable
  have hm : Measurable (fun z : Outcome (Joint X Y) History => ‖z.1.snd-center‖^2) :=
    (by fun_prop : Measurable (fun y : Y => ‖y-center‖^2)).comp
      ((fullSnd (X := X) (Y := Y)).continuous.measurable.comp measurable_fst)
  have hbound (z : Outcome (Joint X Y) History) : ‖z.1.snd-center‖^2 ≤ ‖z.1-c‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (joint_snd_norm_le (z.1-c))
  have hi : Integrable (fun z => ‖z.1.snd-center‖^2) ((estimator P O k h B).law (p,history)) := by
    apply he.1.mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hbound z
  constructor
  · rw [estimatorY, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    exact hi
  · rw [estimatorY, Procedure.map_output_integral _ _ _ _ _ _ hg]
    have hb := (integral_mono hi he.1 hbound).trans he.2
    have hc : ‖Z-c‖^2 = ‖Z.snd-center‖^2 := by
      rw [norm_sq]
      change ‖Z.fst-Z.fst‖^2 + ‖Z.snd-center‖^2 = _
      simp
    exact hb.trans_eq (by rw [hc])

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem populationRadius_y_bias {pmax : WithTop ℕ} {M Λ β V a : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hV : 1 ≤ V) (ha : 0 < a)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax)
    (x : X) (y v : Y) (hv : ‖v‖ ≤ V) :
    ‖(P.gradientDifference x y v (stencilHalfOrder r) (populationRadius b M Λ β V a r)).snd -
      P.gyy x y v‖ ≤ a :=
  (joint_snd_norm_le _).trans (P.populationRadius_bias hM hΛ hβ hV ha hreg r hr hrp x y v hv)

omit [CompleteSpace X] [CompleteSpace Y] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem joint_fst_norm_le (z : Joint X Y) : ‖z.fst‖ ≤ ‖z‖ := by
  have he := norm_sq z
  nlinarith [sq_nonneg ‖z.snd‖, norm_nonneg z, norm_nonneg z.fst]

def estimatorX (k : ℕ) (h B : ℝ) : Procedure (X × Y × Y) History X :=
  (estimator P O k h B).map (fun z => z.2.fst)
    ((fullFst (X := X) (Y := Y)).continuous.measurable.comp measurable_snd)

theorem estimatorX_calls (k : ℕ) (h B : ℝ) :
    (estimatorX P O k h B).CallsEq
      (fun _ => ∑ j ∈ Finset.range (2*k+2), nodeBatch k h B j) :=
  Procedure.CallsEq.map _ _ (estimator_calls P O k h B) _ _

theorem estimatorX_mean (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B) :
    (estimatorX P O k h B).Mean (fun p => (P.gradientDifference p.1 p.2.1 p.2.2 k h).fst) := by
  intro p history
  have hm := estimator_mean P O k hh hB p history
  have hg : StronglyMeasurable
      (fun x : X => x-(P.gradientDifference p.1 p.2.1 p.2.2 k h).fst) :=
    (by fun_prop : Measurable
      (fun x : X => x-(P.gradientDifference p.1 p.2.1 p.2.2 k h).fst)).stronglyMeasurable
  constructor
  · rw [estimatorX, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    exact (fullFst (X := X) (Y := Y)).integrable_comp hm.1
  · rw [estimatorX, Procedure.map_output_integral _ _ _ _ _ _ hg]
    have he := (fullFst (X := X) (Y := Y)).integral_comp_comm hm.1
    rw [hm.2, map_zero] at he
    exact he

theorem estimatorX_center_error (k : ℕ) {h B : ℝ} (hh : 0 < h) (hB : 0 < B)
    (p : X × Y × Y) (history : History) (center : X) :
    Integrable (fun z => ‖z.1-center‖^2) ((estimatorX P O k h B).law (p,history)) ∧
    (∫ z, ‖z.1-center‖^2 ∂(estimatorX P O k h B).law (p,history)) ≤
      ‖(P.gradientDifference p.1 p.2.1 p.2.2 k h).fst-center‖^2 +
        b.σ^2*((2*k+1:ℕ)/h)^2/B := by
  let Z := P.gradientDifference p.1 p.2.1 p.2.2 k h
  let c : Joint X Y := pack center Z.snd
  have he := estimator_center_error P O k hh hB p history c
  have hg : StronglyMeasurable (fun x : X => ‖x-center‖^2) :=
    (by fun_prop : Measurable (fun x : X => ‖x-center‖^2)).stronglyMeasurable
  have hm : Measurable (fun z : Outcome (Joint X Y) History => ‖z.1.fst-center‖^2) :=
    (by fun_prop : Measurable (fun x : X => ‖x-center‖^2)).comp
      ((fullFst (X := X) (Y := Y)).continuous.measurable.comp measurable_fst)
  have hbound (z : Outcome (Joint X Y) History) : ‖z.1.fst-center‖^2 ≤ ‖z.1-c‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (joint_fst_norm_le (z.1-c))
  have hi : Integrable (fun z => ‖z.1.fst-center‖^2) ((estimator P O k h B).law (p,history)) := by
    apply he.1.mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hbound z
  constructor
  · rw [estimatorX, Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    exact hi
  · rw [estimatorX, Procedure.map_output_integral _ _ _ _ _ _ hg]
    have hb := (integral_mono hi he.1 hbound).trans he.2
    have hc : ‖Z-c‖^2 = ‖Z.fst-center‖^2 := by
      rw [norm_sq]
      change ‖Z.fst-center‖^2 + ‖Z.snd-Z.snd‖^2 = _
      simp
    exact hb.trans_eq (by rw [hc])

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem populationRadius_x_bias {pmax : WithTop ℕ} {M Λ β V a : ℝ}
    (hM : 0 < M) (hΛ : 0 < Λ) (hβ : 0 ≤ β) (hV : 1 ≤ V) (ha : 0 < a)
    (hreg : P.HigherRegularity pmax (derivativeEnvelope b M Λ β))
    (r : ℕ) (hr : 1 ≤ r) (hrp : (r : WithTop ℕ) ≤ pmax)
    (x : X) (y v : Y) (hv : ‖v‖ ≤ V) :
    ‖(P.gradientDifference x y v (stencilHalfOrder r) (populationRadius b M Λ β V a r)).fst -
      P.gxy x y v‖ ≤ a :=
  (joint_fst_norm_le _).trans (P.populationRadius_bias hM hΛ hβ hV ha hreg r hr hrp x y v hv)

end Smoothness2601.DifferencingOracle
