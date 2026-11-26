import Smoothness2601.InnerBatch
import Smoothness2601.AdjointContraction

/-! Actual serial difference/upper-gradient updates and radial projection.
All second-moment identities are derived from the two executed kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open Bilevel.Stateful
namespace Smoothness2601.AdjointKernels

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace Ω] {ν : Measure Ω}

theorem affine_error (z : Ω → E) (m d center : E) {α S : ℝ} (hα : α ≠ 0)
    (hc : ∀ c, Integrable (fun ω => ‖z ω-c‖ ^ 2) ν ∧
      (∫ ω, ‖z ω-c‖ ^ 2 ∂ν) ≤ ‖m-c‖ ^ 2+S) :
    Integrable (fun ω => ‖d-α • z ω-center‖ ^ 2) ν ∧
    (∫ ω, ‖d-α • z ω-center‖ ^ 2 ∂ν) ≤ ‖d-α • m-center‖ ^ 2+α ^ 2*S := by
  let c := α⁻¹ • (d-center)
  have he (v : E) : ‖d-α • v-center‖ ^ 2 = α ^ 2*‖v-c‖ ^ 2 := by
    have hv : d-α • v-center = -α • (v-c) := by
      dsimp [c]
      rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hα, neg_one_smul]
      module
    rw [hv,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,neg_sq]
  have hi := (hc c).1.const_mul (α ^ 2)
  constructor
  · simpa only [he] using hi
  · simp_rw [he]
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left (hc c).2 (sq_nonneg α)
    simpa only [mul_add] using hb

variable {Param Query History Obs : Type*} [MeasurableSpace Param] [MeasurableSpace Query]
  [MeasurableSpace History] [MeasurableSpace Obs]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {σ : ℝ} (O : HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := E) σ)

def upperStep (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (n : ℕ) (α : ℝ) :
    Procedure (Param × E) History E :=
  (InnerBatch.affineBatch O n (-α)).reparam
    (fun z => (q z.1,v z.1-α • z.2))
    ((hq.comp measurable_fst).prodMk ((hv.comp measurable_fst).sub (measurable_snd.const_smul α)))

def rawStep (Z : Procedure Param History E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (n : ℕ) (α : ℝ) : Procedure Param History E :=
  Z.bind (upperStep O q hq v hv n α)

def projectedStep (Z : Procedure Param History E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (V : ℝ) (n : ℕ) (α : ℝ) : Procedure Param History E :=
  (rawStep O Z q hq v hv n α).map (fun z => Bilevel.Clipping.clip V z.2)
    (AdjointContraction.clip_stronglyMeasurable V measurable_snd.stronglyMeasurable).measurable

omit [CompleteSpace E] in
theorem projectedStep_calls (Z : Procedure Param History E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (V : ℝ) (n : ℕ) (α : ℝ)
    (N : ℕ) (hZ : Z.CallsEq (fun _ => N)) :
    (projectedStep O Z q hq v hv V n α).CallsEq (fun _ => N+n) := by
  have hu : (upperStep O q hq v hv n α).CallsEq (fun _ => n) :=
    Procedure.CallsEq.reparam _ _ (InnerBatch.affineBatch_calls O n (-α)) _ _
  exact Procedure.CallsEq.map _ _ (Procedure.CallsEq.bind _ _ _ _ hZ hu) _ _

theorem rawStep_error (Z : Procedure Param History E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) (n : ℕ) (hn : 0 < n) {α S : ℝ} (hα : α ≠ 0)
    (p : Param) (h : History) (m center : E)
    (hZ : ∀ c, Integrable (fun z => ‖z.1-c‖ ^ 2) (Z.law (p,h)) ∧
      (∫ z, ‖z.1-c‖ ^ 2 ∂Z.law (p,h)) ≤ ‖m-c‖ ^ 2+S) :
    Integrable (fun z => ‖z.1-center‖ ^ 2) ((rawStep O Z q hq v hv n α).law (p,h)) ∧
    (∫ z, ‖z.1-center‖ ^ 2 ∂(rawStep O Z q hq v hv n α).law (p,h)) ≤
      ‖v p-α • (m-O.truth (q p))-center‖ ^ 2+α ^ 2*(S+σ ^ 2/(n:ℝ)) := by
  have ha := affine_error (ν := Z.law (p,h)) (fun z => z.1) m
    (v p+α • O.truth (q p)) center hα hZ
  have hid (w : E) : v p-α • w-(-α) • O.truth (q p)-center =
      (v p+α • O.truth (q p))-α • w-center := by
    simp only [neg_smul]
    abel
  have hu (z : Outcome E History) := InnerBatch.affineBatch_error O n hn (neg_ne_zero.mpr hα)
    (q p) (v p-α • z.1) center z.2.1
  have hb := Procedure.bind_output_bound Z (upperStep O q hq v hv n α) p h
    (fun w => ‖w-center‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
    (fun w => ‖(v p+α • O.truth (q p))-α • w-center‖ ^ 2+α ^ 2*σ ^ 2/(n:ℝ))
    (ha.1.add (integrable_const _)) (fun z => (hu z).1)
    (fun z => by simpa only [hid,neg_sq] using (hu z).2)
  refine ⟨hb.1,hb.2.trans ?_⟩
  rw [integral_add ha.1 (integrable_const (α ^ 2*σ ^ 2/(n:ℝ)))]
  simp only [integral_const,measureReal_univ_eq_one,one_smul]
  have hm : v p+α • O.truth (q p)-α • m-center =
      v p-α • (m-O.truth (q p))-center := by rw [smul_sub]; abel
  rw [hm] at ha
  calc
    _ ≤ ‖v p-α • (m-O.truth (q p))-center‖ ^ 2+α ^ 2*S+α ^ 2*σ ^ 2/(n:ℝ) :=
      add_le_add_right ha.2 _
    _ = _ := by ring

theorem projectedStep_error (Z : Procedure Param History E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) {V : ℝ} (hV : 0 ≤ V)
    (n : ℕ) (hn : 0 < n) {α S : ℝ} (hα : α ≠ 0)
    (p : Param) (h : History) (m center : E) (hcenter : ‖center‖ ≤ V)
    (hZ : ∀ c, Integrable (fun z => ‖z.1-c‖ ^ 2) (Z.law (p,h)) ∧
      (∫ z, ‖z.1-c‖ ^ 2 ∂Z.law (p,h)) ≤ ‖m-c‖ ^ 2+S) :
    Integrable (fun z => ‖z.1-center‖ ^ 2) ((projectedStep O Z q hq v hv V n α).law (p,h)) ∧
    (∫ z, ‖z.1-center‖ ^ 2 ∂(projectedStep O Z q hq v hv V n α).law (p,h)) ≤
      ‖v p-α • (m-O.truth (q p))-center‖ ^ 2+α ^ 2*(S+σ ^ 2/(n:ℝ)) := by
  have hh := rawStep_error O Z q hq v hv n hn hα p h m center hZ
  have hm : Measurable (fun z : Outcome E History => ‖Bilevel.Clipping.clip V z.1-center‖ ^ 2) :=
    ((AdjointContraction.clip_stronglyMeasurable V measurable_fst.stronglyMeasurable).measurable.sub
      measurable_const).norm.pow_const 2
  have hb (z : Outcome E History) := Bilevel.Clipping.squared_error_nonincreasing V hV z.1 center hcenter
  have hi : Integrable (fun z => ‖Bilevel.Clipping.clip V z.1-center‖ ^ 2)
      ((rawStep O Z q hq v hv n α).law (p,h)) := by
    apply hh.1.mono' hm.aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs,abs_sq] using hb z
  have hg : StronglyMeasurable (fun w : E => ‖w-center‖ ^ 2) := (by fun_prop :
    Measurable (fun w : E => ‖w-center‖ ^ 2)).stronglyMeasurable
  constructor
  · rw [projectedStep,Procedure.map_output_integrable_iff _ _ _ _ _ _ hg]
    exact hi
  · rw [projectedStep,Procedure.map_output_integral _ _ _ _ _ _ hg]
    exact (integral_mono hi hh.1 hb).trans hh.2

omit [CompleteSpace E] in
theorem projectedStep_bounded (Z : Procedure Param History E) (q : Param → Query) (hq : Measurable q)
    (v : Param → E) (hv : Measurable v) {V : ℝ} (hV : 0 ≤ V) (n : ℕ) (α : ℝ)
    (p : Param) (h : History) :
    ∀ᵐ z ∂(projectedStep O Z q hq v hv V n α).law (p,h), ‖z.1‖ ≤ V := by
  rw [projectedStep,Procedure.map_law]
  have hm : Measurable (fun z : Outcome E History => (Bilevel.Clipping.clip V z.1,z.2)) :=
    (AdjointContraction.clip_stronglyMeasurable V measurable_fst.stronglyMeasurable).measurable.prodMk measurable_snd
  apply (ae_map_iff hm.aemeasurable (measurableSet_le measurable_fst.norm measurable_const)).mpr
  filter_upwards with z
  exact Bilevel.Clipping.bounded V hV z.1

end Smoothness2601.AdjointKernels
