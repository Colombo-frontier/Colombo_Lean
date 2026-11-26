import SampleReuse.TraceMoment
import SampleReuse.WordCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SampleReuse
noncomputable section
open Classical

def operatorWord {A : Type*} [Monoid A] {n p : ℕ}
    (X : Fin n → A) (w : Fin p → Fin n) : A :=
  (List.ofFn (fun i => X (w i))).prod

/-- Expansion retaining the order of all factors, valid in a noncommutative ring. -/
theorem sum_pow_eq_operatorWords {A : Type*} [Semiring A] {n : ℕ}
    (X : Fin n → A) (p : ℕ) :
    (∑ i, X i)^p = ∑ w : Fin p → Fin n, operatorWord X w := by
  induction p with
  | zero => simp [operatorWord]
  | succ p ih =>
    rw [pow_succ', ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ z : Fin n × (Fin p → Fin n),
          operatorWord X (Fin.cons z.1 z.2) := by
        simp [Fintype.sum_prod_type, operatorWord, List.ofFn_succ]
      _ = _ := (Fin.consEquiv (fun _ : Fin (p+1) => Fin n)).sum_comp (operatorWord X)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def traceSandwichL (L R : E →L[ℝ] E) : (E →L[ℝ] E) →L[ℝ] ℝ :=
  opTraceL.comp (((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip R).comp
    (ContinuousLinearMap.mul ℝ (E →L[ℝ] E) L))

@[simp] theorem traceSandwichL_apply (L R X : E →L[ℝ] E) :
    traceSandwichL L R X = opTrace (L*X*R) := rfl

theorem traceSandwich_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → (E →L[ℝ] E)} (hX : Integrable X μ)
    (hzero : (∫ ω, X ω ∂μ) = 0) (L R : E →L[ℝ] E) :
    (∫ ω, opTrace (L * X ω * R) ∂μ) = 0 := by
  change (∫ ω, traceSandwichL L R (X ω) ∂μ) = 0
  rw [(traceSandwichL L R).integral_comp_comm hX, hzero, map_zero]

/-- A centered random operator independent of both surrounding products has
zero expected trace in its singleton position. All expectations are Bochner
integrals of the actual operator products. -/
theorem independent_trace_sandwich_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → (E →L[ℝ] E)) (Y : Ω → (E →L[ℝ] E) × (E →L[ℝ] E))
    (hX : Measurable X) (hY : Measurable Y) (hXi : Integrable X μ)
    (hzero : (∫ ω, X ω ∂μ) = 0) (hind : IndepFun Y X μ)
    (hi : Integrable (fun ω => opTrace ((Y ω).1 * X ω * (Y ω).2)) μ) :
    (∫ ω, opTrace ((Y ω).1 * X ω * (Y ω).2) ∂μ) = 0 := by
  let f : ((E →L[ℝ] E) × (E →L[ℝ] E)) × (E →L[ℝ] E) → ℝ :=
    fun z => opTrace (z.1.1 * z.2 * z.1.2)
  have hf : Continuous f := opTraceL.continuous.comp
    ((continuous_fst.fst.mul continuous_snd).mul continuous_fst.snd)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable).mp hind
  have hip : Integrable f ((μ.map Y).prod (μ.map X)) := by
    rw [← hmap]
    exact (integrable_map_measure hf.aestronglyMeasurable
      (hY.prodMk hX).aemeasurable).mpr hi
  have hXm : Integrable (fun x : E →L[ℝ] E => x) (μ.map X) :=
    (integrable_map_measure continuous_id.aestronglyMeasurable hX.aemeasurable).mpr hXi
  have hmean : (∫ x : E →L[ℝ] E, x ∂μ.map X) = 0 := by
    exact (integral_map hX.aemeasurable continuous_id.aestronglyMeasurable).trans hzero
  calc
    _ = ∫ z, f z ∂μ.map (fun ω => (Y ω, X ω)) :=
      (integral_map (hY.prodMk hX).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(μ.map Y).prod (μ.map X) := by rw [hmap]
    _ = ∫ y, ∫ x, f (y,x) ∂μ.map X ∂μ.map Y := integral_prod f hip
    _ = 0 := by
      have hz (y : (E →L[ℝ] E) × (E →L[ℝ] E)) :
          (∫ x, f (y,x) ∂μ.map X) = 0 :=
        traceSandwich_integral_zero hXm hmean y.1 y.2
      simp_rw [hz]
      simp

theorem measurable_operatorList {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    (l : List (Fin n)) : Measurable (fun ω => (l.map (fun i => X i ω)).prod) := by
  induction l with
  | nil => exact measurable_const
  | cons a l ih => exact (hX a).mul ih

def fillExcept {n : ℕ} (i : Fin n)
    (a : ↥(Finset.univ.erase i) → (E →L[ℝ] E)) (j : Fin n) : E →L[ℝ] E :=
  if h : j = i then 0 else a ⟨j, by simp [h]⟩

omit [FiniteDimensional ℝ E] in
theorem measurable_fillExcept {n : ℕ} (i j : Fin n) :
    Measurable (fun a : ↥(Finset.univ.erase i) → (E →L[ℝ] E) => fillExcept i a j) := by
  by_cases h : j = i
  · simp only [fillExcept, dif_pos h]
    exact measurable_const
  · simp only [fillExcept, dif_neg h]
    exact measurable_pi_apply _

omit [FiniteDimensional ℝ E] in
theorem fillExcept_list_eq {Ω : Type*} {n : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (i : Fin n) (l : List (Fin n))
    (hl : i ∉ l) (ω : Ω) :
    (l.map (fillExcept i (fun j => X j.1 ω))).prod =
      (l.map (fun j => X j ω)).prod := by
  congr 1
  apply List.map_congr_left
  intro j hj
  have hji : j ≠ i := by rintro rfl; exact hl hj
  simp [fillExcept, hji]

theorem independent_list_sandwich_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (i : Fin n) (hXi : Integrable (X i) μ)
    (hzero : (∫ ω, X i ω ∂μ) = 0) (l r : List (Fin n))
    (hl : i ∉ l) (hr : i ∉ r)
    (hint : Integrable (fun ω => opTrace
      ((l.map (fun j => X j ω)).prod * X i ω * (r.map (fun j => X j ω)).prod)) μ) :
    (∫ ω, opTrace
      ((l.map (fun j => X j ω)).prod * X i ω * (r.map (fun j => X j ω)).prod) ∂μ) = 0 := by
  let G : (↥(Finset.univ.erase i) → (E →L[ℝ] E)) →
      (E →L[ℝ] E) × (E →L[ℝ] E) := fun a =>
    ((l.map (fillExcept i a)).prod, (r.map (fillExcept i a)).prod)
  have hG : Measurable G :=
    (measurable_operatorList (fun j a => fillExcept i a j) (measurable_fillExcept i) l).prodMk
      (measurable_operatorList (fun j a => fillExcept i a j) (measurable_fillExcept i) r)
  have hd : Disjoint (Finset.univ.erase i) ({i} : Finset (Fin n)) := by simp
  have hbase := hind.indepFun_finset (Finset.univ.erase i) {i} hd hX
  have hfinal := hbase.comp hG (measurable_pi_apply (⟨i, by simp⟩ : ({i} : Finset (Fin n))))
  let Y : Ω → (E →L[ℝ] E) × (E →L[ℝ] E) := fun ω =>
    ((l.map (fun j => X j ω)).prod, (r.map (fun j => X j ω)).prod)
  have hgeq : (fun ω => G (fun j => X j.1 ω)) = Y := by
    funext ω
    exact Prod.ext (fillExcept_list_eq X i l hl ω) (fillExcept_list_eq X i r hr ω)
  have hfinal' : IndepFun Y (X i) μ := by
    simpa only [Function.comp_def, hgeq] using hfinal
  exact independent_trace_sandwich_zero (X i) Y (hX i)
    ((measurable_operatorList X hX l).prodMk (measurable_operatorList X hX r))
    hXi hzero hfinal' hint

theorem list_split_of_count_eq_one {α : Type*} [DecidableEq α]
    (l : List α) (a : α) (h : l.count a = 1) :
    ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ a ∉ l₁ ∧ a ∉ l₂ := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    by_cases hb : b = a
    · subst b
      have hc : l.count a = 0 := by simpa using h
      exact ⟨[], l, rfl, by simp, List.count_eq_zero.mp hc⟩
    · have hc : l.count a = 1 := by simpa [List.count_cons, hb, Ne.symm hb] using h
      obtain ⟨l₁, l₂, he, h₁, h₂⟩ := ih hc
      exact ⟨b :: l₁, l₂, by simp [he], by simp [hb, Ne.symm hb, h₁], h₂⟩

theorem ofFn_count_eq_sum {α : Type*} [DecidableEq α] {p : ℕ}
    (w : Fin p → α) (a : α) :
    (List.ofFn w).count a = ∑ j, if w j = a then 1 else 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq, Nat.add_comm]

theorem ofFn_count_unique {α : Type*} [DecidableEq α] {p : ℕ}
    (w : Fin p → α) (i : Fin p) (hu : ∀ j, w j = w i → j = i) :
    (List.ofFn w).count (w i) = 1 := by
  rw [ofFn_count_eq_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hn : w j ≠ w i := fun h => hji (hu j h)
    simp [hn]
  · simp

theorem singleton_operatorWord_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n p : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (w : Fin p → Fin n) (j : Fin p)
    (hu : ∀ t, w t = w j → t = j)
    (hXi : Integrable (X (w j)) μ) (hzero : (∫ ω, X (w j) ω ∂μ) = 0)
    (hint : Integrable (fun ω => opTrace (operatorWord (fun i => X i ω) w)) μ) :
    (∫ ω, opTrace (operatorWord (fun i => X i ω) w) ∂μ) = 0 := by
  obtain ⟨l, r, he, hl, hr⟩ :=
    list_split_of_count_eq_one (List.ofFn w) (w j) (ofFn_count_unique w j hu)
  have hprod (ω : Ω) : operatorWord (fun i => X i ω) w =
      (l.map (fun i => X i ω)).prod * X (w j) ω * (r.map (fun i => X i ω)).prod := by
    unfold operatorWord
    change (List.ofFn ((fun i => X i ω) ∘ w)).prod = _
    rw [← List.map_ofFn, he]
    simp [List.map_append, List.prod_append, mul_assoc]
  simp_rw [hprod] at hint ⊢
  exact independent_list_sandwich_zero X hX hind (w j) hXi hzero l r hl hr hint

theorem list_norm_prod_le_pow {A : Type*} [SeminormedAddCommGroup A]
    (l : List A) {σ : ℝ} (hσ : 0 ≤ σ) (hl : ∀ a ∈ l, ‖a‖ ≤ σ) :
    (l.map norm).prod ≤ σ^l.length := by
  have hnonneg (s : List A) : 0 ≤ (s.map norm).prod := by
    induction s with
    | nil => simp
    | cons a s ih => exact mul_nonneg (norm_nonneg a) ih
  induction l with
  | nil => simp
  | cons a l ih =>
    have ht : ∀ b ∈ l, ‖b‖ ≤ σ := fun b hb => hl b (List.mem_cons_of_mem a hb)
    have hn : 0 ≤ (l.map norm).prod := hnonneg l
    have hmul := mul_le_mul (hl a (by simp)) (ih ht) hn hσ
    simpa [pow_succ, mul_comm] using hmul

theorem abs_trace_operatorWord_le {n p : ℕ} (X : Fin n → (E →L[ℝ] E))
    (w : Fin p → Fin n) {σ : ℝ} (hσ : 0 ≤ σ) (hX : ∀ i, ‖X i‖ ≤ σ) :
    |opTrace (operatorWord X w)| ≤ (Module.finrank ℝ E : ℝ) * σ^p := by
  have hb := list_norm_prod_le_pow (List.ofFn (fun j => X (w j))) hσ (by
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact hX (w j))
  have ht := abs_opTrace_list_prod_le (List.ofFn (fun j => X (w j)))
  exact ht.trans (mul_le_mul_of_nonneg_left (by simpa using hb) (Nat.cast_nonneg _))

theorem measurable_operatorWord {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    (w : Fin p → Fin n) : Measurable (fun ω => operatorWord (fun i => X i ω) w) := by
  simpa only [operatorWord, List.map_ofFn, Function.comp_def] using
    measurable_operatorList X hX (List.ofFn w)

theorem trace_operatorWord_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n p : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    (w : Fin p → Fin n) {σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ σ) :
    Integrable (fun ω => opTrace (operatorWord (fun i => X i ω) w)) μ := by
  have hm : Measurable (fun ω => opTrace (operatorWord (fun i => X i ω) w)) :=
    opTraceL.continuous.measurable.comp (measurable_operatorWord X hX w)
  apply (integrable_const ((Module.finrank ℝ E : ℝ)*σ^p)).mono' hm.aestronglyMeasurable
  have hall : ∀ᵐ ω ∂μ, ∀ i, ‖X i ω‖ ≤ σ := ae_all_iff.mpr hb
  filter_upwards [hall] with ω hω
  simpa only [Real.norm_eq_abs] using abs_trace_operatorWord_le (fun i => X i ω) w hσ hω

/-- No integrability assumption remains: it follows from the uniform
operator-norm bound and measurable finite word products. -/
theorem bounded_singleton_operatorWord_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n p : ℕ}
    (X : Fin n → Ω → (E →L[ℝ] E)) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (w : Fin p → Fin n) (j : Fin p)
    (hu : ∀ t, w t = w j → t = j)
    (hzero : (∫ ω, X (w j) ω ∂μ) = 0) {σ : ℝ} (hσ : 0 ≤ σ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ σ) :
    (∫ ω, opTrace (operatorWord (fun i => X i ω) w) ∂μ) = 0 := by
  have hi : Integrable (X (w j)) μ :=
    (integrable_const σ).mono' (hX (w j)).aestronglyMeasurable (hb (w j))
  exact singleton_operatorWord_integral_zero X hX hind w j hu hi hzero
    (trace_operatorWord_integrable X hX w hσ hb)

end
end SampleReuse
