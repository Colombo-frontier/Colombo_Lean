import Bilevel.ChiBoundedChainSquareRoot

/-! Actual smooth bounded receivers in the revised weighted local construction.
They are interval-integral primitives of the manuscript's displayed derivatives. -/
noncomputable section
open MeasureTheory Set
namespace Bilevel.ChiBoundedChain

def releaseGate (t : ℝ) : ℝ := Real.smoothTransition (t-1)
def receiverGate (t : ℝ) : ℝ := Real.smoothTransition (4*t-1)
def positiveTail (t : ℝ) : ℝ := 1-Real.smoothTransition (t-2)
def negativeTail (t : ℝ) : ℝ := 1-Real.smoothTransition (t-1)

theorem releaseGate_contDiff {k : ℕ∞} : ContDiff ℝ k releaseGate :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
theorem receiverGate_contDiff {k : ℕ∞} : ContDiff ℝ k receiverGate :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
theorem positiveTail_contDiff {k : ℕ∞} : ContDiff ℝ k positiveTail :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
theorem negativeTail_contDiff {k : ℕ∞} : ContDiff ℝ k negativeTail :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem releaseGate_zero {t : ℝ} (ht : t≤1) : releaseGate t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem releaseGate_one {t : ℝ} (ht : 2≤t) : releaseGate t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem receiverGate_zero {t : ℝ} (ht : t≤1/4) : receiverGate t=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)
theorem receiverGate_one {t : ℝ} (ht : 1/2≤t) : receiverGate t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
theorem positiveTail_one {t : ℝ} (ht : t≤2) : positiveTail t=1 := by
  simp [positiveTail,Real.smoothTransition.zero_of_nonpos (by linarith : t-2≤0)]
theorem positiveTail_zero {t : ℝ} (ht : 3≤t) : positiveTail t=0 := by
  simp [positiveTail,Real.smoothTransition.one_of_one_le (by linarith : 1≤t-2)]
theorem negativeTail_one {t : ℝ} (ht : t≤1) : negativeTail t=1 := by
  simp [negativeTail,Real.smoothTransition.zero_of_nonpos (by linarith : t-1≤0)]
theorem negativeTail_zero {t : ℝ} (ht : 2≤t) : negativeTail t=0 := by
  simp [negativeTail,Real.smoothTransition.one_of_one_le (by linarith : 1≤t-1)]

theorem receiverGate_range (t : ℝ) : 0≤receiverGate t ∧ receiverGate t≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
theorem positiveTail_range (t : ℝ) : 0≤positiveTail t ∧ positiveTail t≤1 := by
  have h₀ := Real.smoothTransition.nonneg (t-2)
  have h₁ := Real.smoothTransition.le_one (t-2)
  unfold positiveTail
  constructor <;> linarith
theorem negativeTail_range (t : ℝ) : 0≤negativeTail t ∧ negativeTail t≤1 := by
  have h₀ := Real.smoothTransition.nonneg (t-1)
  have h₁ := Real.smoothTransition.le_one (t-1)
  unfold negativeTail
  constructor <;> linarith

def positiveReceiverSlope (A ν g h hp t : ℝ) : ℝ :=
  -A*(ν*t+g)*receiverGate (t/h)*positiveTail (t/hp)
def negativeReceiverSlope (A g h T t : ℝ) : ℝ :=
  -A*g*receiverGate (-t/h)*negativeTail (-t/T)
def primitive (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t,f s
def positiveReceiver (A ν g h hp : ℝ) : ℝ → ℝ := primitive (positiveReceiverSlope A ν g h hp)
def negativeReceiver (A g h T : ℝ) : ℝ → ℝ := primitive (negativeReceiverSlope A g h T)

theorem positiveReceiverSlope_contDiff (A ν g h hp : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (positiveReceiverSlope A ν g h hp) :=
  ((contDiff_const.mul ((contDiff_const.mul contDiff_id).add contDiff_const)).mul
    (receiverGate_contDiff.comp (contDiff_id.div_const h))).mul
    (positiveTail_contDiff.comp (contDiff_id.div_const hp))
theorem negativeReceiverSlope_contDiff (A g h T : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (negativeReceiverSlope A g h T) :=
  ((contDiff_const.mul contDiff_const).mul
    (receiverGate_contDiff.comp (contDiff_id.neg.div_const h))).mul
    (negativeTail_contDiff.comp (contDiff_id.neg.div_const T))

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (primitive f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    (hf.stronglyMeasurableAtFilter volume _) hf.continuousAt

theorem primitive_contDiff {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f) (k : ℕ) :
    ContDiff ℝ k (primitive f) := by
  have hd := primitive_hasDerivAt (hf 0).continuous
  cases k with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt))
  | succ k =>
    change ContDiff ℝ ((k : WithTop ℕ∞)+1) (primitive f)
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun t => (hd t).differentiableAt,by norm_num,?_⟩
    have he : deriv (primitive f)=f := funext (fun t => (hd t).deriv)
    rw [he]
    exact hf k

theorem primitive_zero (f : ℝ → ℝ) : primitive f 0=0 := by simp [primitive]

theorem positiveReceiver_hasDerivAt (A ν g h hp t : ℝ) :
    HasDerivAt (positiveReceiver A ν g h hp) (positiveReceiverSlope A ν g h hp t) t :=
  primitive_hasDerivAt (positiveReceiverSlope_contDiff A ν g h hp (k:=0)).continuous t
theorem negativeReceiver_hasDerivAt (A g h T t : ℝ) :
    HasDerivAt (negativeReceiver A g h T) (negativeReceiverSlope A g h T t) t :=
  primitive_hasDerivAt (negativeReceiverSlope_contDiff A g h T (k:=0)).continuous t
theorem positiveReceiver_contDiff (A ν g h hp : ℝ) (k : ℕ) :
    ContDiff ℝ k (positiveReceiver A ν g h hp) :=
  primitive_contDiff (fun _ => positiveReceiverSlope_contDiff A ν g h hp) k
theorem negativeReceiver_contDiff (A g h T : ℝ) (k : ℕ) :
    ContDiff ℝ k (negativeReceiver A g h T) :=
  primitive_contDiff (fun _ => negativeReceiverSlope_contDiff A g h T) k

theorem positiveReceiverSlope_nonpos (A ν g h hp t : ℝ)
    (hA : 0≤A) (hν : 0≤ν) (hg : 0≤g) (hh : 0<h) : positiveReceiverSlope A ν g h hp t≤0 := by
  by_cases ht : t≤0
  · have he : receiverGate (t/h)=0 := receiverGate_zero (by
      have := div_nonpos_of_nonpos_of_nonneg ht hh.le
      linarith)
    simp [positiveReceiverSlope,he]
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA)
          (add_nonneg (mul_nonneg hν (le_of_lt (lt_of_not_ge ht))) hg))
        (receiverGate_range _).1) (positiveTail_range _).1

theorem negativeReceiverSlope_nonpos (A g h T t : ℝ) (hA : 0≤A) (hg : 0≤g) :
    negativeReceiverSlope A g h T t≤0 :=
  mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) hg)
      (receiverGate_range _).1) (negativeTail_range _).1

theorem positiveReceiverSlope_active (A ν g h hp t : ℝ) (hh : 0<h) (hhp : 0<hp)
    (ht : h/2≤t) (htp : t≤2*hp) : positiveReceiverSlope A ν g h hp t=-A*(ν*t+g) := by
  have h₁ : receiverGate (t/h)=1 := receiverGate_one ((le_div_iff₀ hh).mpr (by linarith))
  have h₂ : positiveTail (t/hp)=1 := positiveTail_one ((div_le_iff₀ hhp).mpr (by linarith))
  simp [positiveReceiverSlope,h₁,h₂]

theorem negativeReceiverSlope_active (A g h T t : ℝ) (hh : 0<h) (hT : 0<T)
    (ht : t≤-h/2) (htT : -T≤t) : negativeReceiverSlope A g h T t=-A*g := by
  have h₁ : receiverGate (-t/h)=1 := receiverGate_one ((le_div_iff₀ hh).mpr (by linarith))
  have h₂ : negativeTail (-t/T)=1 := negativeTail_one ((div_le_iff₀ hT).mpr (by linarith))
  simp [negativeReceiverSlope,h₁,h₂]

end Bilevel.ChiBoundedChain
