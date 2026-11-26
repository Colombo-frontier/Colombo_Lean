import SecondOrder.FirstOrderFrontierKernel
import SecondOrder.CurvatureProgress

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ}

def firstOrderProgress (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T) : ℕ :=
  positiveGateFrontier (fun i => firstOrderBlockCompletion (Θ i) (x i))

theorem firstOrderProgress_le (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T) :
    firstOrderProgress Θ x≤T+1 := positiveGateFrontier_le _

theorem firstOrderProgress_future_zero (Θ : Fin (T+1) → Fin d → Bool) (x : FirstOrderSpace d T)
    (i : Fin (T+1)) (hi : firstOrderProgress Θ x ≤ i.val) : firstOrderBlockCompletion (Θ i) (x i)=0 :=
  positiveGateFrontier_future_zero _ (fun j => (firstOrderBlockCompletion_mem (Θ j) (x j)).1) i hi

theorem firstOrderProgress_measurable (Θ : Fin (T+1) → Fin d → Bool) : Measurable (firstOrderProgress Θ) := by
  apply positiveGateFrontier_measurable
  intro i
  exact ((firstOrderBlockCompletion_contDiff (Θ i)).continuous.comp
    (blockProj (E := Point d) i).continuous).measurable

theorem firstOrderProgress_zero (Θ : Fin (T+1) → Fin d → Bool) : firstOrderProgress Θ 0=0 := by
  apply Nat.eq_zero_of_le_zero
  unfold firstOrderProgress positiveGateFrontier
  apply Finset.sup_le
  intro i _
  simp [firstOrderBlockCompletion_zero]

theorem firstOrderRichReply_at_progress (Θ : Fin (T+1) → Fin d → Bool) {R : ℝ}
    (z : FirstOrderCoefficients d T R) (x : FirstOrderSpace d T) :
    firstOrderRichReply Θ z x=firstOrderTruncatedReply Θ z (firstOrderProgress Θ x) x :=
  firstOrderRichReply_truncate Θ z _ x (firstOrderProgress_future_zero Θ x)

theorem firstOrderRichReply_progress_kl (Θ : Fin (T+1) → Fin d → Bool) (θ₀ : Fin d → Bool)
    (R : ℝ) (hR : 2≤R) (x : FirstOrderSpace d T) (hp : firstOrderProgress Θ x≤T) :
    klDiv ((firstOrderChainCoefficientLaw Θ R hR).toMeasure.map (fun z => firstOrderRichReply Θ z x))
      (firstOrderReferenceKernel θ₀ (fun i : Fin (firstOrderProgress Θ x) => Θ ⟨i.val,by omega⟩) R hR x)≤
      ENNReal.ofReal ((d:ℝ)/R^2) :=
  firstOrderRichReply_frontier_kl Θ θ₀ R hR hp x (firstOrderProgress_future_zero Θ x)

theorem firstOrderProgress_unfinished_gradient (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) (hp : firstOrderProgress Θ x≤T) :
    firstOrderGradientConstant≤‖gradient (firstOrderChain Θ) x‖ := by
  apply firstOrderChain_gradient_lower Θ hd x
  let i : Fin (T+1) := ⟨firstOrderProgress Θ x,by omega⟩
  have hh := (firstOrderBlockCompletion_eq_zero_iff (Θ i) (x i)).1
    (firstOrderProgress_future_zero Θ x i (le_refl _))
  exact ⟨i,hh.trans (by norm_num)⟩

theorem firstOrderProgress_complete_of_gradient (Θ : Fin (T+1) → Fin d → Bool) (hd : 0<d)
    (x : FirstOrderSpace d T) (hg : ‖gradient (firstOrderChain Θ) x‖<firstOrderGradientConstant) :
    firstOrderProgress Θ x=T+1 := by
  have hp := firstOrderProgress_le Θ x
  by_contra he
  exact (not_lt_of_ge (firstOrderProgress_unfinished_gradient Θ hd x (by omega))) hg

theorem firstOrderBlockCompletion_pos_iff (θ : Fin d → Bool) (x : Point d) :
    0<firstOrderBlockCompletion θ x ↔ 1/4<firstOrderBlockEncoding θ x := by
  constructor
  · intro hp
    by_contra hn
    have hz := (firstOrderBlockCompletion_eq_zero_iff θ x).2 (le_of_not_gt hn)
    linarith only [hp,hz]
  · intro hp
    have hn : firstOrderBlockCompletion θ x≠0 := by
      intro hz
      exact (not_le_of_gt hp) ((firstOrderBlockCompletion_eq_zero_iff θ x).1 hz)
    exact lt_of_le_of_ne (firstOrderBlockCompletion_mem θ x).1 (Ne.symm hn)

theorem firstOrderBlockCompletion_activation_tail (x : Point d) :
    signLaw d {θ | 0<firstOrderBlockCompletion θ x}≤ENNReal.ofReal (2*Real.exp (-(d:ℝ)/128)) := by
  have he : {θ : Fin d → Bool | 0<firstOrderBlockCompletion θ x}=
      {θ | 1/4<firstOrderEncoding (fun i => x i) θ} := by
    ext θ
    change 0<firstOrderBlockCompletion θ x ↔ 1/4<firstOrderEncoding (fun i => x i) θ
    rw [firstOrderBlockCompletion_pos_iff,firstOrderBlockEncoding_eq]
  rw [he]
  exact firstOrderEncoding_tail (fun i => x i)

theorem firstOrderProgress_joint_measurable (d T : ℕ) :
    Measurable (fun w : (Fin (T+1) → Fin d → Bool) × FirstOrderSpace d T => firstOrderProgress w.1 w.2) := by
  apply positiveGateFrontier_measurable
  intro i
  have hy : Measurable (fun x : FirstOrderSpace d T => fun j : Fin d => (x i) j) :=
    measurable_pi_iff.mpr (fun j => (EuclideanSpace.proj j).continuous.measurable.comp
      (blockProj (E := Point d) i).continuous.measurable)
  have hc : Measurable (fun w : (Fin (T+1) → Fin d → Bool) × FirstOrderSpace d T =>
      (w.2,w.1 i)) :=
    measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)
  have hm := (firstOrderEncoding_joint_measurable hy).comp hc
  change Measurable (fun w : (Fin (T+1) → Fin d → Bool) × FirstOrderSpace d T =>
    firstOrderCompletion (firstOrderBlockEncoding (w.1 i) (w.2 i)))
  simp only [firstOrderBlockEncoding_eq]
  exact firstOrderCompletion_contDiff.continuous.measurable.comp hm

theorem firstOrderBlockCompletion_activation_past_tail {A : Type*} [MeasurableSpace A]
    {η : Measure A} {y : A → Point d} (hy : Measurable y) {past : Set A} (hp : MeasurableSet past) :
    (η.prod (signLaw d)) {w | w.1 ∈ past ∧ 0<firstOrderBlockCompletion w.2 (y w.1)}≤
      ENNReal.ofReal (2*Real.exp (-(d:ℝ)/128))*η past := by
  have he : {w : A × (Fin d → Bool) | w.1 ∈ past ∧ 0<firstOrderBlockCompletion w.2 (y w.1)}=
      {w | w.1 ∈ past ∧ 1/4<firstOrderEncoding (fun i => y w.1 i) w.2} := by
    ext w
    simp only [Set.mem_setOf_eq,firstOrderBlockCompletion_pos_iff,firstOrderBlockEncoding_eq]
  rw [he]
  exact firstOrderEncoding_past_tail
    (measurable_pi_iff.mpr (fun i => (EuclideanSpace.proj i).continuous.measurable.comp hy)) hp

end
end SecondOrder
