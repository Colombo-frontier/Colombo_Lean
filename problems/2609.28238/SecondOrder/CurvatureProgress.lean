import SecondOrder.CurvatureFrontierKernel
import SecondOrder.CurvatureGeometry

open MeasureTheory InformationTheory ProbabilityTheory
open scoped Classical ENNReal InnerProductSpace

namespace SecondOrder
noncomputable section

/-- Number of the last positive gate, with zero for no positive gates. -/
def positiveGateFrontier {n : ℕ} (b : Fin n → ℝ) : ℕ :=
  Finset.univ.sup (fun i => if 0<b i then i.val+1 else 0)

theorem positiveGateFrontier_le {n : ℕ} (b : Fin n → ℝ) : positiveGateFrontier b≤n := by
  apply Finset.sup_le
  intro i _
  split_ifs <;> omega

theorem positiveGateFrontier_future_zero {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, 0≤b i) (i : Fin n) (hi : positiveGateFrontier b ≤ i.val) : b i=0 := by
  by_contra hn
  have hp : 0<b i := lt_of_le_of_ne (hb i) (Ne.symm hn)
  have hh := Finset.le_sup (f := fun j : Fin n => if 0<b j then j.val+1 else 0) (Finset.mem_univ i)
  simp only [hp, if_true] at hh
  change i.val+1≤positiveGateFrontier b at hh
  omega

theorem measurable_nat_finset_sup {A ι : Type*} [MeasurableSpace A] (s : Finset ι)
    (f : ι → A → ℕ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun a => s.sup (fun i => f i a)) := by
  induction s using Finset.induction_on with
  | empty => simpa using (measurable_const : Measurable (fun _ : A => (0:ℕ)))
  | @insert i s hi ih =>
    simpa only [Finset.sup_insert] using
      (hf i (Finset.mem_insert_self _ _)).max (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem positiveGateFrontier_measurable {A : Type*} [MeasurableSpace A] {n : ℕ}
    (b : A → Fin n → ℝ) (hb : ∀ i, Measurable (fun a => b a i)) :
    Measurable (fun a => positiveGateFrontier (b a)) := by
  apply measurable_nat_finset_sup
  intro i _
  exact Measurable.ite (measurableSet_lt measurable_const (hb i)) measurable_const measurable_const

variable {m T : ℕ}

def curvatureProgress (Θ : Fin (T+1) → BalancedVector m) (x : CurvatureSpace m T) : ℕ :=
  positiveGateFrontier (fun i => periodicCompletion (Θ i) (x i))

theorem curvatureProgress_le (Θ : Fin (T+1) → BalancedVector m) (x : CurvatureSpace m T) :
    curvatureProgress Θ x≤T+1 := positiveGateFrontier_le _

theorem curvatureProgress_future_zero (Θ : Fin (T+1) → BalancedVector m) (x : CurvatureSpace m T)
    (i : Fin (T+1)) (hi : curvatureProgress Θ x ≤ i.val) : periodicCompletion (Θ i) (x i)=0 :=
  positiveGateFrontier_future_zero _ (fun j => (periodicCompletion_mem (Θ j) (x j)).1) i hi

theorem curvatureProgress_measurable (Θ : Fin (T+1) → BalancedVector m) : Measurable (curvatureProgress Θ) := by
  apply positiveGateFrontier_measurable
  intro i
  exact ((periodicCompletion_contDiff (Θ i)).continuous.comp
    (blockProj (E := Point (2*m)) i).continuous).measurable

theorem curvatureProgress_zero (Θ : Fin (T+1) → BalancedVector m) : curvatureProgress Θ 0=0 := by
  apply Nat.eq_zero_of_le_zero
  unfold curvatureProgress positiveGateFrontier
  apply Finset.sup_le
  intro i _
  simp [periodicCompletion_zero]

/-- The extended response agrees with the genuine oracle at its actual
measurable maximal progress index. -/
theorem curvatureRichReply_at_progress (Θ : Fin (T+1) → BalancedVector m) {R : ℝ}
    (z : CurvatureCoefficients m T R) (x : CurvatureSpace m T) :
    curvatureRichReply Θ z x = curvatureTruncatedReply Θ z (curvatureProgress Θ x) x :=
  curvatureRichReply_truncate Θ z _ x (curvatureProgress_future_zero Θ x)

theorem curvatureRichReply_progress_kl (Θ : Fin (T+1) → BalancedVector m) (θ₀ : BalancedVector m)
    (R : ℝ) (hR : 2≤R) (x : CurvatureSpace m T) (hp : curvatureProgress Θ x≤T) :
    klDiv ((curvatureCoefficientLaw Θ R hR).toMeasure.map (fun z => curvatureRichReply Θ z x))
      (curvatureReferenceKernel θ₀ (fun i : Fin (curvatureProgress Θ x) => Θ ⟨i.val,by omega⟩) R hR x) ≤
      ENNReal.ofReal ((((2*m:ℕ):ℝ)*(((2*m:ℕ):ℝ)-1))/(2*R^2)) :=
  curvatureRichReply_frontier_kl Θ θ₀ R hR hp x (curvatureProgress_future_zero Θ x)

theorem curvatureProgress_unfinished_negative (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (x : CurvatureSpace m T) (hp : curvatureProgress Θ x≤T) :
    ∃ v : CurvatureSpace m T, ‖v‖=1 ∧
      ⟪fderiv ℝ (gradient (curvatureChain Θ)) x v,v⟫_ℝ ≤ -1/(4*((2*m:ℕ):ℝ)) := by
  apply curvatureChain_negative Θ hm x
  let i : Fin (T+1) := ⟨curvatureProgress Θ x,by omega⟩
  have hh := (periodicCompletion_eq_zero_iff (Θ i) (x i)).1
    (curvatureProgress_future_zero Θ x i (le_refl _))
  exact ⟨i, hh.trans (by norm_num)⟩

/-- Genuine second-order stationarity forces completion of the full chain. -/
theorem curvatureProgress_complete_of_curvature (Θ : Fin (T+1) → BalancedVector m) (hm : 0<m)
    (x : CurvatureSpace m T) {γ : ℝ} (hγ : γ<1/(4*((2*m:ℕ):ℝ)))
    (hH : ∀ v : CurvatureSpace m T, ‖v‖=1 →
      -γ ≤ ⟪fderiv ℝ (gradient (curvatureChain Θ)) x v,v⟫_ℝ) :
    curvatureProgress Θ x=T+1 := by
  have hp := curvatureProgress_le Θ x
  by_contra he
  obtain ⟨v,hv,hq⟩ := curvatureProgress_unfinished_negative Θ hm x (by omega)
  have hh := hH v hv
  rw [neg_div] at hq
  linarith only [hγ, hq, hh]

theorem periodicCompletion_pos_iff {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    0<periodicCompletion θ x ↔ 1/8<‖periodicMean x θ‖ := by
  constructor
  · intro hp
    by_contra hn
    have hz := (periodicCompletion_eq_zero_iff θ x).2 (le_of_not_gt hn)
    linarith only [hp, hz]
  · intro hp
    have hn : periodicCompletion θ x ≠ 0 := by
      intro hz
      exact (not_le_of_gt hp) ((periodicCompletion_eq_zero_iff θ x).1 hz)
    exact lt_of_le_of_ne (periodicCompletion_mem θ x).1 (Ne.symm hn)

theorem periodicCompletion_activation_tail {m : ℕ} (x : Point (2*m)) :
    balancedVectorLaw m {θ | 0<periodicCompletion θ x} ≤
      ENNReal.ofReal (4*Real.exp (-((2*m:ℕ):ℝ)/512)) := by
  simp only [periodicCompletion_pos_iff]
  exact periodicMean_tail x

theorem curvatureProgress_joint_measurable (m T : ℕ) :
    Measurable (fun w : (Fin (T+1) → BalancedVector m) × CurvatureSpace m T =>
      curvatureProgress w.1 w.2) := by
  apply positiveGateFrontier_measurable
  intro i
  have hy : Measurable (fun x : CurvatureSpace m T => fun j : Fin (2*m) => (x i) j) :=
    measurable_pi_iff.mpr (fun j => (EuclideanSpace.proj j).continuous.measurable.comp
      (blockProj (E := Point (2*m)) i).continuous.measurable)
  have hc : Measurable (fun w : (Fin (T+1) → BalancedVector m) × CurvatureSpace m T =>
      (w.2,w.1 i)) :=
    measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst)
  have hm := (periodicMean_joint_measurable hy).comp hc
  change Measurable (fun w : (Fin (T+1) → BalancedVector m) × CurvatureSpace m T =>
    curvatureCompletion (periodicEnergy (w.1 i) (w.2 i)))
  simp only [periodicEnergy_eq]
  exact curvatureCompletion_contDiff.continuous.measurable.comp ((hm.norm.pow_const 2).div_const 2)

/-- The gate-activation rarity is valid for queries depending on independent
history, with an arbitrary measurable history event retained. -/
theorem periodicCompletion_activation_past_tail {A : Type*} [MeasurableSpace A]
    {η : Measure A} {m : ℕ} {y : A → Point (2*m)} (hy : Measurable y)
    {past : Set A} (hp : MeasurableSet past) :
    (η.prod (balancedVectorLaw m)) {w | w.1 ∈ past ∧ 0<periodicCompletion w.2 (y w.1)} ≤
      ENNReal.ofReal (4*Real.exp (-((2*m:ℕ):ℝ)/512))*η past := by
  simp only [periodicCompletion_pos_iff]
  apply periodicMean_past_tail _ hp
  exact measurable_pi_iff.mpr (fun i => (EuclideanSpace.proj i).continuous.measurable.comp hy)

end
end SecondOrder
