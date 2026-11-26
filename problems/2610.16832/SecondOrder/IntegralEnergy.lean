import SecondOrder.DyadicIntervals
import SecondOrder.IntegralMoments

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {μ : Measure Ω}

theorem integrable_inner_of_second_moments {X Y : Ω → E}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) (hY2 : Integrable (fun w => ‖Y w‖^2) μ) :
    Integrable (fun w => ⟪X w,Y w⟫_ℝ) μ := by
  apply ((hX2.add hY2).div_const 2).mono' (hX.aestronglyMeasurable.inner hY.aestronglyMeasurable)
  apply Eventually.of_forall
  intro w
  simp only [Pi.add_apply]
  have hi := norm_inner_le_norm (𝕜 := ℝ) (X w) (Y w)
  nlinarith [sq_nonneg (‖X w‖-‖Y w‖)]

theorem integrable_norm_add_sq {X Y : Ω → E}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hX2 : Integrable (fun w => ‖X w‖^2) μ) (hY2 : Integrable (fun w => ‖Y w‖^2) μ) :
    Integrable (fun w => ‖X w+Y w‖^2) μ := by
  have hi := (hX2.add ((integrable_inner_of_second_moments hX hY hX2 hY2).const_mul 2)).add hY2
  simpa only [norm_add_sq_real] using hi

theorem integrable_norm_sum_sq {ι : Type*} (s : Finset ι) (X : ι → Ω → E)
    (hX : ∀ i ∈ s, Integrable (X i) μ)
    (hX2 : ∀ i ∈ s, Integrable (fun w => ‖X i w‖^2) μ) :
    Integrable (fun w => ‖∑ i ∈ s, X i w‖^2) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hv := hX i (Finset.mem_insert_self _ _)
    have hv2 := hX2 i (Finset.mem_insert_self _ _)
    have hs := ih (fun j hj => hX j (Finset.mem_insert_of_mem hj))
      (fun j hj => hX2 j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using integrable_norm_add_sq hv
      (integrable_finset_sum s (fun j hj => hX j (Finset.mem_insert_of_mem hj))) hv2 hs

/-- Hilbert-space martingale isometry over an arbitrary measure, once
orthogonality and square integrability have been established. -/
theorem integral_orthogonal_sum_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (X : ι → Ω → E)
    (hX : ∀ i ∈ s, Integrable (X i) μ)
    (hX2 : ∀ i ∈ s, Integrable (fun w => ‖X i w‖^2) μ)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (∫ w, ⟪X i w,X j w⟫_ℝ ∂μ) = 0) :
    (∫ w, ‖∑ i ∈ s, X i w‖^2 ∂μ) = ∑ i ∈ s, ∫ w, ‖X i w‖^2 ∂μ := by
  have hi (i) (hi : i ∈ s) (j) (hj : j ∈ s) : Integrable (fun w => ⟪X i w,X j w⟫_ℝ) μ :=
    integrable_inner_of_second_moments (hX i hi) (hX j hj) (hX2 i hi) (hX2 j hj)
  simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
  rw [integral_finset_sum s (fun i hi' => integrable_finset_sum s (fun j hj => hi i hi' j hj))]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finset_sum s (fun j hj => hi i hi' j hj)]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact ho i hi' j hj hji.symm
  · intro hn
    exact False.elim (hn hi')

/-- The stopped-tree energy inequality on any probability space. The
martingale term retains its coefficient without the gradient-move count q. -/
theorem integral_tree_energy {ι t : Type*} [Fintype ι] [Fintype t] [DecidableEq t]
    (I : ι → Finset t) (q L : ℕ) (a m : t → Ω → E)
    (ha : ∀ k, Integrable (a k) μ) (hm : ∀ k, Integrable (m k) μ)
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) μ)
    (hm2 : ∀ k, Integrable (fun w => ‖m k w‖^2) μ)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪m i w,m j w⟫_ℝ ∂μ) = 0)
    (hL : ∀ k, (Finset.univ.filter (fun i => k ∈ I i)).card ≤ L) :
    (∫ w, ∑ i, ‖∑ k ∈ I i, (a k w+m k w)‖^2 ∂μ) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ)+(∫ w, ∑ k, ‖m k w‖^2 ∂μ)) := by
  classical
  have hv (k : t) : Integrable (fun w => a k w+m k w) μ := (ha k).add (hm k)
  have hv2 (k : t) : Integrable (fun w => ‖a k w+m k w‖^2) μ :=
    integrable_norm_add_sq (ha k) (hm k) (ha2 k) (hm2 k)
  have hnodeI (i : ι) := integrable_norm_sum_sq (I i) (fun k w => a k w+m k w)
    (fun k _ => hv k) (fun k _ => hv2 k)
  have hnode (i : ι) :
      (∫ w, ‖∑ k ∈ I i, (a k w+m k w)‖^2 ∂μ) ≤
        2*(q : ℝ)*(∑ k ∈ I i, ∫ w, ‖a k w‖^2 ∂μ)+
        2*(∑ k ∈ I i, ∫ w, ‖m k w‖^2 ∂μ) := by
    have hAi := integrable_finset_sum (I i) (fun k _ => ha2 k)
    have hMi := integrable_norm_sum_sq (I i) m (fun k _ => hm k) (fun k _ => hm2 k)
    have hpoint (w : Ω) : ‖∑ k ∈ I i, (a k w+m k w)‖^2 ≤
        2*(q : ℝ)*(∑ k ∈ I i, ‖a k w‖^2)+2*‖∑ k ∈ I i, m k w‖^2 := by
      rw [Finset.sum_add_distrib]
      have hd := sparse_drift_energy (I i) (fun k => a k w) q
        ((Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hs w))
      have hh := norm_add_sq_le_twice (∑ k ∈ I i, a k w) (∑ k ∈ I i, m k w)
      linarith
    have h := integral_mono (hnodeI i) ((hAi.const_mul (2*(q : ℝ))).add (hMi.const_mul 2)) hpoint
    simp only [Pi.add_apply] at h
    rw [integral_add (hAi.const_mul _) (hMi.const_mul _), integral_const_mul, integral_const_mul,
      integral_finset_sum (I i) (fun k _ => ha2 k),
      integral_orthogonal_sum_sq (I i) m (fun k _ => hm k) (fun k _ => hm2 k)
        (fun j _ k _ hjk => ho j k hjk)] at h
    exact h
  rw [integral_finset_sum Finset.univ (fun i _ => hnodeI i)]
  have hd := bounded_overlap_sum I L hL (fun k => ∫ w, ‖a k w‖^2 ∂μ)
    (fun k => integral_nonneg (fun _ => sq_nonneg _))
  have hM := bounded_overlap_sum I L hL (fun k => ∫ w, ‖m k w‖^2 ∂μ)
    (fun k => integral_nonneg (fun _ => sq_nonneg _))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hnode i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [integral_finset_sum Finset.univ (fun k _ => ha2 k),
    integral_finset_sum Finset.univ (fun k _ => hm2 k)]
  simp only [Finset.sum_add_distrib]
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*(q : ℝ)),
    mul_le_mul_of_nonneg_left hM (by norm_num : (0:ℝ) ≤ 2)]

theorem integral_dyadic_energy (M L q : ℕ) (a m : Fin M → Ω → E)
    (ha : ∀ k, Integrable (a k) μ) (hm : ∀ k, Integrable (m k) μ)
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) μ)
    (hm2 : ∀ k, Integrable (fun w => ‖m k w‖^2) μ)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪m i w,m j w⟫_ℝ ∂μ) = 0) :
    (∫ w, ∑ i : Fin L × Fin M, ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2 ∂μ) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ)+(∫ w, ∑ k, ‖m k w‖^2 ∂μ)) :=
  integral_tree_energy _ q L a m ha hm ha2 hm2 hs ho dyadic_overlap

/-- Future-dependent selection is handled pointwise before integration.
No orthogonality is asserted after conditioning on the selected nodes. -/
theorem integral_selected_dyadic_energy (M L q : ℕ) (a m : Fin M → Ω → E)
    (created : Ω → Fin L × Fin M → Prop) [∀ w i, Decidable (created w i)]
    (hc : ∀ i, MeasurableSet {w | created w i})
    (ha : ∀ k, Integrable (a k) μ) (hm : ∀ k, Integrable (m k) μ)
    (ha2 : ∀ k, Integrable (fun w => ‖a k w‖^2) μ)
    (hm2 : ∀ k, Integrable (fun w => ‖m k w‖^2) μ)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q)
    (ho : ∀ i j, i ≠ j → (∫ w, ⟪m i w,m j w⟫_ℝ ∂μ) = 0) :
    (∫ w, ∑ i : Fin L × Fin M, if created w i then
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2 else 0 ∂μ) ≤
      2*(L : ℝ)*((q : ℝ)*(∫ w, ∑ k, ‖a k w‖^2 ∂μ)+(∫ w, ∑ k, ‖m k w‖^2 ∂μ)) := by
  have hi (i : Fin L × Fin M) :
      Integrable (fun w => ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2) μ :=
    integrable_norm_sum_sq _ _ (fun k _ => (ha k).add (hm k))
      (fun k _ => integrable_norm_add_sq (ha k) (hm k) (ha2 k) (hm2 k))
  have hsi (i : Fin L × Fin M) : Integrable (fun w => if created w i then
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+m k w)‖^2 else 0) μ := by
    apply ((hi i).indicator (hc i)).congr
    filter_upwards with w
    by_cases hw : created w i
    · rw [Set.indicator_of_mem (show w ∈ {w | created w i} from hw), if_pos hw]
    · rw [Set.indicator_of_not_mem (show w ∉ {w | created w i} from hw), if_neg hw]
  apply le_trans (integral_mono (integrable_finset_sum Finset.univ (fun i _ => hsi i))
    (integrable_finset_sum Finset.univ (fun i _ => hi i)) ?_)
    (integral_dyadic_energy M L q a m ha hm ha2 hm2 hs ho)
  intro w
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> simp [sq_nonneg]

end SecondOrder
