import GradientHessian.InnerSelector

/-! Finite stick breaking with a terminal payload. Exact endpoint first jets
and ordered-tail estimates are valid even at endpoints of flat plateaus. -/

noncomputable section
namespace GradientHessian.FirstHeightSelector

def select : (m : ℕ) → (Fin m → ℝ) → (Fin m → ℝ) → ℝ → ℝ
  | 0, _, _, t => t
  | m + 1, p, e, t => (1 - p 0) * e 0 +
      p 0 * select m (fun i => p i.succ) (fun i => e i.succ) t

theorem select_eq_inner (m : ℕ) (p e : Fin m → ℝ) (t : ℝ) :
    select m p e t = InnerSelector.select m p e + (∏ i, p i) * t := by
  induction m with
  | zero => simp [select, InnerSelector.select]
  | succ m ih => rw [select, ih, InnerSelector.select, Fin.prod_univ_succ]; ring

theorem select_eq_shift (m : ℕ) (p e : Fin m → ℝ) (t : ℝ) :
    select m p e t = t + InnerSelector.select m p (fun i => e i - t) := by
  induction m with
  | zero => simp [select, InnerSelector.select]
  | succ m ih => rw [select, ih, InnerSelector.select]; ring

theorem select_head_one (m : ℕ) (p e : Fin (m + 1) → ℝ) (t : ℝ) (hp : p 0 = 1) :
    select (m + 1) p e t = select m (fun i => p i.succ) (fun i => e i.succ) t := by
  simp [select, hp]

theorem select_all_one (m : ℕ) (p e : Fin m → ℝ) (t : ℝ) (hp : ∀ i, p i = 1) :
    select m p e t = t := by
  rw [select_eq_shift, InnerSelector.select_all_one m _ _ hp, add_zero]

theorem select_constant (m : ℕ) (p : Fin m → ℝ) (t : ℝ) : select m p (fun _ => t) t = t := by
  induction m with
  | zero => rfl
  | succ m ih => rw [select, ih]; ring

theorem select_sub_baseline (m : ℕ) (p e cost : Fin m → ℝ) (a t : ℝ) :
    a + select m p (fun i => e i - a - cost i) t =
      (∏ i, p i) * a + (∑ i, InnerSelector.weight p i * e i) -
        (∑ i, InnerSelector.weight p i * cost i) + (∏ i, p i) * t := by
  have hsum := select_constant m p 1
  rw [select_eq_inner, InnerSelector.select_eq_weighted_sum] at hsum
  simp only [mul_one] at hsum
  have hs : (∑ i, InnerSelector.weight p i) = 1 - ∏ i, p i := by linarith
  rw [select_eq_inner, InnerSelector.select_eq_weighted_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs]
  ring

theorem select_le (m : ℕ) (p e : Fin m → ℝ) (t C : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (he : ∀ i, e i ≤ C) (ht : t ≤ C) :
    select m p e t ≤ C := by
  induction m with
  | zero => exact ht
  | succ m ih =>
    have htail := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ) (fun i => he i.succ)
    have h1 := mul_le_mul_of_nonneg_left (he 0) (sub_nonneg.mpr (hp 0).2)
    have h2 := mul_le_mul_of_nonneg_left htail (hp 0).1
    dsimp [select]
    nlinarith

theorem le_select (m : ℕ) (p e : Fin m → ℝ) (t C : ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (he : ∀ i, C ≤ e i) (ht : C ≤ t) :
    C ≤ select m p e t := by
  induction m with
  | zero => exact ht
  | succ m ih =>
    have htail := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ) (fun i => he i.succ)
    have h1 := mul_le_mul_of_nonneg_left (he 0) (sub_nonneg.mpr (hp 0).2)
    have h2 := mul_le_mul_of_nonneg_left htail (hp 0).1
    dsimp [select]
    nlinarith

theorem select_update_first (m : ℕ) (p e : Fin m → ℝ) (t : ℝ) (i : Fin m)
    (hprev : ∀ j, j < i → p j = 1) (z : ℝ) :
    select m (Function.update p i z) e t =
      (1 - z) * e i + z * select m (Function.update p i 1) e t := by
  simp only [select_eq_shift]
  rw [InnerSelector.select_update_first m p (fun j => e j - t) i hprev z]
  ring

theorem select_after_le (m : ℕ) (p e : Fin m → ℝ) (t C : ℝ) (i : Fin m)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hprev : ∀ j, j ≤ i → p j = 1)
    (he : ∀ j, i < j → e j ≤ C) (ht : t ≤ C) : select m p e t ≤ C := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    revert hprev he
    refine Fin.cases (fun hprev he => ?_) (fun i hprev he => ?_) i
    · rw [select_head_one m p e t (hprev 0 le_rfl)]
      exact select_le m _ _ t C (fun j => hp j.succ) (fun j => he j.succ (by simp)) ht
    · rw [select_head_one m p e t (hprev 0 (by simp))]
      exact ih (fun j => p j.succ) (fun j => e j.succ) i
        (fun j => hp j.succ) (fun j hj => hprev j.succ (Fin.succ_le_succ_iff.mpr hj))
        (fun j hj => he j.succ (Fin.succ_lt_succ_iff.mpr hj))

/-- Later disjoint payload intervals force the tail coefficient to be no
greater than the current payload. This is the source transition sign. -/
theorem ordered_tail (m : ℕ) (p e : Fin m → ℝ) {S : ℝ} (hS : 0 ≤ S) (i : Fin m)
    (hp : ∀ j, p j ∈ Set.Icc (0 : ℝ) 1) (hprev : ∀ j, j < i → p j = 1)
    (he : ∀ j, -((j.val : ℝ) + 1) * S ≤ e j ∧ e j ≤ -(j.val : ℝ) * S) :
    select m (Function.update p i 1) e (-(m : ℝ) * S) ≤ e i := by
  apply select_after_le m _ e _ (e i) i
  · intro j
    by_cases hj : j = i
    · subst j; simp
    · simpa [Function.update_of_ne hj] using hp j
  · intro j hj
    rcases lt_or_eq_of_le hj with hj | hj
    · rw [Function.update_of_ne (ne_of_lt hj), hprev j hj]
    · subst j; simp
  · intro j hij
    have hidx : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    have hmul := mul_le_mul_of_nonneg_right hidx hS
    linarith [(he i).1, (he j).2]
  · have hidx : (i.val : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
    have hmul := mul_le_mul_of_nonneg_right hidx hS
    linarith [(he i).1]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem select_contDiff (m : ℕ) (p e : Fin m → F → ℝ) (t : F → ℝ)
    {n : WithTop ℕ∞} (hp : ∀ i, ContDiff ℝ n (p i)) (he : ∀ i, ContDiff ℝ n (e i))
    (ht : ContDiff ℝ n t) :
    ContDiff ℝ n (fun x => select m (fun i => p i x) (fun i => e i x) (t x)) := by
  simp_rw [select_eq_shift]
  exact ht.add (InnerSelector.select_contDiff m p (fun i x => e i x - t x)
    hp (fun i => (he i).sub ht))

theorem select_fderiv_first_zero (m : ℕ) (p e : Fin m → F → ℝ) (t : F → ℝ) (x : F)
    (hp : ∀ i, ContDiff ℝ 1 (p i)) (he : ∀ i, ContDiff ℝ 1 (e i)) (ht : ContDiff ℝ 1 t)
    (hb : ∀ i y, p i y ∈ Set.Icc (0 : ℝ) 1) (i : Fin m)
    (hprev : ∀ j, j < i → p j x = 1) (hi : p i x = 0) :
    fderiv ℝ (fun y => select m (fun j => p j y) (fun j => e j y) (t y)) x =
      fderiv ℝ (e i) x := by
  simp_rw [select_eq_shift]
  have hsel := InnerSelector.select_fderiv_first_zero m p (fun i y => e i y - t y) x
    hp (fun i => (he i).sub ht) hb i hprev hi
  rw [fderiv_add (ht.differentiable (by norm_num) x)
    ((InnerSelector.select_contDiff m p (fun i y => e i y - t y) hp
      (fun i => (he i).sub ht)).differentiable (by norm_num) x), hsel,
    fderiv_sub ((he i).differentiable (by norm_num) x) (ht.differentiable (by norm_num) x)]
  abel

end GradientHessian.FirstHeightSelector
