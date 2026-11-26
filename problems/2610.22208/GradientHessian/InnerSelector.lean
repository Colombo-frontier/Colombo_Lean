import GradientHessian.Profiles
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Exact finite stick breaking, with first derivative restrictions at the
flat endpoints. No neighborhood plateau assumption is made at an endpoint. -/

noncomputable section
namespace GradientHessian.InnerSelector

def select : (m : ℕ) → (Fin m → ℝ) → (Fin m → ℝ) → ℝ
  | 0, _, _ => 0
  | m + 1, p, e => (1 - p 0) * e 0 + p 0 * select m (fun i => p i.succ) (fun i => e i.succ)

def weight {m : ℕ} (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  (1 - p i) * ∏ j : Fin m, if j < i then p j else 1

theorem weight_zero (m : ℕ) (p : Fin (m + 1) → ℝ) : weight p 0 = 1 - p 0 := by
  simp [weight]

theorem weight_succ (m : ℕ) (p : Fin (m + 1) → ℝ) (i : Fin m) :
    weight p i.succ = p 0 * weight (fun j => p j.succ) i := by
  simp only [weight, Fin.prod_univ_succ, Fin.succ_lt_succ_iff]
  have hi : (0 : Fin (m + 1)) < i.succ := by simp
  rw [if_pos hi]
  ring

/-- The recursive scalar is literally the manuscript's finite weighted sum. -/
theorem select_eq_weighted_sum (m : ℕ) (p e : Fin m → ℝ) :
    select m p e = ∑ i, weight p i * e i := by
  induction m with
  | zero => simp [select]
  | succ m ih =>
    rw [select, ih, Fin.sum_univ_succ, weight_zero]
    simp_rw [weight_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem select_bounds (m : ℕ) (p e : Fin m → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (he : ∀ i, e i ∈ Set.Icc (0 : ℝ) C) :
    select m p e ∈ Set.Icc (0 : ℝ) C := by
  induction m with
  | zero => simpa [select] using hC
  | succ m ih =>
    have ht := ih (fun i => p i.succ) (fun i => e i.succ) (fun i => hp i.succ) (fun i => he i.succ)
    have h0 := hp 0
    have he0 := he 0
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr h0.2) he0.1) (mul_nonneg h0.1 ht.1)
    · have h1 := mul_le_mul_of_nonneg_left he0.2 (sub_nonneg.mpr h0.2)
      have h2 := mul_le_mul_of_nonneg_left ht.2 h0.1
      dsimp [select]
      nlinarith

theorem select_head_one (m : ℕ) (p e : Fin (m + 1) → ℝ) (hp : p 0 = 1) :
    select (m + 1) p e = select m (fun i => p i.succ) (fun i => e i.succ) := by
  simp [select, hp]

theorem select_head_zero (m : ℕ) (p e : Fin (m + 1) → ℝ) (hp : p 0 = 0) :
    select (m + 1) p e = e 0 := by simp [select, hp]

theorem select_all_one (m : ℕ) (p e : Fin m → ℝ) (hp : ∀ i, p i = 1) :
    select m p e = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [select_head_one m p e (hp 0)]; exact ih _ _ (fun i => hp i.succ)

theorem select_update_first (m : ℕ) (p e : Fin m → ℝ) (i : Fin m)
    (hprev : ∀ j, j < i → p j = 1) (t : ℝ) :
    select m (Function.update p i t) e =
      (1 - t) * e i + t * select m (Function.update p i 1) e := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    revert hprev
    refine Fin.cases (fun hprev => ?_) (fun j hprev => ?_) i
    · simp [select, Function.update]
    · have hhead : p 0 = 1 := hprev 0 (by simp)
      have ht (z : ℝ) : (fun l : Fin m => Function.update p j.succ z l.succ) =
          Function.update (fun l : Fin m => p l.succ) j z := by
        funext l
        simp [Function.update, Fin.succ_inj]
      have hzero (z : ℝ) : Function.update p j.succ z 0 = 1 := by
        rw [Function.update_of_ne (ne_of_lt (show (0 : Fin (m + 1)) < j.succ by simp)), hhead]
      rw [select_head_one m _ _ (hzero t), select_head_one m _ _ (hzero 1), ht t, ht 1]
      exact ih _ _ j (fun l hl => hprev l.succ (Fin.succ_lt_succ_iff.mpr hl))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem endpoint_fderiv_zero (f : F → ℝ) (x : F) (hb : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (hx : f x = 0 ∨ f x = 1) : fderiv ℝ f x = 0 := by
  rcases hx with hx | hx
  · apply IsLocalMin.fderiv_eq_zero
    exact Filter.Eventually.of_forall (fun y => by simpa [hx] using (hb y).1)
  · apply IsLocalMax.fderiv_eq_zero
    exact Filter.Eventually.of_forall (fun y => by simpa [hx] using (hb y).2)

theorem select_contDiff (m : ℕ) (p e : Fin m → F → ℝ) {n : WithTop ℕ∞}
    (hp : ∀ i, ContDiff ℝ n (p i)) (he : ∀ i, ContDiff ℝ n (e i)) :
    ContDiff ℝ n (fun x => select m (fun i => p i x) (fun i => e i x)) := by
  induction m with
  | zero => exact contDiff_const
  | succ m ih =>
    exact ((contDiff_const.sub (hp 0)).mul (he 0)).add
      ((hp 0).mul (ih _ _ (fun i => hp i.succ) (fun i => he i.succ)))

theorem select_hasFDerivAt_head_one (m : ℕ) (p e : Fin (m + 1) → F → ℝ) (x : F)
    (hp : HasFDerivAt (p 0) (0 : F →L[ℝ] ℝ) x) (hp1 : p 0 x = 1)
    (he : DifferentiableAt ℝ (e 0) x)
    {L : F →L[ℝ] ℝ}
    (ht : HasFDerivAt (fun y => select m (fun i => p i.succ y) (fun i => e i.succ y)) L x) :
    HasFDerivAt (fun y => select (m + 1) (fun i => p i y) (fun i => e i y)) L x := by
  convert (((hasFDerivAt_const (1 : ℝ) x).sub hp).mul he.hasFDerivAt).add (hp.mul ht) using 1
  simp [select, hp1]

theorem select_hasFDerivAt_head_zero (m : ℕ) (p e : Fin (m + 1) → F → ℝ) (x : F)
    (hp : HasFDerivAt (p 0) (0 : F →L[ℝ] ℝ) x) (hp0 : p 0 x = 0)
    {L : F →L[ℝ] ℝ} (he : HasFDerivAt (e 0) L x)
    (ht : DifferentiableAt ℝ (fun y => select m (fun i => p i.succ y) (fun i => e i.succ y)) x) :
    HasFDerivAt (fun y => select (m + 1) (fun i => p i y) (fun i => e i y)) L x := by
  convert (((hasFDerivAt_const (1 : ℝ) x).sub hp).mul he).add (hp.mul ht.hasFDerivAt) using 1
  simp [select, hp0]

theorem select_fderiv_first_zero (m : ℕ) (p e : Fin m → F → ℝ) (x : F)
    (hp : ∀ i, ContDiff ℝ 1 (p i)) (he : ∀ i, ContDiff ℝ 1 (e i))
    (hb : ∀ i y, p i y ∈ Set.Icc (0 : ℝ) 1) (i : Fin m)
    (hprev : ∀ j, j < i → p j x = 1) (hi : p i x = 0) :
    fderiv ℝ (fun y => select m (fun j => p j y) (fun j => e j y)) x = fderiv ℝ (e i) x := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    revert hprev hi
    refine Fin.cases (fun hprev hi => ?_) (fun j hprev hi => ?_) i
    · have hp0 : HasFDerivAt (p 0) (0 : F →L[ℝ] ℝ) x := by
        convert ((hp 0).differentiable (by norm_num) x).hasFDerivAt using 1
        exact (endpoint_fderiv_zero (p 0) x (hb 0) (Or.inl hi)).symm
      exact (select_hasFDerivAt_head_zero m p e x hp0 hi
        ((he 0).differentiable (by norm_num) x).hasFDerivAt
        ((select_contDiff m _ _ (fun j => hp j.succ) (fun j => he j.succ)).differentiable
          (by norm_num) x)).fderiv
    · have hp1 : p 0 x = 1 := hprev 0 (by simp)
      have hp0 : HasFDerivAt (p 0) (0 : F →L[ℝ] ℝ) x := by
        convert ((hp 0).differentiable (by norm_num) x).hasFDerivAt using 1
        exact (endpoint_fderiv_zero (p 0) x (hb 0) (Or.inr hp1)).symm
      have htail := ih (fun j => p j.succ) (fun j => e j.succ)
        (fun j => hp j.succ) (fun j => he j.succ) (fun j => hb j.succ) j
        (fun l hl => hprev l.succ (Fin.succ_lt_succ_iff.mpr hl)) hi
      have hd := ((select_contDiff m _ _ (fun j => hp j.succ) (fun j => he j.succ)).differentiable
        (by norm_num) x).hasFDerivAt
      rw [htail] at hd
      exact (select_hasFDerivAt_head_one m p e x hp0 hp1
        ((he 0).differentiable (by norm_num) x) hd).fderiv

theorem select_fderiv_all_one (m : ℕ) (p e : Fin m → F → ℝ) (x : F)
    (hp : ∀ i, ContDiff ℝ 1 (p i)) (he : ∀ i, ContDiff ℝ 1 (e i))
    (hb : ∀ i y, p i y ∈ Set.Icc (0 : ℝ) 1) (hx : ∀ i, p i x = 1) :
    fderiv ℝ (fun y => select m (fun j => p j y) (fun j => e j y)) x = 0 := by
  induction m with
  | zero => simp [select]
  | succ m ih =>
    have hp0 : HasFDerivAt (p 0) (0 : F →L[ℝ] ℝ) x := by
      convert ((hp 0).differentiable (by norm_num) x).hasFDerivAt using 1
      exact (endpoint_fderiv_zero (p 0) x (hb 0) (Or.inr (hx 0))).symm
    have ht := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ) (fun i => he i.succ) (fun i => hb i.succ) (fun i => hx i.succ)
    have hd := ((select_contDiff m _ _ (fun j => hp j.succ) (fun j => he j.succ)).differentiable
      (by norm_num) x).hasFDerivAt
    rw [ht] at hd
    exact (select_hasFDerivAt_head_one m p e x hp0 (hx 0)
      ((he 0).differentiable (by norm_num) x) hd).fderiv

end GradientHessian.InnerSelector
