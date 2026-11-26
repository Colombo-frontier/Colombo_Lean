import Bilevel.ZeroChainFlatteningBounds

/-! Residuals with unchanged predecessor gates and arbitrary child profiles. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainChildProfiles
open ZeroChain ZeroChainProfiles ZeroChainPotential ZeroChainResidualCutoffs ZeroChainResidual
  ZeroChainResidualBounds ZeroChainFlatteningCutoff ZeroChainFlatteningMap

def childComponent (n : ℕ) (p m : ℝ → ℝ) (i : Fin (n+1)) : Space n → ℝ :=
  Fin.cases (fun z => -p (z 0))
    (fun j z => psi (-z j.castSucc)*m (z j.succ)-psi (z j.castSucc)*p (z j.succ)) i

def maskedChild {n : ℕ} (p m : ℝ → ℝ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  childComponent n p m i z*tailMask i z

def rawChild (n : ℕ) (p m : ℝ → ℝ) (z : Space n) : ℝ := ∑ i : Fin (n+1), maskedChild p m i z

theorem childComponent_contDiff (n : ℕ) {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i : Fin (n+1)) : ContDiff ℝ 3 (childComponent n p m i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (hp.comp (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1))).contDiff).neg
  · exact (((psi_contDiff (n:=3)).comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff.neg).mul
      (hm.comp (EuclideanSpace.proj (𝕜:=ℝ) j.succ).contDiff)).sub
      (((psi_contDiff (n:=3)).comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff).mul
      (hp.comp (EuclideanSpace.proj (𝕜:=ℝ) j.succ).contDiff))

theorem maskedChild_contDiff {n : ℕ} {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m)
    (i : Fin (n+1)) : ContDiff ℝ 3 (maskedChild p m i) :=
  (childComponent_contDiff n hp hm i).mul (tailMask_contDiff i)

theorem rawChild_contDiff (n : ℕ) {p m : ℝ → ℝ} (hp : ContDiff ℝ 3 p) (hm : ContDiff ℝ 3 m) :
    ContDiff ℝ 3 (rawChild n p m) := ContDiff.sum (fun i _ => maskedChild_contDiff hp hm i)

theorem childComponent_inactive {n : ℕ} (p m : ℝ → ℝ) (i : Fin n) (z : Space n)
    (hz : |z i.castSucc| ≤ 1/2) : childComponent n p m i.succ z = 0 := by
  change psi (-z i.castSucc)*m (z i.succ)-psi (z i.castSucc)*p (z i.succ) = 0
  rw [psi_zero_of_le (by linarith [(abs_le.mp hz).1]), psi_zero_of_le (abs_le.mp hz).2]
  ring

theorem mask_zero_before_child {n : ℕ} (p m : ℝ → ℝ) (i j : Fin (n+1)) (z : Space n)
    (hij : i < j) (hj : childComponent n p m j z ≠ 0) : tailMask i z = 0 := by
  revert hij hj
  refine Fin.cases ?_ (fun l => ?_) j
  · intro hij _
    exact (Fin.not_lt_zero i hij).elim
  · intro hij hj
    have hl : 1/2 < |z l.castSucc| := by
      by_contra! hh
      exact hj (childComponent_inactive p m l z hh)
    apply tailMask_zero_of_large_coordinate i l.castSucc z ?_ hl.le
    change i.val ≤ l.val
    have hh : i.val < l.val+1 := hij
    omega

theorem maskedChild_exclusive {n : ℕ} (p m : ℝ → ℝ) (z : Space n) (i j : Fin (n+1))
    (hij : i ≠ j) (hi : maskedChild p m i z ≠ 0) : maskedChild p m j z = 0 := by
  have hi0 := (mul_ne_zero_iff.mp hi).1
  have hi1 := (mul_ne_zero_iff.mp hi).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · by_contra hj
    exact hi1 (mask_zero_before_child p m i j z hlt (mul_ne_zero_iff.mp hj).1)
  · rw [maskedChild, mask_zero_before_child p m j i z hgt hi0, mul_zero]

theorem childComponent_abs_bound (n : ℕ) (p m : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ t, |p t| ≤ B) (hm : ∀ t, |m t| ≤ B) (i : Fin (n+1)) (z : Space n) :
    |childComponent n p m i z| ≤ (1+2*Real.exp 1)*B := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change |-p (z 0)| ≤ _
    rw [abs_neg]
    exact (hp _).trans (by nlinarith [mul_nonneg (Real.exp_pos 1).le hB])
  · change |psi (-z j.castSucc)*m (z j.succ)-psi (z j.castSucc)*p (z j.succ)| ≤ _
    have h0 : |psi (-z j.castSucc)*m (z j.succ)| ≤ Real.exp 1*B := by
      rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
      exact mul_le_mul (psi_le_exp_one _) (hm _) (abs_nonneg _) (Real.exp_pos 1).le
    have h1 : |psi (z j.castSucc)*p (z j.succ)| ≤ Real.exp 1*B := by
      rw [abs_mul, abs_of_nonneg (psi_nonneg _)]
      exact mul_le_mul (psi_le_exp_one _) (hp _) (abs_nonneg _) (Real.exp_pos 1).le
    exact (abs_sub _ _).trans (by linarith)

theorem rawChild_abs_bound (n : ℕ) (p m : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ t, |p t| ≤ B) (hm : ∀ t, |m t| ≤ B) (z : Space n) :
    |rawChild n p m z| ≤ (1+2*Real.exp 1)*B := by
  apply sum_abs_le_of_exclusive _ _ (by positivity) _ (maskedChild_exclusive p m z)
  intro i
  rw [maskedChild, abs_mul, abs_of_nonneg (tailMask_range i z).1]
  exact (mul_le_mul (childComponent_abs_bound n p m B hB hp hm i z)
    (tailMask_range i z).2 (tailMask_range i z).1 (by positivity)).trans_eq (mul_one _)

theorem childComponent_sub (n : ℕ) (p m p' m' : ℝ → ℝ) (i : Fin (n+1)) (z : Space n) :
    childComponent n p m i z-childComponent n p' m' i z =
      childComponent n (fun t => p t-p' t) (fun t => m t-m' t) i z := by
  refine Fin.cases ?_ (fun j => ?_) i <;> dsimp [childComponent] <;> ring

theorem rawChild_sub (n : ℕ) (p m p' m' : ℝ → ℝ) (z : Space n) :
    rawChild n p m z-rawChild n p' m' z =
      rawChild n (fun t => p t-p' t) (fun t => m t-m' t) z := by
  rw [rawChild, rawChild, rawChild, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [maskedChild, maskedChild, maskedChild, ← sub_mul, childComponent_sub]

theorem rawResidual_eq_rawChild (n : ℕ) (z : Space n) :
    rawResidual n z = rawChild n phi (fun t => phi (-t)) z := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1

theorem small_changed_coordinate {δ : ℝ} (hδ : δ ≤ 1/16) {t : ℝ} (ht : |t| < 2*δ) :
    |t| ≤ 1/4 ∧ |flatten δ t| ≤ 1/4 := by
  have h : |t| ≤ 1/4 := by linarith
  exact ⟨h,(flatten_abs_le δ t).trans h⟩

theorem coordinateCutoff_flatten_eq {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16) (t : ℝ) :
    coordinateCutoff (flatten δ t) = coordinateCutoff t := by
  by_cases ht : 2*δ ≤ |t|
  · rw [flatten_identity hδ ht]
  · have hh := small_changed_coordinate hsmall (lt_of_not_ge ht)
    rw [coordinateCutoff_zero hh.1, coordinateCutoff_zero hh.2]

theorem psi_flatten_eq {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16) (t : ℝ) :
    psi (flatten δ t) = psi t := by
  by_cases ht : 2*δ ≤ |t|
  · rw [flatten_identity hδ ht]
  · have hh := small_changed_coordinate hsmall (lt_of_not_ge ht)
    rw [psi_zero_of_le (by linarith [(abs_le.mp hh.2).2]), psi_zero_of_le (by linarith [(abs_le.mp hh.1).2])]

theorem psi_neg_flatten_eq {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16) (t : ℝ) :
    psi (-flatten δ t) = psi (-t) := by
  by_cases ht : 2*δ ≤ |t|
  · rw [flatten_identity hδ ht]
  · have hh := small_changed_coordinate hsmall (lt_of_not_ge ht)
    rw [psi_zero_of_le (by linarith [(abs_le.mp hh.2).1]), psi_zero_of_le (by linarith [(abs_le.mp hh.1).1])]

theorem tailMask_flattenMap_eq {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) : tailMask i (flattenMap n δ z) = tailMask i z := by
  simp only [tailMask, tailEnergy, flattenMap, coordinateMap_apply, coordinateCutoff_flatten_eq hδ hsmall]

theorem rawResidual_flattenMap_eq {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/16)
    (n : ℕ) (z : Space n) : rawResidual n (flattenMap n δ z) =
      rawChild n (fun t => phi (flatten δ t)) (fun t => phi (-flatten δ t)) z := by
  apply Finset.sum_congr rfl
  intro i _
  rw [maskedComponent, maskedChild, tailMask_flattenMap_eq hδ hsmall]
  congr 1
  refine Fin.cases rfl (fun j => ?_) i
  change psi (-flatten δ (z j.castSucc))*phi (-flatten δ (z j.succ))-
    psi (flatten δ (z j.castSucc))*phi (flatten δ (z j.succ)) = _
  rw [psi_flatten_eq hδ hsmall, psi_neg_flatten_eq hδ hsmall]
  rfl

end Bilevel.ZeroChainChildProfiles
