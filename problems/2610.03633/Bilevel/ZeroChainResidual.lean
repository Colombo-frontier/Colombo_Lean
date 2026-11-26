import Bilevel.ZeroChainResidualCutoffs

/-!
# Exact tail-mask decomposition of the original finite chain

The unscaled construction is the paper's formula at amplitude and length scale
one. Values, C³ regularity, exact centering, and the single-active-term value
bound are derived from the actual cutoffs and chain profiles.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Bilevel.ZeroChainResidual
open ZeroChain ZeroChainProfiles ZeroChainPotential ZeroChainResidualCutoffs

def component (n : ℕ) (i : Fin (n+1)) : Space n → ℝ :=
  Fin.cases (fun z => -phi (z 0)) (fun j z => edge (z j.castSucc) (z j.succ)) i

def tailEnergy {n : ℕ} (i : Fin (n+1)) (z : Space n) : ℝ :=
  ∑ j : Fin (n+1), if i ≤ j then coordinateCutoff (z j)^2 else 0

def tailMask {n : ℕ} (i : Fin (n+1)) (z : Space n) : ℝ := energyCutoff (tailEnergy i z)

def maskedComponent {n : ℕ} (i : Fin (n+1)) (z : Space n) : ℝ :=
  component n i z*tailMask i z

def rawResidual (n : ℕ) (z : Space n) : ℝ := ∑ i : Fin (n+1), maskedComponent i z
def residual (n : ℕ) (z : Space n) : ℝ := rawResidual n z-rawResidual n 0
def revealed (n : ℕ) (z : Space n) : ℝ := value n z-residual n z

@[simp] theorem component_zero (n : ℕ) (z : Space n) : component n 0 z = -phi (z 0) := rfl
@[simp] theorem component_succ {n : ℕ} (i : Fin n) (z : Space n) :
    component n i.succ z = edge (z i.castSucc) (z i.succ) := rfl

theorem sum_component (n : ℕ) (z : Space n) : (∑ i : Fin (n+1), component n i z) = value n z := by
  rw [Fin.sum_univ_succ]
  rfl

theorem component_contDiff (n : ℕ) (i : Fin (n+1)) : ContDiff ℝ 3 (component n i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ((phi_contDiff 3).comp (EuclideanSpace.proj (𝕜:=ℝ) (0:Fin (n+1))).contDiff).neg
  · exact edge_contDiff j 3

theorem tailEnergy_contDiff {n : ℕ} (i : Fin (n+1)) : ContDiff ℝ 3 (tailEnergy i) := by
  apply ContDiff.sum
  intro j _
  by_cases hij : i ≤ j
  · simp only [if_pos hij]
    exact (coordinateCutoff_contDiff.comp (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff).pow 2
  · simp only [if_neg hij]
    exact contDiff_const

theorem tailMask_contDiff {n : ℕ} (i : Fin (n+1)) : ContDiff ℝ 3 (tailMask i) :=
  energyCutoff_contDiff.comp (tailEnergy_contDiff i)

theorem maskedComponent_contDiff {n : ℕ} (i : Fin (n+1)) : ContDiff ℝ 3 (maskedComponent i) :=
  (component_contDiff n i).mul (tailMask_contDiff i)

theorem rawResidual_contDiff (n : ℕ) : ContDiff ℝ 3 (rawResidual n) :=
  ContDiff.sum (fun i _ => maskedComponent_contDiff i)

theorem residual_contDiff (n : ℕ) : ContDiff ℝ 3 (residual n) :=
  (rawResidual_contDiff n).sub contDiff_const

theorem revealed_contDiff (n : ℕ) : ContDiff ℝ 3 (revealed n) :=
  (value_contDiff n 3).sub (residual_contDiff n)

@[simp] theorem residual_zero (n : ℕ) : residual n 0 = 0 := sub_self _

theorem exact_split (n : ℕ) (z : Space n) : revealed n z+residual n z = value n z := by
  simp [revealed]

theorem tailEnergy_nonneg {n : ℕ} (i : Fin (n+1)) (z : Space n) : 0 ≤ tailEnergy i z := by
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem coordinate_energy_le {n : ℕ} (i j : Fin (n+1)) (z : Space n) (hij : i ≤ j) :
    coordinateCutoff (z j)^2 ≤ tailEnergy i z := by
  have h := Finset.single_le_sum (f:=fun k : Fin (n+1) =>
    if i ≤ k then coordinateCutoff (z k)^2 else 0)
    (fun _ _ => by dsimp only; split_ifs <;> positivity) (Finset.mem_univ j)
  simpa only [if_pos hij] using h

theorem tailMask_range {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    0 ≤ tailMask i z ∧ tailMask i z ≤ 1 := energyCutoff_range _

theorem tailMask_zero_of_large_coordinate {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i ≤ j) (hj : 1/2 ≤ |z j|) : tailMask i z = 0 := by
  apply energyCutoff_zero
  have h := coordinate_energy_le i j z hij
  rw [coordinateCutoff_one hj, one_pow] at h
  exact h

theorem tailEnergy_zero_of_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hz : ∀ j, i ≤ j → |z j| ≤ 1/4) : tailEnergy i z = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hij
  · rw [coordinateCutoff_zero (hz j hij), zero_pow (by norm_num)]
  · rfl

theorem tailMask_one_of_small {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hz : ∀ j, i ≤ j → |z j| ≤ 1/4) : tailMask i z = 1 := by
  rw [tailMask, tailEnergy_zero_of_small i z hz]
  exact energyCutoff_one (by norm_num)

theorem mask_zero_before_nonzero_component {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hij : i < j) (hj : component n j z ≠ 0) : tailMask i z = 0 := by
  revert hij hj
  refine Fin.cases ?_ (fun k => ?_) j
  · intro hij _
    exact (Fin.not_lt_zero i hij).elim
  · intro hij hj
    have hk : 1/2 < |z k.castSucc| := by
      by_contra! hk
      exact hj (edge_inactive _ _ hk)
    apply tailMask_zero_of_large_coordinate i k.castSucc z ?_ hk.le
    change i.val ≤ k.val
    have h : i.val < k.val+1 := hij
    omega

theorem masked_components_exclusive {n : ℕ} (z : Space n) (i j : Fin (n+1))
    (hij : i ≠ j) (hi : maskedComponent i z ≠ 0) : maskedComponent j z = 0 := by
  have hi0 := (mul_ne_zero_iff.mp hi).1
  have hi1 := (mul_ne_zero_iff.mp hi).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · by_contra hj
    have hj0 := (mul_ne_zero_iff.mp hj).1
    exact hi1 (mask_zero_before_nonzero_component i j z hlt hj0)
  · rw [maskedComponent, mask_zero_before_nonzero_component j i z hgt hi0, mul_zero]

def componentBound : ℝ := (1+2*Real.exp 1)*phiBound

theorem componentBound_nonneg : 0 ≤ componentBound :=
  mul_nonneg (by positivity) phiBound_nonneg

theorem component_abs_bound (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    |component n i z| ≤ componentBound := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [component_zero, abs_neg, abs_of_nonneg (phi_nonneg _)]
    have h := phi_bounded (z 0)
    change phi (z 0) ≤ phiBound at h
    dsimp [componentBound]
    nlinarith [mul_nonneg (Real.exp_pos 1).le phiBound_nonneg]
  · have h := edge_abs_bound (z j.castSucc) (z j.succ)
    change |edge (z j.castSucc) (z j.succ)| ≤ componentBound
    dsimp [componentBound]
    nlinarith [phiBound_nonneg]

theorem maskedComponent_abs_bound {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    |maskedComponent i z| ≤ componentBound := by
  rw [maskedComponent, abs_mul, abs_of_nonneg (tailMask_range i z).1]
  exact (mul_le_mul (component_abs_bound n i z) (tailMask_range i z).2
    (tailMask_range i z).1 componentBound_nonneg).trans_eq (mul_one _)

theorem sum_abs_le_of_exclusive {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ i, |f i| ≤ B)
    (he : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : |∑ i, f i| ≤ B := by
  by_cases hf : ∃ i, f i ≠ 0
  · obtain ⟨i,hi⟩ := hf
    rw [Finset.sum_eq_single i]
    · exact hb i
    · intro j _ hji
      exact he i j hji.symm hi
    · simp
  · have hz : ∀ i, f i = 0 := by simpa only [not_exists, not_not] using hf
    simp only [hz, Finset.sum_const_zero, abs_zero]
    exact hB

/-- Unlike the chain, the residual value is bounded independently of its
length because at most one masked component is nonzero. -/
theorem rawResidual_abs_bound (n : ℕ) (z : Space n) : |rawResidual n z| ≤ componentBound :=
  sum_abs_le_of_exclusive (fun i => maskedComponent i z) componentBound componentBound_nonneg
    (fun i => maskedComponent_abs_bound i z) (masked_components_exclusive z)

theorem residual_abs_bound (n : ℕ) (z : Space n) : |residual n z| ≤ 2*componentBound := by
  exact (abs_sub _ _).trans (by linarith [rawResidual_abs_bound n z, rawResidual_abs_bound n 0])

end Bilevel.ZeroChainResidual
