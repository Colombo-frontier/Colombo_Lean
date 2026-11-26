import SampleReuse.ReverseStickThirdOrthogonality
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Length-independent energy bounds for fixed-degree score polynomials. -/

open SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section
variable {ι : Type*}

theorem subsetProductSum_insert (a : ι → ℝ) (s : Finset ι) (i : ι)
    (hi : i ∉ s) (n : ℕ) :
    (∑ t ∈ (insert i s).powersetCard (n + 1), ∏ j ∈ t, a j) =
      (∑ t ∈ s.powersetCard (n + 1), ∏ j ∈ t, a j) +
        a i * ∑ t ∈ s.powersetCard n, ∏ j ∈ t, a j := by
  have hnot {t : Finset ι} {k : ℕ} (ht : t ∈ s.powersetCard k) : i ∉ t :=
    fun hit => hi ((Finset.mem_powersetCard.mp ht).1 hit)
  have hd : Disjoint (s.powersetCard (n + 1)) ((s.powersetCard n).image (insert i)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    exact hnot ht (Finset.mem_insert_self i r)
  rw [Finset.powersetCard_succ_insert hi n, Finset.sum_union hd,
    Finset.sum_image, Finset.mul_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.prod_insert (hnot ht)]
  · intro t ht r hr he
    have hh := congrArg (fun v : Finset ι => v.erase i) he
    simpa only [Finset.erase_insert (hnot ht), Finset.erase_insert (hnot hr)] using hh

/-- A degree-n elementary subset sum is bounded by the nth power of the
sum of nonnegative entries. This intentionally uses a loose constant one;
it suffices for length-independent third-order bounds. -/
theorem subsetProductSum_le_sum_pow (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (s : Finset ι) (n : ℕ) :
    (∑ t ∈ s.powersetCard n, ∏ i ∈ t, a i) ≤ (∑ i ∈ s, a i) ^ n := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp
    | succ n =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert i s hi ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [subsetProductSum_insert a s i hi n, Finset.sum_insert hi]
      have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg (fun j _ => ha j)
      calc
        _ ≤ (∑ j ∈ s, a j) ^ (n + 1) + a i * (∑ j ∈ s, a j) ^ n :=
          add_le_add (ih (n + 1)) (mul_le_mul_of_nonneg_left (ih n) (ha i))
        _ = (a i + ∑ j ∈ s, a j) * (∑ j ∈ s, a j) ^ n := by ring
        _ ≤ (a i + ∑ j ∈ s, a j) * (a i + ∑ j ∈ s, a j) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs (le_add_of_nonneg_left (ha i)) n)
            (add_nonneg (ha i) hs)
        _ = _ := by ring

variable [Fintype ι]

/-- A score polynomial whose subset coefficient is bounded by K times a
product of directional magnitudes has energy at most K² times total Fisher
energy to the degree. This covers degree three with a universal K. -/
theorem score_subset_energy_le
    (p a : ι → ℝ) (hp0 : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1)
    (n : ℕ) (c : Finset ι → ℝ) {K : ℝ}
    (hc : ∀ s ∈ Finset.univ.powersetCard n, |c s| ≤ K * ∏ i ∈ s, |a i|) :
    (∑ s ∈ Finset.univ.powersetCard n,
        c s ^ 2 * ∏ i ∈ s, (1 / (p i * (1 - p i)))) ≤
      K ^ 2 * bernoulliFisherEnergy p a ^ n := by
  have hv (i : ι) : 0 ≤ 1 / (p i * (1 - p i)) :=
    (one_div_pos.mpr (mul_pos (hp0 i) (sub_pos.mpr (hp1 i)))).le
  have he (s : Finset ι) :
      (∏ i ∈ s, |a i|) ^ 2 * (∏ i ∈ s, (1 / (p i * (1 - p i)))) =
        ∏ i ∈ s, (a i ^ 2 / (p i * (1 - p i))) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [sq_abs, div_eq_mul_inv, one_mul]
  calc
    _ ≤ ∑ s ∈ Finset.univ.powersetCard n,
        K ^ 2 * ∏ i ∈ s, (a i ^ 2 / (p i * (1 - p i))) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsq := mul_self_le_mul_self (abs_nonneg (c s)) (hc s hs)
      have hsq' : c s ^ 2 ≤ K ^ 2 * (∏ i ∈ s, |a i|) ^ 2 := by
        simpa only [← pow_two, sq_abs, mul_pow] using hsq
      have hh := mul_le_mul_of_nonneg_right hsq'
        (show 0 ≤ ∏ i ∈ s, (1 / (p i * (1 - p i))) from
          Finset.prod_nonneg (fun i _ => hv i))
      simpa only [mul_assoc, he] using hh
    _ = K ^ 2 * ∑ s ∈ Finset.univ.powersetCard n,
        ∏ i ∈ s, (a i ^ 2 / (p i * (1 - p i))) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (subsetProductSum_le_sum_pow (fun i => a i ^ 2 / (p i * (1 - p i)))
        (fun i => div_nonneg (sq_nonneg _) (mul_pos (hp0 i) (sub_pos.mpr (hp1 i))).le)
        Finset.univ n) (sq_nonneg K)

end
end SampleReuse
