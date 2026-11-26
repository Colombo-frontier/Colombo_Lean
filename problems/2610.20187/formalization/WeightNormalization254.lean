import NumericalPrimitives254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Normalization is stable uniformly in the number of experts and in
individual weights, including zero weights. -/
theorem normalized_weight_error {ι : Type*} [Fintype ι]
    (w : ProbabilityWeights ι) (e r : ι → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1/4)
    (he : ∀ i, 1/2 ≤ e i) (herr : ∀ i, |r i-e i| ≤ ε) (i : ι) :
    let Z := ∑ j,w.weight j*e j
    let R := ∑ j,w.weight j*r j
    0 < R ∧ 0 ≤ w.weight i*r i/R ∧ w.weight i*r i/R ≤ 1 ∧
      |w.weight i*r i/R-w.weight i*e i/Z| ≤ 4*ε := by
  classical
  let Z := ∑ j,w.weight j*e j
  let R := ∑ j,w.weight j*r j
  have hr : ∀ j,1/4 ≤ r j := by
    intro j
    have hh := abs_le.mp (herr j)
    linarith [he j]
  have hZ : 1/2 ≤ Z := by
    calc
      _ = ∑ j,w.weight j*(1/2) := by rw [← Finset.sum_mul,w.total]; ring
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (he j) (w.nonneg j))
  have hR : 1/4 ≤ R := by
    calc
      _ = ∑ j,w.weight j*(1/4) := by rw [← Finset.sum_mul,w.total]; ring
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hr j) (w.nonneg j))
  have hR0 : 0 < R := by linarith
  have hZ0 : 0 < Z := by linarith
  have hsum : |R-Z| ≤ ε := by
    calc
      _ = |∑ j,w.weight j*(r j-e j)| := by congr 1; simp [R,Z,mul_sub,Finset.sum_sub_distrib]
      _ ≤ ∑ j,|w.weight j*(r j-e j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j,w.weight j*ε := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (w.nonneg j)]
        exact mul_le_mul_of_nonneg_left (herr j) (w.nonneg j)
      _ = ε := by rw [← Finset.sum_mul,w.total,one_mul]
  let a := w.weight i*r i/R
  have ha0 : 0 ≤ a := div_nonneg (mul_nonneg (w.nonneg i) (by linarith [hr i])) hR0.le
  have ha1 : a ≤ 1 := by
    apply (div_le_one hR0).mpr
    exact Finset.single_le_sum (fun j _ => mul_nonneg (w.nonneg j) (by linarith [hr j])) (Finset.mem_univ i)
  refine ⟨hR0,ha0,ha1,?_⟩
  have hid : a-w.weight i*e i/Z=(w.weight i*(r i-e i)+a*(Z-R))/Z := by
    dsimp [a]
    field_simp
    ring
  have hnum : |w.weight i*(r i-e i)+a*(Z-R)| ≤ 2*ε := by
    calc
      _ ≤ |w.weight i*(r i-e i)|+|a*(Z-R)| := abs_add_le _ _
      _ = w.weight i*|r i-e i|+a*|R-Z| := by rw [abs_mul,abs_mul,abs_of_nonneg (w.nonneg i),abs_of_nonneg ha0,abs_sub_comm Z R]
      _ ≤ w.weight i*ε+a*ε := add_le_add
        (mul_le_mul_of_nonneg_left (herr i) (w.nonneg i)) (mul_le_mul_of_nonneg_left hsum ha0)
      _ ≤ 2*ε := by nlinarith [w.weight_le_one i]
  change |a-w.weight i*e i/Z| ≤ 4*ε
  rw [hid,abs_div,abs_of_pos hZ0]
  apply (div_le_iff₀ hZ0).mpr
  nlinarith

end Paper254
#print axioms Paper254.normalized_weight_error
